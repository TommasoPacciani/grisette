{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.SymPair
-- Copyright   :   (c) Sirui Lu 2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Solver-native symbolic binary products.
module Grisette.Internal.SymPrim.SymPair
  ( SymPair,
    underlyingPairTerm,
    fromPairTerm,
    symItePair,
    pair,
    first,
    second,
  )
where

import Control.DeepSeq (NFData (rnf))
import qualified Data.Binary as Binary
import Data.Bytes.Serial (Serial (deserialize, serialize))
import qualified Data.Serialize as Cereal
import Data.String (IsString (fromString))
import GHC.Generics (Generic)
import Grisette.Internal.Core.Data.Class.Solvable
  ( Solvable (con, conView, sym),
    ssym,
  )
import Grisette.Internal.Internal.Decl.SymPrim.AllSyms
  ( AllSyms (allSymsS),
    SomeSym (SomeSym),
  )
import Grisette.Internal.SymPrim.Prim.Internal.Serialize ()
import Grisette.Internal.SymPrim.Prim.Internal.Term
  ( ConRep (ConType),
    LinkedRep (underlyingTerm, wrapTerm),
    SupportedPrim (pevalITETerm),
    SupportedNonFuncPrim,
    SymRep (SymType),
    Term,
    conTerm,
    pevalFirstTerm,
    pevalPairTerm,
    pevalSecondTerm,
    pformatTerm,
    symTerm,
    typedConstantSymbol,
    pattern ConTerm,
  )
import Language.Haskell.TH.Syntax (Lift)

-- | A solver-native tuple together with its lifetime-bounded semantic view.
--
-- The whole term remains authoritative for equality, hashing, serialization,
-- model operations and solver lowering.  The component pair is deliberately
-- lazy: an opaque tuple or array selection pays for a projection only when it
-- is observed, and every live 'SymPair' pays at most once per side.  Keeping
-- the view here avoids repeating the complete weak-interning lookup at every
-- row lens without retaining either the tuple or its projections globally.
data SymPair a b = SymPair
  { underlyingPairTerm :: !(Term (ConType a, ConType b)),
    pairComponents :: (a, b)
  }
  deriving stock (Generic)

deriving stock instance (Lift a, Lift b) => Lift (SymPair a b)

instance NFData (SymPair a b) where
  rnf = rnf . underlyingPairTerm

-- | Construct a symbolic pair view from an arbitrary solver tuple term.
-- Component projections remain suspended and are shared by every consumer of
-- the resulting value.
fromPairTerm ::
  ( SupportedNonFuncPrim (ConType a),
    SupportedNonFuncPrim (ConType b),
    LinkedRep (ConType a) a,
    LinkedRep (ConType b) b
  ) =>
  Term (ConType a, ConType b) ->
  SymPair a b
fromPairTerm term = SymPair term
  ( wrapTerm (pevalFirstTerm term),
    wrapTerm (pevalSecondTerm term)
  )

-- | Select a solver-native tuple while retaining componentwise views lazily.
-- The two views are extensionally the projections of the authoritative whole
-- tuple ITE, but accessing either one never interns that whole-tuple
-- projection more than once.
symItePair ::
  ( SupportedNonFuncPrim (ConType a),
    SupportedNonFuncPrim (ConType b),
    LinkedRep (ConType a) a,
    LinkedRep (ConType b) b
  ) =>
  Term Bool ->
  SymPair a b ->
  SymPair a b ->
  SymPair a b
symItePair condition
    (SymPair trueTerm trueComponents)
    (SymPair falseTerm falseComponents) =
  SymPair
    (pevalITETerm condition trueTerm falseTerm)
    ( wrapTerm $ pevalITETerm condition
        (underlyingTerm (fst trueComponents))
        (underlyingTerm (fst falseComponents)),
      wrapTerm $ pevalITETerm condition
        (underlyingTerm (snd trueComponents))
        (underlyingTerm (snd falseComponents))
    )

instance ConRep (SymPair a b) where
  type ConType (SymPair a b) = (ConType a, ConType b)

instance
  (SupportedNonFuncPrim a, SupportedNonFuncPrim b, SymRep a, SymRep b) =>
  SymRep (a, b)
  where
  type SymType (a, b) = SymPair (SymType a) (SymType b)

instance
  ( SupportedNonFuncPrim ca,
    SupportedNonFuncPrim cb,
    LinkedRep ca sa,
    LinkedRep cb sb
  ) =>
  LinkedRep (ca, cb) (SymPair sa sb)
  where
  underlyingTerm = underlyingPairTerm
  wrapTerm = fromPairTerm

instance
  ( SupportedNonFuncPrim ca,
    SupportedNonFuncPrim cb,
    LinkedRep ca sa,
    LinkedRep cb sb
  ) =>
  Solvable (ca, cb) (SymPair sa sb)
  where
  con = wrapTerm . conTerm
  sym = wrapTerm . symTerm . typedConstantSymbol
  conView value = case underlyingTerm value of
    ConTerm concrete -> Just concrete
    _ -> Nothing

instance
  ( SupportedNonFuncPrim ca,
    SupportedNonFuncPrim cb,
    LinkedRep ca sa,
    LinkedRep cb sb
  ) =>
  AllSyms (SymPair sa sb)
  where
  allSymsS value = (SomeSym value :)

instance
  ( SupportedNonFuncPrim ca,
    SupportedNonFuncPrim cb,
    LinkedRep ca sa,
    LinkedRep cb sb
  ) =>
  IsString (SymPair sa sb)
  where
  fromString = ssym . fromString

instance Show (SymPair a b) where
  show = pformatTerm . underlyingPairTerm

instance
  ( SupportedNonFuncPrim ca,
    SupportedNonFuncPrim cb,
    LinkedRep ca sa,
    LinkedRep cb sb
  ) =>
  Serial (SymPair sa sb)
  where
  serialize = serialize . underlyingTerm
  deserialize = wrapTerm <$> deserialize

instance
  ( SupportedNonFuncPrim ca,
    SupportedNonFuncPrim cb,
    LinkedRep ca sa,
    LinkedRep cb sb
  ) =>
  Cereal.Serialize (SymPair sa sb)
  where
  put = serialize
  get = deserialize

instance
  ( SupportedNonFuncPrim ca,
    SupportedNonFuncPrim cb,
    LinkedRep ca sa,
    LinkedRep cb sb
  ) =>
  Binary.Binary (SymPair sa sb)
  where
  put = serialize
  get = deserialize

pair ::
  ( SupportedNonFuncPrim (ConType a),
    SupportedNonFuncPrim (ConType b),
    LinkedRep (ConType a) a,
    LinkedRep (ConType b) b
  ) =>
  a ->
  b ->
  SymPair a b
pair firstValue secondValue =
  SymPair
    (pevalPairTerm (underlyingTerm firstValue) (underlyingTerm secondValue))
    (firstValue, secondValue)

first ::
  ( SupportedNonFuncPrim (ConType a),
    SupportedNonFuncPrim (ConType b),
    LinkedRep (ConType a) a,
    LinkedRep (ConType b) b
  ) =>
  SymPair a b ->
  a
first (SymPair _ components) = fst components

second ::
  ( SupportedNonFuncPrim (ConType a),
    SupportedNonFuncPrim (ConType b),
    LinkedRep (ConType a) a,
    LinkedRep (ConType b) b
  ) =>
  SymPair a b ->
  b
second (SymPair _ components) = snd components
