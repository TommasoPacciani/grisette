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
  ( SymPair (..),
    pair,
    first,
    second,
  )
where

import Control.DeepSeq (NFData)
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

newtype SymPair a b = SymPair
  { underlyingPairTerm :: Term (ConType a, ConType b)
  }
  deriving (Lift, NFData, Generic)

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
  wrapTerm = SymPair

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
  wrapTerm $ pevalPairTerm (underlyingTerm firstValue) (underlyingTerm secondValue)

first ::
  ( SupportedNonFuncPrim (ConType a),
    SupportedNonFuncPrim (ConType b),
    LinkedRep (ConType a) a,
    LinkedRep (ConType b) b
  ) =>
  SymPair a b ->
  a
first = wrapTerm . pevalFirstTerm . underlyingTerm

second ::
  ( SupportedNonFuncPrim (ConType a),
    SupportedNonFuncPrim (ConType b),
    LinkedRep (ConType a) a,
    LinkedRep (ConType b) b
  ) =>
  SymPair a b ->
  b
second = wrapTerm . pevalSecondTerm . underlyingTerm
