{-# LANGUAGE GHC2024 #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.SymNominal
-- Copyright   :   (c) Sirui Lu 2021-2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Symbolic carrier for solver-erased nominal values.
module Grisette.Internal.SymPrim.SymNominal
  ( SymNominal (..),
  )
where

import Control.DeepSeq (NFData)
import Data.Binary qualified as Binary
import Data.Bytes.Serial (Serial (deserialize, serialize))
import Data.Hashable (Hashable (hashWithSalt))
import Data.Serialize qualified as Cereal
import Data.String (IsString (fromString))
import GHC.Generics (Generic)
import Grisette.Internal.Core.Data.Class.AsKey
  ( KeyEq (keyEq),
    KeyHashable (keyHashWithSalt),
    shouldUseAsKeyHasSymbolicVersionError,
  )
import Grisette.Internal.Core.Data.Class.Solvable
  ( Solvable (con, conView, ssym, sym),
  )
import Grisette.Internal.Internal.Decl.SymPrim.AllSyms
  ( AllSyms (allSymsS),
    SomeSym (SomeSym),
  )
import Grisette.Internal.SymPrim.Nominal
  ( KnownNominalDomain,
    Nominal,
    NominalDomain,
  )
import Grisette.Internal.SymPrim.Prim.Term
  ( ConRep (ConType),
    LinkedRep (underlyingTerm, wrapTerm),
    SupportedNonFuncPrim,
    SymRep (SymType),
    Term,
    conTerm,
    pformatTerm,
    symTerm,
    typedConstantSymbol,
    pattern ConTerm,
  )
import Language.Haskell.TH.Syntax (Lift)

-- | Symbolic nominal value. The domain is represented in the term type but
-- erases to the underlying solver sort.
newtype SymNominal (domain :: NominalDomain) value = SymNominal
  { underlyingNominalTerm :: Term (Nominal domain value)
  }
  deriving stock (Generic, Lift)
  deriving newtype (NFData)

type role SymNominal nominal nominal

instance Eq (SymNominal domain value) where
  (==) =
    shouldUseAsKeyHasSymbolicVersionError "SymNominal" "(==)" "(.==)"

instance KeyEq (SymNominal domain value) where
  keyEq (SymNominal left) (SymNominal right) = left == right

instance KeyHashable (SymNominal domain value) where
  keyHashWithSalt salt (SymNominal value) = salt `hashWithSalt` value

instance ConRep (SymNominal domain value) where
  type ConType (SymNominal domain value) = Nominal domain value

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  SymRep (Nominal domain value)
  where
  type SymType (Nominal domain value) = SymNominal domain value

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  LinkedRep (Nominal domain value) (SymNominal domain value)
  where
  underlyingTerm = underlyingNominalTerm
  wrapTerm = SymNominal

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  Solvable (Nominal domain value) (SymNominal domain value)
  where
  con = SymNominal . conTerm
  sym = SymNominal . symTerm . typedConstantSymbol
  conView (SymNominal (ConTerm value)) = Just value
  conView _ = Nothing

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  AllSyms (SymNominal domain value)
  where
  allSymsS value = (SomeSym value :)

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  IsString (SymNominal domain value)
  where
  fromString = ssym . fromString

instance Show (SymNominal domain value) where
  show = pformatTerm . underlyingNominalTerm

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  Serial (SymNominal domain value)
  where
  serialize = serialize . underlyingNominalTerm
  deserialize = SymNominal <$> deserialize

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  Cereal.Serialize (SymNominal domain value)
  where
  put = serialize
  get = deserialize

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  Binary.Binary (SymNominal domain value)
  where
  put = serialize
  get = deserialize
