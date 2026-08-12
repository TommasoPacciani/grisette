{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.SymSeq
-- Copyright   :   (c) Sirui Lu 2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Solver-native finite symbolic sequences.
module Grisette.Internal.SymPrim.SymSeq
  ( SymSeq (..),
    nil,
    cons,
    append,
    zip,
    length,
    fold,
    foldWith,
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
import Grisette.Internal.SymPrim.GeneralFun
  ( pevalClosedSeqFold,
    pevalClosedSeqFoldWith,
  )
import Grisette.Internal.SymPrim.Prim.Internal.Serialize ()
import Grisette.Internal.SymPrim.Prim.Internal.Term
  ( ConRep (ConType),
    LinkedRep (underlyingTerm, wrapTerm),
    SupportedNonFuncPrim,
    SymRep (SymType),
    Term,
    conTerm,
    pevalSeqAppendTerm,
    pevalSeqConsTerm,
    pevalSeqZipTerm,
    pevalSeqLengthTerm,
    pformatTerm,
    symTerm,
    typedConstantSymbol,
    pattern ConTerm,
    pattern SupportedTerm,
  )
import Grisette.Internal.SymPrim.SymGeneralFun
  ( type (-~>) (SymGeneralFun),
  )
import Grisette.Internal.SymPrim.SymPair (SymPair)
import Language.Haskell.TH.Syntax (Lift)
import Prelude hiding (fold, length, zip)

newtype SymSeq a = SymSeq
  { underlyingSeqTerm :: Term [ConType a]
  }
  deriving (Lift, NFData, Generic)

instance ConRep (SymSeq a) where
  type ConType (SymSeq a) = [ConType a]

instance (SupportedNonFuncPrim a, SymRep a) => SymRep [a] where
  type SymType [a] = SymSeq (SymType a)

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  LinkedRep [ca] (SymSeq sa)
  where
  underlyingTerm = underlyingSeqTerm
  wrapTerm = SymSeq

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  Solvable [ca] (SymSeq sa)
  where
  con = wrapTerm . conTerm
  sym = wrapTerm . symTerm . typedConstantSymbol
  conView value = case underlyingTerm value of
    ConTerm concrete -> Just concrete
    _ -> Nothing

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  AllSyms (SymSeq sa)
  where
  allSymsS value = (SomeSym value :)

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  IsString (SymSeq sa)
  where
  fromString = ssym . fromString

instance Show (SymSeq a) where
  show = pformatTerm . underlyingSeqTerm

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  Serial (SymSeq sa)
  where
  serialize = serialize . underlyingTerm
  deserialize = wrapTerm <$> deserialize

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  Cereal.Serialize (SymSeq sa)
  where
  put = serialize
  get = deserialize

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  Binary.Binary (SymSeq sa)
  where
  put = serialize
  get = deserialize

nil ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  SymSeq a
nil = wrapTerm (conTerm [])

cons ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  a ->
  SymSeq a ->
  SymSeq a
cons element sequence =
  wrapTerm $ pevalSeqConsTerm (underlyingTerm element) (underlyingTerm sequence)

append ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  SymSeq a ->
  SymSeq a ->
  SymSeq a
append left right =
  wrapTerm $ pevalSeqAppendTerm (underlyingTerm left) (underlyingTerm right)

zip ::
  ( SupportedNonFuncPrim (ConType a),
    SupportedNonFuncPrim (ConType b),
    LinkedRep (ConType a) a,
    LinkedRep (ConType b) b
  ) =>
  SymSeq a ->
  SymSeq b ->
  SymSeq (SymPair a b)
zip left right =
  wrapTerm $ pevalSeqZipTerm (underlyingTerm left) (underlyingTerm right)

length ::
  ( SupportedNonFuncPrim (ConType a),
    LinkedRep (ConType a) a,
    LinkedRep Integer integer
  ) =>
  SymSeq a ->
  integer
length = wrapTerm . pevalSeqLengthTerm . underlyingTerm

fold ::
  ( SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  (state -~> element -~> state) ->
  state ->
  SymSeq element ->
  state
fold (SymGeneralFun (stepTerm@SupportedTerm)) initial sequence =
  let folded =
        pevalClosedSeqFold
          stepTerm
          (underlyingTerm initial)
          (underlyingTerm sequence)
   in folded `seq` wrapTerm folded

foldWith ::
  ( SupportedNonFuncPrim (ConType environment),
    SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    LinkedRep (ConType environment) environment,
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  (environment -~> state -~> element -~> state) ->
  environment ->
  state ->
  SymSeq element ->
  state
foldWith (SymGeneralFun (stepTerm@SupportedTerm)) environment initial sequence =
  let folded =
        pevalClosedSeqFoldWith
          stepTerm
          (underlyingTerm environment)
          (underlyingTerm initial)
          (underlyingTerm sequence)
   in folded `seq` wrapTerm folded
