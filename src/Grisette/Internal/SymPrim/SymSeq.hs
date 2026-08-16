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
    range,
    tail,
    lookup,
    zip,
    length,
    fold,
    foldWith,
    foldHost,
    foldWithHost,
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
import Grisette.Internal.Core.Data.Symbol (freshBoundSymbol)
import Grisette.Internal.SymPrim.GeneralFun
  ( buildGeneralFun,
    pevalClosedSeqFold,
    pevalClosedSeqFoldWith,
    type (-->),
  )
import System.IO.Unsafe (unsafePerformIO)
import Grisette.Internal.SymPrim.Prim.Internal.Serialize ()
import Grisette.Internal.SymPrim.Prim.Internal.Term
  ( ConRep (ConType),
    LinkedRep (underlyingTerm, wrapTerm),
    SupportedNonFuncPrim,
    SupportedPrim,
    SymRep (SymType),
    Term,
    conTerm,
    pevalSeqAppendTerm,
    pevalSeqConsTerm,
    pevalSeqRangeTerm,
    pevalSeqTailTerm,
    pevalSeqLookupTerm,
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
import Grisette.Internal.SymPrim.SymBool (SymBool)
import Grisette.Internal.SymPrim.SymInteger (SymInteger)
import Language.Haskell.TH.Syntax (Lift)
import Prelude hiding (fold, length, lookup, tail, zip)

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

range :: SymInteger -> SymSeq SymInteger
range = wrapTerm . pevalSeqRangeTerm . underlyingTerm

-- | Drop the first element; the tail of an empty sequence is empty.
tail ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  SymSeq a ->
  SymSeq a
tail = wrapTerm . pevalSeqTailTerm . underlyingTerm

lookup ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  a ->
  SymSeq a ->
  SymInteger ->
  SymPair SymBool a
lookup seed sequence index =
  wrapTerm $
    pevalSeqLookupTerm
      (underlyingTerm seed)
      (underlyingTerm sequence)
      (underlyingTerm index)

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

-- | Fold a symbolic sequence with a step given as an ordinary Haskell function
-- over symbolic values.
--
-- The solver-native fold needs its step as a closed function /term/, which
-- previously forced every caller to build @sym --> sym --> body@ by hand and
-- therefore to write one step for concrete evaluation and a second, separately
-- authored step for symbolic evaluation.  Two authored steps are two programs, so
-- they can disagree.  Abstracting the caller's function over fresh bound symbols
-- here means one step serves both modes.
--
-- The step is applied to bound variables only, so a step that reaches out to a
-- solver value from its enclosing scope produces a non-closed term; that is
-- rejected by 'pevalClosedSeqFold', exactly as a hand-built step would be.
foldHost ::
  forall state element.
  ( SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    SupportedPrim (ConType element --> ConType state),
    SupportedPrim (ConType state --> ConType element --> ConType state),
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  (state -> element -> state) ->
  state ->
  SymSeq element ->
  state
foldHost step initial sequence = unsafePerformIO $ do
  -- The step is an arbitrary Haskell function, so it cannot be inspected; it can
  -- only be applied and its result examined.  Two properties make that sound.
  -- The arguments are bound to symbols in a namespace the public API cannot
  -- construct, so a symbol the step returns is either one it was handed or one
  -- that stays free and is reported by the closure check below.  And each
  -- allocation is distinct, so an enclosing abstraction's binder can never be
  -- rebound here: a step closing over an enclosing fold's state leaves it free and
  -- is rejected instead of silently reading this fold's argument.
  stateSymbol <- typedConstantSymbol <$> freshBoundSymbol "foldSeq.state"
  elementSymbol <- typedConstantSymbol <$> freshBoundSymbol "foldSeq.element"
  let body =
        underlyingTerm
          ( step
              (wrapTerm (symTerm stateSymbol))
              (wrapTerm (symTerm elementSymbol))
          )
      stepTerm =
        conTerm
          ( buildGeneralFun
              stateSymbol
              (conTerm (buildGeneralFun elementSymbol body))
          )
      folded =
        pevalClosedSeqFold
          stepTerm
          (underlyingTerm initial)
          (underlyingTerm sequence)
  folded `seq` return (wrapTerm folded)
{-# NOINLINE foldHost #-}

-- | 'foldHost' with an environment the step reads on every element.
foldWithHost ::
  forall environment state element.
  ( SupportedNonFuncPrim (ConType environment),
    SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    SupportedPrim (ConType element --> ConType state),
    SupportedPrim (ConType state --> ConType element --> ConType state),
    SupportedPrim
      (ConType environment --> ConType state --> ConType element --> ConType state),
    LinkedRep (ConType environment) environment,
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  (environment -> state -> element -> state) ->
  environment ->
  state ->
  SymSeq element ->
  state
foldWithHost step environment initial sequence = unsafePerformIO $ do
  -- See 'foldHost' for why the binders are private and freshly allocated.
  environmentSymbol <-
    typedConstantSymbol <$> freshBoundSymbol "foldSeqWith.environment"
  stateSymbol <- typedConstantSymbol <$> freshBoundSymbol "foldSeqWith.state"
  elementSymbol <- typedConstantSymbol <$> freshBoundSymbol "foldSeqWith.element"
  let body =
        underlyingTerm
          ( step
              (wrapTerm (symTerm environmentSymbol))
              (wrapTerm (symTerm stateSymbol))
              (wrapTerm (symTerm elementSymbol))
          )
      stepTerm =
        conTerm
          ( buildGeneralFun
              environmentSymbol
              ( conTerm
                  ( buildGeneralFun
                      stateSymbol
                      (conTerm (buildGeneralFun elementSymbol body))
                  )
              )
          )
      folded =
        pevalClosedSeqFoldWith
          stepTerm
          (underlyingTerm environment)
          (underlyingTerm initial)
          (underlyingTerm sequence)
  folded `seq` return (wrapTerm folded)
{-# NOINLINE foldWithHost #-}
