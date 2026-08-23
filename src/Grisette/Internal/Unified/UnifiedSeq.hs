{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- |
-- Module      :   Grisette.Internal.Unified.UnifiedSeq
-- Copyright   :   (c) Sirui Lu 2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Mode-polymorphic solver-native sequences and binary products.
module Grisette.Internal.Unified.UnifiedSeq
  ( SolverValue,
    GetSeq,
    GetPair,
    SeqValue,
    SeqStep,
    SeqStepWith,
    SeqStepValue,
    SeqStepWithValue,
    SeqFoldKey,
    seqFoldKey,
    UnifiedSeq (..),
    UnifiedPair (..),
  )
where

import Data.Foldable (foldl')
import Data.Kind (Constraint)
import qualified Data.Text as T
import Grisette.Internal.Core.Data.Symbol (Identifier, withLocation)
import Grisette.Internal.SymPrim.Prim.Term
  ( ConRep (ConType),
    SupportedPrim,
    type (-->),
    LinkedRep,
    SupportedNonFuncPrim,
  )
import Grisette.Internal.SymPrim.SymPair (SymPair)
import qualified Grisette.Internal.SymPrim.SymPair as SPair
import Grisette.Internal.SymPrim.SymSeq (SymSeq)
import qualified Grisette.Internal.SymPrim.SymSeq as SSeq
import Grisette.Internal.Unified.EvalModeTag (EvalModeTag (C, S))
import Grisette.Internal.Unified.UnifiedBool (UnifiedBool (GetBool))
import Grisette.Internal.Unified.UnifiedInteger (GetInteger)
import Language.Haskell.TH.Syntax.Compat (SpliceQ)
import qualified Prelude as P

-- | A statically unique identity for one closed host-authored sequence fold.
--
-- The constructor stays private: sharing a key between different fold bodies
-- could make a nested abstraction bind the wrong private variables.  Use
-- 'seqFoldKey', which incorporates the splice location as well as its label.
newtype SeqFoldKey = SeqFoldKey Identifier

-- | Construct a fold key whose identity is the source location of the splice.
-- Repeated executions at that location intentionally reuse the same closed
-- function term.
seqFoldKey :: P.String -> SpliceQ SeqFoldKey
seqFoldKey label =
  [||SeqFoldKey $$(withLocation (T.pack label))||]

type SolverValue a =
  ( SupportedNonFuncPrim (ConType a),
    LinkedRep (ConType a) a
  )

type family GetSeq (mode :: EvalModeTag) a = sequence | sequence -> mode a where
  GetSeq 'C a = [a]
  GetSeq 'S a = SymSeq a

type family GetPair (mode :: EvalModeTag) a b = product | product -> mode a b where
  GetPair 'C a b = (a, b)
  GetPair 'S a b = SymPair a b

type family SeqValue (mode :: EvalModeTag) a :: Constraint where
  SeqValue 'C _a = ()
  SeqValue 'S a = SolverValue a

-- | What a mode needs in order to turn a fold step into what its fold consumes.
--
-- Concrete evaluation applies the step directly and needs nothing.  Symbolic
-- evaluation abstracts it into a closed function term, which needs that term's
-- sort to be supported.
type family SeqStepValue (mode :: EvalModeTag) state element :: Constraint where
  SeqStepValue 'C _state _element = ()
  SeqStepValue 'S state element =
    ( SupportedPrim (ConType element --> ConType state),
      SupportedPrim (ConType state --> ConType element --> ConType state)
    )

-- | 'SeqStepValue' for a step that also reads an environment.
type family SeqStepWithValue
  (mode :: EvalModeTag) environment state element :: Constraint where
  SeqStepWithValue 'C _environment _state _element = ()
  SeqStepWithValue 'S environment state element =
    ( SupportedPrim (ConType element --> ConType state),
      SupportedPrim (ConType state --> ConType element --> ConType state),
      SupportedPrim
        ( ConType environment
            --> ConType state
            --> ConType element
            --> ConType state
        )
    )

-- | One fold step, as an ordinary function over the mode's values.
--
-- Not mode-indexed, and it carries no mode parameter: the step is the same
-- function in both modes.  The solver-native fold needs a closed function term,
-- but building that term is 'SSeq.foldHost''s job, not the caller's; a
-- mode-indexed step type would make every caller author one step for concrete
-- evaluation and a second for symbolic evaluation, and two authored programs can
-- disagree.  What does remain mode-indexed is the evidence the term construction
-- needs, as 'SeqStepValue' and 'SeqStepWithValue'.
type SeqStep state element = state -> element -> state

-- | 'SeqStep' with an environment the step reads on every element.
type SeqStepWith environment state element =
  environment -> state -> element -> state

class UnifiedSeq (mode :: EvalModeTag) where
  nilSeq :: SeqValue mode a => GetSeq mode a
  consSeq :: SeqValue mode a => a -> GetSeq mode a -> GetSeq mode a
  appendSeq :: SeqValue mode a => GetSeq mode a -> GetSeq mode a -> GetSeq mode a
  lengthSeq :: SeqValue mode a => GetSeq mode a -> GetInteger mode
  rangeSeq :: GetInteger mode -> GetSeq mode (GetInteger mode)
  tailSeq :: SeqValue mode a => GetSeq mode a -> GetSeq mode a
  lookupSeq ::
    SeqValue mode a =>
    a ->
    GetSeq mode a ->
    GetInteger mode ->
    GetPair mode (GetBool mode) a
  zipSeq ::
    ( SeqValue mode a,
      SeqValue mode b,
      SeqValue mode (GetPair mode a b)
    ) =>
    GetSeq mode a ->
    GetSeq mode b ->
    GetSeq mode (GetPair mode a b)
  foldSeq ::
    ( SeqValue mode state,
      SeqValue mode element,
      SeqStepValue mode state element
    ) =>
    SeqStep state element ->
    state ->
    GetSeq mode element ->
    state
  foldSeqWith ::
    ( SeqValue mode environment,
      SeqValue mode state,
      SeqValue mode element,
      SeqStepWithValue mode environment state element
    ) =>
    SeqStepWith environment state element ->
    environment ->
    state ->
    GetSeq mode element ->
    state
  foldSeqWithKey ::
    ( SeqValue mode environment,
      SeqValue mode state,
      SeqValue mode element,
      SeqStepWithValue mode environment state element
    ) =>
    SeqFoldKey ->
    SeqStepWith environment state element ->
    environment ->
    state ->
    GetSeq mode element ->
    state

instance UnifiedSeq 'C where
  nilSeq = []
  consSeq = (:)
  appendSeq = (P.++)
  lengthSeq values = P.fromIntegral (P.length values)
  rangeSeq n = [0 .. n P.- 1]
  tailSeq = P.drop 1
  lookupSeq seed values index = go values index
    where
      go [] _ = (P.False, seed)
      go (value : _) 0 = (P.True, value)
      go (_ : rest) current
        | current P.> 0 = go rest (current P.- 1)
      go _ _ = (P.False, seed)
  zipSeq = P.zip
  foldSeq = foldl'
  foldSeqWith step environment = foldl' (step environment)
  foldSeqWithKey _ step environment = foldl' (step environment)

instance UnifiedSeq 'S where
  nilSeq = SSeq.nil
  consSeq = SSeq.cons
  appendSeq = SSeq.append
  lengthSeq = SSeq.length
  rangeSeq = SSeq.range
  tailSeq = SSeq.tail
  lookupSeq = SSeq.lookup
  zipSeq = SSeq.zip
  foldSeq = SSeq.foldHost
  foldSeqWith = SSeq.foldWithHost
  foldSeqWithKey (SeqFoldKey key) = SSeq.foldWithHostKey key

class UnifiedPair (mode :: EvalModeTag) where
  pair ::
    (SeqValue mode a, SeqValue mode b) =>
    a ->
    b ->
    GetPair mode a b
  first ::
    (SeqValue mode a, SeqValue mode b) =>
    GetPair mode a b ->
    a
  second ::
    (SeqValue mode a, SeqValue mode b) =>
    GetPair mode a b ->
    b

instance UnifiedPair 'C where
  pair = (,)
  first = P.fst
  second = P.snd

instance UnifiedPair 'S where
  pair = SPair.pair
  first = SPair.first
  second = SPair.second
