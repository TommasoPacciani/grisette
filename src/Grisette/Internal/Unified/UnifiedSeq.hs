{-# LANGUAGE GHC2024 #-}
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
    PreparedSeqFold,
    PreparedSeqFoldWith,
    FocusedCaptures (..),
    PreparedFocusedSeqFold,
    UnifiedSeq (..),
    UnifiedPair (..),
  )
where

import Data.Foldable (foldl')
import Data.Kind (Constraint, Type)
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
import qualified Prelude as P

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

-- | A heterogeneous bundle whose symbolic members are guaranteed to be
-- first-order solver values.  Concrete mode needs no solver dictionaries.
data FocusedCaptures (mode :: EvalModeTag) (captures :: [Type]) where
  FocusedNoCaptures :: FocusedCaptures mode '[]
  FocusedCapture
    :: SeqValue mode value
    => !value
    -> !(FocusedCaptures mode rest)
    -> FocusedCaptures mode (value ': rest)

infixr 5 `FocusedCapture`

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

-- | A host-authored sequence step prepared for repeated application.  The
-- constructors are private so symbolic callers cannot forge an unchecked
-- function term.
data family PreparedSeqFold
  (mode :: EvalModeTag) state element :: Type

newtype instance PreparedSeqFold 'C state element =
  ConcretePreparedSeqFold (SeqStep state element)

newtype instance PreparedSeqFold 'S state element =
  SymbolicPreparedSeqFold (SSeq.PreparedSeqFold state element)

-- | 'PreparedSeqFold' with a first-order environment.
data family PreparedSeqFoldWith
  (mode :: EvalModeTag) environment state element :: Type

newtype instance PreparedSeqFoldWith 'C environment state element =
  ConcretePreparedSeqFoldWith (SeqStepWith environment state element)

newtype instance PreparedSeqFoldWith 'S environment state element =
  SymbolicPreparedSeqFoldWith
    (SSeq.PreparedSeqFoldWith environment state element)

-- | A prepared scalar-driver fold whose symbolic program may read a fixed
-- heterogeneous bundle of first-order solver values.  Preparation constructs
-- the callback body and its binders once; application only supplies the current
-- primitive captures, initial state, and driver sequence.
data family PreparedFocusedSeqFold
  (mode :: EvalModeTag) (captures :: [Type]) state element :: Type

newtype instance PreparedFocusedSeqFold 'C captures state element =
  ConcretePreparedFocusedSeqFold
    (FocusedCaptures 'C captures -> SeqStep state element)

newtype instance PreparedFocusedSeqFold 'S captures state element =
  SymbolicPreparedFocusedSeqFold
    (SSeq.PreparedFocusedSeqFold captures state element)

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
  -- | Total value-only lookup; absence returns the supplied seed.
  lookupSeqValue ::
    SeqValue mode a =>
    a ->
    GetSeq mode a ->
    GetInteger mode ->
    a
  -- | Compute one presence scalar from the authoritative length and pair it at
  -- the host level with a value-only lookup.  No solver product is introduced.
  lookupSeqParts ::
    SeqValue mode a =>
    GetInteger mode ->
    a ->
    GetSeq mode a ->
    GetInteger mode ->
    (GetBool mode, a)
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
  -- | Prepare a focused scalar-driver fold.  The template fixes only the
  -- capture types; concrete values supplied here are not retained as runtime
  -- inputs.  In symbolic mode the callback is evaluated exactly once.
  prepareFocusedSeqFold ::
    ( SeqValue mode state,
      SeqValue mode element,
      SeqStepValue mode state element
    ) =>
    FocusedCaptures mode captures ->
    (FocusedCaptures mode captures -> state -> element -> state) ->
    PreparedFocusedSeqFold mode captures state element
  -- | Apply a retained focused fold without rebuilding its symbolic callback.
  applyFocusedSeqFold ::
    PreparedFocusedSeqFold mode captures state element ->
    FocusedCaptures mode captures ->
    state ->
    GetSeq mode element ->
    state
  prepareSeqFold ::
    ( SeqValue mode state,
      SeqValue mode element,
      SeqStepValue mode state element
    ) =>
    SeqStep state element ->
    PreparedSeqFold mode state element
  applySeqFold ::
    PreparedSeqFold mode state element ->
    state ->
    GetSeq mode element ->
    state
  prepareSeqFoldWith ::
    ( SeqValue mode environment,
      SeqValue mode state,
      SeqValue mode element,
      SeqStepWithValue mode environment state element
    ) =>
    SeqStepWith environment state element ->
    PreparedSeqFoldWith mode environment state element
  applySeqFoldWith ::
    PreparedSeqFoldWith mode environment state element ->
    environment ->
    state ->
    GetSeq mode element ->
    state

instance UnifiedSeq 'C where
  nilSeq = []
  consSeq = (:)
  appendSeq = (P.++)
  lengthSeq = foldl' (\count _ -> count P.+ 1) 0
  rangeSeq n = [0 .. n P.- 1]
  tailSeq = P.drop 1
  lookupSeq seed values index = go values index
    where
      go [] _ = (P.False, seed)
      go (value : _) 0 = (P.True, value)
      go (_ : rest) current
        | current P.> 0 = go rest (current P.- 1)
      go _ _ = (P.False, seed)
  lookupSeqValue seed values index = P.snd (lookupSeq seed values index)
  lookupSeqParts authoritativeLength seed values index =
    (0 P.<= index P.&& index P.< authoritativeLength,
      lookupSeqValue seed values index)
  zipSeq = P.zip
  foldSeq step = applySeqFold (prepareSeqFold step)
  foldSeqWith step = applySeqFoldWith (prepareSeqFoldWith step)
  prepareFocusedSeqFold _ = ConcretePreparedFocusedSeqFold
  applyFocusedSeqFold (ConcretePreparedFocusedSeqFold step) captures =
    foldl' (step captures)
  prepareSeqFold = ConcretePreparedSeqFold
  applySeqFold (ConcretePreparedSeqFold step) = foldl' step
  prepareSeqFoldWith = ConcretePreparedSeqFoldWith
  applySeqFoldWith (ConcretePreparedSeqFoldWith step) environment =
    foldl' (step environment)

instance UnifiedSeq 'S where
  nilSeq = SSeq.nil
  consSeq = SSeq.cons
  appendSeq = SSeq.append
  lengthSeq = SSeq.length
  rangeSeq = SSeq.range
  tailSeq = SSeq.tail
  lookupSeq = SSeq.lookup
  lookupSeqValue = SSeq.lookupValue
  lookupSeqParts = SSeq.lookupParts
  zipSeq = SSeq.zip
  foldSeq step = applySeqFold (prepareSeqFold step)
  foldSeqWith step = applySeqFoldWith (prepareSeqFoldWith step)
  prepareFocusedSeqFold template step =
    SymbolicPreparedFocusedSeqFold
      (SSeq.prepareFocusedFoldHost (toSymbolicCaptures template)
        (step P.. fromSymbolicCaptures))
  applyFocusedSeqFold (SymbolicPreparedFocusedSeqFold prepared) captures =
    SSeq.applyPreparedFocusedFold prepared
      (toSymbolicCaptures captures)
  prepareSeqFold step =
    SymbolicPreparedSeqFold (SSeq.prepareFoldHost step)
  applySeqFold (SymbolicPreparedSeqFold prepared) =
    SSeq.applyPreparedFold prepared
  prepareSeqFoldWith step =
    SymbolicPreparedSeqFoldWith (SSeq.prepareFoldWithHost step)
  applySeqFoldWith (SymbolicPreparedSeqFoldWith prepared) =
    SSeq.applyPreparedFoldWith prepared

toSymbolicCaptures
  :: FocusedCaptures 'S captures
  -> SSeq.SymbolicFocusedCaptures captures
toSymbolicCaptures FocusedNoCaptures = SSeq.FocusedNoCaptures
toSymbolicCaptures (FocusedCapture value rest) =
  SSeq.FocusedCapture value (toSymbolicCaptures rest)

fromSymbolicCaptures
  :: SSeq.SymbolicFocusedCaptures captures
  -> FocusedCaptures 'S captures
fromSymbolicCaptures SSeq.FocusedNoCaptures = FocusedNoCaptures
fromSymbolicCaptures (SSeq.FocusedCapture value rest) =
  FocusedCapture value (fromSymbolicCaptures rest)

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
