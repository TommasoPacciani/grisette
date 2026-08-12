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
    UnifiedSeq (..),
    UnifiedPair (..),
  )
where

import Data.Foldable (foldl')
import Data.Kind (Constraint)
import Grisette.Internal.SymPrim.Prim.Term
  ( ConRep (ConType),
    LinkedRep,
    SupportedNonFuncPrim,
  )
import Grisette.Internal.SymPrim.SymGeneralFun (type (-~>))
import Grisette.Internal.SymPrim.SymPair (SymPair)
import qualified Grisette.Internal.SymPrim.SymPair as SPair
import Grisette.Internal.SymPrim.SymSeq (SymSeq)
import qualified Grisette.Internal.SymPrim.SymSeq as SSeq
import Grisette.Internal.Unified.EvalModeTag (EvalModeTag (C, S))
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

type family SeqStep (mode :: EvalModeTag) state element where
  SeqStep 'C state element = state -> element -> state
  SeqStep 'S state element = state -~> element -~> state

type family SeqStepWith (mode :: EvalModeTag) environment state element where
  SeqStepWith 'C environment state element =
    environment -> state -> element -> state
  SeqStepWith 'S environment state element =
    environment -~> state -~> element -~> state

class UnifiedSeq (mode :: EvalModeTag) where
  nilSeq :: SeqValue mode a => GetSeq mode a
  consSeq :: SeqValue mode a => a -> GetSeq mode a -> GetSeq mode a
  appendSeq :: SeqValue mode a => GetSeq mode a -> GetSeq mode a -> GetSeq mode a
  lengthSeq :: SeqValue mode a => GetSeq mode a -> GetInteger mode
  zipSeq ::
    ( SeqValue mode a,
      SeqValue mode b,
      SeqValue mode (GetPair mode a b)
    ) =>
    GetSeq mode a ->
    GetSeq mode b ->
    GetSeq mode (GetPair mode a b)
  foldSeq ::
    (SeqValue mode state, SeqValue mode element) =>
    SeqStep mode state element ->
    state ->
    GetSeq mode element ->
    state
  foldSeqWith ::
    ( SeqValue mode environment,
      SeqValue mode state,
      SeqValue mode element
    ) =>
    SeqStepWith mode environment state element ->
    environment ->
    state ->
    GetSeq mode element ->
    state

instance UnifiedSeq 'C where
  nilSeq = []
  consSeq = (:)
  appendSeq = (P.++)
  lengthSeq values = P.fromIntegral (P.length values)
  zipSeq = P.zip
  foldSeq = foldl'
  foldSeqWith step environment = foldl' (step environment)

instance UnifiedSeq 'S where
  nilSeq = SSeq.nil
  consSeq = SSeq.cons
  appendSeq = SSeq.append
  lengthSeq = SSeq.length
  zipSeq = SSeq.zip
  foldSeq = SSeq.fold
  foldSeqWith = SSeq.foldWith

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
