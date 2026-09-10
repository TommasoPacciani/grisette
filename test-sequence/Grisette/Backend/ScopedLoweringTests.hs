{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}

module Grisette.Backend.ScopedLoweringTests (scopedLoweringTests) where

import Data.List (foldl')
import Grisette
  ( LogicalOp (symNot, (.&&)),
    SimpleMergeable (mrgIte),
    Solvable (con),
    SymBool,
    SymEq ((.==)),
    SymInteger,
    SymOrd ((.>)),
    solve,
  )
import Grisette.Internal.Backend.Solving (z3)
import Grisette.Internal.Core.Data.Class.Solver (SolvingFailure (Unsat))
import Grisette.Internal.SymPrim.Prim.Term (LinkedRep (underlyingTerm))
import Grisette.Internal.SymPrim.Prim.TermUtils (termSize)
import Grisette.Internal.SymPrim.Quantifier (existsSym, forallSym)
import Grisette.SymPrim (SymSeq)
import Grisette.Unified (EvalModeTag (S))
import qualified Grisette.Unified as U
import System.Timeout (timeout)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assertBool, assertFailure)

within :: String -> IO value -> IO value
within label action =
  timeout 10000000 action >>= \case
    Nothing -> fail $ label ++ " did not finish within 10 seconds"
    Just value -> pure value

-- Check both directions: the pinned inputs must be inhabited, and they must
-- not admit an incorrect result. Do not print a potentially shared term DAG.
expectPinned :: SymBool -> SymBool -> Assertion
expectPinned inputs result = do
  solve z3 (inputs .&& result) >>= \case
    Right _ -> pure ()
    Left failure -> assertFailure $ "expected real-Z3 SAT, received " ++ show failure
  solve z3 (inputs .&& symNot result) >>= \case
    Left Unsat -> pure ()
    Left failure -> assertFailure $ "expected real-Z3 UNSAT, received " ++ show failure
    Right _ -> assertFailure "pinned inputs admitted an incorrect result"

scopedLoweringTests :: Test
scopedLoweringTests =
  testGroup
    "lexically scoped solver lowering"
    [ testCase "a shared callback DAG lowers within a bounded solve" $
        within "shared callback DAG" $ do
          let depth = 24 :: Integer
              -- Each level refers to the same predecessor in its condition
              -- and both arms. Unlike repeated addition, these distinct arms
              -- cannot collapse to a constant multiple of the predecessor.
              -- Its DAG is linear; expanding its occurrences is exponential.
              step :: SymInteger -> SymInteger -> SymInteger -> SymInteger
              step scale state element =
                foldl'
                  (\shared index ->
                    mrgIte (shared .> con index)
                      (shared + con index) (shared - con index))
                  (state + scale * element)
                  [1 .. depth]
              oracle scale state element =
                foldl'
                  (\shared index ->
                    if shared > index then shared + index else shared - index)
                  (state + scale * element)
                  [1 .. depth]
              prepared = U.prepareSeqFoldWith @'S step
              first = "scoped-dag.first" :: SymSeq SymInteger
              second = "scoped-dag.second" :: SymSeq SymInteger
              apply = U.applySeqFoldWith @'S prepared 2 1
              inputs = (first .== con [3, -2 :: Integer])
                .&& (second .== con [-2 :: Integer])
              result = (apply first .== con (foldl' (oracle 2) 1 [3, -2]))
                .&& (apply second .== con (foldl' (oracle 2) 1 [-2]))
              nodes = termSize $ underlyingTerm $
                step 2 "scoped-dag.probe-state" "scoped-dag.probe-element"
          assertBool "the callback was unexpectedly simplified away"
            (nodes > 3 * fromInteger depth)
          assertBool "the callback term graph is not linear in depth"
            (nodes <= 8 * fromInteger depth + 16)
          expectPinned inputs result,
      testCase "one prepared callback keeps distinct argument values" $
        within "distinct callback arguments" $ do
          let step :: SymInteger -> SymInteger -> SymInteger -> SymInteger
              step scale state element = 3 * state + scale * element
              prepared = U.prepareSeqFoldWith @'S step
              first = "scoped-arguments.first" :: SymSeq SymInteger
              second = "scoped-arguments.second" :: SymSeq SymInteger
              firstScale = "scoped-arguments.first-scale" :: SymInteger
              secondScale = "scoped-arguments.second-scale" :: SymInteger
              apply = U.applySeqFoldWith @'S prepared
              inputs = (first .== con [1, 2, 3 :: Integer])
                .&& (second .== con [4, -1 :: Integer])
                .&& (firstScale .== 2)
                .&& (secondScale .== 5)
              result = (apply firstScale 1 first .== 63)
                .&& (apply secondScale 1 first .== 117)
                .&& (apply firstScale 7 first .== 225)
                .&& (apply firstScale 1 second .== 31)
          expectPinned inputs result,
      testCase "focused scalar and sequence captures stay application-local" $
        within "focused callback captures" $ do
          let template = U.FocusedCapture (U.nilSeq @'S @SymInteger) $
                U.FocusedCapture (0 :: SymInteger) $
                  U.FocusedCapture (con False :: SymBool) U.FocusedNoCaptures
              step
                :: U.FocusedCaptures 'S '[SymSeq SymInteger, SymInteger, SymBool]
                -> SymInteger -> SymInteger -> SymInteger
              step
                  (U.FocusedCapture values
                    (U.FocusedCapture shift
                      (U.FocusedCapture enabled U.FocusedNoCaptures)))
                  state index =
                let value = U.lookupSeqValue @'S (-11) values index
                 in 2 * state + mrgIte enabled (value + shift) (value - shift)
              prepared = U.prepareFocusedSeqFold @'S template step
              first = "scoped-captures.first" :: SymSeq SymInteger
              second = "scoped-captures.second" :: SymSeq SymInteger
              indices = "scoped-captures.indices" :: SymSeq SymInteger
              shift = "scoped-captures.shift" :: SymInteger
              enabled = "scoped-captures.enabled" :: SymBool
              apply values bias active initial =
                U.applyFocusedSeqFold @'S prepared
                  (U.FocusedCapture values $
                    U.FocusedCapture bias $
                      U.FocusedCapture active U.FocusedNoCaptures)
                  initial indices
              inputs = (first .== con [10, 20 :: Integer])
                .&& (second .== con [3, 7 :: Integer])
                .&& (indices .== con [0, 1, 0, 2 :: Integer])
                .&& (shift .== 1)
                .&& enabled
              result = (apply first shift enabled 2 .== 216)
                .&& (apply second (shift + 3) (symNot enabled) 5 .== 67)
                .&& (apply first shift enabled 0 .== 184)
          expectPinned inputs result,
      testCase "nested quantifiers separate shadowed and free symbols" $
        within "nested and shadowed quantifiers" $ do
          let outer = "scoped-quantifiers.outer" :: SymInteger
              inner = "scoped-quantifiers.inner" :: SymInteger
              shared = outer + 1
              -- The same shared expression is free, bound by the outer
              -- quantifier, and bound by a shadowing quantifier below.
              nested = forallSym outer $
                existsSym inner $
                  (inner .== shared)
                    .&& existsSym outer (outer .== inner + 1)
              impossible = forallSym outer $
                existsSym inner $
                  (inner .== shared)
                    .&& forallSym outer (inner .== shared)
              inputs = outer .== 41
              result = (shared .== 42) .&& nested .&& symNot impossible
          expectPinned inputs result,
      testCase "a focused operand is not captured by callback quantifiers" $
        within "quantified focused callback" $ do
          let operand = "scoped-focused.bound" :: SymInteger
              inner = "scoped-focused.inner" :: SymInteger
              template = U.FocusedCapture (0 :: SymInteger) U.FocusedNoCaptures
              step
                :: U.FocusedCaptures 'S '[SymInteger]
                -> SymBool -> SymInteger -> SymBool
              step (U.FocusedCapture lane U.FocusedNoCaptures) state element =
                state .&& forallSym operand
                  (existsSym inner $
                    (inner .== operand + lane + element)
                      .&& (inner .> operand + element))
              prepared = U.prepareFocusedSeqFold @'S template step
              sequenceValue = "scoped-focused.sequence" :: SymSeq SymInteger
              apply lane = U.applyFocusedSeqFold @'S prepared
                (U.FocusedCapture lane U.FocusedNoCaptures)
                (con True) sequenceValue
              inputs = (operand .== 2)
                .&& (sequenceValue .== con [1, 3 :: Integer])
              result = apply operand .&& symNot (apply (operand - 4))
          expectPinned inputs result
    ]
