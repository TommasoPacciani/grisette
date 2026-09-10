{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}

module Grisette.Backend.LiteralFoldLoweringTests (literalFoldLoweringTests) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.List (isInfixOf)
import Data.SBV qualified as SBV
import Grisette
  ( LogicalOp (symNot, (.&&)), Solvable (con), SymBool, SymEq ((.==))
  , SymInteger, solve )
import Grisette.Internal.Backend.QuantifiedStack (emptyQuantifiedStack)
import Grisette.Internal.Backend.Solving (lowerSinglePrim, z3)
import Grisette.Internal.Core.Data.Class.Solver (SolvingFailure (Unsat))
import Grisette.Internal.SymPrim.GeneralFun
  ( buildFocusedGeneralFun, buildGeneralFun2, buildGeneralFun3
  , validateClosedFocusedSeqFold, validateClosedSeqFold, validateClosedSeqFoldWith )
import Grisette.Internal.SymPrim.Prim.Term
  ( FocusedSeqFoldBinderSymbols(..), FocusedSeqFoldOperands(..)
  , LinkedRep (underlyingTerm, wrapTerm), Term, TypedConstantSymbol
  , conTerm, focusedSeqFoldTerm, seqFoldTerm, seqFoldWithTerm, seqRangeTerm
  , symTerm )
import Grisette.SymPrim (SymPair, SymSeq)
import Grisette.Unified (EvalModeTag (S))
import Grisette.Unified qualified as U
import System.Timeout (timeout)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assertBool, assertFailure)

type IntegerFold =
  SymInteger -> SymInteger -> SymSeq SymInteger -> SymInteger

type RawIntegerFold =
  SymInteger -> SymInteger -> Term [Integer] -> SymInteger

step :: SymInteger -> SymInteger -> SymInteger -> SymInteger
step scale state index = 3 * state + scale * index

-- Plain folds cannot close over a solver value. Carry the unchanged scale in
-- their actual tuple state, exercising that arm with symbolic inputs too.
plainStep
  :: SymPair SymInteger SymInteger -> SymInteger
  -> SymPair SymInteger SymInteger
plainStep state index = U.pair @'S (U.first @'S state)
  (step (U.first @'S state) (U.second @'S state) index)

preparedFolds :: [(String, IntegerFold)]
preparedFolds =
  [ ("plain", \scale initial values -> U.second @'S $
      U.applySeqFold @'S plain (U.pair @'S scale initial) values)
  , ("With", U.applySeqFoldWith @'S withEnvironment)
  , ("Focused", \scale initial values -> U.applyFocusedSeqFold @'S focused
      (U.FocusedCapture scale U.FocusedNoCaptures) initial values)
  ]
  where
    plain = U.prepareSeqFold @'S plainStep
    withEnvironment = U.prepareSeqFoldWith @'S step
    focused = U.prepareFocusedSeqFold @'S
      (U.FocusedCapture (0 :: SymInteger) U.FocusedNoCaptures) $
        \(U.FocusedCapture scale U.FocusedNoCaptures) -> step scale

-- Public prepared application already evaluates literal lists at the AST
-- boundary. These raw term constructors deliberately retain the real fold
-- node so the new lowering-only ConTerm branch is tested independently.
-- Callback closure construction uses the same checked binder abstraction API;
-- no backend function, result, or node identity is fabricated.
rawFolds :: [(String, RawIntegerFold)]
rawFolds =
  [ ("plain", \scale initial values -> U.second @'S $
      (wrapTerm (seqFoldTerm plain
        (underlyingTerm (U.pair @'S scale initial)) values)
        :: SymPair SymInteger SymInteger))
  , ("With", \scale initial values -> wrapTerm $
      seqFoldWithTerm withEnvironment (underlyingTerm scale)
        (underlyingTerm initial) values)
  , ("Focused", \scale initial values -> wrapTerm $
      focusedSeqFoldTerm focused
        (FocusedSeqFoldOperand (underlyingTerm scale) NoFocusedSeqFoldOperands)
        (underlyingTerm initial) values)
  ]
  where
    scaleSymbol = "literal-fold.capture" :: TypedConstantSymbol Integer
    stateSymbol = "literal-fold.state" :: TypedConstantSymbol Integer
    indexSymbol = "literal-fold.index" :: TypedConstantSymbol Integer
    pairSymbol = "literal-fold.pair-state" :: TypedConstantSymbol (Integer, Integer)
    symbolicScale = wrapTerm (symTerm scaleSymbol) :: SymInteger
    symbolicState = wrapTerm (symTerm stateSymbol) :: SymInteger
    symbolicIndex = wrapTerm (symTerm indexSymbol) :: SymInteger
    symbolicPairState = wrapTerm (symTerm pairSymbol) :: SymPair SymInteger SymInteger
    body = underlyingTerm (step symbolicScale symbolicState symbolicIndex)
    plain = validateClosedSeqFold . conTerm $ buildGeneralFun2 pairSymbol indexSymbol
      (underlyingTerm (plainStep symbolicPairState symbolicIndex))
    withEnvironment = validateClosedSeqFoldWith . conTerm $
      buildGeneralFun3 scaleSymbol stateSymbol indexSymbol body
    focused = validateClosedFocusedSeqFold $ buildFocusedGeneralFun
      (FocusedSeqFoldBinderSymbol scaleSymbol NoFocusedSeqFoldBinderSymbols)
      stateSymbol indexSymbol body

within :: String -> IO value -> IO value
within label action = timeout 10000000 action >>= \case
  Nothing -> fail (label ++ " exceeded 10 seconds")
  Just value -> pure value

-- SAT guards against a vacuous premise; UNSAT rules out every alternative
-- initial/capture value, not just a solver-selected convenient example.
expectPinned :: SymBool -> SymBool -> Assertion
expectPinned inputs result = do
  solve z3 (inputs .&& result) >>= \case
    Right _ -> pure ()
    Left failure -> assertFailure ("expected SAT: " ++ show failure)
  solve z3 (inputs .&& symNot result) >>= \case
    Left Unsat -> pure ()
    Left failure -> assertFailure ("expected UNSAT: " ++ show failure)
    Right _ -> assertFailure "literal fold disagreed with the independent oracle"

-- The existing benchmark generator lowers and renders an SMT program without
-- starting a solver. Retain the actual lowerer's auxiliary constraints.
compileSMT :: SymInteger -> IO String
compileSMT value = within "literal-fold SMT rendering" $ do
  let program :: SBV.Symbolic SBV.SBool
      program = do
        (_, lowered, constraints) <- lowerSinglePrim (underlyingTerm value)
        pure (constraints SBV..&& lowered emptyQuantifiedStack SBV../= 0)
  rendered <- SBV.generateSMTBenchmarkSat program
  evaluate (force rendered)

assertFoldShape :: Bool -> SymInteger -> Assertion
assertFoldShape recursive value = do
  rendered <- compileSMT value
  let hasFold = "sbv.foldl" `isInfixOf` rendered
        || "sbv.closureFoldl" `isInfixOf` rendered
      hasRecursiveDefinition = "(define-fun-rec " `isInfixOf` rendered
        || "(define-funs-rec" `isInfixOf` rendered
  if recursive
    then assertBool "the native recursive fold fallback was not retained"
      (hasFold && hasRecursiveDefinition)
    else assertBool "a small literal fold retained a recursive backend fold"
      (not hasFold)

literalFoldLoweringTests :: Test
literalFoldLoweringTests = testGroup "small literal fold solver lowering" $
  [ testCase (name ++ ": range 3/4 preserve order and prepared argument reuse") $
      within "range fold oracle" $ do
        let initial = "literal-range.initial" :: SymInteger
            scale = "literal-range.scale" :: SymInteger
            first = apply scale initial (U.rangeSeq @'S 3)
            second = apply (scale + 2) (initial - 1) (U.rangeSeq @'S 4)
            reused = apply (scale - 5) (initial + 7) (U.rangeSeq @'S 3)
            -- [0,1,2] contributes 5*c; [0,1,2,3] contributes 18*c.
            correct = (first .== 27 * initial + 5 * scale)
              .&& (second .== 81 * (initial - 1) + 18 * (scale + 2))
              .&& (reused .== 27 * (initial + 7) + 5 * (scale - 5))
        expectPinned (con True) correct
        forM_ [first, second, reused] (assertFoldShape False)
  | (name, apply) <- preparedFolds
  ] ++
  [ testCase (name ++ ": retained literal lists preserve exact left-fold values") $
      within "literal-list fold oracle" $ do
        let initial = "literal-list.initial" :: SymInteger
            scale = "literal-list.scale" :: SymInteger
            first = apply scale initial (conTerm [2, -1, 4])
            second = apply (scale - 3) (initial + 2) (conTerm [3, -1, 4, 2])
            correct = (first .== 27 * initial + 19 * scale)
              .&& (second .== 81 * (initial + 2) + 86 * (scale - 3))
        expectPinned (con True) correct
        forM_ [first, second] (assertFoldShape False)
  | (name, apply) <- rawFolds
  ] ++
  [ testCase (name ++ ": empty raw drivers return the exact symbolic initial") $
      within "empty fold oracle" $ do
        let initial = "literal-empty.initial" :: SymInteger
            scale = "literal-empty.scale" :: SymInteger
            emptyList = apply scale initial (conTerm [])
            emptyRange = apply scale initial (seqRangeTerm (conTerm 0))
        expectPinned (con True)
          ((emptyList .== initial) .&& (emptyRange .== initial))
        forM_ [emptyList, emptyRange] (assertFoldShape False)
  | (name, apply) <- rawFolds
  ] ++
  [ testCase (name ++ ": 32 lowers directly; 33 and dynamic drivers retain recursion") $ do
      let initial = "literal-boundary.initial" :: SymInteger
          scale = "literal-boundary.scale" :: SymInteger
          dynamicExtent = "literal-boundary.extent" :: SymInteger
          dynamicValues = "literal-boundary.values" :: SymSeq SymInteger
      -- This batch only renders SMT. In particular, it never asks a solver to
      -- prove anything about the large or unbounded recursive fallbacks.
      forM_ [conTerm [0 .. 31], seqRangeTerm (conTerm 32)] $ \driver ->
        assertFoldShape False (apply scale initial driver)
      forM_
        [ conTerm [0 .. 32], seqRangeTerm (conTerm 33)
        , seqRangeTerm (underlyingTerm dynamicExtent), underlyingTerm dynamicValues
        ] $ \driver -> assertFoldShape True (apply scale initial driver)
  | (name, apply) <- rawFolds
  ] ++
  [ testCase "nested focused/With small ranges retain local binders" $
      within "nested literal-fold oracle" $ do
        let initial = "literal-nested.initial" :: SymInteger
            scale = "literal-nested.scale" :: SymInteger
            inner = U.prepareSeqFoldWith @'S step
            outer = U.prepareFocusedSeqFold @'S
              (U.FocusedCapture (0 :: SymInteger) U.FocusedNoCaptures) $
                \(U.FocusedCapture capture U.FocusedNoCaptures) state index ->
                  3 * state + U.applySeqFoldWith @'S inner capture index
                    (U.rangeSeq @'S 4)
            apply capture start = U.applyFocusedSeqFold @'S outer
              (U.FocusedCapture capture U.FocusedNoCaptures) start
              (U.rangeSeq @'S 3)
            first = apply scale initial
            second = apply (scale + 2) (initial - 1)
            -- Inner: 81*index + 18*c. Outer weights are 9,3,1.
            oracle capture start = 27 * start + 234 * capture + 405
        expectPinned (con True)
          ((first .== oracle scale initial)
            .&& (second .== oracle (scale + 2) (initial - 1)))
        forM_ [first, second] (assertFoldShape False)
  , testCase "focused sequence captures stay distinct across small range applications" $
      within "literal sequence-capture oracle" $ do
        let firstValues = "literal-capture.first" :: SymSeq SymInteger
            secondValues = "literal-capture.second" :: SymSeq SymInteger
            initial = "literal-capture.initial" :: SymInteger
            bias = "literal-capture.bias" :: SymInteger
            prepared = U.prepareFocusedSeqFold @'S
              (U.FocusedCapture (U.nilSeq @'S @SymInteger) $
                U.FocusedCapture (0 :: SymInteger) U.FocusedNoCaptures) $
                \(U.FocusedCapture values
                    (U.FocusedCapture shift U.FocusedNoCaptures)) state index ->
                  3 * state + U.lookupSeqValue @'S (-11) values index + shift * index
            apply values shift start = U.applyFocusedSeqFold @'S prepared
              (U.FocusedCapture values $ U.FocusedCapture shift U.FocusedNoCaptures)
              start (U.rangeSeq @'S 3)
            first = apply firstValues bias initial
            second = apply secondValues (bias - 3) (initial + 1)
            inputs = (firstValues .== con [7, -2, 5 :: Integer])
              .&& (secondValues .== con [4, 9 :: Integer])
            -- 9*7 + 3*(-2) + 5 = 62; 9*4 + 3*9 + (-11) = 52.
            correct = (first .== 27 * initial + 62 + 5 * bias)
              .&& (second .== 27 * (initial + 1) + 52 + 5 * (bias - 3))
        expectPinned inputs correct
        forM_ [first, second] (assertFoldShape False)
  ]
