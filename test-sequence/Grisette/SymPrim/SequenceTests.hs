{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}

module Grisette.SymPrim.SequenceTests (sequenceTests) where

import Control.DeepSeq (NFData, force)
import Control.Exception (ErrorCall, displayException, evaluate, try)
import qualified Data.Binary as Binary
import Data.List (foldl', isPrefixOf)
import qualified Data.SBV.Dynamic as SBVD
import Grisette
  ( EvalSym (evalSym),
    Function ((#)),
    LogicalOp (symNot, (.&&)),
    SimpleMergeable (mrgIte),
    Solvable (con),
    SymEq ((.==)),
    SymBool,
    SymInteger,
    ToCon (toCon),
    TypedConstantSymbol,
    solve,
  )
import Grisette.Internal.Backend.Solving (z3)
import Grisette.Internal.Core.Data.Class.Solver (SolvingFailure (Unsat))
import Grisette.Internal.SymPrim.Prim.Term
  ( SupportedPrim (parseSMTModelResult),
  )
import Grisette.SymPrim
  ( SymPair,
    SymSeq,
    type (=~>),
    type (-~>),
    (-->),
  )
import Grisette.Unified (EvalModeTag (C, S))
import qualified Grisette.Unified as U
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assertBool, assertEqual, assertFailure)

sequenceTests :: Test
sequenceTests =
  testGroup
    "solver-native sequences and products"
    [ testCase "concrete folds are ordinary strict left folds" $ do
        assertEqual "foldSeq" 10 (U.foldSeq @'C (+) 0 [1 .. 4 :: Integer])
        assertEqual
          "foldSeqWith"
          20
          (U.foldSeqWith @'C (\scale acc x -> acc + scale * x) 2 0 [1 .. 4]),
      testCase "unknown four-pair sequence, symbolic environment, pair fold, and whole-value ITE" $ do
        let concrete = [(1, 2), (3, 4), (5, 6), (7, 8)] :: [(Integer, Integer)]
            expectedSequence = symbolicPairs concrete
            candidate = "pairs" :: SymSeq (SymPair SymInteger SymInteger)
            environment = "environment" :: SymInteger
            observed = "observed" :: SymPair SymInteger SymInteger
            choose = "choose" :: SymBool
            initial = U.pair @'S (0 :: SymInteger) (0 :: SymInteger)
            step ::
              SymInteger
                -~> SymPair SymInteger SymInteger
                -~> SymPair SymInteger SymInteger
                -~> SymPair SymInteger SymInteger
            step =
              con $
                ("environmentArg" :: TypedConstantSymbol Integer)
                  --> con
                    ( ("stateArg" :: TypedConstantSymbol (Integer, Integer))
                        --> con
                          ( ("elementArg" :: TypedConstantSymbol (Integer, Integer))
                              --> U.pair @'S
                                ( U.first @'S
                                    ("stateArg" :: SymPair SymInteger SymInteger)
                                    + U.first @'S
                                      ("elementArg" :: SymPair SymInteger SymInteger)
                                )
                                ( U.second @'S
                                    ("stateArg" :: SymPair SymInteger SymInteger)
                                    + ("environmentArg" :: SymInteger)
                                      * U.second @'S
                                        ("elementArg" :: SymPair SymInteger SymInteger)
                                )
                          )
                    )
            folded = U.foldSeqWith @'S step environment initial candidate
            alternativeSequence = symbolicPairs [(-1, -2)]
            alternativePair = U.pair @'S 99 100
            constraint =
              (candidate .== expectedSequence)
                .&& (environment .== 2)
                .&& (observed .== folded)
        solved <- solve z3 constraint
        case solved of
          Left failure -> assertFailure $ "expected SAT: " ++ show failure
          Right model -> do
            let decodedSequence = toCon (evalSym False model candidate)
                decodedEnvironment = toCon (evalSym False model environment)
                decodedFolded = toCon (evalSym False model folded)
                decodedResult = toCon (evalSym False model observed)
                recomputed = do
                  concreteSequence <- decodedSequence
                  concreteEnvironment <- decodedEnvironment
                  pure $
                    foldl'
                      (\(sumFirst, weightedSecond) (firstValue, secondValue) ->
                          ( sumFirst + firstValue,
                            weightedSecond + concreteEnvironment * secondValue
                          )
                      )
                      (0, 0)
                      concreteSequence
            assertEqual "decoded candidate" (Just concrete) decodedSequence
            assertEqual "direct decoded fold result" recomputed decodedFolded
            assertEqual "decoded fold result" recomputed decodedResult
            let roundTrip = Binary.decode (Binary.encode folded) :: SymPair SymInteger SymInteger
            roundTripFailure <- solve z3 (symNot (roundTrip .== folded))
            case roundTripFailure of
              Left Unsat -> pure ()
              Left failure -> assertFailure $ "solver failed: " ++ show failure
              Right _ -> assertFailure "serialized fold did not round-trip"
        trueBranch <- solve z3 (constraint .&& choose)
        falseBranch <- solve z3 (constraint .&& symNot choose)
        case (trueBranch, falseBranch) of
          (Right trueModel, Right falseModel) -> do
            assertEqual
              "sequence whole-value ITE true"
              (Just concrete)
              ( toCon $
                  evalSym
                    False
                    trueModel
                    (mrgIte choose candidate alternativeSequence)
              )
            assertEqual
              "sequence whole-value ITE false"
              (Just [(-1, -2)])
              ( toCon $
                  evalSym
                    False
                    falseModel
                    (mrgIte choose candidate alternativeSequence)
              )
            assertEqual
              "pair whole-value ITE true"
              (toCon (evalSym False trueModel observed) :: Maybe (Integer, Integer))
              ( toCon
                  (evalSym False trueModel (mrgIte choose observed alternativePair))
                  :: Maybe (Integer, Integer)
              )
            assertEqual
              "pair whole-value ITE false"
              (Just (99, 100))
              ( toCon
                  (evalSym False falseModel (mrgIte choose observed alternativePair))
                  :: Maybe (Integer, Integer)
              )
          (Left failure, _) ->
            assertFailure $ "expected true ITE branch SAT: " ++ show failure
          (_, Left failure) ->
            assertFailure $ "expected false ITE branch SAT: " ++ show failure,
      testCase "closed folds accept explicit environment and global UFs" $ do
        let environmentStep ::
              SymInteger -~> SymInteger -~> SymInteger -~> SymInteger
            environmentStep =
              con $
                ("environment" :: TypedConstantSymbol Integer)
                  --> con
                    ( ("state" :: TypedConstantSymbol Integer)
                        --> con
                          ( ("element" :: TypedConstantSymbol Integer)
                              --> ( ("environment" :: SymInteger)
                                      + ("state" :: SymInteger)
                                      + ("element" :: SymInteger)
                                  )
                          )
                    )
            generalUF = "generalUF" :: SymInteger -~> SymInteger
            tabularUF = "tabularUF" :: SymInteger =~> SymInteger
            ufStep :: SymInteger -~> SymInteger -~> SymInteger
            ufStep =
              con $
                ("state" :: TypedConstantSymbol Integer)
                  --> con
                    ( ("element" :: TypedConstantSymbol Integer)
                        --> ( ("state" :: SymInteger)
                                + generalUF # ("element" :: SymInteger)
                                + tabularUF # ("element" :: SymInteger)
                            )
                    )
            one = U.consSeq @'S (1 :: SymInteger) U.nilSeq
        _ <- evaluate (U.foldSeqWith @'S environmentStep ("env" :: SymInteger) 0 one)
        _ <- evaluate (U.foldSeq @'S ufStep 0 one)
        assertEqual
          "global UF nil identity"
          (Just 0)
          ( toCon (U.foldSeq @'S ufStep 0 (U.nilSeq @'S @SymInteger)) ::
              Maybe Integer
          ),
      testCase "captured scalar solver values are rejected before folding nil" $ do
        let hidden = "hidden" :: SymInteger
            capturedStep :: SymInteger -~> SymInteger -~> SymInteger
            capturedStep =
              con $
                ("state" :: TypedConstantSymbol Integer)
                  --> con
                    ( ("element" :: TypedConstantSymbol Integer)
                        --> ( ("state" :: SymInteger)
                                + ("element" :: SymInteger)
                                + hidden
                            )
                    )
        result <-
          try @ErrorCall $
            evaluate (U.foldSeq @'S capturedStep 0 (U.nilSeq @'S @SymInteger))
        case result of
          Left exception ->
            assertBool
              "capture diagnostic"
              ( "foldSeq step function captures solver values:"
                  `isPrefixOf` displayException exception
              )
          Right _ -> assertFailure "foldSeq accepted a captured solver value",
      testCase "raw nested pair sequence model decoder is exact" $ do
        let concrete = [(1, 2), (3, 4), (5, 6), (7, 8)] :: [(Integer, Integer)]
            cell (firstValue, secondValue) =
              SBVD.CTuple
                [SBVD.CInteger firstValue, SBVD.CInteger secondValue]
            value =
              SBVD.CV
                (SBVD.KList (SBVD.KTuple [SBVD.KUnbounded, SBVD.KUnbounded]))
                (SBVD.CList (cell <$> concrete))
        assertEqual
          "strict recursive decode"
          concrete
          (parseSMTModelResult @[(Integer, Integer)] 0 ([], value)),
      testCase "malformed list and pair models fail loudly" $ do
        let integer = SBVD.CV SBVD.KUnbounded (SBVD.CInteger 1)
            listOfIntegers =
              SBVD.CV (SBVD.KList SBVD.KUnbounded) (SBVD.CList [SBVD.CInteger 1])
            malformed =
              [ assertDecoderFailure $ force $
                  parseSMTModelResult @[Integer] 0 ([([], integer)], listOfIntegers),
                assertDecoderFailure $ force $
                  parseSMTModelResult @[Integer] 0 ([], integer),
                assertDecoderFailure $ force $
                  parseSMTModelResult @[Integer] 0
                    ( [],
                      SBVD.CV
                        (SBVD.KList SBVD.KUnbounded)
                        (SBVD.CInteger 1)
                    ),
                assertDecoderFailure $ force $
                  parseSMTModelResult @[Bool] 0
                    ( [],
                      SBVD.CV
                        (SBVD.KList SBVD.KBool)
                        (SBVD.CList [SBVD.CList []])
                    ),
                assertDecoderFailure $ force $
                  parseSMTModelResult @(Integer, Integer) 0
                    ( [],
                      SBVD.CV
                        (SBVD.KTuple [SBVD.KUnbounded])
                        (SBVD.CTuple [SBVD.CInteger 1])
                    ),
                assertDecoderFailure $ force $
                  parseSMTModelResult @(Integer, Integer) 0
                    ( [],
                      SBVD.CV
                        (SBVD.KTuple [SBVD.KUnbounded, SBVD.KUnbounded])
                        (SBVD.CTuple [SBVD.CInteger 1])
                    )
              ]
        sequence_ malformed,
      testCase "public exact model extraction preserves every pair" $ do
        let concrete = [(1, 2), (3, 4), (5, 6), (7, 8)] :: [(Integer, Integer)]
            candidate = "modelPairs" :: SymSeq (SymPair SymInteger SymInteger)
        solved <- solve z3 (candidate .== symbolicPairs concrete)
        case solved of
          Left failure -> assertFailure $ "expected SAT: " ++ show failure
          Right model ->
            assertEqual
              "production parseModel result"
              (Just concrete)
              (toCon (evalSym False model candidate))
    ]

assertDecoderFailure :: NFData value => value -> Assertion
assertDecoderFailure value = do
  result <- try @ErrorCall (evaluate value)
  case result of
    Left exception ->
      assertBool
        "strict decoder diagnostic"
        ("BUG: cannot parse SBV model value" `isPrefixOf` displayException exception)
    Right _ -> assertFailure "malformed model value decoded successfully"

symbolicPairs :: [(Integer, Integer)] -> SymSeq (SymPair SymInteger SymInteger)
symbolicPairs =
  foldr
    (\(firstValue, secondValue) ->
        U.consSeq @'S
          (U.pair @'S (fromInteger firstValue) (fromInteger secondValue))
    )
    U.nilSeq
