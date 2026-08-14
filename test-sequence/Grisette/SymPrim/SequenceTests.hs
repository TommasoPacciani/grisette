{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}

module Grisette.SymPrim.SequenceTests (sequenceTests) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.DeepSeq (NFData, force)
import Control.Exception (ErrorCall, displayException, evaluate, try)
import qualified Data.Binary as Binary
import qualified Data.ByteString.Lazy as LazyByteString
import Data.Int (Int64)
import Data.List (foldl', isPrefixOf)
import qualified Data.SBV.Dynamic as SBVD
import Grisette
  ( EvalSym (evalSym),
    Function ((#)),
    LogicalOp (symNot, (.&&)),
    SimpleMergeable (mrgIte),
    Solvable (con, ssym),
    SubstSym (substSym),
    SymEq ((.==)),
    SymBool,
    SymInteger,
    ToCon (toCon),
    TypedConstantSymbol,
    solve,
  )
import Grisette.Internal.Backend.Solving (z3)
import Grisette.Internal.Core.Data.Class.Solver (SolvingFailure (Unsat))
import Grisette.Internal.SymPrim.Array (Array)
import Grisette.Internal.SymPrim.Prim.Term
  ( LinkedRep (underlyingTerm, wrapTerm),
    SupportedPrim (parseSMTModelResult),
    Term,
    eqTerm,
    pevalNotTerm,
    ssymTerm,
    toCurThread,
  )
import Grisette.SymPrim
  ( SymArray,
    Nominal,
    NominalDomain (Domain),
    SymPair,
    SymNominal,
    SymSeq,
    SymWordN32,
    WordN32,
    type (=~>),
    type (-~>),
    (-->),
  )
import qualified Grisette.SymPrim.SymArray as A
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
      testCase "dense integer ranges stay native and preserve whole-term operations" $ do
        assertEqual "concrete zero" [] (U.rangeSeq @'C 0)
        assertEqual "concrete negative" [] (U.rangeSeq @'C (-3))
        assertEqual "concrete positive" [0, 1, 2, 3] (U.rangeSeq @'C 4)
        let extent = "rangeExtent" :: SymInteger
            ranged = U.rangeSeq @'S extent
            largeRange = U.rangeSeq @'S (100000 :: SymInteger)
            candidate = "rangeCandidate" :: SymSeq SymInteger
            expected =
              foldr
                (U.consSeq @'S . fromInteger)
                U.nilSeq
                [0, 1, 2, 3]
            checkedLast = U.lookupSeq @'S (-1) ranged 3
            checkedPastEnd = U.lookupSeq @'S (-1) ranged 4
            roundTrip =
              Binary.decode (Binary.encode ranged) ::
                SymSeq SymInteger
            substituted =
              substSym
                ("rangeExtent" :: TypedConstantSymbol Integer)
                (4 :: SymInteger)
                ranged
            rangeFunction :: SymInteger -~> SymSeq SymInteger
            rangeFunction =
              con $
                ("rangeArgument" :: TypedConstantSymbol Integer)
                  --> U.rangeSeq @'S ("rangeArgument" :: SymInteger)
        assertEqual "single native symbolic node" "(seq.range rangeExtent)" (show ranged)
        assertEqual
          "large concrete extent remains one native node"
          "(seq.range 100000)"
          (show largeRange)
        assertEqual
          "same range term is interned"
          (underlyingTerm ranged)
          (underlyingTerm (U.rangeSeq @'S extent))
        assertEqual
          "substitution rebuilds range"
          "(seq.range 4)"
          (show substituted)
        assertEqual
          "general function rebuilds range"
          "(seq.range 4)"
          (show (rangeFunction # (4 :: SymInteger)))
        foreignRange <- newEmptyMVar
        _ <- forkIO $ do
          let value = U.rangeSeq @'S ("foreignRangeExtent" :: SymInteger)
          term <- evaluate $ force (underlyingTerm value)
          putMVar foreignRange term
        reconstructed <- takeMVar foreignRange >>= toCurThread
        assertEqual
          "cross-thread reconstruction"
          "(seq.range foreignRangeExtent)"
          (show (wrapTerm reconstructed :: SymSeq SymInteger))
        solved <-
          solve z3 $
            (extent .== 4)
              .&& (candidate .== ranged)
              .&& (ranged .== expected)
              .&& (roundTrip .== ranged)
              .&& (U.lengthSeq @'S ranged .== 4)
              .&& (U.first @'S checkedLast .== con True)
              .&& (U.second @'S checkedLast .== 3)
              .&& (U.first @'S checkedPastEnd .== con False)
              .&& (U.second @'S checkedPastEnd .== (-1))
        case solved of
          Left failure -> assertFailure $ "expected native range SAT: " ++ show failure
          Right model -> do
            assertEqual
              "exact extent model"
              (Just 4 :: Maybe Integer)
              (toCon (evalSym False model extent))
            assertEqual
              "exact range model"
              (Just [0, 1, 2, 3] :: Maybe [Integer])
              (toCon (evalSym False model candidate)),
      testCase "sequence tail is native, total, and stack-shaped" $ do
        assertEqual "concrete empty" ([] :: [Integer]) (U.tailSeq @'C [])
        assertEqual "concrete singleton" ([] :: [Integer]) (U.tailSeq @'C [7])
        assertEqual "concrete drop head" [2, 3] (U.tailSeq @'C [1, 2, 3 :: Integer])
        let stack = "tailStack" :: SymSeq SymInteger
            pushed = U.consSeq @'S (11 :: SymInteger) stack
            popped = U.tailSeq @'S pushed
            symbolicTail = U.tailSeq @'S stack
            roundTrip =
              Binary.decode (Binary.encode symbolicTail) ::
                SymSeq SymInteger
            substituted =
              substSym
                ("tailStack" :: TypedConstantSymbol [Integer])
                (foldr (U.consSeq @'S . fromInteger) U.nilSeq [4, 5, 6] ::
                   SymSeq SymInteger)
                symbolicTail
            tailFunction :: SymSeq SymInteger -~> SymSeq SymInteger
            tailFunction =
              con $
                ("tailArgument" :: TypedConstantSymbol [Integer])
                  --> U.tailSeq @'S ("tailArgument" :: SymSeq SymInteger)
        assertEqual
          "push then pop cancels without a solver node"
          (underlyingTerm stack)
          (underlyingTerm popped)
        assertEqual
          "single native symbolic node"
          "(seq.tail tailStack)"
          (show symbolicTail)
        assertEqual
          "same tail term is interned"
          (underlyingTerm symbolicTail)
          (underlyingTerm (U.tailSeq @'S stack))
        assertEqual
          "substitution evaluates the tail"
          (show (foldr (U.consSeq @'S . fromInteger) U.nilSeq [5, 6] ::
                   SymSeq SymInteger))
          (show substituted)
        assertEqual
          "general function rebuilds tail"
          "(seq.tail tailArgument)"
          (show (tailFunction # ("tailArgument" :: SymSeq SymInteger)))
        solved <-
          solve z3 $
            ( stack
                .== (foldr (U.consSeq @'S . fromInteger) U.nilSeq [1, 2, 3] ::
                       SymSeq SymInteger)
            )
              .&& (roundTrip .== symbolicTail)
              .&& (U.lengthSeq @'S symbolicTail .== 2)
        case solved of
          Left failure -> assertFailure $ "expected native tail SAT: " ++ show failure
          Right model ->
            assertEqual
              "exact tail model"
              (Just [2, 3] :: Maybe [Integer])
              (toCon (evalSym False model symbolicTail)),
      testCase "empty symbolic tail stays empty" $ do
        emptyTail <-
          solve z3 $
            U.lengthSeq @'S (U.tailSeq @'S (U.nilSeq @'S @SymInteger)) .== 0
        case emptyTail of
          Left failure -> assertFailure $ "expected empty tail SAT: " ++ show failure
          Right _ -> pure ()
        negative <-
          solve z3 $
            U.lengthSeq @'S (U.tailSeq @'S ("negativeTail" :: SymSeq SymInteger))
              .== (-1)
        case negative of
          Left Unsat -> pure ()
          Left failure -> assertFailure $ "expected Unsat: " ++ show failure
          Right _ -> assertFailure "tail length must never be negative",
      testCase "checked sequence lookup guards the partial solver operation" $ do
        assertEqual
          "concrete in bounds"
          (True, 20)
          (U.lookupSeq @'C 99 [10, 20 :: Integer] 1)
        assertEqual
          "concrete negative"
          (False, 99)
          (U.lookupSeq @'C 99 [10, 20 :: Integer] (-1))
        assertEqual
          "concrete upper bound"
          (False, 99)
          (U.lookupSeq @'C 99 [10, 20 :: Integer] 2)
        let values = "lookupValues" :: SymSeq SymInteger
            index = "lookupIndex" :: SymInteger
            lookedUp = U.lookupSeq @'S 99 values index
            present = U.first @'S lookedUp
            selected = U.second @'S lookedUp
            expected =
              U.consSeq @'S 10 $ U.consSeq @'S 20 U.nilSeq
            roundTrip =
              Binary.decode (Binary.encode lookedUp) ::
                SymPair SymBool SymInteger
            expectModel :: String -> Integer -> Bool -> Integer -> Assertion
            expectModel label requested guard value = do
              solved <-
                solve z3 $
                  (values .== expected)
                    .&& (index .== con requested)
                    .&& (present .== con guard)
                    .&& (selected .== con value)
                    .&& (roundTrip .== lookedUp)
              case solved of
                Left failure ->
                  assertFailure $ label ++ " lookup failed: " ++ show failure
                Right model ->
                  assertEqual
                    label
                    (Just (guard, value))
                    (toCon (evalSym False model lookedUp))
        expectModel "symbolic in bounds" 1 True 20
        expectModel "symbolic negative" (-1) False 99
        expectModel "symbolic upper bound" 2 False 99,
      testCase "native zip truncates unknown sequences and preserves array products" $ do
        assertEqual
          "concrete unequal lengths"
          [(1, 4), (2, 5)]
          (U.zipSeq @'C [1, 2, 3 :: Integer] [4, 5])
        assertEqual
          "concrete equal lengths"
          [(1, 4), (2, 5), (3, 6)]
          (U.zipSeq @'C [1, 2, 3 :: Integer] [4, 5, 6])
        let left = "zipLeft" :: SymSeq SymInteger
            right = "zipRight" :: SymSeq SymInteger
            zipped = U.zipSeq @'S left right
            integers =
              foldr
                (U.consSeq @'S . fromInteger)
                U.nilSeq
            solveZip rightValues expected = do
              solved <-
                solve z3 $
                  (left .== integers [1, 2, 3])
                    .&& (right .== integers rightValues)
                    .&& (zipped .== symbolicPairs expected)
                    .&& (U.lengthSeq @'S zipped .== fromIntegral (length expected))
              case solved of
                Left failure -> assertFailure $ "expected zipped sequence SAT: " ++ show failure
                Right model ->
                  assertEqual
                    "exact zipped model"
                    (Just expected)
                    (toCon (evalSym False model zipped))
        solveZip [4, 5] [(1, 4), (2, 5)]
        solveZip [4, 5, 6] [(1, 4), (2, 5), (3, 6)]
        solveZip [4, 5, 6, 7] [(1, 4), (2, 5), (3, 6)]
        let roundTrip =
              Binary.decode (Binary.encode zipped) ::
                SymSeq (SymPair SymInteger SymInteger)
        roundTripFailure <- solve z3 (symNot (roundTrip .== zipped))
        case roundTripFailure of
          Left Unsat -> pure ()
          Left failure -> assertFailure $ "serialized zip solver failed: " ++ show failure
          Right _ -> assertFailure "serialized native zip did not round-trip"
        let arraySequence =
              U.consSeq @'S
                (A.const (7 :: SymInteger) :: SymArray SymInteger SymInteger)
                U.nilSeq
            indexSequence = U.consSeq @'S (3 :: SymInteger) U.nilSeq
            arrayStep ::
              SymInteger
                -~> SymPair
                  (SymArray SymInteger SymInteger)
                  SymInteger
                -~> SymInteger
            arrayStep =
              con $
                ("arrayState" :: TypedConstantSymbol Integer)
                  --> con
                    ( ( "arrayElement" ::
                          TypedConstantSymbol (Array Integer Integer, Integer)
                      )
                        --> ( ("arrayState" :: SymInteger)
                                + A.select
                                  ( U.first @'S
                                      ( "arrayElement" ::
                                          SymPair
                                            (SymArray SymInteger SymInteger)
                                            SymInteger
                                      )
                                  )
                                  ( U.second @'S
                                      ( "arrayElement" ::
                                          SymPair
                                            (SymArray SymInteger SymInteger)
                                            SymInteger
                                      )
                                  )
                            )
                    )
            arrayFold =
              U.foldSeq @'S
                arrayStep
                0
                (U.zipSeq @'S arraySequence indexSequence)
        arraySolved <- solve z3 (arrayFold .== 7)
        case arraySolved of
          Left failure -> assertFailure $ "array-bearing zip failed: " ++ show failure
          Right _ -> pure (),
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
      testCase "unit model decoder accepts only the exact zero tuple" $ do
        let unit = SBVD.CV (SBVD.KTuple []) (SBVD.CTuple [])
            integer = SBVD.CV SBVD.KUnbounded (SBVD.CInteger 0)
            wrongArity = SBVD.CV (SBVD.KTuple []) (SBVD.CTuple [SBVD.CInteger 0])
        assertEqual "exact unit decode" () (parseSMTModelResult @() 0 ([], unit))
        let serializedUnit = ssymTerm @() "serializedUnit"
        assertEqual
          "unit known-type round-trip"
          serializedUnit
          (Binary.decode (Binary.encode serializedUnit) :: Term ())
        sequence_
          [ assertDecoderFailure $ force $
              parseSMTModelResult @() 0 ([([], unit)], unit),
            assertDecoderFailure $ force $
              parseSMTModelResult @() 0 ([([unit], unit)], unit),
            assertDecoderFailure $ force $
              parseSMTModelResult @() 0 ([], integer),
            assertDecoderFailure $ force $
              parseSMTModelResult @() 0 ([], wrongArity)
          ],
      testCase "symbolic unit disequality is unsatisfiable" $ do
        let disequality =
              wrapTerm
                ( pevalNotTerm $
                    eqTerm (ssymTerm @() "unitLeft") (ssymTerm @() "unitRight")
                ) :: SymBool
        solved <- solve z3 disequality
        case solved of
          Left Unsat -> pure ()
          Left failure -> assertFailure $ "solver failed: " ++ show failure
          Right _ -> assertFailure "distinct symbolic unit values were admitted",
      testCase "a unit-keyed array is determined by its sole cell" $ do
        let left = "unitLeftArray" :: SymArray () SymInteger
            right = "unitRightArray" :: SymArray () SymInteger
            counterexample =
              (A.select left () .== A.select right ())
                .&& symNot (left .== right)
        solved <- solve z3 counterexample
        case solved of
          Left Unsat -> pure ()
          Left failure -> assertFailure $ "solver failed: " ++ show failure
          Right _ -> assertFailure "equal sole cells did not determine unit-keyed arrays",
      testCase "structural nominal domains erase only at the solver boundary" $ do
        let left =
              ssym "grisette.uninterp.con.adversarial" ::
                SymNominal
                  ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                  WordN32
            right =
              ssym "grisette.uninterp.con.adversarial" ::
                SymNominal
                  ('Domain "p4runtime" '[ 'Domain "right" '[] ])
                  WordN32
            alternative =
              ssym "alternativeNominal" ::
                SymNominal
                  ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                  WordN32
            leftValue = U.nominalValue @'S left :: SymWordN32
            rightValue = U.nominalValue @'S right :: SymWordN32
            alternativeValue = U.nominalValue @'S alternative :: SymWordN32
            leftSequence = U.consSeq @'S left U.nilSeq
            step ::
              SymWordN32
                -~> SymNominal
                  ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                  WordN32
                -~> SymWordN32
            step =
              con $
                ("nominalState" :: TypedConstantSymbol WordN32)
                  --> con
                    ( ( "nominalElement" ::
                          TypedConstantSymbol
                            ( Nominal
                                ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                                WordN32
                            )
                      )
                        --> ( ("nominalState" :: SymWordN32)
                                + U.nominalValue
                                  @'S
                                  ( "nominalElement" ::
                                      SymNominal
                                        ( 'Domain
                                            "p4runtime"
                                            '[ 'Domain "left" '[] ]
                                        )
                                        WordN32
                                  )
                            )
                    )
            folded = U.foldSeq @'S step 0 leftSequence
            nested = U.pair @'S leftSequence (U.pair @'S left right)
            leftArray = "nominalArray" ::
              SymArray
                ( SymNominal
                    ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                    WordN32
                )
                SymInteger
            chooseNominal = "chooseNominal" :: SymBool
            chosenNominal = mrgIte chooseNominal left alternative
            chosenValue = U.nominalValue @'S chosenNominal :: SymWordN32
            constraint =
              (leftValue .== 1)
                .&& (rightValue .== 2)
                .&& (alternativeValue .== 3)
                .&& (folded .== 1)
                .&& chooseNominal
                .&& (chosenValue .== 1)
                .&& (A.select leftArray left .== 9)
        solved <- solve z3 constraint
        case solved of
          Left failure -> assertFailure $ "expected distinct nominal symbols SAT: " ++ show failure
          Right model -> do
            assertEqual
              "left nominal model"
              (Just 1)
              ( U.nominalValue @'C
                  <$> ( toCon (evalSym False model left) ::
                          Maybe
                            ( Nominal
                                ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                                WordN32
                            )
                      )
              )
            assertEqual
              "right nominal model"
              (Just 2)
              ( U.nominalValue @'C
                  <$> ( toCon (evalSym False model right) ::
                          Maybe
                            ( Nominal
                                ('Domain "p4runtime" '[ 'Domain "right" '[] ])
                                WordN32
                            )
                      )
              )
            assertEqual
              "nested nominal product model"
              (Just ([1], (1, 2)))
              ( do
                  (values, (leftResult, rightResult)) <-
                    ( toCon (evalSym False model nested) ::
                        Maybe
                          ( [ Nominal
                                ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                                WordN32
                            ],
                            ( Nominal
                                ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                                WordN32,
                              Nominal
                                ('Domain "p4runtime" '[ 'Domain "right" '[] ])
                                WordN32
                            )
                          )
                    )
                  pure
                    ( U.nominalValue @'C <$> values,
                      ( U.nominalValue @'C leftResult,
                        U.nominalValue @'C rightResult
                      )
                    )
              )
        falseBranch <-
          solve z3 $
            (leftValue .== 1)
              .&& (alternativeValue .== 3)
              .&& symNot chooseNominal
              .&& (chosenValue .== 3)
        case falseBranch of
          Left failure -> assertFailure $ "nominal false ITE branch failed: " ++ show failure
          Right _ -> pure ()
        let wrapped =
              U.nominal @'S
                ("wrappedNominal" :: SymWordN32) ::
                SymNominal
                  ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                  WordN32
            wrappedRoundTrip = Binary.decode (Binary.encode wrapped)
            unwrapped = U.nominalValue @'S left :: SymWordN32
            unwrappedRoundTrip = Binary.decode (Binary.encode unwrapped)
            nestedNominal =
              U.nominal @'S
                ( U.nominal @'S
                    ("nestedNominal" :: SymWordN32) ::
                    SymNominal ('Domain "inner" '[]) WordN32
                ) ::
                SymNominal
                  ('Domain "outer" '[])
                  (Nominal ('Domain "inner" '[]) WordN32)
            nestedNominalRoundTrip =
              Binary.decode (Binary.encode nestedNominal)
        wrapMismatch <- solve z3 (symNot (wrappedRoundTrip .== wrapped))
        unwrapMismatch <- solve z3 (symNot (unwrappedRoundTrip .== unwrapped))
        nestedMismatch <-
          solve z3 (symNot (nestedNominalRoundTrip .== nestedNominal))
        case (wrapMismatch, unwrapMismatch, nestedMismatch) of
          (Left Unsat, Left Unsat, Left Unsat) -> pure ()
          (Left failure, _, _) ->
            assertFailure $ "nominal wrap round-trip failed: " ++ show failure
          (_, Left failure, _) ->
            assertFailure $ "nominal unwrap round-trip failed: " ++ show failure
          (_, _, Left failure) ->
            assertFailure $ "nested nominal round-trip failed: " ++ show failure
          _ -> assertFailure "serialized nominal casts changed their terms"
        let encoded = Binary.encode wrapped
            wrongDomain = Binary.decodeOrFail encoded ::
              Either
                (LazyByteString.ByteString, Int64, String)
                ( LazyByteString.ByteString,
                  Int64,
                  SymNominal
                    ('Domain "p4runtime" '[ 'Domain "right" '[] ])
                    WordN32
                )
            wrongBase = Binary.decodeOrFail encoded ::
              Either
                (LazyByteString.ByteString, Int64, String)
                ( LazyByteString.ByteString,
                  Int64,
                  SymNominal
                    ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                    Integer
                )
        case (wrongDomain, wrongBase) of
          (Left _, Left _) -> pure ()
          (Right _, _) -> assertFailure "nominal term decoded at a different domain"
          (_, Right _) -> assertFailure "nominal term decoded at a different recursive base",
      testCase "wrapping one raw term in two domains preserves its identity" $ do
        let raw = "sharedNominalValue" :: SymWordN32
            left =
              U.nominal @'S raw ::
                SymNominal ('Domain "left" '[]) WordN32
            right =
              U.nominal @'S raw ::
                SymNominal ('Domain "right" '[]) WordN32
        solved <-
          solve z3 $
            symNot
              ( (U.nominalValue @'S left :: SymWordN32)
                  .== (U.nominalValue @'S right :: SymWordN32)
              )
        case solved of
          Left Unsat -> pure ()
          Left failure -> assertFailure $ "solver failed: " ++ show failure
          Right _ -> assertFailure "nominal casts manufactured a second solver value",
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
