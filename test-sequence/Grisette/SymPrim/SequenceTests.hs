{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Grisette.SymPrim.SequenceTests (sequenceTests) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.DeepSeq (NFData, force)
import Control.Exception (ErrorCall, displayException, evaluate, try)
import Control.Monad (forM_)
import qualified Data.Binary as Binary
import qualified Data.ByteString.Lazy as LazyByteString
import Data.Int (Int64)
import Data.List (foldl', isPrefixOf)
import Data.String (fromString)
import qualified Data.SBV.Dynamic as SBVD
import Grisette
  ( AsKey (AsKey),
    EvalSym (evalSym),
    Function ((#)),
    LogicalOp (symNot, (.&&)),
    SimpleMergeable (mrgIte),
    Solvable (con, isym, ssym),
    SubstSym (substSym),
    SymEq ((.==)),
    SymOrd ((.>)),
    SymBool,
    SymInteger,
    ToCon (toCon),
    TypedConstantSymbol,
    solve,
  )
import Grisette.Internal.Backend.Solving (z3)
import Grisette.Internal.SymPrim.Quantifier (forallSym)
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
import Grisette.Internal.SymPrim.Prim.Term (typedConstantSymbol)
import Grisette.Internal.Core.Data.Symbol (Symbol (IndexedSymbol))
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
              SymInteger ->
              SymPair (SymArray SymInteger SymInteger) SymInteger ->
              SymInteger
            arrayStep arrayState arrayElement =
              arrayState
                + A.select
                  (U.first @'S arrayElement)
                  (U.second @'S arrayElement)
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
              SymInteger ->
              SymPair SymInteger SymInteger ->
              SymPair SymInteger SymInteger ->
              SymPair SymInteger SymInteger
            step environmentArg stateArg elementArg =
              U.pair @'S
                (U.first @'S stateArg + U.first @'S elementArg)
                ( U.second @'S stateArg
                    + environmentArg * U.second @'S elementArg
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
              SymInteger -> SymInteger -> SymInteger -> SymInteger
            environmentStep environment state element =
              environment + state + element
            generalUF = "generalUF" :: SymInteger -~> SymInteger
            tabularUF = "tabularUF" :: SymInteger =~> SymInteger
            ufStep :: SymInteger -> SymInteger -> SymInteger
            ufStep state element =
              state + generalUF # element + tabularUF # element
            one = U.consSeq @'S (1 :: SymInteger) U.nilSeq
        _ <- evaluate (U.foldSeqWith @'S environmentStep ("env" :: SymInteger) 0 one)
        _ <- evaluate (U.foldSeq @'S ufStep 0 one)
        assertEqual
          "global UF nil identity"
          (Just 0)
          ( toCon (U.foldSeq @'S ufStep 0 (U.nilSeq @'S @SymInteger)) ::
              Maybe Integer
          ),
      testCase "closed fold abstraction shares its step term DAG" $ do
        let sharedStep ::
              SymInteger -> SymInteger -> SymInteger -> SymInteger
            sharedStep environment state element =
              foldl'
                (\shared _ -> shared + shared)
                (environment + state + element)
                [1 .. 20 :: Int]
            candidate = "shared-fold-candidate" :: SymSeq SymInteger
            firstFold = U.foldSeqWith @'S sharedStep 2 5 candidate
            secondFold = U.foldSeqWith @'S sharedStep 2 5 candidate
        assertEqual
          "nil identity after abstracting a deeply shared step"
          (Just 5)
          ( toCon
              ( U.foldSeqWith @'S
                  sharedStep
                  2
                  5
                  (U.nilSeq @'S @SymInteger)
              ) ::
              Maybe Integer
          )
        assertEqual
          "fresh private binders retain one alpha-normalized fold term"
          (AsKey firstFold)
          (AsKey secondFold),
      testCase "location-keyed folds reuse a closed step and reject captures" $ do
        let key = $$(U.seqFoldKey "sequence-test.reusable")
            step :: SymInteger -> SymInteger -> SymInteger -> SymInteger
            step environment state element = environment + state + element
            candidate = "keyed-fold-candidate" :: SymSeq SymInteger
            firstFold = U.foldSeqWithKey @'S key step 2 5 candidate
            secondFold = U.foldSeqWithKey @'S key step 2 5 candidate
        assertEqual "keyed concrete fold" 20
          (U.foldSeqWithKey @'C key (\scale acc x -> acc + scale * x)
            2 0 [1 .. 4 :: Integer])
        assertEqual "keyed symbolic fold is shared"
          (AsKey firstFold) (AsKey secondFold)
        let hidden = "keyed-hidden" :: SymInteger
            captured :: SymInteger -> SymInteger -> SymInteger -> SymInteger
            captured environment state element =
              environment + state + element + hidden
        result <- try @ErrorCall $ evaluate
          (U.foldSeqWithKey @'S key captured 1 0 (U.nilSeq @'S @SymInteger))
        case result of
          Left exception -> assertBool "keyed capture diagnostic"
            ( "foldSeqWith step function captures solver values:"
                `isPrefixOf` displayException exception )
          Right _ -> assertFailure "location-keyed fold accepted a capture",
      testCase "re-entrant location-keyed folds keep binders distinct" $ do
        let key = $$(U.seqFoldKey "sequence-test.reentrant")
            one = U.consSeq @'S (1 :: SymInteger) U.nilSeq
            outerStep
              :: SymInteger -> SymInteger -> SymInteger -> SymInteger
            outerStep environment state element =
              state + element + U.foldSeqWithKey @'S key
                (\_ innerState innerElement ->
                  innerState + innerElement + environment)
                (0 :: SymInteger) 0 one
        result <- try @ErrorCall $ evaluate
          (U.foldSeqWithKey @'S key outerStep 1 0 one)
        case result of
          Left exception -> assertBool "re-entrant capture diagnostic"
            ( "foldSeqWith step function captures solver values:"
                `isPrefixOf` displayException exception )
          Right _ -> assertFailure
            "re-entrant keyed fold captured an enclosing binder",
      testCase "captured scalar solver values are rejected before folding nil" $ do
        let hidden = "hidden" :: SymInteger
            capturedStep :: SymInteger -> SymInteger -> SymInteger
            capturedStep state element = state + element + hidden
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
      testCase "a global named like the fold's own binder is still a capture" $ do
        -- The abstraction picks binder names that avoid every name the step's body
        -- uses.  A fixed binder name would bind this global instead, turning a
        -- capture that must be reported into a silently wrong fold.
        let shadowed = ssym "grisette.foldSeq.state" :: SymInteger
            shadowingStep :: SymInteger -> SymInteger -> SymInteger
            shadowingStep state element = state + element + shadowed
            shadowedWith = ssym "grisette.foldSeqWith.state" :: SymInteger
            shadowingStepWith ::
              SymInteger -> SymInteger -> SymInteger -> SymInteger
            shadowingStepWith environment state element =
              environment + state + element + shadowedWith
        folded <-
          try @ErrorCall $
            evaluate (U.foldSeq @'S shadowingStep 0 (U.nilSeq @'S @SymInteger))
        case folded of
          Left exception ->
            assertBool
              "capture diagnostic for a binder-named global"
              ( "foldSeq step function captures solver values:"
                  `isPrefixOf` displayException exception
              )
          Right _ ->
            assertFailure "foldSeq captured a global named like its own binder"
        foldedWith <-
          try @ErrorCall $
            evaluate
              ( U.foldSeqWith @'S
                  shadowingStepWith
                  1
                  0
                  (U.nilSeq @'S @SymInteger)
              )
        case foldedWith of
          Left exception ->
            assertBool
              "capture diagnostic for a binder-named global with environment"
              ( "foldSeqWith step function captures solver values:"
                  `isPrefixOf` displayException exception
              )
          Right _ ->
            assertFailure
              "foldSeqWith captured a global named like its own binder",
      testCase "substituting under a quantifier does not capture its binder" $ do
        -- Function binders live in a namespace the public API cannot write, so a
        -- replacement can no longer collide with one.  Quantifier binders are
        -- still caller-chosen, so they are where capture avoidance is observable:
        -- (forall q. q > w)[w := q] means (forall q'. q' > q), not (forall q. q > q).
        let quantified =
              forallSym ("q" :: SymInteger) (("q" :: SymInteger) .> "w")
            replaced =
              substSym
                (typedConstantSymbol "w" :: TypedConstantSymbol Integer)
                ("q" :: SymInteger)
                quantified
            captured = forallSym ("q" :: SymInteger) (("q" :: SymInteger) .> "q")
        assertBool
          ("the quantified binder must be renamed, got " ++ show replaced)
          (AsKey replaced /= AsKey captured)
        solved <- solve z3 (symNot replaced)
        case solved of
          Right _ -> pure ()
          Left failure ->
            assertFailure
              ( "a renamed quantifier leaves a satisfiable negation, got "
                  ++ show failure
              ),
      testCase "no name lets a step smuggle a captured solver value past the check" $ do
        -- A step is an arbitrary Haskell function: it may inspect the identity of
        -- what it is handed and return a different expression on a later call, so
        -- examining one application's output cannot establish closedness.  What
        -- makes the check sound is that the step cannot name a binder, so every
        -- guess below stays free and is reported.
        let names =
              [ "arg",
                "arg@0",
                "arg!0",
                "foldSeq.state",
                "foldSeq.element",
                "grisette.foldSeq.state"
              ]
            -- Every shape a caller can write: a plain symbol, and an indexed one
            -- at the indices an abstraction is likely to allocate.
            guesses =
              [ (name, ssym (fromString name) :: SymInteger)
                | name <- names
              ]
                ++ [ (name ++ "@" ++ show index, isym (fromString name) index)
                     | name <- names,
                       index <- [0 .. 3 :: Int]
                   ]
            inspecting :: SymInteger -> SymInteger -> SymInteger -> SymInteger
            inspecting hidden state _ =
              if AsKey state == AsKey hidden then hidden else state + hidden
        forM_ guesses $ \(name, hidden) -> do
          outcome <-
            try @ErrorCall $
              evaluate
                ( U.foldSeq @'S
                    (inspecting hidden)
                    0
                    (U.nilSeq @'S @SymInteger)
                )
          case outcome of
            Left exception ->
              assertBool
                ("capture diagnostic for " ++ name)
                ( "foldSeq step function captures solver values:"
                    `isPrefixOf` displayException exception
                )
            Right _ ->
              assertFailure
                ("a step capturing " ++ show name ++ " was accepted"),
      testCase "a step closing over an enclosing fold's argument is rejected" $ do
        -- Each abstraction allocates its own binder, so an inner step that closes
        -- over the outer argument leaves it free and is reported.  A shared binder
        -- name would instead rebind it to the inner argument, silently.
        let nested :: SymInteger -> SymInteger -> SymInteger
            nested outerState _ =
              U.foldSeq @'S
                (\innerState _ -> innerState + outerState)
                0
                (U.nilSeq @'S @SymInteger)
        outcome <-
          try @ErrorCall $
            evaluate (U.foldSeq @'S nested 0 (U.nilSeq @'S @SymInteger))
        case outcome of
          Left exception ->
            assertBool
              ("capture diagnostic, got " ++ displayException exception)
              ( "foldSeq step function captures solver values:"
                  `isPrefixOf` displayException exception
              )
          Right _ ->
            assertFailure "an inner step captured the enclosing fold's argument",
      testCase "an enclosing value reaches an inner fold through the environment" $ do
        -- The sanctioned way to use an enclosing value: pass it as the fold's
        -- environment, which is an argument of the fold and not part of the step.
        let nested :: SymInteger -> SymInteger -> SymInteger
            nested outerState _ =
              U.foldSeqWith @'S
                (\environment innerState _ -> innerState + environment)
                outerState
                0
                (U.consSeq @'S 1 (U.nilSeq @'S @SymInteger))
            folded = U.foldSeq @'S nested 5 (U.consSeq @'S 2 U.nilSeq)
        assertEqual "the environment carries the outer state" (AsKey 5) (AsKey folded),
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
              SymWordN32 ->
              SymNominal
                ('Domain "p4runtime" '[ 'Domain "left" '[] ])
                WordN32 ->
              SymWordN32
            step nominalState nominalElement =
              nominalState + U.nominalValue @'S nominalElement
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
