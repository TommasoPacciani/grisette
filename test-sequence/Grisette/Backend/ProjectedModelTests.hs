{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}

module Grisette.Backend.ProjectedModelTests (projectedModelTests) where

import Control.Concurrent (newEmptyMVar, putMVar, readMVar, takeMVar, tryPutMVar)
import Control.Exception (Exception, finally, throwIO, try)
import Control.Monad (forM_, void)
import qualified Data.ByteString.Char8 as ByteString
import Data.Char (isSpace)
import Data.List (isInfixOf, isPrefixOf)
import qualified Data.SBV as SBV
import Grisette
  ( AnySymbolSet,
    EvalSym (evalSym),
    ExtractSym (extractSym),
    Function ((#)),
    LogicalOp ((.&&), symNot),
    Model,
    ModelOps (emptyModel, isEmptyModel, restrictTo),
    Solvable (con, isym),
    SymBool,
    SymEq ((./=), (.==)),
    SymInteger,
    ToCon (toCon),
  )
import Grisette.Internal.Backend.Solving
  ( GrisetteSMTConfig (sbvConfig),
    runSBVIncremental,
    z3,
  )
import Grisette.Internal.Core.Data.Class.Solver
  ( ModelProjection (AllModelSymbols, OnlyModelSymbols),
    MonadicSolver (monadicSolverAssert, monadicSolverCheckSat),
    Solver
      ( solverAssert,
        solverCheckSat,
        solverPop,
        solverPush,
        solverResetAssertions,
        solverRunCommand
      ),
    SolverCommand (SolverCheckSat),
    SolvingFailure (Terminated, Unsat),
    withSolver,
  )
import Grisette.SymPrim
  ( SymArray,
    SymPair,
    SymSeq,
    SymUninterp,
    type (-~>),
    type (=~>),
  )
import qualified Grisette.SymPrim.SymArray as Array
import System.IO (hClose, openTempFile)
import System.Timeout (timeout)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (assertBool, assertEqual)

within :: String -> IO value -> IO value
within label action =
  timeout 10000000 action >>= \case
    Nothing -> fail $ label ++ " did not finish within 10 seconds"
    Just value -> pure value

expectRight :: String -> Either SolvingFailure value -> IO value
expectRight label = \case
  Left failure -> fail $ label ++ ": " ++ show failure
  Right value -> pure value

command :: String -> IO (Either SolvingFailure ()) -> IO ()
command label action = action >>= expectRight label

modelFor :: Solver solver => solver -> ModelProjection -> IO Model
modelFor solver projection =
  solverCheckSat solver projection >>= expectRight "expected real-Z3 SAT"

onlyRequested :: AnySymbolSet -> Model -> IO ()
onlyRequested requested model =
  assertEqual "no unrequested assignment escapes" model (restrictTo requested model)

modelSatisfies :: Model -> SymBool -> IO ()
modelSatisfies model formula =
  assertEqual "requested assignments decode the constrained observations"
    (Just True) (toCon (evalSym False model formula))

-- Keep each real solver conversation as a unique persistent artifact. Read it
-- only after withSolver has joined its worker: assertions merely enqueue work,
-- and SBV opens the file separately for startup and each recorded message.
withTranscript :: (FilePath -> GrisetteSMTConfig -> IO value) -> IO value
withTranscript action = do
  (path, handle) <- openTempFile "/tmp" "p4check2-projected-model-.smt2"
  hClose handle
  putStrLn $ "projected-model transcript: " ++ path
  action path (z3 {sbvConfig = (sbvConfig z3) {SBV.transcript = Just path}})

sentCommands :: FilePath -> IO [String]
sentCommands path = do
  contents <- ByteString.readFile path
  pure
    [ line
    | bytes <- ByteString.lines contents
    , let line = dropWhile isSpace (ByteString.unpack bytes)
    , "(" `isPrefixOf` line
    ]

countCommands :: String -> [String] -> Int
countCommands prefix = length . filter (isPrefixOf prefix)

readbackCount :: [String] -> Int
readbackCount commands =
  countCommands "(get-value " commands + countCommands "(get-model" commands

-- Partition the closed transcript at actual sent checks. Assertions between
-- checks may occur in a window, but do not count as model readback. Startup
-- must not issue readback before the first check either.
checkWindows :: [String] -> [[String]]
checkWindows commands = case dropWhile (not . isPrefixOf "(check-sat") commands of
  [] -> []
  first : rest ->
    let (window, remaining) = break (isPrefixOf "(check-sat") rest
     in (first : window) : checkWindows remaining

assertReadbackWindows :: [Int] -> [String] -> IO ()
assertReadbackWindows expected commands = do
  assertEqual "exact number of actual solver checks" (length expected)
    (countCommands "(check-sat" commands)
  assertEqual "no model readback precedes the first check" 0
    (readbackCount (takeWhile (not . isPrefixOf "(check-sat") commands))
  assertEqual "exact readback commands in chronological check windows"
    expected (map readbackCount (checkWindows commands))

data ProjectedCallbackInterrupted = ProjectedCallbackInterrupted
  deriving (Eq, Show)

instance Exception ProjectedCallbackInterrupted

-- The gate wraps the production engine's already initialized real-Z3 query
-- context. It controls scheduling only; it never supplies a solver result.
gatedZ3 :: IO () -> IO () -> GrisetteSMTConfig
gatedZ3 before after =
  let config = sbvConfig z3
      original = SBV.solver config
   in z3
        { sbvConfig = config
            { SBV.solver = original
                { SBV.engine = \activeConfig state program use ->
                    SBV.engine original activeConfig state program
                      (\active -> before >> use active)
                      `finally` after
                }
            }
        }

projectedModelTests :: Test
projectedModelTests =
  testGroup "incremental projected models"
    [ testCase "scalar projections agree with the full model" $
        within "scalar projected models" $ withSolver z3 $ \solver -> do
          let left = "projection.scalar.left" :: SymInteger
              right = "projection.scalar.right" :: SymInteger
              flag = "projection.scalar.flag" :: SymBool
              formula = (left .== 17) .&& (right .== 29) .&& flag
              requested = extractSym (left, flag)
          command "assert scalar fixture" $ solverAssert solver formula
          projected <- modelFor solver (OnlyModelSymbols requested)
          full <- modelFor solver AllModelSymbols
          onlyRequested requested projected
          modelSatisfies projected ((left .== 17) .&& flag)
          modelSatisfies full formula
          assertEqual "fixed requested values agree with the legacy full query"
            (restrictTo requested full) projected,
      testCase "readback depends on the projection, not the asserted prefix" $
        within "projected request counts" $ withTranscript $ \path config -> do
          withSolver config $ \solver -> do
            let symbol index = isym "projection.prefix" index :: SymInteger
                constrain indices = foldr (.&&) (con True)
                  [symbol index .== con (toInteger index + 100) | index <- indices]
                selected = symbol 3
                requested = extractSym selected
            command "assert 12-symbol prefix" $ solverAssert solver (constrain [0 .. 11])
            empty <- modelFor solver (OnlyModelSymbols mempty)
            assertBool "SAT with empty projection has an empty model" (isEmptyModel empty)
            first <- modelFor solver (OnlyModelSymbols requested)
            onlyRequested requested first
            modelSatisfies first (selected .== 103)
            command "grow prefix to 24 symbols" $ solverAssert solver (constrain [12 .. 23])
            second <- modelFor solver (OnlyModelSymbols requested)
            assertEqual "prefix growth does not alter the chosen fixed value" first second
            full <- modelFor solver AllModelSymbols
            modelSatisfies full (constrain [0 .. 23])
          sentCommands path >>= assertReadbackWindows [0, 1, 1, 24],
      testCase "absent requests do not declare or default-fill a symbol" $
        within "absent projected symbol" $ withTranscript $ \path config -> do
          withSolver config $ \solver -> do
            let absent = "projection.never-lowered" :: SymInteger
            -- The first check marks the end of startup in the subsequently
            -- closed transcript; no declaration may follow that baseline.
            _ <- modelFor solver (OnlyModelSymbols mempty)
            missing <- modelFor solver (OnlyModelSymbols (extractSym absent))
            assertEqual "an unregistered request remains absent" emptyModel missing
            full <- modelFor solver AllModelSymbols
            assertEqual "the later full query is also sparse" emptyModel full
          commands <- sentCommands path
          assertReadbackWindows [0, 0, 0] commands
          assertEqual "projection does not declare a symbol after startup" 0
            (countCommands "(declare-" (concat (checkWindows commands))),
      testCase "empty projection preserves UNSAT without model readback" $
        within "empty UNSAT projection" $ withTranscript $ \path config -> do
          withSolver config $ \solver -> do
            command "assert contradiction" $ solverAssert solver (con False)
            result <- solverCheckSat solver (OnlyModelSymbols mempty)
            assertEqual "UNSAT is not converted to an empty SAT model" (Left Unsat) result
          sentCommands path >>= assertReadbackWindows [0],
      testCase "push, pop, and reset do not reuse a projected assignment" $
        within "projected scope reuse" $ withSolver z3 $ \solver -> do
          let value = "projection.reused" :: SymInteger
              projected expected = do
                command "push formula scope" $ solverPush solver 1
                command "assert scoped value" $ solverAssert solver (value .== con expected)
                model <- modelFor solver (OnlyModelSymbols (extractSym value))
                modelSatisfies model (value .== con expected)
                command "pop formula scope" $ solverPop solver 1
          projected 11
          projected 37
          command "reset assertions" $ solverResetAssertions solver
          command "assert after reset" $ solverAssert solver (value .== 53)
          model <- modelFor solver (OnlyModelSymbols (extractSym value))
          modelSatisfies model (value .== 53),
      testCase "monadic projected checks use the same SAT and UNSAT contract" $
        within "monadic projected models" $ do
          let value = "projection.monadic" :: SymInteger
          (first, second) <- runSBVIncremental z3 $ do
            monadicSolverAssert (value .== 31)
            first <- monadicSolverCheckSat (OnlyModelSymbols (extractSym value))
            monadicSolverAssert (con False)
            second <- monadicSolverCheckSat (OnlyModelSymbols mempty)
            pure (first, second)
          model <- expectRight "monadic SAT" first
          onlyRequested (extractSym value) model
          modelSatisfies model (value .== 31)
          assertEqual "monadic empty projection remains UNSAT" (Left Unsat) second,
      testCase "projection preserves configured scalar and function exclusions" $
        within "projected exclusion policy" $ do
          -- GeneralFun's generated solver names contain .gfunc2_, not the
          -- source symbol's text. There is exactly one such UF in this fixture;
          -- the retained TabularFun uses .tfunc2_ and exercises selective policy.
          let config = z3 {sbvConfig = (sbvConfig z3)
                {SBV.isNonModelVar = \name -> isInfixOf "excluded-policy" name
                  || isInfixOf ".gfunc2_" name}}
              excluded = "excluded-policy.scalar" :: SymInteger
              function = "excluded-policy.function" :: SymInteger -~> SymInteger
              kept = "projection.policy.kept" :: SymInteger
              retainedFunction = "projection.policy.retained-function" ::
                SymInteger =~> SymInteger
              requested = extractSym (excluded, function, kept, retainedFunction)
              retainedLaw = (kept .== 41) .&& (retainedFunction # 5 .== 43)
          withSolver config $ \solver -> do
            command "assert excluded fixture" $ solverAssert solver
              ((excluded .== 19) .&& (function # 3 .== 23) .&& retainedLaw)
            projected <- modelFor solver (OnlyModelSymbols requested)
            full <- modelFor solver AllModelSymbols
            assertEqual "configured exclusions match restriction of the full model"
              (restrictTo requested full) projected
            onlyRequested (extractSym (kept, retainedFunction)) projected
            modelSatisfies projected retainedLaw
            modelSatisfies full retainedLaw,
      testCase "projection preserves disabled uninterpreted-function tracking" $
        within "projected function tracking policy" $ do
          let config = z3 {sbvConfig = (sbvConfig z3) {SBV.allSatTrackUFs = False}}
              function = "projection.untracked-function" :: SymInteger -~> SymInteger
              kept = "projection.tracking.kept" :: SymInteger
              requested = extractSym (function, kept)
          withSolver config $ \solver -> do
            command "assert untracked function" $ solverAssert solver
              ((function # 7 .== 13) .&& (kept .== 47))
            projected <- modelFor solver (OnlyModelSymbols requested)
            full <- modelFor solver AllModelSymbols
            assertEqual "disabled UF tracking agrees with full-model policy"
              (restrictTo requested full) projected
            onlyRequested (extractSym kept) projected
            modelSatisfies projected (kept .== 47),
      testCase "native sequences, pairs, and both array decoder routes survive projection" $
        within "projected native composite values" $ withSolver z3 $ \solver -> do
          let sequenceValue = "projection.sequence" :: SymSeq (SymPair SymInteger SymBool)
              pairValue = "projection.pair" :: SymPair SymInteger SymBool
              unbounded = "projection.unbounded-array" :: SymArray SymInteger SymInteger
              finite = "projection.finite-array" :: SymArray SymBool SymInteger
              decoy = "projection.composite-decoy" :: SymInteger
              pairs = [(3, True), (5, False), (8, True)] :: [(Integer, Bool)]
              pair = (17, False) :: (Integer, Bool)
              unboundedValue = Array.store (Array.const 7) 2 19
              finiteValue = Array.store (Array.const 11) (con True) 29
              observations = (sequenceValue .== con pairs)
                .&& (pairValue .== con pair)
                .&& (unbounded .== unboundedValue)
                .&& (finite .== finiteValue)
              requested = extractSym (sequenceValue, pairValue, unbounded, finite)
              checkCompositeModel model = do
                assertEqual "every sequence pair is decoded" (Just pairs)
                  (toCon (evalSym False model sequenceValue))
                assertEqual "the standalone product is decoded" (Just pair)
                  (toCon (evalSym False model pairValue))
                forM_ ([(-1, 7), (0, 7), (2, 19), (3, 7)] :: [(Integer, Integer)]) $ \(key, expected) ->
                  assertEqual "unbounded array default and override" (Just expected)
                    (toCon (evalSym False model (Array.select unbounded (con key))))
                forM_ ([(False, 11), (True, 29)] :: [(Bool, Integer)]) $ \(key, expected) ->
                  assertEqual "every finite-domain cell is decoded" (Just expected)
                    (toCon (evalSym False model (Array.select finite (con key))))
                -- Distinct concrete array representations retain extensional
                -- equality as a solver term. Check the complete closed value
                -- law with Z3 as well as the independent cell-value oracles.
                let closedObservations = evalSym False model observations
                assertEqual "model substitution leaves no free symbols"
                  (mempty :: AnySymbolSet) (extractSym closedObservations)
                withSolver z3 $ \checker -> do
                  command "assert negated closed composite model law" $
                    solverAssert checker (symNot closedObservations)
                  result <- solverCheckSat checker (OnlyModelSymbols mempty)
                  assertEqual "the decoded arrays satisfy full extensional equality"
                    (Left Unsat) result
          command "assert composite fixture" $ solverAssert solver
            (observations .&& (decoy .== 101))
          projected <- modelFor solver (OnlyModelSymbols requested)
          onlyRequested requested projected
          checkCompositeModel projected
          full <- modelFor solver AllModelSymbols
          checkCompositeModel full,
      testCase "curried general and tabular functions retain all constrained applications" $
        within "projected curried functions" $ withSolver z3 $ \solver -> do
          let general = "projection.general" :: SymInteger -~> SymBool -~> SymInteger
              tabular = "projection.tabular" :: SymInteger =~> SymInteger =~> SymInteger
              generalLaw = (general # 2 # con True .== 11)
                .&& (general # 2 # con False .== 17)
                .&& (general # 5 # con True .== 31)
              tabularLaw = (tabular # 2 # 3 .== 5)
                .&& (tabular # 2 # 7 .== 9)
                .&& (tabular # 11 # 3 .== 14)
          command "assert curried functions" $ solverAssert solver (generalLaw .&& tabularLaw)
          generalModel <- modelFor solver (OnlyModelSymbols (extractSym general))
          onlyRequested (extractSym general) generalModel
          modelSatisfies generalModel generalLaw
          tabularModel <- modelFor solver (OnlyModelSymbols (extractSym tabular))
          onlyRequested (extractSym tabular) tabularModel
          modelSatisfies tabularModel tabularLaw
          full <- modelFor solver AllModelSymbols
          -- Compare observed applications, not arbitrary default branches or
          -- the representation of an extensionally equivalent function model.
          modelSatisfies full (generalLaw .&& tabularLaw),
      testCase "opaque-domain functions decode only requested user symbols" $
        within "projected opaque-domain function" $ withSolver z3 $ \solver -> do
          let left = "projection.opaque.left" :: SymUninterp "projected-payload"
              right = "projection.opaque.right" :: SymUninterp "projected-payload"
              function = "projection.opaque.function" ::
                SymUninterp "projected-payload" -~> SymBool -~> SymInteger
              decoy = "projection.opaque.decoy" :: SymInteger
              law = (left ./= right)
                .&& (function # left # con True .== 17)
                .&& (function # left # con False .== 19)
                .&& (function # right # con True .== 23)
              requested = extractSym (left, right, function)
          command "assert opaque-domain function" $ solverAssert solver
            (law .&& (decoy .== 71))
          projected <- modelFor solver (OnlyModelSymbols requested)
          onlyRequested requested projected
          modelSatisfies projected law
          full <- modelFor solver AllModelSymbols
          modelSatisfies full law,
      testCase "a cancelled projected request cannot leave a reusable result channel" $
        within "projected command cancellation" $ do
          ready <- newEmptyMVar
          release <- newEmptyMVar
          exited <- newEmptyMVar
          let config = gatedZ3
                (putMVar ready () >> takeMVar release)
                (putMVar exited ())
          withSolver config $ \solver ->
            ( do
                takeMVar ready
                interrupted <- try @ProjectedCallbackInterrupted $
                  solverRunCommand
                    (const $ throwIO ProjectedCallbackInterrupted)
                    solver
                    (SolverCheckSat (OnlyModelSymbols mempty))
                assertEqual "the dispatch callback's exception is preserved"
                  (Left ProjectedCallbackInterrupted ::
                    Either ProjectedCallbackInterrupted (Either SolvingFailure ()))
                  interrupted
                asserted <- solverAssert solver (con False)
                assertEqual "later assertions observe termination" (Left Terminated) asserted
                checked <- solverCheckSat solver AllModelSymbols
                assertEqual "no orphaned projected result is consumed"
                  (Left Terminated) (void checked)
                readMVar exited
            ) `finally` void (tryPutMVar release ())
    ]
