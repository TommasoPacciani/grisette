{-# LANGUAGE GHC2024 #-}

module Grisette.Backend.KindRegistrationTests (kindRegistrationTests) where

import Control.DeepSeq (force)
import Control.Exception (ErrorCall, displayException, evaluate, try)
import Control.Monad (forM_, replicateM_, void)
import Control.Monad.IO.Class (liftIO)
import Data.ByteString.Char8 qualified as ByteString
import Data.Char (isSpace)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (isPrefixOf, nub, sort)
import Data.SBV qualified as SBV
import Data.SBV.Control qualified as SBVC
import Data.SBV.Internals qualified as SBVI
import Data.SBV.Internals (Kind(..))
import System.IO (hClose, openTempFile)
import System.Mem (performMajorGC)
import System.Timeout (timeout)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assertEqual, assertFailure)

within :: IO value -> IO value
within action = timeout 10000000 action >>= \case
  Nothing -> fail "kind registration witness exceeded 10 seconds"
  Just value -> pure value

freshState :: IO SBVI.State
freshState = SBVI.mkNewState SBV.defaultSMTCfg SBVI.CodeGen

assertKinds :: String -> [Kind] -> SBVI.State -> Assertion
assertKinds label expected state = do
  actual <- SBVI.sInfoKinds <$> SBVI.getSInfo state
  assertEqual label (sort (nub expected)) actual

expectReserved :: String -> IO value -> Assertion
expectReserved name action = try @ErrorCall (void action) >>= \case
  Left exception -> assertEqual "the original first reserved-sort diagnostic"
    ("SBV: " ++ show name ++ " is a reserved sort; please use a different name.")
    (takeWhile (/= '\n') (displayException exception))
  Right () -> assertFailure "a reserved child passed kind registration"

-- Fixed expected sets, not another implementation of recursive registration.
-- Every constructor is covered, including the metadata ignored by smtType.
registrationExamples :: [(String, Kind, [Kind])]
registrationExamples =
  [ ("variable", KVar "element", [])
  , ("Boolean", KBool, [])
  , ("unsigned bitvector", KBounded False 13, [])
  , ("signed bitvector", KBounded True 13, [])
  , ("integer", KUnbounded, [])
  , ("real", KReal, [])
  , ("float", KFloat, [])
  , ("double", KDouble, [])
  , ("general float", KFP 5 11, [])
  , ("rational", KRational, [])
  , ("character", KChar, [])
  , ("string", KString, [])
  , ("application", KApp "RegistryApp" [KBool, KList KUnbounded]
    , [KBool, KList KUnbounded, KUnbounded])
  , ("datatype", KADT "RegistryData" [("element", KUnbounded)]
      [("First", [KBool]), ("Second", [KSet KChar])]
    , [KUnbounded, KBool, KSet KChar, KChar])
  , ("list", KList KReal, [KReal])
  , ("set", KSet KBool, [KBool])
  , ("tuple", KTuple [KBool, KReal], [KBool, KReal])
  , ("empty tuple", KTuple [], [])
  , ("array", KArray KUnbounded (KList KChar)
    , [KUnbounded, KList KChar, KChar])
  ]

-- The reserved-name table is actually case-sensitive. Lowercase bool/int
-- exercise its existing diagnostic; changing that policy is not this repair.
reservedBool :: Kind
reservedBool = KADT "bool" [] []

failedParents :: [(String, Kind, [Kind])]
failedParents =
  [ ("application first", KApp "RegistryApp" [reservedBool, KReal], [])
  , ("application later", KApp "RegistryApp" [KChar, reservedBool, KReal], [KChar])
  , ("datatype first parameter", KADT "RegistryData"
      [("first", reservedBool), ("later", KChar)] [("Constructor", [KReal])], [])
  , ("datatype later parameter", KADT "RegistryData"
      [("first", KUnbounded), ("later", reservedBool)] [("Constructor", [KReal])]
    , [KUnbounded])
  , ("datatype first field", KADT "RegistryData" [("element", KUnbounded)]
      [("Constructor", [reservedBool, KReal])], [KUnbounded])
  , ("datatype later field", KADT "RegistryData" [("element", KUnbounded)]
      [("Constructor", [KChar, reservedBool, KReal])], [KUnbounded, KChar])
  , ("datatype later constructor", KADT "RegistryData" [("element", KUnbounded)]
      [("First", [KChar]), ("Second", [reservedBool, KReal])], [KUnbounded, KChar])
  , ("list element", KList reservedBool, [])
  , ("set element", KSet reservedBool, [])
  , ("tuple first", KTuple [reservedBool, KReal], [])
  , ("tuple later", KTuple [KChar, reservedBool, KReal], [KChar])
  , ("array index", KArray reservedBool KReal, [])
  , ("array value", KArray KUnbounded reservedBool, [KUnbounded])
  ]

failureOrderExamples :: [(String, Kind)]
failureOrderExamples =
  [ ("application arguments", KApp "RegistryApp" [reservedBool, later])
  , ("datatype parameters", KADT "RegistryData"
      [("first", reservedBool), ("second", later)] [])
  , ("datatype parameters before fields", KADT "RegistryData"
      [("element", reservedBool)] [("Constructor", [later])])
  , ("datatype fields", KADT "RegistryData" [] [("Constructor", [reservedBool, later])])
  , ("datatype constructors", KADT "RegistryData" [] [("First", [reservedBool]), ("Second", [later])])
  , ("tuple elements", KTuple [reservedBool, later])
  , ("array index before value", KArray reservedBool later)
  ]
  where later = KADT "int" [] []

cachedBool :: (SBVI.State -> IO SBVI.SV) -> SBV.SBool
cachedBool action = SBVI.SBV (SBVI.SVal KBool (Right (SBVI.cache action)))

-- Both lambda conversions run their real symbolic computations and context
-- checks. Their only result is the genuine global Boolean reference; no node
-- identity or symbolic state is reconstructed for this witness.
registerInNestedLambdas :: SBVI.State -> [Kind] -> IO ()
registerInNestedLambdas state kinds = do
  outer <- SBVI.lambdaStr state SBVI.TopLevel KBool $ \(_ :: SBV.SInteger) ->
    cachedBool $ \outerState -> do
      inner <- SBVI.lambdaStr outerState SBVI.TopLevel KBool $ \(_ :: SBV.SInteger) ->
        cachedBool $ \innerState -> do
          mapM_ (SBVI.registerKind innerState) kinds
          pure SBVI.trueSV
      void (evaluate (force (show inner)))
      pure SBVI.trueSV
  void (evaluate (force (show outer)))

-- A fresh counter also gives every assertion a distinct cached callback.
-- addQueryConstraint forces it inside withNewIncState and flushes declarations
-- before discarding the tautological assertion. The real queries below also
-- constrain, read back, and contradict an unknown integer: this callback is
-- evidence of registration execution, not a substitute solver result.
forceRegistration :: (SBVI.State -> IO ()) -> SBVC.Query ()
forceRegistration action = do
  calls <- SBVC.io (newIORef (0 :: Int))
  SBV.constrain $ cachedBool $ \state -> do
    modifyIORef' calls (+ 1)
    action state
    pure SBVI.trueSV
  count <- SBVC.io (readIORef calls)
  SBVC.io (assertEqual "the incremental registration callback executes once" 1 count)

checkFixedInteger :: SBV.SInteger -> SBVC.Query ()
checkFixedInteger value = do
  result <- SBVC.checkSat
  SBVC.io (assertEqual "the live registered context is SAT" SBVC.Sat result)
  observed <- SBVC.getValue value
  SBVC.io (assertEqual "the actual model retains the integer constraint" 31 observed)

checkContradiction :: SBV.SInteger -> SBVC.Query ()
checkContradiction value = do
  SBV.constrain (value SBV../= 31)
  result <- SBVC.checkSat
  SBVC.io (assertEqual "the same live context rejects the contradictory constraint" SBVC.Unsat result)

-- Persistent transcript is read strictly only after runSMTWith closes Z3.
withTranscript :: (SBV.SMTConfig -> IO ()) -> IO [String]
withTranscript action = do
  (path, handle) <- openTempFile "/tmp" "p4check2-kind-registration-.smt2"
  hClose handle
  putStrLn ("kind-registration transcript: " ++ path)
  action (SBV.z3 {SBV.transcript = Just path})
  contents <- ByteString.readFile path
  pure [line | bytes <- ByteString.lines contents
       , let line = dropWhile isSpace (ByteString.unpack bytes)
       , "(" `isPrefixOf` line]

-- Each bucket ends at an actual check-sat. Post-check model reads belong to
-- the next bucket but cannot masquerade as declarations or flatten options.
beforeChecks :: [String] -> [[String]]
beforeChecks = go []
  where
    go _ [] = []
    go reversed (command : rest)
      | "(check-sat" `isPrefixOf` command = reverse reversed : go [] rest
      | otherwise = go (command : reversed) rest

assertCommandWindows :: String -> [Int] -> [String] -> Assertion
assertCommandWindows prefix expected commands = do
  let windows = beforeChecks commands
  assertEqual "exact number of actual solver checks" (length expected) (length windows)
  assertEqual ("chronological command counts: " ++ prefix) expected
    (map (length . filter (isPrefixOf prefix)) windows)

kindRegistrationTests :: Test
kindRegistrationTests = testGroup "context-owned kind registration" $
  [ testCase ("register and repeat " ++ label) $ within $
      forM_ [SBVI.CodeGen, SBVI.Concrete Nothing, SBVI.LambdaGen (Just 0)] $ \mode -> do
        state <- SBVI.mkNewState SBV.defaultSMTCfg mode
        SBVI.registerKind state kind
        assertKinds "all and only the expected kinds register" (kind : children) state
        SBVI.registerKind state kind
        assertKinds "successful registration is idempotent" (kind : children) state
  | (label, kind, children) <- registrationExamples
  ] ++
  [ testCase ("failed parent retries: " ++ label) $ within $ do
      state <- freshState
      replicateM_ 2 $ do
        expectReserved "bool" (SBVI.registerKind state parent)
        assertKinds "parent and earlier children survive; later children do not"
          (parent : earlier) state
  | (label, parent, earlier) <- failedParents
  ] ++
  [ testCase ("first diagnostic follows " ++ label) $ within $ do
      state <- freshState
      expectReserved "bool" (SBVI.registerKind state parent)
      assertKinds "neither failing child is published" [parent] state
  | (label, parent) <- failureOrderExamples
  ] ++
  [ testCase "reserved-root failure preserves the prior registry and exact case policy" $ within $ do
      state <- freshState
      let allowed = KADT "Bool" [] []
      SBVI.registerKind state allowed
      replicateM_ 2 $ expectReserved "bool" (SBVI.registerKind state reservedBool)
      assertKinds "uppercase is retained and lowercase remains rejected" [allowed] state
  , testCase "same-name datatype variants register their distinct children" $ within $ do
      state <- freshState
      let original = KADT "RegistrySame" [] [("First", [KBool])]
          variant = KADT "RegistrySame" [("element", KUnbounded)] [("Second", [KList KReal])]
          failing = KADT "RegistrySame" [("new", KChar), ("bad", reservedBool)]
            [("Unreached", [KDouble])]
          expected = [original, KBool, KUnbounded, KList KReal, KReal]
      SBVI.registerKind state original
      replicateM_ 2 (SBVI.registerKind state variant)
      assertKinds "the first definition owns the name; both payloads contribute children" expected state
      replicateM_ 2 $ do
        expectReserved "bool" (SBVI.registerKind state failing)
        assertKinds "same-name suppression cannot skip a later payload's failing child"
          (KChar : expected) state
  , testCase "fresh roots do not share completion or declaration ownership" $ within $ do
      first <- freshState
      second <- freshState
      let kind = KTuple [KBool, KList KUnbounded]
          expected = [kind, KBool, KList KUnbounded, KUnbounded]
      SBVI.registerKind first kind
      assertKinds "the other root is still empty" [] second
      SBVI.registerKind second kind
      assertKinds "the first root keeps its registry" expected first
      assertKinds "the same heap kind also registers in the second root" expected second
  , testCase "nested lambdas publish into their parent registry" $ within $ do
      state <- freshState
      let kind = KTuple [KChar, KReal]
          opaque = KADT "RegistryNestedPure" [] []
          expected = [KBool, KUnbounded, kind, KChar, KReal, opaque]
      registerInNestedLambdas state [kind, opaque]
      assertKinds "both nested scopes share the original registry" expected state
      mapM_ (SBVI.registerKind state) [kind, opaque]
      assertKinds "parent repetition retains exact kind information" expected state
  , testCase "a shared nested tail can be repeatedly registered after major GC" $ within $ do
      state <- freshState
      let tails = scanr (\_ rest -> KTuple [KBool, rest]) (KTuple []) [1 .. 96 :: Int]
      case tails of
        [] -> assertFailure "scanr did not retain its terminal tuple"
        root : _ -> do
          SBVI.registerKind state root
          performMajorGC
          replicateM_ 256 (mapM_ (SBVI.registerKind state) tails)
          assertKinds "repeated sharing retains every exact tail and no extra kind" (KBool : tails) state
      -- This bounds one shared-tail workload, not arbitrary rebuilt Kind trees.
  , testCase "real Z3 reuses tuple arities and ADT names across nested query scopes" $ within $ do
      commands <- withTranscript $ \config -> SBV.runSMTWith config $ do
        state <- SBVI.contextState
        let initialTuple = KTuple [KBool, KUnbounded]
            alias = KADT "RegistryAlias" [] []
            newTuple = KTuple [KBool, KChar, KReal]
            nestedSort = KADT "RegistryNestedQuery" [] []
            laterKinds = [newTuple, nestedSort]
        liftIO (mapM_ (SBVI.registerKind state) [initialTuple, alias])
        value <- SBV.sInteger "kind-registration.fixed"
        SBV.constrain (value SBV..== 31)
        SBVC.query $ do
          checkFixedInteger value
          forceRegistration $ \active -> mapM_ (SBVI.registerKind active)
            [KTuple [KChar, KReal], KADT "RegistryAlias" [("element", KUnbounded)] []]
          checkFixedInteger value
          forceRegistration (\active -> registerInNestedLambdas active laterKinds)
          checkFixedInteger value
          forceRegistration (\active -> mapM_ (SBVI.registerKind active) laterKinds)
          checkFixedInteger value
          checkContradiction value
      assertCommandWindows "(declare-datatypes ((SBVTuple2 2))" [1, 0, 0, 0, 0] commands
      assertCommandWindows "(declare-datatypes ((SBVTuple3 3))" [0, 0, 1, 0, 0] commands
      assertCommandWindows "(declare-sort RegistryAlias 0)" [1, 0, 0, 0, 0] commands
      assertCommandWindows "(declare-sort RegistryNestedQuery 0)" [0, 0, 1, 0, 0] commands
  , testCase "real Z3 list registration distinguishes element kinds across incremental resets" $ within $ do
      commands <- withTranscript $ \config -> SBV.runSMTWith config $ do
        value <- SBV.sInteger "kind-registration.list-fixed"
        SBV.constrain (value SBV..== 31)
        SBVC.query $ do
          checkFixedInteger value
          forM_ [KList KUnbounded, KList KUnbounded, KList KBool, KList KBool] $ \kind -> do
            forceRegistration (\state -> SBVI.registerKind state kind)
            checkFixedInteger value
          checkContradiction value
      assertCommandWindows "(set-option :pp.max_depth" [0, 1, 0, 1, 0, 0] commands
      assertCommandWindows "(set-option :pp.min_alias_size" [0, 1, 0, 1, 0, 0] commands
      assertCommandWindows "(set-option :model.inline_def" [0, 1, 0, 1, 0, 0] commands
  ]
