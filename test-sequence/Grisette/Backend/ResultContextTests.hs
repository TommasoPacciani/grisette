{-# LANGUAGE GHC2024 #-}

-- These witnesses use SBV's existing low-level public APIs to retain actual
-- references from separate symbolic runs. No solver or replacement context
-- checker participates in the assertions.
module Grisette.Backend.ResultContextTests (resultContextTests) where

import Control.Exception (ErrorCall, displayException, try)
import Control.Monad (void)
import Data.List (isPrefixOf)
import Data.SBV qualified as SBV
import Data.SBV.Internals qualified as SBVI
import System.Timeout (timeout)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assertBool, assertEqual, assertFailure)

runRecorded :: SBV.Symbolic value -> IO (value, SBVI.Result)
runRecorded = SBVI.runSymbolic SBV.defaultSMTCfg SBVI.CodeGen

captureReference :: SBV.Symbolic (SBV.SBV value) -> IO SBVI.SV
captureReference create = fst <$> runRecorded (do
  value <- create
  void (SBV.output value)
  SBVI.sbvToSymSV value)

-- The phantom value is fixed by each typed use below. The kind and returned
-- SV are the actual ones of that value, not a reconstructed node identity.
cachedValue :: SBVI.Kind -> (SBVI.State -> IO SBVI.SV) -> SBV.SBV value
cachedValue kind action = SBVI.SBV (SBVI.SVal kind (Right (SBVI.cache action)))

retainedBool :: SBVI.SV -> SBV.SBool
retainedBool reference = cachedValue SBVI.KBool (const (pure reference))

retainedInteger :: SBVI.SV -> SBV.SInteger
retainedInteger reference = cachedValue SBVI.KUnbounded (const (pure reference))

-- A real table and well-kinded lookup with its references inside the Op.
-- Its ordinary argument list is empty, so newExpr's args-only context check
-- cannot accidentally supply evidence for the final Result check.
lookupValue :: SBVI.SV -> SBVI.SV -> SBV.SBool
lookupValue index absent = cachedValue SBVI.KBool $ \state -> do
  table <- SBVI.getTableIndex state SBVI.KUnbounded SBVI.KBool [SBVI.trueSV]
  SBVI.newExpr state SBVI.KBool
    (SBVI.SBVApp (SBVI.LkUp (table, SBVI.KUnbounded, SBVI.KBool, 1) index absent) [])

-- The converted value is current-context; only the rounding operand can be
-- foreign. FP_Cast stores rounding inside the operator, not its argument list.
castValue :: SBVI.SV -> SBV.SInteger -> SBV.SDouble
castValue rounding value = cachedValue SBVI.KDouble $ \state -> do
  argument <- SBVI.sbvToSV state value
  SBVI.newExpr state SBVI.KDouble
    (SBVI.SBVApp (SBVI.IEEEFP
      (SBVI.FP_Cast SBVI.KUnbounded SBVI.KDouble rounding)) [argument])

-- Two nested lambda conversions run the final checker before returning their
-- rendered bodies. The inner body receives its genuine local argument.
nestedLambda :: (SBV.SInteger -> SBV.SInteger) -> IO String
nestedLambda body = do
  state <- SBVI.mkNewState SBV.defaultSMTCfg (SBVI.LambdaGen (Just 0))
  let nested :: SBV.SInteger
      nested = cachedValue SBVI.KUnbounded $ \outerState -> do
        void (SBVI.lambdaStr outerState SBVI.TopLevel SBVI.KUnbounded body)
        SBVI.sbvToSV outerState (SBV.literal 0 :: SBV.SInteger)
  show <$> SBVI.lambdaStr state SBVI.TopLevel SBVI.KUnbounded
    (\(_ :: SBV.SInteger) -> nested)

within :: IO value -> IO value
within action = timeout 10000000 action >>= \case
  Nothing -> fail "SBV Result context witness did not finish within 10 seconds"
  Just value -> pure value

expectMismatch :: IO value -> Assertion
expectMismatch action = within (try @ErrorCall (void action)) >>= \case
  Left failure -> assertBool "the complete existing context-mismatch diagnostic is retained"
    (mismatchDiagnostic `isPrefixOf` displayException failure)
  Right () -> assertFailure "a foreign symbolic context passed the final Result check"

mismatchDiagnostic :: String
mismatchDiagnostic = unlines
  [ "Data.SBV: Mismatched contexts detected."
  , "***"
  , "*** This happens if you call a proof-function (prove/sat/runSMT/isSatisfiable) etc."
  , "*** while another one is in execution, or use results from one such call in another."
  , "*** Please avoid such nested calls, all interactions should be from the same context."
  , "*** See https://github.com/LeventErkok/sbv/issues/71 for several examples."
  ]

resultContextTests :: Test
resultContextTests = testGroup "SBV Result context boundaries"
  [ testCase "a foreign output is rejected without an expression check" $ do
      foreignReference <- captureReference (SBV.sBool "foreign-output")
      expectMismatch (runRecorded (SBV.output (retainedBool foreignReference)))
  , testCase "a foreign lookup index is checked inside its operator" $ do
      foreignIndex <- captureReference (SBV.sInteger "foreign-index")
      expectMismatch (runRecorded (SBV.output (lookupValue foreignIndex SBVI.falseSV)))
  , testCase "a foreign lookup default is checked inside its operator" $ do
      foreignDefault <- captureReference (SBV.sBool "foreign-default")
      expectMismatch (runRecorded (do
        index <- SBV.sInteger "current-index" >>= SBVI.sbvToSymSV
        SBV.output (lookupValue index foreignDefault)))
  , testCase "a foreign table element is checked independently of lookup operands" $ do
      foreignElement <- captureReference (SBV.sBool "foreign-table-element")
      let value :: SBV.SBool
          value = cachedValue SBVI.KBool $ \state -> do
            void (SBVI.getTableIndex state SBVI.KUnbounded SBVI.KBool [foreignElement])
            pure SBVI.trueSV
      expectMismatch (runRecorded (SBV.output value))
  , testCase "a foreign floating-point rounding operand is checked inside its operator" $ do
      foreignRounding <- captureReference
        (SBV.free "foreign-rounding" :: SBV.Symbolic SBV.SRoundingMode)
      expectMismatch (runRecorded (do
        value <- SBV.sInteger "current-cast-value"
        SBV.output (castValue foreignRounding value)))
  , testCase "a foreign value is rejected during nested lambda conversion" $ do
      foreignReference <- captureReference (SBV.sInteger "foreign-nested-lambda")
      expectMismatch (nestedLambda (const (retainedInteger foreignReference)))
  , testCase "current-context outputs retain their exact references" $ within $ do
      (reference, result) <- runRecorded $ do
        reference <- SBV.sBool "current-output" >>= SBVI.sbvToSymSV
        void (SBV.output (retainedBool reference))
        pure reference
      assertEqual "the original reference is the sole output" [reference] (SBVI.resOutputs result)
  , testCase "global Boolean outputs remain admissible" $ within $ do
      (_, result) <- runRecorded (SBV.output
        [retainedBool SBVI.trueSV, retainedBool SBVI.falseSV])
      assertEqual "global constants keep their exact output order"
        [SBVI.trueSV, SBVI.falseSV] (SBVI.resOutputs result)
  , testCase "lookup operands may mix current and global contexts" $ within $ do
      (_, result) <- runRecorded $ do
        index <- SBV.sInteger "valid-lookup-index" >>= SBVI.sbvToSymSV
        SBV.output (lookupValue index SBVI.falseSV)
      assertEqual "the valid lookup produces one output" 1 (length (SBVI.resOutputs result))
  , testCase "current-context rounding and cast argument remain admissible" $ within $ do
      (_, result) <- runRecorded $ do
        rounding <- (SBV.free "current-rounding" :: SBV.Symbolic SBV.SRoundingMode)
          >>= SBVI.sbvToSymSV
        value <- SBV.sInteger "valid-cast-value"
        SBV.output (castValue rounding value)
      assertEqual "the valid cast produces one output" 1 (length (SBVI.resOutputs result))
  , testCase "nested lambda-local arguments retain their shared context" $ within $ do
      rendered <- nestedLambda (+ 1)
      assertBool "valid nested conversion returns a lambda" ("(lambda " `isPrefixOf` rendered)
  ]
