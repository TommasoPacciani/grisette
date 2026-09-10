{-# LANGUAGE GHC2024 #-}

module Grisette.Backend.KindRenderingTests (kindRenderingTests) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.SBV qualified as SBV
import Data.SBV.Control qualified as SBVC
import Data.SBV.Internals (Kind(..), smtType)
import Data.SBV.List qualified as SBVL
import Data.SBV.Tuple qualified as SBVTuple
import System.Timeout (timeout)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (assertBool, assertEqual)

-- These are byte-level interface examples, not another recursive renderer.
-- In particular, Float's two spaces and the raw application-name behavior
-- affect lambda text consumed by SBV's higher-order-function firstification.
renderingExamples :: [(String, Kind, String)]
renderingExamples =
  [ ("variable", KVar "a b", "a b")
  , ("boolean", KBool, "Bool")
  , ("unsigned bitvector", KBounded False 13, "(_ BitVec 13)")
  , ("signed bitvector", KBounded True 13, "(_ BitVec 13)")
  , ("raw bitvector width", KBounded False (-1), "(_ BitVec -1)")
  , ("integer", KUnbounded, "Int")
  , ("real", KReal, "Real")
  , ("float historical whitespace", KFloat, "(_ FloatingPoint  8 24)")
  , ("double", KDouble, "(_ FloatingPoint 11 53)")
  , ("general floating point", KFP 5 11, "(_ FloatingPoint 5 11)")
  , ("rational", KRational, "SBVRational")
  , ("character", KChar, "String")
  , ("string", KString, "String")
  , ("sequence", KList KUnbounded, "(Seq Int)")
  , ("set", KSet KUnbounded, "(Array Int Bool)")
  , ("unit tuple", KTuple [], "SBVTuple0")
  , ("singleton tuple", KTuple [KBool], "(SBVTuple1 Bool)")
  , ("heterogeneous tuple", KTuple [KBool, KList KChar, KReal]
    , "(SBVTuple3 Bool (Seq String) Real)")
  , ("array", KArray KUnbounded KBool, "(Array Int Bool)")
  , ("nested array", KArray (KList KChar) (KTuple [KUnbounded, KSet KBool])
    , "(Array (Seq String) (SBVTuple2 Int (Array Bool Bool)))")
  , ("application", KApp "Map" [KArray KUnbounded KBool, KList (KTuple [KBool, KChar])]
    , "(Map (Array Int Bool) (Seq (SBVTuple2 Bool String)))")
  , ("datatype parameters only"
    , KADT "Tree" [("element", KUnbounded), ("flag", KBool)]
        [("Leaf", [KVar "ignored"]), ("Node", [KList KReal])]
    , "(Tree Int Bool)")
  , ("uninterpreted datatype", KADT "Opaque" [] [], "Opaque")
  , ("rounding mode datatype"
    , KADT "RoundingMode" [] [("RNE", []), ("RNA", [])], "RoundingMode")
  , ("empty argument spelling", KApp "Named" [KVar ""], "(Named )")
  ]

-- Test both application owners against fixed spellings, including names that
-- are not ordinary SMT identifiers. The renderer does not validate or rewrite
-- these names, and the cutover must not silently add such a policy.
rawNameExamples :: [(String, String, String, String)]
rawNameExamples =
  [ ("ordinary", "Named", "Named", "(Named Int Bool)")
  , ("empty", "", "", "( Int Bool)")
  , ("space", "two words", "(two words)", "(two words Int Bool)")
  , ("leading tab", "\tNamed", "(\tNamed)", "(\tNamed Int Bool)")
  , ("newline", "two\nwords", "(two\nwords)", "(two\nwords Int Bool)")
  , ("Unicode space", "two\x00a0words", "(two\x00a0words)", "(two\x00a0words Int Bool)")
  , ("parenthesized", "(already)", "(already)", "(already) Int Bool")
  , ("bracketed", "[already]", "[already]", "[already] Int Bool")
  , ("parenthesized with space", "(two words)", "(two words)", "(two words) Int Bool")
  , ("bracketed with space", "[two words]", "[two words]", "[two words] Int Bool")
  , ("open parenthesis", "(", "(", "( Int Bool")
  , ("open bracket", "[", "[", "[ Int Bool")
  ]

kindRenderingTests :: Test
kindRenderingTests = testGroup "native SMT kind rendering" $
  [ testCase label $ assertEqual "exact SMT spelling" expected (smtType kind)
  | (label, kind, expected) <- renderingExamples
  ] ++
  [ testCase (owner ++ " raw name: " ++ label) $ do
      assertEqual "unapplied spelling" unapplied (smtType (construct name []))
      assertEqual "applied spelling" applied
        (smtType (construct name [KUnbounded, KBool]))
  | (owner, construct) <-
      [ ("application", KApp)
      , ("datatype", \name kinds -> KADT name (zip (repeat "ignored") kinds) [])
      ]
  , (label, name, unapplied, applied) <- rawNameExamples
  ] ++
  [ testCase "deep tuple rendering has output-linear construction" $ do
      let depth = 8192
          nested = foldr (\_ rest -> KTuple [KUnbounded, rest])
            (KTuple []) [1 .. depth]
          expected = concat (replicate depth "(SBVTuple2 Int ")
            ++ "SBVTuple0" ++ replicate depth ')'
      rendered <- timeout 5000000 (evaluate (force (smtType nested))) >>= \case
        Nothing -> fail "rendering 8192 nested tuple types exceeded 5 seconds"
        Just value -> pure value
      -- Keep a failure bounded: do not print the entire 128 KiB type.
      assertEqual "exact output length" (length expected) (length rendered)
      assertBool "all nested prefixes and suffixes retain their exact bytes"
        (rendered == expected)
  , testCase "real Z3 lowers a nested heterogeneous closure environment" $ do
      result <- timeout 10000000 nestedClosureQuery >>= \case
        Nothing -> fail "nested closure query exceeded 10 seconds"
        Just value -> pure value
      case result of
        Left status -> fail ("expected non-vacuous SAT, received " ++ status)
        Right (value, contradictory) -> do
          assertEqual "3 * 1 + 2, followed by 3 * 2 + 2" 13 value
          assertEqual "the same live model cannot change the fold result"
            SBVC.Unsat contradictory
  ]

-- Unknown inputs are constrained, not substituted before lowering. The
-- native closure therefore really renders nested tuple/sequence argument
-- types and firstifies its callback. Sequence length is total; no out-of-range
-- read or fabricated backend value is needed for the independent result 13.
nestedClosureQuery :: IO (Either String (Integer, SBVC.CheckSatResult))
nestedClosureQuery = SBV.runSMTWith SBV.z3 $ do
  scale <- SBV.sInteger "kind-rendering.scale"
  enabled <- SBV.sBool "kind-rendering.enabled"
  offsets <- SBV.sList @Integer "kind-rendering.offsets"
  inputs <- SBV.sList @Integer "kind-rendering.inputs"
  observed <- SBV.sInteger "kind-rendering.result"
  let environment = SBVTuple.tuple
        (scale, SBVTuple.tuple (enabled, offsets))
      closure = SBV.Closure environment $ \captured accumulated element ->
        let capturedScale = SBVTuple.fst captured
            rest = SBVTuple.snd captured
            capturedEnabled = SBVTuple.fst rest
            capturedOffsets = SBVTuple.snd rest
        in SBV.ite capturedEnabled
          (accumulated + capturedScale * element + SBVL.length capturedOffsets + 1)
          accumulated
  SBV.constrain (scale SBV..== 3)
  SBV.constrain enabled
  SBV.constrain (offsets SBV..== SBV.literal [9])
  SBV.constrain (inputs SBV..== SBV.literal [1, 2])
  SBV.constrain (observed SBV..== SBVL.foldl closure 0 inputs)
  SBVC.query $ SBVC.checkSat >>= \case
    SBVC.Sat -> do
      value <- SBVC.getValue observed
      SBV.constrain (observed SBV../= 13)
      contradictory <- SBVC.checkSat
      pure (Right (value, contradictory))
    other -> pure (Left (show other))
