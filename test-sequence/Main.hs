{-# LANGUAGE GHC2024 #-}

module Main (main) where

import Grisette.Backend.KindRenderingTests (kindRenderingTests)
import Grisette.Backend.KindRegistrationTests (kindRegistrationTests)
import Grisette.Backend.ResultContextTests (resultContextTests)
import Grisette.Backend.SolverLifecycleTests (solverLifecycleTests)
import Grisette.Backend.ScopedLoweringTests (scopedLoweringTests)
import Grisette.Backend.LiteralFoldLoweringTests (literalFoldLoweringTests)
import Grisette.Backend.MemoUtilsTests (memoUtilsTests)
import Grisette.Backend.ProjectedModelTests (projectedModelTests)
import Grisette.SymPrim.SequenceTests (sequenceTests)
import Grisette.SymPrim.SequenceLaneTests (sequenceLaneTests)
import Grisette.SymPrim.IntegerSerializationTests (integerSerializationTests)
import Grisette.SymPrim.TermUtilsTests (termUtilsTests)
import Test.Framework (defaultMain)

main :: IO ()
main = defaultMain [sequenceTests, solverLifecycleTests, scopedLoweringTests, literalFoldLoweringTests, memoUtilsTests, projectedModelTests, kindRenderingTests, resultContextTests, kindRegistrationTests, sequenceLaneTests, integerSerializationTests, termUtilsTests]
