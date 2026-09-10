{-# LANGUAGE GHC2024 #-}

module Grisette.Backend.SolverLifecycleTests (solverLifecycleTests) where

import Control.Concurrent (newEmptyMVar, putMVar, readMVar, takeMVar, tryPutMVar)
import Control.Exception
  ( Exception,
    MaskingState (Unmasked),
    bracket,
    finally,
    getMaskingState,
    mask_,
    throwIO,
    try,
  )
import Control.Monad (void)
import qualified Data.SBV as SBV
import Grisette (Solvable (con))
import Grisette.Internal.Backend.Solving (GrisetteSMTConfig (sbvConfig), z3)
import Grisette.Internal.Core.Data.Class.Solver
  ( ConfigurableSolver (newSolver),
    ModelProjection (AllModelSymbols),
    Solver (solverAssert, solverCheckSat, solverForceTerminate, solverRunCommand),
    SolverCommand (SolverCheckSat),
    SolvingFailure (Terminated, Unsat),
    solverSolve,
    withSolver,
  )
import System.Timeout (timeout)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (assertEqual, assertFailure)

data CallbackInterrupted = CallbackInterrupted
  deriving (Eq, Show)

instance Exception CallbackInterrupted

-- The hook runs only after the real Z3 engine has initialized its query
-- context. It observes or gates the production command loop; it does not
-- replace the solver or manufacture a solver result.
hookedZ3 :: IO () -> IO () -> GrisetteSMTConfig
hookedZ3 before after =
  let config = sbvConfig z3
      original = SBV.solver config
   in z3
        { sbvConfig =
            config
              { SBV.solver =
                  original
                    { SBV.engine = \activeConfig state program use ->
                        SBV.engine original activeConfig state program
                          (\active -> before >> use active)
                          `finally` after
                    }
              }
        }

within :: String -> IO value -> IO value
within label action =
  timeout 10000000 action >>= \case
    Nothing -> fail $ label ++ " did not finish within 10 seconds"
    Just value -> pure value

solverLifecycleTests :: Test
solverLifecycleTests =
  testGroup
    "solver worker lifecycle"
    [ testCase "withSolver starts an unmasked real-Z3 worker" $ do
        masking <- newEmptyMVar
        exited <- newEmptyMVar
        let config =
              hookedZ3
                (getMaskingState >>= putMVar masking)
                (putMVar exited ())
        within "withSolver round trip and cleanup" $
          withSolver config $ \solver -> do
            observed <- within "real-Z3 worker readiness" $ takeMVar masking
            assertEqual "worker does not inherit acquisition masking" Unmasked observed
            satisfiable <- within "real-Z3 SAT check" $ solverSolve solver (con True)
            case satisfiable of
              Left failure -> assertFailure $ "expected SAT, received " ++ show failure
              Right _ -> pure ()
            unsatisfiable <- within "real-Z3 UNSAT check" $ solverSolve solver (con False)
            assertEqual "assertions reach the same real solver" (Left Unsat) (void unsatisfiable)
        within "normal engine exit" $ readMVar exited,
      testCase "a post-dispatch callback exception closes the solver permanently" $ do
        ready <- newEmptyMVar
        release <- newEmptyMVar
        exited <- newEmptyMVar
        let config =
              hookedZ3
                (putMVar ready () >> takeMVar release)
                (putMVar exited ())
        withSolver config $ \solver ->
          ( do
              within "gated real-Z3 worker readiness" $ takeMVar ready
              -- solverRunCommand queues CheckSat before invoking its callback.
              -- The gate keeps that request outstanding while the callback
              -- fails, so restoring a reusable status would be unsound.
              interrupted <-
                within "interrupted command cleanup" $
                  try @CallbackInterrupted $
                    solverRunCommand
                      (const $ throwIO CallbackInterrupted)
                      solver
                      (SolverCheckSat AllModelSymbols)
              assertEqual
                "the original callback exception is preserved"
                (Left CallbackInterrupted :: Either CallbackInterrupted (Either SolvingFailure ()))
                interrupted
              asserted <- within "command after interruption" $ solverAssert solver (con False)
              assertEqual "the status lock is closed, not abandoned or reusable" (Left Terminated) asserted
              checked <- within "check after interruption" $ solverCheckSat solver AllModelSymbols
              assertEqual "an orphaned result cannot be consumed" (Left Terminated) (void checked)
              within "interrupted engine exit" $ readMVar exited
          )
            `finally` void (tryPutMVar release ()),
      testCase "a directly acquired masked worker can be force-terminated" $ do
        masking <- newEmptyMVar
        release <- newEmptyMVar
        exited <- newEmptyMVar
        let config =
              hookedZ3
                (getMaskingState >>= putMVar masking >> takeMVar release)
                (putMVar exited ())
            cleanup solver = do
              void $ tryPutMVar release ()
              within "direct solver cleanup" $ solverForceTerminate solver
        bracket (mask_ $ newSolver config) cleanup $ \solver -> do
          observed <- within "direct real-Z3 worker readiness" $ takeMVar masking
          assertEqual "direct acquisition masking is not inherited" Unmasked observed
          within "force termination of the gated worker" $ solverForceTerminate solver
          within "force-terminated engine exit" $ readMVar exited
          checked <- within "check after force termination" $ solverCheckSat solver AllModelSymbols
          assertEqual "force termination leaves a closed handle" (Left Terminated) (void checked)
    ]
