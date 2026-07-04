{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Soundness gate for Grisette's first-class uninterpreted (abstract) SMT sort
-- ('SymUninterp'). An opaque sort must support exactly three things — a fresh
-- symbol, equality\/distinctness, and use as an uninterpreted-function argument
-- — and nothing else (no arithmetic, ordering, or bit-indexing). These
-- solver-backed checks pin that contract end-to-end: each one only passes if
-- the sort actually lowers to an SMT @(declare-sort ...)@ with the right
-- theory (equality of uninterpreted constants + functional consistency).
module Grisette.SymPrim.SymUninterpTests (symUninterpTests) where

import GHC.Stack (HasCallStack)
import Grisette
  ( Function ((#)),
    LogicalOp ((.&&)),
    SymBool,
    SymEq ((./=), (.==)),
    SymInteger,
    solve,
  )
import Grisette.Internal.Backend.Solving (z3)
import Grisette.Internal.Core.Data.Class.Solver (SolvingFailure (Unsat))
import Grisette.SymPrim (SymUninterp, type (-~>))
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assertFailure)

-- | The single opaque domain exercised here: a payload identity.
type Payload = SymUninterp "payload"

checkSat :: (HasCallStack) => SymBool -> Assertion
checkSat phi = do
  r <- solve z3 phi
  case r of
    Right _ -> return ()
    Left Unsat -> assertFailure "expected SAT, but UNSAT"
    Left e -> assertFailure $ "expected SAT, but solver failed: " ++ show e

checkUnsat :: (HasCallStack) => SymBool -> Assertion
checkUnsat phi = do
  r <- solve z3 phi
  case r of
    Left Unsat -> return ()
    Left e -> assertFailure $ "expected UNSAT, but solver failed: " ++ show e
    Right _ -> assertFailure "expected UNSAT, but found a model"

symUninterpTests :: Test
symUninterpTests =
  testGroup
    "SymUninterp (uninterpreted / abstract SMT sort)"
    [ testCase "two fresh opaque values can differ (SAT)" $
        let a = "a" :: Payload
            b = "b" :: Payload
         in checkSat (a ./= b),
      testCase "an opaque value is never distinct from itself (UNSAT)" $
        let a = "a" :: Payload
         in checkUnsat (a ./= a),
      testCase "equal opaque values differ only by name, not identity (SAT)" $
        -- Two distinct fresh symbols may be assigned the same sort element.
        let a = "a" :: Payload
            b = "b" :: Payload
         in checkSat (a .== b),
      testCase "UF over the sort: functional consistency (UNSAT)" $
        -- If two opaque identities are equal, an uninterpreted function of them
        -- must agree — so a==b together with f(a)/=f(b) is unsatisfiable. This
        -- only holds if the sort is a real UF-argument kind.
        let a = "a" :: Payload
            b = "b" :: Payload
            f = "f" :: Payload -~> SymInteger
         in checkUnsat ((a .== b) .&& (f # a ./= f # b)),
      testCase "UF over the sort: distinct arguments may differ (SAT)" $
        let a = "a" :: Payload
            b = "b" :: Payload
            f = "f" :: Payload -~> SymInteger
         in checkSat (f # a ./= f # b)
    ]
