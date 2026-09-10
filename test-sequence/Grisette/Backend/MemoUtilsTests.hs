{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}

module Grisette.Backend.MemoUtilsTests (memoUtilsTests) where

import Control.Exception (evaluate)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Grisette.Internal.Core.Data.MemoUtils
  ( stableMemo,
    weakStableMemo,
    weakStableMemo2,
    weakStableMemo3,
  )
import System.IO.Unsafe (unsafePerformIO)
import System.Mem (performMajorGC)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assertBool, assertEqual)

-- The immutable payload determines the result. A fresh IORef token makes two
-- separately allocated keys observably distinct even when their payloads agree.
-- The anchor retains the actual forced heap object, including across a GC.
data HeapKey = HeapKey !Int !(IORef ())

type KeyAnchor = IORef HeapKey

newKeyAnchor :: Int -> IO KeyAnchor
newKeyAnchor payload = do
  token <- newIORef ()
  key <- evaluate $ HeapKey payload token
  newIORef key

keyValue :: HeapKey -> Int
keyValue (HeapKey value _) = value

-- These test-only effects count entry into otherwise deterministic callbacks.
-- NOINLINE and the module's optimizer flags prevent the instrumentation from
-- being duplicated or commoned independently of the memoizer being tested.
countedUnary :: IORef Int -> HeapKey -> Int
countedUnary calls key = unsafePerformIO $ do
  modifyIORef' calls (+ 1)
  pure $ keyValue key
{-# NOINLINE countedUnary #-}

countedBinary :: IORef Int -> HeapKey -> HeapKey -> Int
countedBinary calls first second = unsafePerformIO $ do
  modifyIORef' calls (+ 1)
  pure $ 100 * keyValue first + keyValue second
{-# NOINLINE countedBinary #-}

countedTernary :: IORef Int -> HeapKey -> HeapKey -> HeapKey -> Int
countedTernary calls first second third = unsafePerformIO $ do
  modifyIORef' calls (+ 1)
  pure $ 100 * keyValue first + 10 * keyValue second + keyValue third
{-# NOINLINE countedTernary #-}

-- Every IO invocation reloads its keys and creates a new memo application.
-- Evaluating a shared `let result = memo key` twice would not test a cache hit.
applyUnary :: (HeapKey -> Int) -> KeyAnchor -> IO Int
applyUnary memo anchor = do
  key <- readIORef anchor >>= evaluate
  evaluate $ memo key
{-# NOINLINE applyUnary #-}

applyBinary
  :: (HeapKey -> HeapKey -> Int) -> KeyAnchor -> KeyAnchor -> IO Int
applyBinary memo firstAnchor secondAnchor = do
  first <- readIORef firstAnchor >>= evaluate
  second <- readIORef secondAnchor >>= evaluate
  evaluate $ memo first second
{-# NOINLINE applyBinary #-}

applyTernary
  :: (HeapKey -> HeapKey -> HeapKey -> Int)
  -> KeyAnchor -> KeyAnchor -> KeyAnchor -> IO Int
applyTernary memo firstAnchor secondAnchor thirdAnchor = do
  first <- readIORef firstAnchor >>= evaluate
  second <- readIORef secondAnchor >>= evaluate
  third <- readIORef thirdAnchor >>= evaluate
  evaluate $ memo first second third
{-# NOINLINE applyTernary #-}

checkUnaryIdentity :: ((HeapKey -> Int) -> HeapKey -> Int) -> Assertion
checkUnaryIdentity memoize = do
  calls <- newIORef 0
  first <- newKeyAnchor 17
  equalPayload <- newKeyAnchor 17
  differentPayload <- newKeyAnchor 29
  HeapKey _ firstToken <- readIORef first
  HeapKey _ equalToken <- readIORef equalPayload
  assertBool "equal-payload keys must have distinct allocated identities"
    (firstToken /= equalToken)
  let memo = memoize $ countedUnary calls
  applyUnary memo first >>= assertEqual "first result" 17
  applyUnary memo first >>= assertEqual "same-key result" 17
  readIORef calls >>= assertEqual "same heap key invokes the callback once" 1
  applyUnary memo equalPayload >>= assertEqual "equal-payload result" 17
  readIORef calls >>= assertEqual "a distinct heap key is not an identity hit" 2
  applyUnary memo differentPayload >>= assertEqual "distinct payload result" 29
  readIORef calls >>= assertEqual "a distinct value cannot reuse another result" 3
  applyUnary memo first >>= assertEqual "original key remains cached" 17
  readIORef calls >>= assertEqual "returning to the original key is a hit" 3

checkHeldKey :: ((HeapKey -> Int) -> HeapKey -> Int) -> Assertion
checkHeldKey memoize = do
  calls <- newIORef 0
  anchor <- newKeyAnchor 731
  let memo = memoize $ countedUnary calls
  applyUnary memo anchor >>= assertEqual "result before GC" 731
  performMajorGC
  applyUnary memo anchor >>= assertEqual "result after GC" 731
  performMajorGC
  applyUnary memo anchor >>= assertEqual "result after another GC" 731
  readIORef calls >>= assertEqual "a retained key remains a cache hit across GC" 1

memoUtilsTests :: Test
memoUtilsTests =
  testGroup
    "stable heap-identity memoization"
    [ testCase "strong memo reuses only the actual same heap key" $
        checkUnaryIdentity stableMemo,
      testCase "weak memo reuses only the actual same heap key" $
        checkUnaryIdentity weakStableMemo,
      testCase "strong memo retains hits while its key is held across GC" $
        checkHeldKey stableMemo,
      testCase "weak memo retains hits while its key is held across GC" $
        checkHeldKey weakStableMemo,
      testCase "curried weak memo keeps both argument identities" $ do
        calls <- newIORef 0
        first <- newKeyAnchor 2
        otherFirst <- newKeyAnchor 5
        second <- newKeyAnchor 3
        otherSecond <- newKeyAnchor 7
        let memo = weakStableMemo2 $ countedBinary calls
            checkPairs = do
              applyBinary memo first second >>= assertEqual "original pair" 203
              applyBinary memo first otherSecond >>= assertEqual "changed second" 207
              applyBinary memo otherFirst second >>= assertEqual "changed first" 503
              applyBinary memo otherFirst otherSecond >>= assertEqual "both changed" 507
        checkPairs
        readIORef calls >>= assertEqual "one callback per argument pair" 4
        checkPairs
        readIORef calls >>= assertEqual "each repeated pair is a hit" 4
        performMajorGC
        checkPairs
        readIORef calls >>= assertEqual "held curried keys survive GC" 4,
      testCase "curried weak memo keeps all three argument identities" $ do
        calls <- newIORef 0
        first <- newKeyAnchor 2
        second <- newKeyAnchor 3
        third <- newKeyAnchor 4
        replacement <- newKeyAnchor 5
        let memo = weakStableMemo3 $ countedTernary calls
            checkTriples = do
              applyTernary memo first second third >>= assertEqual "original triple" 234
              applyTernary memo first second replacement >>= assertEqual "changed third" 235
              applyTernary memo first replacement third >>= assertEqual "changed second" 254
              applyTernary memo replacement second third >>= assertEqual "changed first" 534
              applyTernary memo first replacement replacement >>= assertEqual "second and third" 255
              applyTernary memo replacement second replacement >>= assertEqual "first and third" 535
              applyTernary memo replacement replacement third >>= assertEqual "first and second" 554
              applyTernary memo replacement replacement replacement >>= assertEqual "all changed" 555
        checkTriples
        readIORef calls >>= assertEqual "one callback per argument triple" 8
        checkTriples
        readIORef calls >>= assertEqual "each repeated triple is a hit" 8
        performMajorGC
        checkTriples
        readIORef calls >>= assertEqual "all held curried keys survive GC" 8
    ]
