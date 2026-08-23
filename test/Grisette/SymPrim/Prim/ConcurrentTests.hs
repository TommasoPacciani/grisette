{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-cse #-}

module Grisette.SymPrim.Prim.ConcurrentTests (concurrentTests) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.Hashable (Hashable (hash))
import Data.String (IsString (fromString))
import Grisette
  ( LogicalOp(symNot, (.&&), (.||)), SolvingFailure(Unsat)
  , SymBool(SymBool), SymEq ((.==)), SymInteger (SymInteger)
  , evalSymToCon, solve, ssym, z3 )
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (assertFailure, (@?=))

concurrentTests :: Test
concurrentTests =
  testGroup
    "Concurrent"
    [ testCase "Consistent hash/eq" $ do
        aref <- newEmptyMVar
        bref <- newEmptyMVar
        _ <- forkIO $ do
          evaluate $ force (map (fromString . show) [1 .. 1000] :: [SymInteger])
          evaluate $ force ("x" :: SymInteger)
          SymInteger p <- evaluate $ force ("y" + "z" :: SymInteger)
          putMVar aref p
        ar <- takeMVar aref
        _ <- forkIO $ do
          SymInteger p <- evaluate $ force ("y" + "z" :: SymInteger)
          putMVar bref p
        br <- takeMVar bref
        ar @?= br
        hash ar @?= hash br,
      testCase "Eval" $ do
        aref <- newEmptyMVar
        bref <- newEmptyMVar
        _ <- forkIO $ do
          a <- evaluate $ force ("a" :: SymInteger)
          putMVar aref a
        _ <- forkIO $ do
          b <- evaluate $ force ("b" :: SymInteger)
          putMVar bref b
        a <- takeMVar aref
        b <- takeMVar bref
        r <- solve z3 $ a .== b
        case r of
          Left err -> error $ show err
          Right m -> evalSymToCon m a @?= (evalSymToCon m b :: Integer),
      testCase "large Boolean sets retain same-thread identity" $ do
        SymBool conjunction <- evaluate $ force
          (largeConjunction "same-thread.conjunction")
        SymBool conjunctionAgain <- evaluate $ force
          (largeConjunction "same-thread.conjunction")
        conjunction @?= conjunctionAgain
        hash conjunction @?= hash conjunctionAgain
        SymBool disjunction <- evaluate $ force
          (largeDisjunction "same-thread.disjunction")
        SymBool disjunctionAgain <- evaluate $ force
          (largeDisjunction "same-thread.disjunction")
        disjunction @?= disjunctionAgain
        hash disjunction @?= hash disjunctionAgain,
      testCase "large Boolean sets reconstruct across threads" $ do
        foreignRef <- newEmptyMVar
        _ <- forkIO $ do
          foreignValue <- evaluate $ force
            (largeConjunction "cross-thread.left")
          putMVar foreignRef foreignValue
        foreignValue <- takeMVar foreignRef
        let actual = foreignValue .&& largeDisjunction "cross-thread.right"
            expected = largeConjunction "cross-thread.left"
              .&& largeDisjunction "cross-thread.right"
        SymBool actualTerm <- evaluate $ force actual
        SymBool expectedTerm <- evaluate $ force expected
        actualTerm @?= expectedTerm
        hash actualTerm @?= hash expectedTerm
        result <- solve z3 (symNot (actual .== expected))
        case result of
          Left Unsat -> pure ()
          Left failure -> assertFailure (show failure)
          Right{} -> assertFailure
            "cross-thread Boolean reconstruction changed solver semantics"
    ]

largeConjunction :: String -> SymBool
largeConjunction prefix = foldl' (.&&)
  (ssym (fromString (prefix ++ ".0")))
  [ ssym (fromString (prefix ++ "." ++ show ordinal))
  | ordinal <- [1 :: Int .. 96]
  ]

largeDisjunction :: String -> SymBool
largeDisjunction prefix = foldl' (.||)
  (ssym (fromString (prefix ++ ".0")))
  [ ssym (fromString (prefix ++ "." ++ show ordinal))
  | ordinal <- [1 :: Int .. 96]
  ]
