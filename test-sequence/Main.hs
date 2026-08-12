{-# LANGUAGE GHC2024 #-}

module Main (main) where

import Grisette.SymPrim.SequenceTests (sequenceTests)
import Test.Framework (defaultMain)

main :: IO ()
main = defaultMain [sequenceTests]
