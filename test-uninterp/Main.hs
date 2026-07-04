module Main (main) where

import Grisette.SymPrim.SymUninterpTests (symUninterpTests)
import Test.Framework (defaultMain)

main :: IO ()
main = defaultMain [symUninterpTests]
