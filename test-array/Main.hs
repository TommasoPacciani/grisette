module Main (main) where

import Grisette.SymPrim.SymArrayTests (symArrayTests)
import Test.Framework (defaultMain)

main :: IO ()
main = defaultMain [symArrayTests]
