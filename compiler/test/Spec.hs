module Main (main) where

import Test.Tasty

import AllocationSpec (allocationStressTests)
import Arith.Spec (arithTests)
import BackendSpec (backendTests)
import ElaborateSpec (elaborateTests)
import IRSpec (irTests)
import ModuleSpec (moduleTests)
import OptimizeSpec (optimizeTests)
import ParserSpec (parserTests)
import QuantitySpec (quantityTests)

main :: IO ()
main = defaultMain $ testGroup "Once"
  [ arithTests
  , quantityTests
  , irTests
  , optimizeTests
  , parserTests
  , elaborateTests
  , moduleTests
  , backendTests
  , allocationStressTests
  ]
