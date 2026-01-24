module Main (main) where

import Test.Tasty

import AllocationSpec (allocationStressTests)
import BackendSpec (backendTests)
import ElaborateSpec (elaborateTests)
import IRSpec (irTests)
import ModuleSpec (moduleTests)
import OptimizeSpec (optimizeTests)
import ParserSpec (parserTests)
import QuantitySpec (quantityTests)

main :: IO ()
main = defaultMain $ testGroup "Once"
  [ quantityTests
  , irTests
  , optimizeTests
  , parserTests
  , elaborateTests
  , moduleTests
  , backendTests
  , allocationStressTests
  ]
