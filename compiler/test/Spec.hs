module Main (main) where

import Test.Tasty

import BackendSpec (backendTests)
import ElaborateSpec (elaborateTests)
import IRSpec (irTests)
import ModuleSpec (moduleTests)
import OptimizeSpec (optimizeTests)
import ParserSpec (parserTests)
import QuantitySpec (quantityTests)
import TypeCheckSpec (typeCheckTests)

main :: IO ()
main = defaultMain $ testGroup "Once"
  [ quantityTests
  , irTests
  , optimizeTests
  , parserTests
  , elaborateTests
  , typeCheckTests
  , moduleTests
  , backendTests
  ]
