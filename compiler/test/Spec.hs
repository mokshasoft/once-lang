module Main (main) where

import Test.Tasty

import ElaborateSpec (elaborateTests)
import IRSpec (irTests)
import ParserSpec (parserTests)
import QuantitySpec (quantityTests)

main :: IO ()
main = defaultMain $ testGroup "Once"
  [ quantityTests
  , irTests
  , parserTests
  , elaborateTests
  ]
