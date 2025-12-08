module Main (main) where

import Test.Tasty

import IRSpec (irTests)
import QuantitySpec (quantityTests)

main :: IO ()
main = defaultMain $ testGroup "Once"
  [ quantityTests
  , irTests
  ]
