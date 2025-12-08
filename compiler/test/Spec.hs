module Main (main) where

import Test.Tasty

import QuantitySpec (quantityTests)

main :: IO ()
main = defaultMain $ testGroup "Once"
  [ quantityTests
  ]
