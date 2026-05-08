module Main (main) where

import Test.Tasty

import AllocationSpec (allocationStressTests)
import BackendSpec (backendTests)
import IRSpec (irTests)
import Layer0Spec (layer0Tests)
import Layer1Spec (layer1Tests)
import ParseSpec (parseTests)
import TypeCheckSpec (typeCheckTests)
import TypeErrorSpec (typeErrorTests)

main :: IO ()
main = defaultMain $ testGroup "Once"
  [ parseTests
  , typeCheckTests
  , typeErrorTests
  , irTests
  , layer0Tests
  , layer1Tests
  , backendTests
  , allocationStressTests
  ]
