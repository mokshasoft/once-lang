module Main (main) where

import Test.Tasty

import AllocationSpec (allocationStressTests)
import ArithSpec (arithTests)
import BackendSpec (backendTests)
import IRSpec (irTests)
import Layer0Spec (layer0Tests)
import Layer1Spec (layer1Tests)
import Layer2Spec (layer2Tests)
import Layer3Spec (layer3Tests)
import Layer4Spec (layer4Tests)
import Layer5Spec (layer5Tests)
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
  , layer2Tests
  , layer3Tests
  , layer4Tests
  , layer5Tests
  , arithTests
  , backendTests
  , allocationStressTests
  ]
