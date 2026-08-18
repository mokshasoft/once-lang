module Main (main) where

import Test.Tasty
import Test.Tasty.Runners (NumThreads (..))

import ArithSpec (arithTests)
import FloatSpec (floatTests)
import GeneratorSpec (generatorTests)
import IRSpec (irTests)
import Layer0Spec (layer0Tests)
import Layer1Spec (layer1Tests)
import Layer2Spec (layer2Tests)
import Layer3Spec (layer3Tests)
import Layer4Spec (layer4Tests)
import Layer5Spec (layer5Tests)
import OptimizeSpec (optimizeTests)
import ParseSpec (parseTests)
import QttSpec (qttTests)
import SymbolNameSpec (symbolNameTests)
import TraceSpec (traceTests)
import TypeCheckSpec (typeCheckTests)
import TypeErrorSpec (typeErrorTests)

main :: IO ()
-- Run sequentially (NumThreads 1). The codegen/integration tests shell out to
-- `once`, which builds against the shared `Strata/` interpretation tree and
-- writes/removes a shared object file there (e.g.
-- `Strata/Interpretations/Linux/Syscalls.x86_64.o`). Running them in parallel
-- races on that artifact (`removeLink: does not exist`). Serialising keeps the
-- suite deterministic; total runtime is ~12s.
main = defaultMain $ localOption (NumThreads 1) $ testGroup "Once"
  [ parseTests
  , typeCheckTests
  , typeErrorTests
  , qttTests
  , generatorTests
  , irTests
  , layer0Tests
  , layer1Tests
  , layer2Tests
  , layer3Tests
  , layer4Tests
  , layer5Tests
  , arithTests
  , floatTests
  , optimizeTests
  , traceTests
  , symbolNameTests
  ]
