module Main (main) where

import Test.Tasty
import Test.Tasty.Runners (NumThreads (..))

import ArithSpec (arithTests)
import FloatSpec (floatTests)
import FmtSpec (fmtTests)
import ImportSpec (importTests)
import FloatEmitSpec (floatEmitTests)
import LitRangeSpec (litRangeTests)
import GeneratorSpec (generatorTests)
import IRSpec (irTests)
import Layer0Spec (layer0Tests)
import Layer1Spec (layer1Tests)
import Layer2Spec (layer2Tests)
import Layer3Spec (layer3Tests)
import InferSpec (inferTests)
import Layer4Spec (layer4Tests)
import Layer5Spec (layer5Tests)
import OptimizeSpec (optimizeTests)
import ParseSpec (parseTests)
import QttSpec (qttTests)
import PuritySpec (purityTests)
import TelescopeSpec (telescopeTests)
import SpecMatrixSpec (specMatrixTests)
import SymbolNameSpec (symbolNameTests, thunkSymbolTests)
import TraceSpec (traceTests)
import TypeCheckSpec (typeCheckTests)
import TypeErrorSpec (typeErrorTests)

main :: IO ()
-- Run sequentially (NumThreads 1). The codegen/integration tests shell out to
-- `once`. Until plan 0.125 the compiler wrote a shared object file into the
-- `Strata/` tree (e.g. `Strata/Interpretations/Linux/Syscalls.x86_64.o`) and
-- parallel runs raced on it (`removeLink: does not exist`); objects now go
-- beside each build's output. Serialising is kept for determinism; total
-- runtime is ~12s.
main = defaultMain $ localOption (NumThreads 1) $ testGroup "Once"
  [ parseTests
  , typeCheckTests
  , typeErrorTests
  , qttTests
  , purityTests
  , importTests
  , fmtTests
  , telescopeTests
  , specMatrixTests
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
  , floatEmitTests
  , litRangeTests
  , optimizeTests
  , traceTests
  , inferTests
  , symbolNameTests
  , thunkSymbolTests
  ]
