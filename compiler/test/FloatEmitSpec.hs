-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | The target's FLOAT FORMAT, checked in the emitted machine code
-- (plan 0.73, D113/D114).
--
-- WHAT THIS TESTS THAT NOTHING ELSE DID. Until D113 a float literal's
-- denotation was an exact dyadic and the format was applied by a per-arch
-- `fenc` parameter that every target happened to instantiate consistently
-- with its own emitter — so nothing could disagree, and nothing was checked.
-- Now `⟦ Float ⟧` IS the target's representation, the machine materialises a
-- literal at `FrameSemantics.float-format FS`, and the apex reads the same
-- fact from `arch-float-format arch`. The proof pins those two channels
-- together (`fmt-eq`, `fmt-agree`); THIS pins them to the bytes.
--
-- It is deliberately arch-DISCRIMINATING. x86-32 keeps a float in a 32-bit
-- GPR, so `0.5` there is `0x3F000000`; on the 64-bit targets it is
-- `0x3FE0000000000000`. Each case asserts the right pattern is present AND
-- that the other target's pattern is ABSENT — a test that only checked
-- "some immediate" would pass with every arch using the same format, which
-- is exactly the bug D109 was.
--
-- Why the assembly rather than the exit code: `emitF`'s runtime is a nop
-- (`Strata/Interpretations/Test/Emit.once` says so), so a float argument is
-- not observable at process level. The `.s` is where the encoding becomes
-- visible without inventing a runtime that does not exist yet.
--
-- Run with: cabal test --test-option='-p "/Float format/"'

module FloatEmitSpec (floatEmitTests) where

import Data.Char (isDigit)
import Data.List (isPrefixOf, tails)
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))

import qualified Data.Text.IO as TIO

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure)

import Backend.Common (BackendArch (..), archName, backendArches, cleanupDir, runOnceArch)

------------------------------------------------------------------------
-- The expected encodings, computed by hand from IEEE-754 and written in
-- decimal because that is what the AT&T emitter prints (`$<n>`).
------------------------------------------------------------------------

-- | `(source literal, binary64 pattern, binary32 pattern)`.
--
-- Matched as a DECIMAL TOKEN, not with a syntax prefix: x86 is AT&T (`$imm`)
-- while riscv64 writes `li a0, imm` bare, and this test is about the ENCODING,
-- not about either assembler's spelling.
data Case = Case
  { caseFile :: String   -- ^ the `.once` under test/
  , caseLit  :: String   -- ^ the literal it contains, for the test name
  , caseB64  :: Integer
  , caseB32  :: Integer
  }

cases :: [Case]
cases =
  [ Case "float-emit-half"     "0.5"   4602678819172646912 1056964608
  , Case "float-emit-eighth"   "0.125" 4593671619917905920 1040187392
  , Case "float-emit-quarters" "2.75"  4613374868287651840 1076887552
  ]

-- | What this arch must emit, and what it must NOT.
expectedFor :: BackendArch -> Case -> (Integer, Integer)
expectedFor X86_32  c = (caseB32 c, caseB64 c)
expectedFor X86_64  c = (caseB64 c, caseB32 c)
expectedFor RiscV64 c = (caseB64 c, caseB32 c)

------------------------------------------------------------------------
-- Build to assembly and hand back the text.
------------------------------------------------------------------------

-- | Build `test/<name>.once` for `arch`, keeping the `.s`, and return it.
-- `--no-optimize` so the literal cannot be folded away by a pass this test
-- is not about; `--alloc heap` to match the other backend specs.
buildAsmOn :: BackendArch -> String -> IO (Either String String)
buildAsmOn arch name = do
  let tag     = archName arch
      testDir = "/tmp/once_asm_" ++ tag ++ "_" ++ name
      srcFile = testDir </> name ++ ".once"
      outBase = testDir </> name
  createDirectoryIfMissing True testDir
  source <- TIO.readFile ("test/" ++ name ++ ".once")
  TIO.writeFile srcFile source
  (code, _out, err) <- runOnceArch arch
    [ "build", "--target", tag, "--alloc", "heap", "--no-optimize"
    , "--save-temps", "--exe", srcFile, "-o", outBase ]
  case code of
    ExitFailure _ -> cleanupDir testDir >> pure (Left ("[" ++ tag ++ "] build failed: " ++ err))
    ExitSuccess   -> do
      asm <- readFile (outBase ++ ".s")
      length asm `seq` cleanupDir testDir
      pure (Right asm)

------------------------------------------------------------------------
-- The tests
------------------------------------------------------------------------

floatEmitTests :: TestTree
floatEmitTests = testGroup "Float format in emitted code"
  [ testGroup (caseLit c)
      [ testCase (archName a) (checkOne a c) | a <- backendArches ]
  | c <- cases ]

-- | Does this exact integer appear in the text as a whole decimal token?
-- Substring matching alone would let `1056964608` be found inside a longer
-- number, so both neighbours must be non-digits.
containsImm :: Integer -> String -> Bool
containsImm n asm = any hit (tails (' ' : asm))
  where
    d = show n
    hit (prev : rest) = not (isDigit prev) && d `isPrefixOf` rest
                        && not (any isDigit (take 1 (drop (length d) rest)))
    hit []            = False

checkOne :: BackendArch -> Case -> IO ()
checkOne arch c = do
  r <- buildAsmOn arch (caseFile c)
  case r of
    Left err  -> assertFailure err
    Right asm -> do
      let (want, avoid) = expectedFor arch c
          wantS  = show want
          avoidS = show avoid
          tag    = archName arch
      if not (containsImm want asm)
        then assertFailure
               ("[" ++ tag ++ "] " ++ caseLit c ++ " should encode to " ++ wantS
                ++ " but that immediate is absent from the emitted assembly."
                ++ (if containsImm avoid asm
                      then "  The OTHER format's pattern (" ++ avoidS
                           ++ ") is present instead — `arch-float-format` and this"
                           ++ " target's emitter disagree."
                      else ""))
        else if containsImm avoid asm
          then assertFailure
                 ("[" ++ tag ++ "] emitted " ++ wantS ++ " (correct) but ALSO "
                  ++ avoidS ++ ", the other format's pattern for the same literal.")
          else pure ()
