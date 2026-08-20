-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | The target's FLOAT FORMAT, observed in the EFFECT TRACE (plan 0.73,
-- D113/D114).
--
-- WHAT THIS TESTS THAT NOTHING ELSE DID. Until D113 a float literal's
-- denotation was an exact dyadic and the format was applied by a per-arch
-- `fenc` parameter that every target happened to instantiate consistently with
-- its own emitter — so nothing could disagree and nothing was checked. Now
-- `⟦ Float ⟧` IS the target's representation, the machine materialises a
-- literal at `FrameSemantics.float-format FS`, and the apex reads the same
-- fact from `arch-float-format arch`. The proof pins those two channels
-- together (`fmt-eq`, `fmt-agree`); this pins them to what the program
-- actually does.
--
-- THE OBSERVABLE IS THE TRACE, NOT THE ASSEMBLY. `I.Test.Emit`'s `emitF`
-- writes its argument's whole machine word to stdout, exactly as `emit` has
-- always written an Int's low byte, so the bytes below ARE the SigOp
-- invocation's argument — the thing D114 made the spec able to see. Reading
-- the `.s` would only show what the compiler wrote down; this shows what the
-- program passed.
--
-- IT IS DELIBERATELY ARCH-DISCRIMINATING. x86-32 keeps a float in a 32-bit
-- GPR, so `0.5` there is four bytes of `binary32`; on the 64-bit targets it is
-- eight of `binary64`. A test that only checked "some bytes" would pass with
-- every arch sharing one format, which is exactly the bug D109 was.
--
-- Run with: cabal test --test-option='-p "/Float format/"'

module FloatEmitSpec (floatEmitTests) where

import qualified Data.Text as T

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)

import Backend.Common (BackendArch (..), archName, backendArches, buildAndRunTraceOn)

------------------------------------------------------------------------
-- The expected encodings, as the LITTLE-ENDIAN byte sequence `emitF` writes.
------------------------------------------------------------------------

data Case = Case
  { caseLit :: String    -- ^ the literal, as written in the source
  , caseB64 :: [Int]     -- ^ binary64, little-endian
  , caseB32 :: [Int]     -- ^ binary32, little-endian
  }

-- 0.5   = 0x3FE0000000000000 / 0x3F000000
-- 0.125 = 0x3FC0000000000000 / 0x3E000000
-- 2.75  = 0x4006000000000000 / 0x40300000
cases :: [Case]
cases =
  [ Case "0.5"   [0,0,0,0,0,0,0xE0,0x3F] [0,0,0x00,0x3F]
  , Case "0.125" [0,0,0,0,0,0,0xC0,0x3F] [0,0,0x00,0x3E]
  , Case "2.75"  [0,0,0,0,0,0,0x06,0x40] [0,0,0x30,0x40]
  ]

-- | What this arch must write, and what it must NOT.
expectedFor :: BackendArch -> Case -> ([Int], [Int])
expectedFor X86_32  c = (caseB32 c, caseB64 c)
expectedFor X86_64  c = (caseB64 c, caseB32 c)
expectedFor RiscV64 c = (caseB64 c, caseB32 c)

-- | `emitF <lit>` then `exit 7`. The exit code is asserted too, so a program
-- that emitted the right bytes and then died would still fail.
--
-- TWO SHAPE CONSTRAINTS, both learned the hard way and both worth keeping:
--
--   * The effect must be SEQUENCED with `compose`, not bound by `let _ = … in`.
--     A `let`-bound effect compiles to a thunk that is never entered, so it
--     emits nothing — verified with the Int `emit` too, so this is not a float
--     matter. (The shipped `test/float-emit-*.once` exit tests use the `let`
--     shape and therefore never invoke `emitF` at runtime; they only show the
--     program builds and exits.)
--   * The literal needs a SIGNATURE-CARRYING binding. `compose emitF@E 0.5`
--     checks fine against a declared `IO Unit`, but nested inside another
--     `compose` it lands in an INFERENCE position and the float literal has no
--     inferable type — a pre-existing frontend gap, not something this branch
--     introduced. Hoisting it into `emitLit : IO Unit` puts it back in a
--     checking position.
program :: String -> T.Text
program lit = T.unlines
  [ "import I.Linux.Syscalls as S"
  , "import I.Test.Emit as E"
  , ""
  , "emitLit : IO Unit"
  , T.pack ("emitLit = compose emitF@E " ++ lit)
  , ""
  , "main : IO Unit"
  , "main = compose exit@S (compose 7 emitLit)"
  ]

------------------------------------------------------------------------
-- The tests
------------------------------------------------------------------------

floatEmitTests :: TestTree
floatEmitTests = testGroup "Float format in the effect trace"
  [ testGroup (caseLit c)
      [ testCase (archName a) (checkOne a c) | a <- backendArches ]
  | c <- cases ]

checkOne :: BackendArch -> Case -> IO ()
checkOne arch c = do
  r <- buildAndRunTraceOn arch (slug (caseLit c)) (program (caseLit c))
  case r of
    Left err -> assertFailure err
    Right (out, code) -> do
      let (want, avoid) = expectedFor arch c
          got           = map fromEnum out
          tag           = archName arch
      if got == avoid
        then assertFailure
               ("[" ++ tag ++ "] " ++ caseLit c ++ " was emitted at the OTHER"
                ++ " target's format: got " ++ show got
                ++ " (" ++ show (length avoid) ++ " bytes), expected "
                ++ show want ++ ".  `arch-float-format` and this target's"
                ++ " emitter disagree.")
        else do
          assertEqual ("[" ++ tag ++ "] emitted machine word for " ++ caseLit c)
                      want got
          assertEqual ("[" ++ tag ++ "] exit code") 7 code

-- | A filesystem-safe per-test build directory name.
slug :: String -> String
slug = map (\ch -> if ch == '.' then '_' else ch) . ("floatemit_" ++)
