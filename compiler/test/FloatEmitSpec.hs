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
-- literal at `FrameSemantics.float-format FS`, and the apex reads the same fact
-- from `arch-float-format arch`. The proof pins those two channels together
-- (`fmt-eq`, `fmt-agree`); this pins them to what the program actually does.
--
-- THE OBSERVABLE IS THE TRACE, NOT THE ASSEMBLY. `I.Test.Emit`'s `emitF`
-- writes its argument's whole machine word to stdout, exactly as `emit` does
-- for an Int, so what is read back IS the SigOp invocation's argument — the
-- thing D114 made the spec able to see. Reading the `.s` would only show what
-- the compiler wrote down; this shows what the program passed.
--
-- HOW IT STAYS GENERAL ACROSS ARCHES OF DIFFERENT WIDTH. Nothing here is a
-- hand-computed bit pattern. A case names a LITERAL; the expectation is
-- DERIVED by encoding that literal at the arch's own format, from one table
-- (`archFloatFormat`) that mirrors the compiler's `arch-float-format`. Adding
-- a target means adding a row, not re-deriving every expectation — and if the
-- compiler's table and this one ever disagree, every case fails at once, which
-- is the point.
--
-- Run with: cabal test --test-option='-p "/Float format/"'

module FloatEmitSpec (floatEmitTests) where

import Data.List (nub)
import qualified Data.Text as T
import GHC.Float (castDoubleToWord64, castFloatToWord32)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)

import Backend.Common (BackendArch (..), archName, backendArches,
                       buildAndRunTraceOn, decodeTrace)

------------------------------------------------------------------------
-- The per-target float format — this test's mirror of `arch-float-format`.
------------------------------------------------------------------------

data Format = Binary32 | Binary64 deriving (Eq, Show)

-- | Adding an arch is a row here, and nothing else.
archFloatFormat :: BackendArch -> Format
archFloatFormat X86_32  = Binary32   -- a float lives in a 32-bit GPR
archFloatFormat X86_64  = Binary64
archFloatFormat RiscV64 = Binary64

-- | Encode a literal at a format — IEEE-754, via the host's own conversion, so
-- the expectation is computed rather than transcribed.
encodeAt :: Format -> Double -> Integer
encodeAt Binary64 v = fromIntegral (castDoubleToWord64 v)
encodeAt Binary32 v = fromIntegral (castFloatToWord32 (realToFrac v))

-- | The literals under test: exact dyadic rationals, so the frontend accepts
-- them at every supported format (`Once.Float.Representable.accept?`) and the
-- only thing that varies is the ENCODING.
literals :: [(String, Double)]
literals = [ ("0.5", 0.5), ("0.125", 0.125), ("2.75", 2.75) ]

------------------------------------------------------------------------
-- The program: `emitF <lit>` sequenced before `exit 7`.
------------------------------------------------------------------------

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
--     `compose` it lands in an INFERENCE position and a float literal has no
--     inferable type — a pre-existing frontend gap, not something this branch
--     introduced. Hoisting it into `emitLit : IO Unit` restores a checking
--     position.
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
  [ testGroup lit [ testCase (archName a) (checkOne a lit v) | a <- backendArches ]
  | (lit, v) <- literals ]

checkOne :: BackendArch -> String -> Double -> IO ()
checkOne arch lit v = do
  r <- buildAndRunTraceOn arch (slug lit) (program lit)
  case r of
    Left err -> assertFailure err
    Right (out, code) -> case decodeTrace arch out of
      Left err  -> assertFailure ("[" ++ tag ++ "] " ++ err)
      Right ws  -> do
        assertEqual ("[" ++ tag ++ "] one emitF invocation") 1 (length ws)
        let got  = head ws
            want = encodeAt (archFloatFormat arch) v
        -- Naming the OTHER formats' encodings makes a format mix-up report
        -- itself, instead of surfacing as an opaque number mismatch.
        case [ f | f <- others, encodeAt f v == got ] of
          (f : _) -> assertFailure
            ("[" ++ tag ++ "] " ++ lit ++ " was emitted at " ++ show f
             ++ ", but this target's format is "
             ++ show (archFloatFormat arch)
             ++ " — `arch-float-format` and this target's emitter disagree.")
          [] -> do
            assertEqual ("[" ++ tag ++ "] emitted machine word for " ++ lit)
                        want got
            assertEqual ("[" ++ tag ++ "] exit code") 7 code
  where
    tag    = archName arch
    others = filter (/= archFloatFormat arch)
                    (nub (map archFloatFormat backendArches))

-- | A filesystem-safe per-test build directory name.
slug :: String -> String
slug = ("floatemit_" ++) . map (\ch -> if ch == '.' then '_' else ch)
