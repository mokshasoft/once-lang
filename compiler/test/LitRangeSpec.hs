-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | AN `Int` LITERAL MUST FIT THE TARGET'S WORD (plan 0.74, D115).
--
-- Once's `Int` IS the target's machine word (D054), so what an `Int` literal
-- means depends on the target — and a literal the target cannot hold has no
-- meaning there at all. The compiler therefore REFUSES it rather than
-- silently wrapping it, and that refusal is not a lint: `Once.Adequacy.
-- Compile`'s `accept-gm` proves there is no path from an inadmissible module
-- to a byte, and `correctR-complete` proves the refusal cannot fire for a
-- program the target CAN express. This file is the runtime half of that pair.
--
-- THE SHARPEST STATEMENT IN THE PLAN, and the reason this file exists: the
-- SAME literal is rejected on one target and compiles on a wider one. A test
-- that only checked rejection would be satisfied by a compiler that rejected
-- everything; a test that only checked acceptance would be satisfied by one
-- that wrapped. Only the pair pins the rule.
--
-- AND ARITHMETIC IS NOT CHECKED. `2000000000 + 2000000000` overflows 32 bits
-- and must still compile, wrapping — because the promise `Int` makes is the
-- hardware's, and the hardware wraps. The literal is where the line is drawn,
-- because a literal is something the PROGRAMMER wrote and the compiler can
-- decide statically; an arithmetic result is not. The wrap case below is what
-- keeps a future "let's just range-check everything" from landing quietly.
--
-- HOW IT STAYS GENERAL. Nothing here is hand-computed per arch. `archIntBits`
-- mirrors the compiler's `arch-int-bits`; whether a literal is admissible and
-- what a wrapping sum comes to are both DERIVED from it. Adding a target is a
-- row in that table. If the table and the compiler ever disagree, the arch
-- whose verdict flips fails — which is exactly the alarm wanted.
--
-- Run with: cabal test --test-option='-p "/Int literal range/"'

module LitRangeSpec (litRangeTests) where

import Data.List (isInfixOf)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, assertFailure, testCase)

import Backend.Common (BackendArch (..), archName, backendArches,
                       buildAndRunTraceOn, cleanupDir, decodeTrace,
                       runOnceArch, signedAt, testStrataDir)

------------------------------------------------------------------------
-- The per-target Int width — this test's mirror of `arch-int-bits`.
------------------------------------------------------------------------

-- | Adding an arch is a row here, and nothing else.
archIntBits :: BackendArch -> Integer
archIntBits X86_32  = 32
archIntBits X86_64  = 64
archIntBits RiscV64 = 64

-- | `Once.Word.Width.InRange` — the signed range of a `bits`-wide word. This
-- is the decision the compiler runs (`inRange?`); stating it here rather than
-- listing per-arch verdicts is what makes a width change show up as a test
-- failure instead of a stale expectation.
fitsAt :: Integer -> Integer -> Bool
fitsAt bits z = negate half <= z && z <= half - 1
  where half = 2 ^ (bits - 1)

-- | Two's-complement wrap at `bits` — what ARITHMETIC does, and what a
-- literal is not allowed to need.
wrapAt :: Integer -> Integer -> Integer
wrapAt bits z = ((z + half) `mod` (2 * half)) - half
  where half = 2 ^ (bits - 1)

------------------------------------------------------------------------
-- The literals under test
------------------------------------------------------------------------

-- | Each is admissible on SOME target and not on another, except the last two
-- which pin the boundary itself. Written as `(source text, value)` because a
-- negative literal needs parenthesising in Once source and the value is what
-- the trace is checked against.
--
-- Only literals whose SOURCE TEXT is a plain numeral, plus small negatives.
-- A negated numeral whose MAGNITUDE straddles the target's bound belongs to
-- the known-defect group at the bottom of this file, not here: the parser
-- turns `-N` into `RUnaryOp OpNeg (RInt N)`, so the gate currently decides on
-- N rather than on -N. Keeping the exceptions out of this table is deliberate
-- — the table states the RULE, and a rule with a special case written into it
-- stops being reviewable.
literals :: [(String, Integer)]
literals =
  [ ("3000000000",           3000000000)            -- > 2^31-1, fits 64
  , ("2147483647",           2147483647)            -- exactly 2^31-1: fits 32
  , ("2147483648",           2147483648)            -- one past:      does not
  , ("(-5)",                          -5)           -- a negative arg, all 3 arches
  ]

-- | `emit <lit>` sequenced before `exit 7`. The literal is hoisted into a
-- signature-carrying binding for the same reason `FloatEmitSpec` does it —
-- nested inside a `compose` chain it would land in an inference position.
program :: String -> T.Text
program lit = T.unlines
  [ "import I.Linux.Syscalls as S"
  , "import I.Test.Emit as E"
  , ""
  , "emitLit : IO Unit"
  , T.pack ("emitLit = emit@E " ++ lit)
  , ""
  , "main : IO Unit"
  , "main = compose exit@S (compose 7 emitLit)"
  ]

------------------------------------------------------------------------
-- The tests
------------------------------------------------------------------------

litRangeTests :: TestTree
litRangeTests = testGroup "Int literal range (D115)"
  [ testGroup "a literal must fit the target's word"
      [ testGroup lit [ testCase (archName a) (checkLit a lit z) | a <- backendArches ]
      | (lit, z) <- literals ]
  , wrapTest
  , negatedLiteralDefect
  ]

-- | One literal on one arch. Which assertion runs is DERIVED, not listed.
checkLit :: BackendArch -> String -> Integer -> IO ()
checkLit arch lit z
  | fitsAt bits z = expectAccepted arch lit z
  | otherwise     = expectRejected arch lit z
  where bits = archIntBits arch

-- | Admissible: it builds, it runs, and the value that reaches the SigOp is
-- the literal itself — not a truncation of it. Reading the TRACE rather than
-- the exit code is what makes "compiles" mean "means what it says".
expectAccepted :: BackendArch -> String -> Integer -> IO ()
expectAccepted arch lit z = do
  r <- buildAndRunTraceOn arch (slug arch lit) (program lit)
  case r of
    Left err -> assertFailure
      (err ++ "\n  — " ++ lit ++ " fits " ++ archName arch ++ "'s signed "
           ++ show (archIntBits arch) ++ "-bit range, so it must compile.")
    Right (out, code) -> case decodeTrace arch out of
      Left err -> assertFailure ("[" ++ archName arch ++ "] " ++ err)
      Right ws -> do
        assertEqual (tag ++ " one emit invocation") 1 (length ws)
        assertEqual (tag ++ " emitted argument") z (signedAt arch (head ws))
        assertEqual (tag ++ " exit code") 7 code
  where tag = "[" ++ archName arch ++ "]"

-- | Inadmissible: the build FAILS, and the message names both the literal and
-- the bound. Checking the message is not pedantry — a refusal the programmer
-- cannot act on is a worse failure mode than the wrap it replaced, and D115
-- says the diagnostic is part of the contract.
expectRejected :: BackendArch -> String -> Integer -> IO ()
expectRejected arch lit z = do
  let tag     = "[" ++ archName arch ++ "]"
      bits    = archIntBits arch
      name    = slug arch lit
      testDir = "/tmp/once_litrange_" ++ archName arch ++ "_" ++ name
      srcFile = testDir </> name ++ ".once"
  createDirectoryIfMissing True testDir
  TIO.writeFile srcFile (program lit)
  (code, out, err) <- runOnceArch arch
    [ "build", "--target", archName arch, "--exe"
    , "--strata", testStrataDir, srcFile, "-o", testDir </> name ]
  cleanupDir testDir
  let msg = out ++ err
  case code of
    ExitSuccess -> assertFailure
      (tag ++ " " ++ lit ++ " needs more than " ++ show bits
           ++ " signed bits, but the build SUCCEEDED. A literal the target "
           ++ "cannot hold must be refused, not wrapped (D115).")
    ExitFailure _ -> do
      assertBool (tag ++ " the error should name the literal " ++ show z
                      ++ ", but said:\n" ++ msg)
                 (show z `isInfixOf` msg)
      assertBool (tag ++ " the error should name the " ++ show bits
                      ++ "-bit bound, but said:\n" ++ msg)
                 ((show bits ++ "-bit") `isInfixOf` msg)

-- | ARITHMETIC WRAPS — the other half of D115, and the one that keeps the
-- range check from spreading. Both operands fit 32 bits; their sum does not,
-- and on x86-32 the program must still build and emit the WRAPPED value.
wrapTest :: TestTree
wrapTest = testGroup "arithmetic still wraps — only literals are checked"
  [ testCase (archName a) (checkWrap a) | a <- backendArches ]

checkWrap :: BackendArch -> IO ()
checkWrap arch = do
  r <- buildAndRunTraceOn arch ("litwrap_" ++ archName arch) src
  case r of
    Left err -> assertFailure
      (err ++ "\n  — both operands fit " ++ show bits
           ++ " bits; only their SUM overflows, and arithmetic wraps rather "
           ++ "than being refused (D115).")
    Right (out, code) -> case decodeTrace arch out of
      Left err -> assertFailure (tag ++ " " ++ err)
      Right ws -> do
        assertEqual (tag ++ " one emit invocation") 1 (length ws)
        assertEqual (tag ++ " " ++ show a ++ " + " ++ show b ++ " wrapped at "
                         ++ show bits ++ " bits")
                    (wrapAt bits (a + b)) (signedAt arch (head ws))
        assertEqual (tag ++ " exit code") 7 code
  where
    tag  = "[" ++ archName arch ++ "]"
    bits = archIntBits arch
    a    = 2000000000
    b    = 2000000000
    src  = T.unlines
      [ "import I.Linux.Syscalls as S"
      , "import I.Test.Emit as E"
      , ""
      , "emitSum : IO Unit"
      , T.pack ("emitSum = emit@E (" ++ show a ++ " + " ++ show b ++ ")")
      , ""
      , "main : IO Unit"
      , "main = compose exit@S (compose 7 emitSum)"
      ]

-- | A filesystem-safe per-case build directory name.
slug :: BackendArch -> String -> String
slug arch lit = "litrange_" ++ archName arch ++ "_" ++ map keep lit
  where keep ch | ch `elem` punct = '_'
                | otherwise       = ch
        punct :: [Char]
        punct = "()-"   -- OverloadedStrings is on for this suite

------------------------------------------------------------------------
-- KNOWN DEFECT — a negated numeral is gated on its MAGNITUDE (0.74 J6)
------------------------------------------------------------------------

-- WHAT IS WRONG. `-2147483648` is a perfectly good x86-32 `Int` — it is
-- exactly the least one — and the compiler REFUSES it, saying "Int literal
-- 2147483648 does not fit". A program the target can express is rejected,
-- which is the one failure mode `correctR-complete` exists to rule out. The
-- proof does not catch it because the SPEC shares the blind spot: the gate and
-- `rawIntLits` both walk the same AST, and the AST is what is wrong.
--
-- WHY. `Once/Parser/Expr.agda:1012` parses `-N` as `RUnaryOp OpNeg (RInt N)`,
-- so the only literal in the tree is the MAGNITUDE. Nothing folds the sign in:
-- the elaborator has no constant folder, and `Once/IR.agda`'s `const` carries
-- a `ℤ`, so the IR could hold `-2147483648` and simply never does. The machine
-- therefore materialises 2147483648 at 32 bits — which WRAPS, and a wrapping
-- literal is precisely what D115 forbids. So the refusal is not a bug in the
-- gate: the gate is correctly reporting that this program, as elaborated,
-- needs an unrepresentable literal. The bug is upstream, in the elaboration
-- that made it need one.
--
-- THE TESTS BELOW PIN THE DEFECT, NOT THE INTENT. They assert what the
-- compiler does today, so that the day it is fixed they FAIL and must be moved
-- into `literals` above, where they belong. Read them as a tripwire, never as
-- a specification — the specification is the paragraph above.
negatedLiteralDefect :: TestTree
negatedLiteralDefect =
  testGroup "KNOWN DEFECT (0.74 J6) — a negated numeral is gated on its magnitude"
    [ testCase "-2147483648 is refused on x86_32 though it fits" $ do
        r <- buildRaw X86_32 "negdefect_min32" (program "(-2147483648)")
        case r of
          Left msg -> assertBool
            ("expected the refusal to name the MAGNITUDE 2147483648."
             ++ " If it now names -2147483648, J6 is fixed. Got:\n" ++ msg)
            ("Int literal 2147483648" `isInfixOf` msg)
          Right () -> assertFailure
            ("the build SUCCEEDED — J6 appears to be fixed. Move"
             ++ " (-2147483648), (-3000000000) and (-2147483649) into"
             ++ " `literals` and delete this group.")

    , testCase "a refused negative names its magnitude, not its value" $ do
        r <- buildRaw X86_32 "negdefect_msg" (program "(-3000000000)")
        case r of
          Left msg -> assertBool
            ("expected the magnitude 3000000000 in the message; got:\n" ++ msg)
            ("Int literal 3000000000" `isInfixOf` msg)
          Right () -> assertFailure
            "-3000000000 does not fit x86-32 either way; it must be refused."
    ]

-- | Build only, reporting the compiler's own message on failure. Separate from
-- `expectRejected` because the defect group needs the message whichever way
-- the verdict goes.
buildRaw :: BackendArch -> String -> T.Text -> IO (Either String ())
buildRaw arch name src = do
  let testDir = "/tmp/once_litrange_" ++ archName arch ++ "_" ++ name
      srcFile = testDir </> name ++ ".once"
  createDirectoryIfMissing True testDir
  TIO.writeFile srcFile src
  (code, out, err) <- runOnceArch arch
    [ "build", "--target", archName arch, "--exe"
    , "--strata", testStrataDir, srcFile, "-o", testDir </> name ]
  cleanupDir testDir
  pure (case code of ExitSuccess -> Right () ; ExitFailure _ -> Left (out ++ err))
