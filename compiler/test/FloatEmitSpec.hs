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

-- | An ARITHMETIC expectation, and it CANNOT go through `encodeAt` (plan 0.75
-- F4). `encodeAt Binary32` narrows a `Double` at the END; a binary32 target
-- rounds after EVERY operation. Those differ the moment an intermediate is
-- inexact, so each case carries its value computed at BOTH precisions and the
-- arch picks. Haskell's defaulting does the work: the same literal expression
-- is evaluated at `Double` in one field and at `Float` in the other.
encodeArith :: Format -> (Double, Float) -> Integer
encodeArith Binary64 (d, _) = fromIntegral (castDoubleToWord64 d)
encodeArith Binary32 (_, f) = fromIntegral (castFloatToWord32 f)

-- | The literals under test.
--
-- The first three are exact dyadic rationals, so the only thing that varies is
-- the ENCODING. `accept?` is gone (D116) and a literal no longer has to be
-- exact, so the rest are the cases that could not be written before.
--
-- THE NEGATIVE ONES ARE THE REAL CHECK ON `round` (plan 0.73 F3, D117).
-- `-3.14` elaborates to ONE literal whose payload is `negate (decimalOf 3 14
-- 2)`, and both the compiler and its spec then call the SAME `round` — so the
-- correspondence proof is `refl`-shaped and cannot falsify it. Here the
-- expectation comes from GHC's IEEE conversion instead, which is a genuinely
-- independent implementation. `-3.14` is not exact at either format, so this
-- exercises round-to-nearest-even on a negative significand, not just the
-- sign bit.
--
-- `-0.0` is deliberately ABSENT and is a stated limitation: `Decimal.negate`
-- is `ℤ.-` on the significand and `ℤ.- (+ 0) = + 0`, so Once compiles `-0.0`
-- to POSITIVE zero. IEEE distinguishes them; Once does not, in the same way
-- and for the same reason it has no subnormals (D118). Pinned in
-- `Once.Float.Decimal` so it is read rather than discovered.
literals :: [(String, Double)]
literals =
  [ ("0.5", 0.5), ("0.125", 0.125), ("2.75", 2.75)
  , ("-0.5", -0.5), ("-2.75", -2.75), ("-3.14", -3.14)
  ]

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
  , T.pack ("emitLit = compose emitF@E " ++ paren lit)
  , ""
  , "main : IO Unit"
  , "main = compose exit@S (compose 7 emitLit)"
  ]

------------------------------------------------------------------------
-- The tests
------------------------------------------------------------------------

floatEmitTests :: TestTree
floatEmitTests = testGroup "Float format in the effect trace"
  ([ testGroup lit [ testCase (archName a) (checkOne a lit v) | a <- backendArches ]
   | (lit, v) <- literals ]
   ++
   [ testGroup ("arith: " ++ e) [ testCase (archName a) (checkArith a e vs) | a <- backendArches ]
   | (e, vs) <- arithCases ]
   ++
   [ testGroup ("widen: " ++ e) [ testCase (archName a) (checkArith a e vs) | a <- backendArches ]
   | (e, vs) <- wideningCases ]
   ++
   -- D055: the DECIDED NaN, not the hardware's. x86 answers
   -- `0xfff8000000000000` for `0.0 / 0.0` in silicon.
   [ testGroup ("canonical NaN: " ++ e)
       [ testCase (archName a) (checkCanonNaN a e) | a <- backendArches ]
   | e <- [ "0.0 / 0.0", "0.0 * (1.0 / 0.0)" ] ])

-- | Read an ARITHMETIC result back out of the trace. Same assertions as
-- `checkOne`, against an expectation computed at the arch's OWN precision —
-- which is what makes this a check on the arithmetic and not just on the
-- literal encoding.
checkArith :: BackendArch -> String -> (Double, Float) -> IO ()
checkArith arch expr vs = do
  r <- buildAndRunTraceOn arch (slug expr) (arithProgram expr)
  case r of
    Left err -> assertFailure err
    Right (out, code) -> case decodeTrace arch out of
      Left err  -> assertFailure ("[" ++ tag ++ "] " ++ err)
      Right ws  -> do
        assertEqual ("[" ++ tag ++ "] one emitF invocation") 1 (length ws)
        assertEqual ("[" ++ tag ++ "] emitted machine word for " ++ expr)
                    (encodeArith (archFloatFormat arch) vs) (head ws)
        assertEqual ("[" ++ tag ++ "] exit code") 7 code
  where tag = archName arch

-- | D055's NaN canonicalisation, on the metal.
--
-- The expectation is the DECIDED value, not the measured one, and that is the
-- whole point: x86 hardware answers `0xfff8000000000000` for `0.0 / 0.0` (it
-- sets the sign on an invalid result) and propagates operand payloads, while
-- RISC-V produces one canonical NaN natively. Once promises the RISC-V answer
-- everywhere, so the x86 emitters carry a canonicalising fixup. This test is
-- what makes that promise falsifiable — take the fixup out and x86-64 and
-- x86-32 fail here while riscv64 still passes.
checkCanonNaN :: BackendArch -> String -> IO ()
checkCanonNaN arch expr = do
  r <- buildAndRunTraceOn arch (slug expr) (arithProgram expr)
  case r of
    Left err -> assertFailure err
    Right (out, code) -> case decodeTrace arch out of
      Left err  -> assertFailure ("[" ++ tag ++ "] " ++ err)
      Right ws  -> do
        assertEqual ("[" ++ tag ++ "] one emitF invocation") 1 (length ws)
        assertEqual ("[" ++ tag ++ "] canonical NaN (D055) for " ++ expr)
                    (canonNaN (archFloatFormat arch)) (head ws)
        assertEqual ("[" ++ tag ++ "] exit code") 7 code
  where tag = archName arch

-- | `(2^e − 1) · 2^s + 2^(s−1)` — `Once.Float.Arith.nan`, in Haskell.
canonNaN :: Format -> Integer
canonNaN Binary64 = ((2 ^ (11 :: Int) - 1) * 2 ^ (52 :: Int)) + 2 ^ (51 :: Int)
canonNaN Binary32 = ((2 ^ (8  :: Int) - 1) * 2 ^ (23 :: Int)) + 2 ^ (22 :: Int)

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

-- | A NEGATIVE literal needs parentheses, and the reason is the grammar, not
-- the type checker. `-` is both a prefix and an infix operator, and the
-- application `compose emitF@E` ends at the first token that cannot start an
-- atom — which `-` cannot. So `compose emitF@E -3.14` parses as the
-- SUBTRACTION `(compose emitF@E) - 3.14`. Parenthesising puts the minus back
-- in prefix position, where `parseUnaryWF` reads it.
-- | The ARITHMETIC program. Note the shape: `emitF@E <expr>` APPLIED, not
-- `compose emitF@E <expr>`.
--
-- That distinction cost a wrong conclusion once and is worth writing down.
-- `compose`'s second argument must be a MORPHISM `Unit ⇒ Float`, so a literal
-- gets there by the value-lift (`⊢ᵍ`, closed values) and an EXPRESSION has no
-- route — `compose emit@E (1 + 2)` fails identically for `Int`, so it is not a
-- float limitation and not an `emitF` limitation. Applying the SigOp directly
-- has no such requirement, and the effect IS entered: what is never entered is
-- a `let _ = … in` binding, which is a different shape again.
arithProgram :: String -> T.Text
arithProgram expr = T.unlines
  [ "import I.Linux.Syscalls as S"
  , "import I.Test.Emit as E"
  , ""
  , "emitExpr : IO Unit"
  , T.pack ("emitExpr = emitF@E (" ++ expr ++ ")")
  , ""
  , "main : IO Unit"
  , "main = compose exit@S (compose 7 emitExpr)"
  ]

-- | The expressions under test. Each carries its value at both precisions;
-- the source string and the two Haskell expressions are written once and
-- stay in step by construction.
arithCases :: [(String, (Double, Float))]
arithCases =
  [ ("1.5 + 2.25 * 2.0 - 0.5", (1.5 + 2.25 * 2.0 - 0.5, 1.5 + 2.25 * 2.0 - 0.5))
    -- THE case: inexact at both formats, and the two formats disagree — so
    -- this fails if a target ever computes at the wrong width.
  , ("0.1 + 0.2",              (0.1 + 0.2,              0.1 + 0.2))
  , ("3.14 * 2.0",             (3.14 * 2.0,             3.14 * 2.0))
    -- The expression F4 exists for: `1.5 - 2.1` was a type error until it.
  , ("1.5 - 2.1",              (1.5 - 2.1,              1.5 - 2.1))
    -- Negation of a computed value, and a negative literal inside arithmetic.
  , ("0.0 - (2.5 * 1.5)",      (0.0 - (2.5 * 1.5),      0.0 - (2.5 * 1.5)))
    -- DIVISION. `1.0 / 3.0` is non-terminating in binary, so the quotient is
    -- inexact by construction and every discarded bit has to be accounted for
    -- — this is the case the sticky bit exists for, run on the metal.
  , ("1.0 / 3.0",              (1.0 / 3.0,              1.0 / 3.0))
    -- ⭐ The discriminator. `0.1 / 0.3` answers ONE ULP ABOVE `1.0 / 3.0`
    -- despite both being `0.333…`, because the operands are themselves rounded
    -- and the true quotient falls the other side of the boundary. A divider
    -- that truncated, or that rounded without the remainder, passes the line
    -- above and fails this one.
  , ("0.1 / 0.3",              (0.1 / 0.3,              0.1 / 0.3))
    -- Exact quotient: the remainder is zero, so the sticky fold must be a
    -- no-op. And a division mixed with the other three operations.
  , ("6.0 / 3.0",              (6.0 / 3.0,              6.0 / 3.0))
  , ("1.5 + 7.0 / 11.0",       (1.5 + 7.0 / 11.0,       1.5 + 7.0 / 11.0))
  ]

-- | D125's widening, on the metal: the `Int` operand is converted by a
-- correctly-rounded `arith.i2f` and the expression is a `Float`.
wideningCases :: [(String, (Double, Float))]
wideningCases =
  [ ("1 + 1.5",   (1 + 1.5,   1 + 1.5))
    -- Widening on the LEFT of a division, so the `i2f` and the quotient meet.
  , ("1 / 4.0",   (1 / 4.0,   1 / 4.0))
  , ("2.5 * 3",   (2.5 * 3,   2.5 * 3))
  , ("7 - 0.25",  (7 - 0.25,  7 - 0.25))
  ]

paren :: String -> String
paren lit@('-' : _) = "(" ++ lit ++ ")"
paren lit           = lit

-- | A filesystem-safe per-test build directory name. The leading `-` of a
-- negative literal becomes `neg` rather than `_`: a directory whose name
-- starts with a dash is read as an option by every tool the build shells out
-- to.
-- Arithmetic sources contain spaces and operators, so the slug maps every
-- character that is not alphanumeric to a safe stand-in rather than only `.`.
slug :: String -> String
slug ('-' : rest) = "floatemit_neg" ++ concatMap safe rest
slug lit          = "floatemit_" ++ concatMap safe lit

safe :: Char -> String
safe c
  | c `elem` ['0'..'9'] = [c]
  | c `elem` ['a'..'z'] = [c]
  | c == '.'            = "_"
  | c == '+'            = "p"
  | c == '-'            = "m"
  | c == '*'            = "t"
  | c == ' '            = ""
  | c == '('            = ""
  | c == ')'            = ""
  | otherwise           = "_"
