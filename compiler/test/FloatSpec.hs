-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Float literal tests.
--
-- THE RULE UNDER TEST CHANGED, and this file is the record of it. Plan 0.71
-- accepted a float literal only if it was EXACTLY representable at every
-- supported format, so `0.1` failed to compile. Plan 0.74 K3 (D116) deleted
-- that refusal: a literal's payload is the DECIMAL the programmer wrote, and
-- the backend rounds it at the target's format, because IEEE's promise
-- INCLUDES rounding exactly as `Int`'s promise includes wrapping (D054).
--
-- So every group below now ACCEPTS. What used to be the two halves of the
-- suite — dyadic and not — is now the difference between a literal that is
-- stored exactly and one that is stored rounded, and the compiler treats them
-- alike. The old split is kept as the ORGANISING PRINCIPLE rather than deleted
-- so that the flip is legible: these are the same literals, with the opposite
-- verdict.
--
-- WHAT THIS SUITE CAN NOW SEE. `Once.Warnings.roundingWarnings` (D123) is
-- WIRED to the driver, so "accepted" is no longer the whole observable: every
-- exact literal below asserts SILENCE on stderr and every rounded one asserts
-- the warning FIRES and names the literal. That distinction — `0.5` from `0.1`
-- — is what this suite could not make before, and it is what makes D116's "the
-- refusal is replaced by a warning" true rather than half true.
--
-- Wiring it immediately caught a renderer defect: the fraction numeral was
-- printed UNPADDED, so `0.01` (payload `frac = 1, flen = 2`) rendered as
-- `0.1` — a different literal from the source. `showFrac` pads it now. The
-- per-literal ENCODING is checked elsewhere and for real: `FloatEmitSpec`
-- reads the emitted machine word back out of the effect trace on all three
-- arches, and `Once.Float.Decimal` pins `round` against glibc/GHC patterns.
--
-- NO INTERPRETATION IS NEEDED, and that is not an accident. A literal lowers
-- to `const fits-float d`, i.e. an immediate load; SigOps like `fadd` and
-- `floatToInt` are what need `Strata/Interpretations/Math/*`.
--
-- Run with: cabal test --test-option='-p "/Float/"'

module FloatSpec (floatTests) where

import Test.Tasty
import Test.Tasty.HUnit (testCase, assertBool)
import Data.List (isInfixOf)
import qualified Data.Text as T

import TypeErrorSpec (accepts, typeCheckStderr)

-- | A one-line program binding a float literal at type `Float`.
lit :: String -> [T.Text]
lit v = [ "x : Float", T.pack ("x = " ++ v) ]

-- | A NEGATED literal. The parentheses are not needed here — `x = -3.14` is a
-- definition body, not an argument position, so the minus is already in prefix
-- position for `parseUnaryWF`.
negLit :: String -> [T.Text]
negLit v = lit ('-' : v)

-- | The warning channel is now WIRED (D123 → the driver), so "accepted" is no
-- longer the whole observable: an exact literal must compile AND say nothing,
-- a rounded one must compile AND say so. That distinction is what this suite
-- could not make while `Once.Warnings` was unreachable from `once`.
--
-- `once check` fixes the arch at x86-64, so these are binary64's verdicts.
exact :: String -> TestTree
exact v = testGroup (v ++ " is exact")
  [ accepts "compiles" (lit v)
  , testCase "and warns about nothing" $ do
      err <- typeCheckStderr (T.unlines (lit v))
      assertBool ("expected silence for " ++ v ++ ", got: " ++ err)
                 (not ("warning:" `isInfixOf` err))
  ]

rounded :: String -> TestTree
rounded v = testGroup (v ++ " rounds, and compiles (D116)")
  [ accepts "compiles" (lit v)
  , testCase "and says it rounded" $ do
      err <- typeCheckStderr (T.unlines (lit v))
      assertBool ("expected a rounding warning for " ++ v ++ ", got: " ++ err)
                 ("warning:" `isInfixOf` err && ("literal " ++ v) `isInfixOf` err)
  ]

floatTests :: TestTree
floatTests = testGroup "Float literals"
  [ exactOneDigit
  , exactTwoDigit
  , roundedOneDigit
  , roundedTwoDigit
  , negatedLiterals
  , edgeCases
  ]

------------------------------------------------------------------------
-- EXACT — dyadic, and exact at four significand bits
--
-- `k.0` has significand `2k`; `k.5` has `2k+1`. Both stay within four bits
-- for k <= 7, so every value here survives an 8-bit format. The significand is
-- measured UNNORMALISED — `k.0` has significand `2k`, not `k` — so the bounds
-- are computed on what the frontend actually produces.
------------------------------------------------------------------------

exactOneDigit :: TestTree
exactOneDigit = testGroup "exact, one fraction digit"
  ([ exact (show k ++ ".0") | k <- [0 .. 7 :: Int] ] ++
   [ exact (show k ++ ".5") | k <- [0 .. 7 :: Int] ])

-- Two digits scale the significand by four, so the same four-bit budget
-- allows k <= 3: `k.00` is `4k`, `k.25` is `4k+1`, `k.50` is `4k+2`,
-- `k.75` is `4k+3`.
exactTwoDigit :: TestTree
exactTwoDigit = testGroup "exact, two fraction digits"
  ([ exact (show k ++ ".00") | k <- [0 .. 3 :: Int] ] ++
   [ exact (show k ++ ".25") | k <- [0 .. 3 :: Int] ] ++
   [ exact (show k ++ ".50") | k <- [0 .. 3 :: Int] ] ++
   [ exact (show k ++ ".75") | k <- [0 .. 3 :: Int] ])

------------------------------------------------------------------------
-- ROUNDED — not dyadic at ANY width, and accepted anyway
--
-- `i.f` with `l` fraction digits is dyadic exactly when `5 ^ l` divides
-- `i * 10 ^ l + f`. For one digit that means the digit is 0 or 5; for two, the
-- pair is 00/25/50/75. Everything else has a factor of 5 left in its
-- denominator and no binary format of any width can hold it — which is the
-- point: these are the literals D116 stopped refusing.
------------------------------------------------------------------------

roundedOneDigit :: TestTree
roundedOneDigit = testGroup "rounded, one fraction digit"
  [ rounded (show k ++ "." ++ show d)
  | k <- [0 .. 7 :: Int], d <- [1, 2, 3, 4, 6, 7, 8, 9 :: Int] ]

roundedTwoDigit :: TestTree
roundedTwoDigit = testGroup "rounded, two fraction digits"
  [ rounded (show k ++ "." ++ dd)
  | k <- [0 .. 3 :: Int]
  , dd <- ["01","10","11","20","22","30","33","40","44","60","70","80","90","99"] ]

------------------------------------------------------------------------
-- NEGATED literals (plan 0.73 F3, D124)
--
-- `-3.14` was a TYPE ERROR — not a rejection on representability grounds like
-- the group above, but a plain `TypeMismatch Int Float`: `t-neg`'s premise is
-- at `Int` and `RFloat` infers only at `Float`, so no derivation existed. It
-- is now ONE literal whose payload is `negate (decimalOf i f l)`.
--
-- Both halves are here on purpose: an EXACT negative exercises only the sign
-- bit, while a ROUNDED one puts round-to-nearest-even on a negative
-- significand.
------------------------------------------------------------------------

negatedLiterals :: TestTree
negatedLiterals = testGroup "negated"
  ([ accepts ("-" ++ v ++ " is exact")   (negLit v) | v <- ["0.5","1.5","2.75","3.0","0.0"] ] ++
   [ accepts ("-" ++ v ++ " rounds")     (negLit v) | v <- ["0.1","3.14","0.3","1.9"] ])

------------------------------------------------------------------------
-- The named cases the flip is about
------------------------------------------------------------------------

edgeCases :: TestTree
edgeCases = testGroup "named cases"
  [ -- The three plan 0.71 called out as errors. All three compile now, and
    -- that is D116: the literal is a decimal and the target rounds it.
    accepts "0.1 rounds to the nearest double instead of failing" (lit "0.1")
  , accepts "0.2 likewise"                                        (lit "0.2")
  , accepts "3.14 is writable as a literal"                       (lit "3.14")
    -- …and the values that were exact all along, so the flip is not "accept
    -- everything because the check was deleted" — the exact ones still are.
  , accepts "0.5 = 1/2"    (lit "0.5")
  , accepts "1.5 = 3/2"    (lit "1.5")
  , accepts "2.75 = 11/4"  (lit "2.75")
  , accepts "0.0 is zero"  (lit "0.0")
    -- The first integer binary32 cannot hold. Exact at binary64, rounded at
    -- binary32 — one literal, two targets, and D116 is what lets it compile
    -- for both rather than neither.
  , accepts "16777217.0 is exact at binary64 and rounds at binary32"
      (lit "16777217.0")
  ]
