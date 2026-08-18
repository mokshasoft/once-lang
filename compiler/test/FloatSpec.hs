-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Float literal tests (plan 0.71 F7).
--
-- THE RULE UNDER TEST: a float literal is accepted only if its value is
-- EXACTLY representable at every supported target format; otherwise it is a
-- compile-time error. `0.1` does not become the nearest double — it fails to
-- compile.
--
-- NO INTERPRETATION IS NEEDED, and that is not an accident. A literal lowers
-- to `const fits-float d`, i.e. an immediate load; SigOps like `fadd` and
-- `floatToInt` are what need `Strata/Interpretations/Math/*`, and this plan
-- deliberately does not touch them. (x86-32 has no `Math` implementation for
-- `Int` EITHER — that gap is target-wide and pre-existing, not float-specific.)
--
-- EVERY ACCEPTED VALUE HERE IS EXACT AT FOUR SIGNIFICAND BITS, which is what
-- an 8-bit float format would offer. The suite therefore stays valid if a
-- narrow target ever lands, instead of having to be rewritten. Note the
-- significand is measured UNNORMALISED — `k.0` has significand `2k`, not `k` —
-- so the bounds below are computed on what the frontend actually produces.
--
-- Run with: cabal test --test-option='-p "/Float/"'

module FloatSpec (floatTests) where

import Test.Tasty
import qualified Data.Text as T

import TypeErrorSpec (accepts, rejects)

-- | A one-line program binding a float literal at type `Float`.
lit :: String -> [T.Text]
lit v = [ "x : Float", T.pack ("x = " ++ v) ]

acc :: String -> TestTree
acc v = accepts (v ++ " is exact") (lit v)

rej :: String -> TestTree
rej v = rejects (v ++ " is not a dyadic rational") (lit v)

floatTests :: TestTree
floatTests = testGroup "Float literals"
  [ acceptedOneDigit
  , acceptedTwoDigit
  , rejectedOneDigit
  , rejectedTwoDigit
  , edgeCases
  ]

------------------------------------------------------------------------
-- ACCEPTED — dyadic, and exact at four significand bits
------------------------------------------------------------------------

-- `k.0` has significand `2k`; `k.5` has `2k+1`. Both stay within four bits
-- for k <= 7, so every value here survives an 8-bit format.
acceptedOneDigit :: TestTree
acceptedOneDigit = testGroup "accepted, one fraction digit"
  ([ acc (show k ++ ".0") | k <- [0 .. 7 :: Int] ] ++
   [ acc (show k ++ ".5") | k <- [0 .. 7 :: Int] ])

-- Two digits scale the significand by four, so the same four-bit budget
-- allows k <= 3: `k.00` is `4k`, `k.25` is `4k+1`, `k.50` is `4k+2`,
-- `k.75` is `4k+3`.
acceptedTwoDigit :: TestTree
acceptedTwoDigit = testGroup "accepted, two fraction digits"
  ([ acc (show k ++ ".00") | k <- [0 .. 3 :: Int] ] ++
   [ acc (show k ++ ".25") | k <- [0 .. 3 :: Int] ] ++
   [ acc (show k ++ ".50") | k <- [0 .. 3 :: Int] ] ++
   [ acc (show k ++ ".75") | k <- [0 .. 3 :: Int] ])

------------------------------------------------------------------------
-- REJECTED — not dyadic at ANY width
--
-- `i.f` with `l` fraction digits is dyadic exactly when `5 ^ l` divides
-- `i * 10 ^ l + f`. For one digit that means the digit is 0 or 5; for two, the
-- pair is 00/25/50/75. Everything else has a factor of 5 left in its
-- denominator and no binary format of any width can hold it.
------------------------------------------------------------------------

rejectedOneDigit :: TestTree
rejectedOneDigit = testGroup "rejected, one fraction digit"
  [ rej (show k ++ "." ++ show d)
  | k <- [0 .. 7 :: Int], d <- [1, 2, 3, 4, 6, 7, 8, 9 :: Int] ]

rejectedTwoDigit :: TestTree
rejectedTwoDigit = testGroup "rejected, two fraction digits"
  [ rej (show k ++ "." ++ dd)
  | k <- [0 .. 3 :: Int]
  , dd <- ["01","10","11","20","22","30","33","40","44","60","70","80","90","99"] ]

------------------------------------------------------------------------
-- The named cases the plan calls out
------------------------------------------------------------------------

edgeCases :: TestTree
edgeCases = testGroup "named cases"
  [ -- The case the whole plan exists to make loud.
    rejects "0.1 is rejected, not rounded to the nearest double" (lit "0.1")
  , rejects "0.2 likewise" (lit "0.2")
  , rejects "3.14 is not writable as a literal" (lit "3.14")
    -- …and the values that are exact, so the rule is not merely "reject
    -- everything with a dot in it".
  , accepts "0.5 = 1/2"    (lit "0.5")
  , accepts "1.5 = 3/2"    (lit "1.5")
  , accepts "2.75 = 11/4"  (lit "2.75")
  , accepts "0.0 is zero"  (lit "0.0")
  ]
