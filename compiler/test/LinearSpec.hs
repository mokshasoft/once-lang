-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | The non-linear warning (plan 0.157 S2, D500, decided by the user): a program
-- that owns a value with cells twice is told where it is copied; a linear one
-- (reads are free: `twice f x = f (f x)` only reads `f`) is told nothing.
-- No warning means `Linear₀`, the premise of `NoCopy`.
module LinearSpec (linearTests) where

import Test.Tasty
import Test.Tasty.HUnit (testCase, assertBool)
import Data.List (isInfixOf)
import qualified Data.Text as T

import TypeErrorSpec (accepts, typeCheckStderr)

list :: [T.Text]
list =
  [ "import I.Linux.Syscalls as S"
  , ""
  , "nil : Mu (K Unit + K Int * Id)"
  , "nil = In (inl unit)"
  , ""
  , "cons : Int -> Mu (K Unit + K Int * Id) -> Mu (K Unit + K Int * Id)"
  , "cons x xs = In (inr (x, xs))"
  , ""
  ]

-- the list owned twice: a pair of it
twiceOwned :: [T.Text]
twiceOwned = list ++
  [ "both : Mu (K Unit + K Int * Id) -> (Mu (K Unit + K Int * Id)) * (Mu (K Unit + K Int * Id))"
  , "both xs = (xs, xs)"
  , ""
  , "main : Act Unit Void"
  , "main = exit@S ((\\p -> 3) (both (cons 1 nil)))"
  ]

-- a closure read twice, owned once: linear
readTwice :: [T.Text]
readTwice =
  [ "import I.Linux.Syscalls as S"
  , ""
  , "twice : (Int -> Int) -> Int -> Int"
  , "twice f x = f (f x)"
  , ""
  , "main : Act Unit Void"
  , "main = exit@S (twice (\\y -> y + 1) 40)"
  ]

linearTests :: TestTree
linearTests = testGroup "Linearity warning (D500)"
  [ accepts "a value owned twice compiles" twiceOwned
  , testCase "and is named: not linear, a copy here" $ do
      err <- typeCheckStderr (T.unlines twiceOwned)
      assertBool ("expected a not-linear warning, got: " ++ err)
                 ("not linear" `isInfixOf` err && "pair" `isInfixOf` err)
  , accepts "a closure read twice compiles" readTwice
  , testCase "and is linear: no warning" $ do
      err <- typeCheckStderr (T.unlines readTwice)
      assertBool ("expected no not-linear warning, got: " ++ err)
                 (not ("not linear" `isInfixOf` err))
  ]
