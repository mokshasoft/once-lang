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
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode(..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)

import Backend.Common (runOnce)
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

-- a branching unfold: observing a layer with two seeds copies the coalgebra (D496, D501)
branching :: [T.Text]
branching =
  [ "import I.Linux.Syscalls as S"
  , ""
  , "tree : Int -> Nu (K Int * (Id * Id))"
  , "tree = ana (\\s -> (s, (s + s, s + s + 1)))"
  , ""
  , "left : Nu (K Int * (Id * Id)) -> Int"
  , "left v = fst (Out (fst (snd (Out v))))"
  , ""
  , "main : Act Unit Void"
  , "main = exit@S (left (tree 1))"
  ]

-- plan 0.157 D6's example: `step p = case (next p) (stop p) (fst p == 0)` is linear (one owning use
-- per path, the arms alternatives, the test a read) — no false "case combinator" or "closure" site
stepLoop :: [T.Text]
stepLoop =
  [ "import I.Linux.Syscalls as S"
  , ""
  , "stop : Int * Mu (K Unit + K Int * Id) -> Unit -> Int + Void"
  , "stop p _ = inl 7"
  , ""
  , "next : Int * Mu (K Unit + K Int * Id) -> Unit -> Void + Int * Mu (K Unit + K Int * Id)"
  , "next p _ = inr (fst p - 1, In (inr (fst p, snd p)))"
  , ""
  , "step : Int * Mu (K Unit + K Int * Id) -> Int + Int * Mu (K Unit + K Int * Id)"
  , "step p = case (next p) (stop p) (fst p == 0)"
  , ""
  , "main : Eff Unit Void"
  , "main = exit@S . (ana step . (\\_ -> (10, In (inl unit))))"
  ]

linearTests :: TestTree
linearTests = testGroup "Linearity warning (D500)"
  [ testCase "the plan's step loop is linear: no warning" $ do
      err <- typeCheckStderr (T.unlines stepLoop)
      assertBool ("expected no not-linear warning, got: " ++ err)
                 (not ("not linear" `isInfixOf` err))
  , testCase "a branching unfold is named: each observation copies its coalgebra" $ do
      err <- typeCheckStderr (T.unlines branching)
      assertBool ("expected a not-linear warning, got: " ++ err)
                 ("not linear" `isInfixOf` err && "unfold whose layer branches" `isInfixOf` err)
  , accepts "a value owned twice compiles" twiceOwned
  , testCase "and is named: not linear, a copy here" $ do
      err <- typeCheckStderr (T.unlines twiceOwned)
      assertBool ("expected a not-linear warning, got: " ++ err)
                 ("not linear" `isInfixOf` err && "pair" `isInfixOf` err)
  , accepts "a closure read twice compiles" readTwice
  , testCase "and is linear: no warning" $ do
      err <- typeCheckStderr (T.unlines readTwice)
      assertBool ("expected no not-linear warning, got: " ++ err)
                 (not ("not linear" `isInfixOf` err))
  , testCase "--require-linear refuses the value owned twice" $ do
      (code, _, err) <- checkRequiring twiceOwned
      assertBool ("expected a refusal, got: " ++ show code ++ " " ++ err)
                 (code /= ExitSuccess && "--require-linear" `isInfixOf` err)
  , testCase "--require-linear accepts the linear program" $ do
      (code, _, err) <- checkRequiring readTwice
      assertBool ("expected acceptance, got: " ++ show code ++ " " ++ err) (code == ExitSuccess)
  ]

-- `once check --require-linear` on a program
checkRequiring :: [T.Text] -> IO (ExitCode, String, String)
checkRequiring source = withSystemTempFile "linear.once" $ \path handle -> do
  TIO.hPutStr handle (T.unlines source)
  hClose handle
  runOnce ["check", "--require-linear", path]
