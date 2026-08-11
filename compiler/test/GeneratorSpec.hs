-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Positive typing coverage for the categorical generators and for type
-- inference, via `once check`.
--
-- The negative side (mis-typed generators) lives in TypeErrorSpec; this module
-- asserts that each generator type-checks in a VALID position, and that type
-- inference accepts the cases it is meant to. It also wires up several `.once`
-- fixtures that shipped in compiler/test but had lost their driving spec when
-- ElaborateSpec/ModuleSpec were disabled.
module GeneratorSpec (generatorTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode (..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)

import Backend.Common (runOnce)

generatorTests :: TestTree
generatorTests = testGroup "Generators & inference"
  [ generatorTypingTests
  , inferenceTests
  , inferenceLimitTests
  , fixtureTests
  ]

------------------------------------------------------------------------
-- Each of the ~12 generators type-checks in a valid (check-mode) position
------------------------------------------------------------------------

generatorTypingTests :: TestTree
generatorTypingTests = testGroup "generators type-check in check mode"
  [ accepts "id"       [ "f : Int -> Int", "f = id" ]
  , accepts "fst"      [ "f : (Int * Int) -> Int", "f = fst" ]
  , accepts "snd"      [ "f : (Int * Int) -> Int", "f = snd" ]
  , accepts "terminal" [ "f : Int -> Unit", "f = terminal" ]
  , accepts "compose"  [ "f : Int -> Int", "f = compose id id" ]
  , accepts "pair"     [ "f : Int -> (Int * Int)", "f = pair id id" ]
  , accepts "inl"      [ "f : Int -> (Int + Int)", "f = inl" ]
  , accepts "inr"      [ "f : Int -> (Int + Int)", "f = inr" ]
  , accepts "case"     [ "f : (Int + Int) -> Int", "f = case id id" ]
  , accepts "initial"  [ "f : Void -> Int", "f = initial" ]
  , accepts "curry"
      [ "h : (Int * Int) -> Int"
      , "h p = fst p"
      , "g : Int -> Int -> Int"
      , "g = curry h"
      ]
  , accepts "apply (applied to a (function, argument) pair)"
      [ "inc : Int -> Int"
      , "inc x = x"
      , "r : Int"
      , "r = apply (inc, 5)"
      ]
  , accepts "polymorphic id at several monomorphic types"
      [ "u : Unit -> Unit"
      , "u = id"
      , "p : (Int * Int) -> (Int * Int)"
      , "p = id"
      , "s : (Int + Int) -> (Int + Int)"
      , "s = id"
      ]
  ]

------------------------------------------------------------------------
-- Type inference accepts the cases it is meant to
------------------------------------------------------------------------

inferenceTests :: TestTree
inferenceTests = testGroup "type inference"
  [ accepts "literal body without a signature is inferred"
      [ "code = 7" ]
  , accepts "applied builtin without a signature is inferred"
      [ "f : Int -> Int"
      , "f x = id x"
      ]
  , checksFixture "infer-literal" "test/infer-literal.once"
  , checksFixture "infer-applied" "test/infer-applied.once"
  ]

------------------------------------------------------------------------
-- D072: the former "inference limits" are lifted — the principal-type
-- oracle infers a SCHEMA for bare/composed polymorphic builtins and
-- routes the def to the telescope (each use is kernel-checked).
------------------------------------------------------------------------

inferenceLimitTests :: TestTree
inferenceLimitTests = testGroup "inference schemas (D072: bare polymorphic builtins accepted)"
  [ accepts "bare `id` is inferred (schema t0 -> t0)"       [ "f = id" ]
  , accepts "bare `compose` chain is inferred"              [ "f = compose id id" ]
  , accepts "`pair id id` is inferred"                      [ "f = pair id id" ]
  ]

------------------------------------------------------------------------
-- Previously-orphaned fixtures that should type-check
------------------------------------------------------------------------

fixtureTests :: TestTree
fixtureTests = testGroup "orphan fixtures type-check"
  [ checksFixture "builtins-minimal" "test/builtins-minimal.once"
  , checksFixture "id-poly-test"     "test/id-poly-test.once"
  , checksFixture "layer1-swap"      "test/layer1-swap.once"
  ]

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

accepts :: TestName -> [T.Text] -> TestTree
accepts name sourceLines = testCase name $ do
  result <- typeCheckSource (T.unlines sourceLines)
  result @?= Right ()

rejects :: TestName -> [T.Text] -> TestTree
rejects name sourceLines = testCase name $ do
  result <- typeCheckSource (T.unlines sourceLines)
  assertBool ("Should reject: " ++ name) (isLeft result)

checksFixture :: TestName -> FilePath -> TestTree
checksFixture name path = testCase (name ++ " (fixture)") $ do
  result <- typeCheckFile path
  result @?= Right ()

typeCheckSource :: T.Text -> IO (Either String ())
typeCheckSource source = withSystemTempFile "test.once" $ \path handle -> do
  TIO.hPutStr handle source
  hClose handle
  typeCheckFile path

typeCheckFile :: FilePath -> IO (Either String ())
typeCheckFile path = do
  (exitCode, stdout, stderr) <- runOnce ["check", path]
  case exitCode of
    ExitSuccess -> return (Right ())
    ExitFailure _ -> return (Left (stdout ++ stderr))

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False
