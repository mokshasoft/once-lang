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
import Rejection (assertRejects)

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
  , syntaxDirectedTests
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
  , accepts "inl"      [ "f : Int -> (Int + Void)", "f = inl" ]
  , accepts "inr"      [ "f : Int -> (Void + Int)", "f = inr" ]
  , accepts "case"     [ "f : (Int + Int) -> Int", "f = case id id" ]
  , accepts "initial"  [ "f : Void -> Void", "f = initial" ]
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
-- D323: without a signature, a definition has the type its body synthesizes.
-- A body that only checks (a bare polymorphic builtin, a composition, a
-- lambda) has no type of its own and needs a signature.
------------------------------------------------------------------------

inferenceLimitTests :: TestTree
inferenceLimitTests = testGroup "no signature: the synthesized type (D323)"
  [ rejects "bare `id` needs a signature" "The body has no type of its own"                   [ "f = id" ]
  , rejects "bare `snd` needs a signature" "The body has no type of its own"                  [ "f = snd" ]
  , rejects "a bare `compose` chain needs a signature" "The body has no type of its own"      [ "f = compose id id" ]
  , rejects "`pair id id` needs a signature" "The body has no type of its own"                [ "f = pair id id" ]
  , rejects "a lambda needs a signature" "The body has no type of its own (Lambda without type annotation"                    [ "f x = x + 1" ]
  , accepts "an applied generator synthesizes"              [ "f = id 7" ]
  , accepts "with a signature, a lambda is accepted"        [ "f : Int -> Int", "f x = x + 1" ]
  ]

------------------------------------------------------------------------
-- Plan 0.151: one rule per form. What the table-driven rules accept that the
-- per-generator rules did not, and the two texts they reject.
------------------------------------------------------------------------

syntaxDirectedTests :: TestTree
syntaxDirectedTests = testGroup "plan 0.151: one rule per form"
  [ accepts "bare `apply` is a morphism (c-map)"
      [ "f : ((Int -> Int) * Int) -> Int", "f = apply" ]
  , accepts "bare `apply` checked at grade eff (c-map, every grade)"
      [ "useE : Eff ((Int -> Int) * Int) Int -> Eff ((Int -> Int) * Int) Int"
      , "useE k = k"
      , "f : Eff ((Int -> Int) * Int) Int"
      , "f = useE apply"
      ]
  , accepts "bare `apply` on an effectful arrow: its codomain is the suspension"
      [ "f : ((Act Int Unit) * Int) -> Act Unit Unit", "f = apply" ]
  , accepts "`apply` from a given domain (d-map)"
      [ "f : ((Int -> Int) * Int) -> Int", "f = (\\y -> y * 2) . apply" ]
  , accepts "bare `In` is a morphism (c-map)"
      [ "f : (Unit + Int * Mu (K Unit + K Int * Id)) -> Mu (K Unit + K Int * Id)", "f = In" ]
  , accepts "bare `In` checked at grade act (c-map, every grade)"
      [ "useA : Act (Unit + Int * Mu (K Unit + K Int * Id)) (Mu (K Unit + K Int * Id)) -> Act (Unit + Int * Mu (K Unit + K Int * Id)) (Mu (K Unit + K Int * Id))"
      , "useA k = k"
      , "f : Act (Unit + Int * Mu (K Unit + K Int * Id)) (Mu (K Unit + K Int * Id))"
      , "f = useA In"
      ]
  , accepts "bare `Out` is a morphism (c-map)"
      [ "f : Nu (K Int * Id) -> Int * Nu (K Int * Id)", "f = Out" ]
  , accepts "`Out` from a given domain (d-map)"
      [ "f : Nu (K Int * Id) -> Int", "f = fst . Out" ]
  , accepts "`initial e` synthesizes `Void` (s-app-spine)"
      [ "f : Void -> Void", "f v = let y = initial v in y" ]
  , accepts "checked `id e` checks `e` (c-map-app)"
      [ "pick : (Int + Unit) -> Int", "pick = case (\\x -> x) (\\_ -> 0)", "r = pick (id (inl 5))" ]
  , accepts "domain-given `cata` with a pure algebra in an effectful fold (d-cata)"
      [ "import I.Test.Emit as E"
      , "alg : (Unit + Int * Int) -> Int"
      , "alg = case (\\_ -> 0) (\\p -> fst p + snd p)"
      , "f : Act (Mu (K Unit + K Int * Id)) Unit"
      , "f = emit@E . cata alg"
      ]
  , accepts "domain-given `cata` with an algebra on a larger domain (d-cata)"
      [ "alg : (Unit + Int) -> Int"
      , "alg = case (\\_ -> 3) (\\x -> x)"
      , "f : Mu (K Unit + K Void) -> Int"
      , "f = (\\x -> x + 1) . cata alg"
      ]
  , rejects "`h . case f1 g1` whose branches have no join (c-compose-g, d-case)" "Type mismatch"
      composeCaseNoJoin
  , accepts "... and the same text with `case f1 g1` annotated"
      (init composeCaseNoJoin ++ [ "r = h . (case f1 g1 : (Unit + Unit) -> (Int + Void) -> Int)" ])
  , rejects "`x@Generators`: a generator is not in a module namespace" "Generators"
      [ "f : Int -> Int", "f = id@Generators" ]
  ]
  where
    composeCaseNoJoin =
      [ "f1 : Unit -> (Int + Void) -> Int"
      , "f1 _ = case (\\x -> x) initial"
      , "g1 : Unit -> (Int + Int) -> Int"
      , "g1 _ = case (\\x -> x) (\\y -> y)"
      , "h : ((Int + Void) -> Int) -> Int"
      , "h k = k (inl 7)"
      , "r : (Unit + Unit) -> Int"
      , "r = h . case f1 g1"
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

-- | Assert that a program is REJECTED by `once check`, with an error that
-- mentions `reason` (D368: a rejection names its reason).
rejects :: HasCallStack => TestName -> String -> [T.Text] -> TestTree
rejects name reason sourceLines = testCase name $ do
  result <- typeCheckSource (T.unlines sourceLines)
  assertRejects name reason result

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

