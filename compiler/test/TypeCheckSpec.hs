-- | Tests for the Agda-based type checker via CLI integration tests.
-- Tests inter-function calls, the absence of general recursion (D241), and edge cases.
module TypeCheckSpec (typeCheckTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode(..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)

import Backend.Common (runOnce)

typeCheckTests :: TestTree
typeCheckTests = testGroup "Type Checker (Agda)"
  [ interFunctionCallTests
  , recursionTests
  , builtinShadowingTests
  , exFalsoTests
  ]

------------------------------------------------------------------------
-- Inter-function Call Tests
------------------------------------------------------------------------

interFunctionCallTests :: TestTree
interFunctionCallTests = testGroup "Inter-function calls"
  [ testCase "simple function call" $ do
      -- A function can call another function defined earlier. `main` must be
      -- IO Unit (= Eff Unit Unit), so the inter-function call is exercised by
      -- `useHelper` rather than by `main` directly.
      let source = T.unlines
            [ "helper : Int -> Int"
            , "helper x = x"
            , ""
            , "useHelper : Int -> Int"
            , "useHelper x = helper x"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "chained function calls" $ do
      -- Functions can call multiple other functions
      let source = T.unlines
            [ "add1 : Int -> Int"
            , "add1 x = x + 1"
            , ""
            , "double : Int -> Int"
            , "double x = x + x"
            , ""
            , "compute : Int -> Int"
            , "compute x = double (add1 x)"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "function calling function with an argument" $ do
      -- Inter-function call where the caller forwards its argument.
      -- (Avoid the name `apply`, which is a builtin morphism, just like
      -- `fst`/`snd` — a user binding of that name is shadowed by the builtin.)
      let source = T.unlines
            [ "callee : Int -> Int"
            , "callee x = x"
            , ""
            , "caller : Int -> Int"
            , "caller y = callee y"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "constants can be referenced" $ do
      -- Simple Int constants can be referenced by other functions
      let source = T.unlines
            [ "port : Int"
            , "port = 8080"
            , ""
            , "config : Int"
            , "config = port"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "many functions in sequence" $ do
      -- Test with 5+ functions to ensure accumulation works
      let source = T.unlines
            [ "f1 : Int"
            , "f1 = 1"
            , ""
            , "f2 : Int"
            , "f2 = f1"
            , ""
            , "f3 : Int"
            , "f3 = f2"
            , ""
            , "f4 : Int"
            , "f4 = f3"
            , ""
            , "f5 : Int"
            , "f5 = f4"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      result @?= Right ()
  ]

------------------------------------------------------------------------
-- Recursion Tests
------------------------------------------------------------------------

recursionTests :: TestTree
recursionTests = testGroup "No general recursion (D241)"
  -- D241: a definition's body sees only the definitions BEFORE it (the
  -- module is a telescope). Once has structured recursion (cata/ana) and no
  -- general recursion (OCP-0003), so a body naming its own definition is an
  -- unbound name. These were accepted while the body context carried the
  -- definition itself, which the Spec then read as an opaque SigOp.
  [ testCase "self-reference (no args) is rejected" $ do
      let source = T.unlines
            [ "loop : Int"
            , "loop = loop"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      assertBool "a body cannot name its own definition" (isLeft result)

  , testCase "self-call with a parameter is rejected" $ do
      let source = T.unlines
            [ "countdown : Int -> Int"
            , "countdown n = countdown n"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      assertBool "a body cannot call its own definition" (isLeft result)

  , testCase "self-call with multiple parameters is rejected" $ do
      let source = T.unlines
            [ "gcd : Int -> Int -> Int"
            , "gcd a b = gcd b a"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      assertBool "a body cannot call its own definition" (isLeft result)

  , testCase "mutual recursion through the telescope is rejected" $ do
      -- f2 -> p1 -> p3 -> f2: no definition names itself, but the cycle is
      -- general recursion. Each definition must see only the definitions
      -- declared BEFORE it (D241).
      let source = T.unlines
            [ "p1 : a -> a"
            , "p1 = p3"
            , ""
            , "f2 : Int -> Int"
            , "f2 = p1"
            , ""
            , "p3 : a -> a"
            , "p3 = f2"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      assertBool "a telescope cycle is general recursion" (isLeft result)

  , testCase "a definition cannot use a later one" $ do
      let source = T.unlines
            [ "p1 : a -> a"
            , "p1 = p3"
            , ""
            , "p3 : a -> a"
            , "p3 = id"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      assertBool "a forward reference is unbound" (isLeft result)

  , testCase "a later definition may use an earlier one" $ do
      let source = T.unlines
            [ "inc : Int -> Int"
            , "inc n = n + 1"
            , ""
            , "twice : Int -> Int"
            , "twice n = inc (inc n)"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      result @?= Right ()
  ]

------------------------------------------------------------------------
-- Builtin Shadowing Tests
------------------------------------------------------------------------

builtinShadowingTests :: TestTree
builtinShadowingTests = testGroup "Generator names (D136)"
  -- NOTE: a "user-defined 'id' is shadowed by builtin" test was removed here.
  -- It expected `id : Int -> Int; id x = x; test = id 5` to be REJECTED, but
  -- it can't be: whether the builtin `id : α → α` or the user binding is used,
  -- `id 5` is well-typed at `Int`, so no type error is possible. The real
  -- builtin-shadowing behaviour (the builtin wins, breaking calls that don't
  -- match the builtin's type) is covered by the `fst`/`snd` cases below, where
  -- the builtins require a pair argument.
  [ testCase "non-builtin names work fine" $ do
      -- Using a non-builtin name avoids the shadowing issue
      let source = T.unlines
            [ "myId : Int -> Int"
            , "myId x = x"
            , ""
            , "test : Int"
            , "test = myId 5"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "D136: 'fst@this' reaches the user's own definition" $ do
      let source = T.unlines
            [ "fst : Int -> Int"
            , "fst x = x"
            , ""
            , "test : Int"
            , "test = fst@this 5"
            ]
      result <- typeCheckSource source
      -- `this` is the reserved alias for the own module, so this is the
      -- USER's `fst : Int -> Int` and `fst@this 5` is well-typed.
      result @?= Right ()

  , testCase "D136: bare 'fst' is the GENERATOR, not the user's def" $ do
      let source = T.unlines
            [ "fst : Int -> Int"
            , "fst x = x"
            , ""
            , "test : Int"
            , "test = fst 5"
            ]
      result <- typeCheckSource source
      -- Not shadowing: `fst` NAMES the generator (D136), whose type is
      -- (A * B) → A, so an Int argument is a type error. The user's own `fst`
      -- is still reachable — as `fst@this`, tested above.
      assertBool "bare fst must be the generator" (isLeft result)

  , testCase "D136: bare 'snd' is the GENERATOR, not the user's def" $ do
      let source = T.unlines
            [ "snd : Int -> Int"
            , "snd x = x"
            , ""
            , "test : Int"
            , "test = snd 5"
            ]
      result <- typeCheckSource source
      assertBool "bare snd must be the generator" (isLeft result)
  ]

------------------------------------------------------------------------
-- Ex falso is explicit (D251)
------------------------------------------------------------------------

-- D251: the one ex falso is the initial morphism `initial` (`initial v`
-- checks at any type). No other former is Void-sensitive, so a `Void`
-- operand does not make `+`, `fst` or a `case` synthesize `Void`; usage is
-- syntactic, and typing is closed under instantiating a parameter at `Void`.
exFalsoTests :: TestTree
exFalsoTests = testGroup "Ex falso is explicit (D251)"
  [ testCase "initial v checks at any type" $ do
      let source = T.unlines
            [ "absurdInt : Void -> Int"
            , "absurdInt v = initial v"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "a Void left operand does not type an ill-typed binop" $ do
      let source = T.unlines
            [ "bad : Void -> Unit -> Void"
            , "bad v u = v + u"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      assertBool "v + u with u : Unit is ill-typed" (isLeft result)

  , testCase "a Void right operand does not make a binop synthesize Void" $ do
      let source = T.unlines
            [ "bad : Int -> Void -> Void"
            , "bad x v = x + v"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      assertBool "x + v is an Int (Void <: Int), not a Void" (isLeft result)

  , testCase "fst of a Void does not synthesize" $ do
      let source = T.unlines
            [ "bad : Void -> Int"
            , "bad v = fst v"
            , ""
            , "main : IO Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      assertBool "fst needs a product; ex falso is initial v" (isLeft result)
  ]

------------------------------------------------------------------------
-- Test Helpers
------------------------------------------------------------------------

-- | Type check a source string using the CLI 'check' command.
-- Returns Right () on success, Left error message on failure.
typeCheckSource :: T.Text -> IO (Either String ())
typeCheckSource source = withSystemTempFile "test.once" $ \path handle -> do
  TIO.hPutStr handle source
  hClose handle  -- Must close before external process reads
  -- `once check` prints type errors on stdout, so include both streams in the
  -- Left message. runOnce resolves the on-PATH `once` (see once.cabal
  -- build-tool-depends) and only falls back to `cabal run`.
  (exitCode, stdout, stderr) <- runOnce ["check", path]
  case exitCode of
    ExitSuccess -> return (Right ())
    ExitFailure _ -> return (Left (stdout ++ stderr))

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False
