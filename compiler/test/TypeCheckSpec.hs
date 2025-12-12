module TypeCheckSpec (typeCheckTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Once.Parser (parseModule)
import Once.Syntax (Expr (..))
import Once.Type (Type (..))  -- includes TEff for D032
import Once.TypeCheck (inferType, checkModule, emptyContext, TypeError)

import qualified Data.Text as T

typeCheckTests :: TestTree
typeCheckTests = testGroup "TypeCheck"
  [ testGroup "Generator types"
      [ testCase "fst : A * B -> A" $ do
          case inferExpr (EVar "fst") of
            Right (TArrow (TProduct _ _) _) -> pure ()
            other -> assertFailure $ "Expected A * B -> A, got: " ++ show other

      , testCase "snd : A * B -> B" $ do
          case inferExpr (EVar "snd") of
            Right (TArrow (TProduct _ _) _) -> pure ()
            other -> assertFailure $ "Expected A * B -> B, got: " ++ show other

      , testCase "pair : (C -> A) -> (C -> B) -> C -> A * B" $ do
          case inferExpr (EVar "pair") of
            Right (TArrow (TArrow _ _) (TArrow (TArrow _ _) (TArrow _ (TProduct _ _)))) -> pure ()
            other -> assertFailure $ "Expected pair type, got: " ++ show other

      , testCase "id : A -> A" $ do
          case inferExpr (EVar "id") of
            Right (TArrow a b) | a == b -> pure ()
            other -> assertFailure $ "Expected A -> A, got: " ++ show other
      ]

  , testGroup "Application"
      [ testCase "pair snd : (C -> B) -> C -> B * A" $ do
          let expr = EApp (EVar "pair") (EVar "snd")
          case inferExpr expr of
            Right (TArrow _ (TArrow _ (TProduct _ _))) -> pure ()
            other -> assertFailure $ "Expected function returning product, got: " ++ show other

      , testCase "pair snd fst : C -> B * A (where C = A * B)" $ do
          let expr = EApp (EApp (EVar "pair") (EVar "snd")) (EVar "fst")
          case inferExpr expr of
            Right (TArrow (TProduct _ _) (TProduct _ _)) -> pure ()
            other -> assertFailure $ "Expected A * B -> B * A, got: " ++ show other
      ]

  , testGroup "Module type checking"
      [ testCase "swap.once type checks" $ do
          let input = T.unlines
                [ "swap : A * B -> B * A"
                , "swap = pair snd fst"
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right m -> case checkModule m of
              Right () -> pure ()
              Left err -> assertFailure $ "Type error: " ++ show err

      , testCase "wrong type signature fails" $ do
          let input = T.unlines
                [ "swap : A -> B"  -- wrong type!
                , "swap = pair snd fst"
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right m -> case checkModule m of
              Right () -> assertFailure "Should have failed type check"
              Left _ -> pure ()  -- expected failure
      ]

  , testGroup "Let bindings"
      [ testCase "let x = id in x : A -> A" $ do
          let expr = ELet "x" (EVar "id") (EVar "x")
          case inferExpr expr of
            Right (TArrow a b) | a == b -> pure ()
            other -> assertFailure $ "Expected A -> A, got: " ++ show other

      , testCase "let with string literal" $ do
          let expr = ELet "msg" (EStringLit "hello") (EVar "msg")
          case inferExpr expr of
            Right (TString _) -> pure ()
            other -> assertFailure $ "Expected String, got: " ++ show other

      , testCase "nested let bindings" $ do
          let expr = ELet "x" (EVar "fst")
                          (ELet "y" (EVar "snd") (EVar "x"))
          case inferExpr expr of
            Right (TArrow (TProduct _ _) _) -> pure ()
            other -> assertFailure $ "Expected product projection type, got: " ++ show other

      , testCase "module with let binding type checks" $ do
          let input = T.unlines
                [ "test : Unit -> Unit"
                , "test = let x = terminal in x"
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right m -> case checkModule m of
              Right () -> pure ()
              Left err -> assertFailure $ "Type error: " ++ show err
      ]

  -- D032: Arrow-based effect system tests
  , testGroup "Effect types (D032)"
      [ testCase "arr : (A -> B) -> Eff A B" $ do
          case inferExpr (EVar "arr") of
            Right (TArrow (TArrow a1 b1) (TEff a2 b2))
              | a1 == a2 && b1 == b2 -> pure ()
            other -> assertFailure $ "Expected (A -> B) -> Eff A B, got: " ++ show other

      , testCase "Eff does NOT unify with Arrow" $ do
          -- A function declared as Eff should not type-check when pure is expected
          let input = T.unlines
                [ "effectful : Eff Unit Unit"
                , "effectful = terminal"  -- terminal : A -> Unit is pure
                , "usePure : (Unit -> Unit) -> Unit"
                , "usePure = compose terminal id"
                , "test : Unit -> Unit"
                , "test = usePure effectful"  -- Error: passing Eff where pure expected
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right m -> case checkModule m of
              Right () -> assertFailure "Should have failed: Eff should not unify with Arrow"
              Left _ -> pure ()  -- expected failure

      , testCase "main : Eff Unit Unit is valid" $ do
          let input = T.unlines
                [ "main : Eff Unit Unit"
                , "main = arr terminal"
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right m -> case checkModule m of
              Right () -> pure ()
              Left err -> assertFailure $ "Type error: " ++ show err

      , testCase "arr lifts pure to effectful" $ do
          let input = T.unlines
                [ "pureSwap : A * B -> B * A"
                , "pureSwap = pair snd fst"
                , "effSwap : Eff (A * B) (B * A)"
                , "effSwap = arr pureSwap"
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right m -> case checkModule m of
              Right () -> pure ()
              Left err -> assertFailure $ "Type error: " ++ show err
      ]

  , testGroup "IO sugar (D032)"
      [ testCase "IO A parses to Eff Unit A" $ do
          let input = T.unlines
                [ "action : IO Unit"
                , "action = arr terminal"
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right m -> case checkModule m of
              Right () -> pure ()
              Left err -> assertFailure $ "Type error: " ++ show err

      , testCase "IO Unit unifies with Eff Unit Unit" $ do
          -- These two type signatures should be equivalent
          let input = T.unlines
                [ "main : IO Unit"
                , "main = arr terminal"
                , "alias : Eff Unit Unit"
                , "alias = main"  -- Should work: IO Unit = Eff Unit Unit
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right m -> case checkModule m of
              Right () -> pure ()
              Left err -> assertFailure $ "Type error: " ++ show err
      ]

  , testGroup "No implicit lifting (D032)"
      [ testCase "pure function cannot masquerade as effectful" $ do
          -- This was the bug: terminal (pure) could be used where Eff expected
          let input = T.unlines
                [ "main : Eff Unit Unit"
                , "main = terminal"  -- Error: terminal is pure, not effectful
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right m -> case checkModule m of
              Right () -> assertFailure "Should have failed: pure cannot satisfy Eff"
              Left _ -> pure ()  -- expected failure

      , testCase "must use arr to lift pure to effectful" $ do
          let input = T.unlines
                [ "main : Eff Unit Unit"
                , "main = arr terminal"  -- Correct: use arr to lift
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right m -> case checkModule m of
              Right () -> pure ()
              Left err -> assertFailure $ "Type error: " ++ show err
      ]
  ]

-- Helper to infer type of an expression
inferExpr :: Expr -> Either TypeError Type
inferExpr expr = case inferType emptyContext expr 0 of
  Right (ty, _, _) -> Right ty
  Left err -> Left err
