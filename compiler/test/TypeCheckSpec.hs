module TypeCheckSpec (typeCheckTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Once.Parser (parseModule)
import Once.Syntax (Expr (..))
import Once.Type (Type (..))
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
  ]

-- Helper to infer type of an expression
inferExpr :: Expr -> Either TypeError Type
inferExpr expr = case inferType emptyContext expr 0 of
  Right (ty, _, _) -> Right ty
  Left err -> Left err
