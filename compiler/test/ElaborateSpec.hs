module ElaborateSpec (elaborateTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Once.Elaborate (elaborate)
import Once.Eval (eval)
import Once.IR (IR (..))
import Once.Parser (parseModule)
import Once.Syntax (Module (..), Decl (..), Expr (..))
import Once.Type (Type (..))
import Once.Value (Value (..))

import qualified Data.Text as T

elaborateTests :: TestTree
elaborateTests = testGroup "Elaborate"
  [ testGroup "Generators"
      [ testCase "fst elaborates to Fst" $
          elaborate (EVar "fst") @?= Right (Fst placeholder placeholder)

      , testCase "snd elaborates to Snd" $
          elaborate (EVar "snd") @?= Right (Snd placeholder placeholder)

      , testCase "id elaborates to Id" $
          elaborate (EVar "id") @?= Right (Id placeholder)
      ]

  , testGroup "Generator applications"
      [ testCase "pair snd fst elaborates to Pair (Snd ..) (Fst ..)" $
          let expr = EApp (EApp (EVar "pair") (EVar "snd")) (EVar "fst")
          in case elaborate expr of
               Right (Pair (Snd _ _) (Fst _ _)) -> pure ()
               other -> assertFailure $ "Expected Pair (Snd ..) (Fst ..), got: " ++ show other
      ]

  , testGroup "swap.once end-to-end"
      [ testCase "parse and elaborate swap" $ do
          let input = T.unlines
                [ "swap : A * B -> B * A"
                , "swap = pair snd fst"
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right (Module _ [_, FunDef _ _ expr]) ->
              case elaborate expr of
                Right (Pair (Snd _ _) (Fst _ _)) -> pure ()
                Right other -> assertFailure $ "Wrong IR: " ++ show other
                Left err -> assertFailure $ "Elaboration error: " ++ show err
            Right other -> assertFailure $ "Unexpected parse: " ++ show other

      , testCase "elaborated swap evaluates correctly" $ do
          let expr = EApp (EApp (EVar "pair") (EVar "snd")) (EVar "fst")
          case elaborate expr of
            Left err -> assertFailure $ "Elaboration error: " ++ show err
            Right ir -> do
              let input = VPair (VLeft VUnit) (VRight VUnit)
              case eval ir input of
                Right (VPair (VRight VUnit) (VLeft VUnit)) -> pure ()
                Right other -> assertFailure $ "Wrong result: " ++ show other
                Left err -> assertFailure $ "Eval error: " ++ show err
      ]

  , testGroup "Let bindings"
      [ testCase "let x = id in x elaborates to Let" $ do
          let expr = ELet "x" (EVar "id") (EVar "x")
          case elaborate expr of
            Right (Let "x" (Id _) (LocalVar "x")) -> pure ()
            Right other -> assertFailure $ "Wrong IR: " ++ show other
            Left err -> assertFailure $ "Elaboration error: " ++ show err

      , testCase "let with string literal" $ do
          let expr = ELet "msg" (EStringLit "hello") (EVar "msg")
          case elaborate expr of
            Right (Let "msg" (StringLit "hello") (LocalVar "msg")) -> pure ()
            Right other -> assertFailure $ "Wrong IR: " ++ show other
            Left err -> assertFailure $ "Elaboration error: " ++ show err

      , testCase "nested let bindings elaborate correctly" $ do
          let expr = ELet "x" (EVar "fst") (ELet "y" (EVar "snd") (EVar "x"))
          case elaborate expr of
            Right (Let "x" (Fst _ _) (Let "y" (Snd _ _) (LocalVar "x"))) -> pure ()
            Right other -> assertFailure $ "Wrong IR: " ++ show other
            Left err -> assertFailure $ "Elaboration error: " ++ show err

      , testCase "let body uses outer variable not inner" $ do
          -- let x = fst in let y = snd in x should reference x, not y
          let expr = ELet "x" (EVar "fst") (ELet "y" (EVar "snd") (EVar "x"))
          case elaborate expr of
            Right (Let "x" _ (Let "y" _ (LocalVar "x"))) -> pure ()
            Right other -> assertFailure $ "Wrong IR: " ++ show other
            Left err -> assertFailure $ "Elaboration error: " ++ show err
      ]

  , testGroup "Lambda elaboration"
      [ testCase "identity lambda elaborates to Curry" $ do
          let expr = ELam "x" (EVar "x")
          case elaborate expr of
            Right (Curry "x" (LocalVar "x")) -> pure ()
            Right other -> assertFailure $ "Wrong IR: " ++ show other
            Left err -> assertFailure $ "Elaboration error: " ++ show err

      , testCase "nested lambda elaborates to nested Curry" $ do
          let expr = ELam "x" (ELam "y" (EVar "x"))
          case elaborate expr of
            Right (Curry "x" (Curry "y" (LocalVar "x"))) -> pure ()
            Right other -> assertFailure $ "Wrong IR: " ++ show other
            Left err -> assertFailure $ "Elaboration error: " ++ show err

      , testCase "lambda with fst in body" $ do
          let expr = ELam "p" (EApp (EVar "fst") (EVar "p"))
          case elaborate expr of
            Right (Curry "p" (Compose (Fst _ _) (LocalVar "p"))) -> pure ()
            Right other -> assertFailure $ "Wrong IR: " ++ show other
            Left err -> assertFailure $ "Elaboration error: " ++ show err
      ]

  , testGroup "Pair literal elaboration"
      [ testCase "pair of variables" $ do
          let expr = ELet "a" (EVar "fst") (ELet "b" (EVar "snd") (EPair (EVar "a") (EVar "b")))
          case elaborate expr of
            Right (Let "a" (Fst _ _) (Let "b" (Snd _ _) (Pair (LocalVar "a") (LocalVar "b")))) -> pure ()
            Right other -> assertFailure $ "Wrong IR: " ++ show other
            Left err -> assertFailure $ "Elaboration error: " ++ show err

      , testCase "pair of integers" $ do
          let expr = EPair (EInt 1) (EInt 2)
          case elaborate expr of
            Right (Pair (Prim "__int_1" _ _) (Prim "__int_2" _ _)) -> pure ()
            Right other -> assertFailure $ "Wrong IR: " ++ show other
            Left err -> assertFailure $ "Elaboration error: " ++ show err

      , testCase "nested pair" $ do
          let expr = EPair (EInt 1) (EPair (EInt 2) (EInt 3))
          case elaborate expr of
            Right (Pair (Prim "__int_1" _ _) (Pair (Prim "__int_2" _ _) (Prim "__int_3" _ _))) -> pure ()
            Right other -> assertFailure $ "Wrong IR: " ++ show other
            Left err -> assertFailure $ "Elaboration error: " ++ show err
      ]
  ]

placeholder :: Type
placeholder = TVar "_"
