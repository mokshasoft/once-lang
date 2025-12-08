module ParserSpec (parserTests) where

import qualified Data.Text as T
import Test.Tasty
import Test.Tasty.HUnit

import Once.Parser (parseModule)
import Once.Syntax

parserTests :: TestTree
parserTests = testGroup "Parser"
  [ testGroup "Types"
      [ testCase "type variable" $
          parseType' "A" @?= Right (STVar "A")

      , testCase "product type" $
          parseType' "A * B" @?= Right (STProduct (STVar "A") (STVar "B"))

      , testCase "sum type" $
          parseType' "A + B" @?= Right (STSum (STVar "A") (STVar "B"))

      , testCase "function type" $
          parseType' "A -> B" @?= Right (STArrow (STVar "A") (STVar "B"))

      , testCase "product -> sum precedence" $
          parseType' "A * B -> C + D" @?=
            Right (STArrow (STProduct (STVar "A") (STVar "B"))
                          (STSum (STVar "C") (STVar "D")))

      , testCase "swap type: A * B -> B * A" $
          parseType' "A * B -> B * A" @?=
            Right (STArrow (STProduct (STVar "A") (STVar "B"))
                          (STProduct (STVar "B") (STVar "A")))
      ]

  , testGroup "Expressions"
      [ testCase "variable" $
          parseExpr' "x" @?= Right (EVar "x")

      , testCase "application" $
          parseExpr' "f x" @?= Right (EApp (EVar "f") (EVar "x"))

      , testCase "nested application" $
          parseExpr' "f x y" @?= Right (EApp (EApp (EVar "f") (EVar "x")) (EVar "y"))

      , testCase "pair literal" $
          parseExpr' "(x, y)" @?= Right (EPair (EVar "x") (EVar "y"))

      , testCase "fst (generator)" $
          parseExpr' "fst" @?= Right (EVar "fst")

      , testCase "fst applied" $
          parseExpr' "fst x" @?= Right (EApp (EVar "fst") (EVar "x"))

      , testCase "pair snd fst" $
          parseExpr' "pair snd fst" @?=
            Right (EApp (EApp (EVar "pair") (EVar "snd")) (EVar "fst"))
      ]

  , testGroup "Declarations"
      [ testCase "type signature" $
          parseDecl' "swap : A * B -> B * A" @?=
            Right (TypeSig "swap"
                    (STArrow (STProduct (STVar "A") (STVar "B"))
                            (STProduct (STVar "B") (STVar "A"))))

      , testCase "function definition" $
          parseDecl' "swap = pair snd fst" @?=
            Right (FunDef "swap"
                    (EApp (EApp (EVar "pair") (EVar "snd")) (EVar "fst")))
      ]

  , testGroup "swap.once"
      [ testCase "parses swap.once" $ do
          let input = T.unlines
                [ "-- swap.once"
                , "swap : A * B -> B * A"
                , "swap = pair snd fst"
                ]
          case parseModule input of
            Left err -> assertFailure $ "Parse error: " ++ show err
            Right (Module decls) -> do
              length decls @?= 2
              case decls of
                [TypeSig name1 _, FunDef name2 _] -> do
                  name1 @?= "swap"
                  name2 @?= "swap"
                _ -> assertFailure "Expected type sig and fun def"
      ]
  ]

-- Helper to parse a single type from a type signature
parseType' :: T.Text -> Either String SType
parseType' input = case parseModule ("x : " <> input) of
  Left err -> Left (show err)
  Right (Module [TypeSig _ ty]) -> Right ty
  Right _ -> Left "Unexpected parse result"

-- Helper to parse a single expression from a function definition
parseExpr' :: T.Text -> Either String Expr
parseExpr' input = case parseModule ("x = " <> input) of
  Left err -> Left (show err)
  Right (Module [FunDef _ e]) -> Right e
  Right _ -> Left "Unexpected parse result"

-- Helper to parse a single declaration
parseDecl' :: T.Text -> Either String Decl
parseDecl' input = case parseModule input of
  Left err -> Left (show err)
  Right (Module [d]) -> Right d
  Right (Module ds) -> Left $ "Expected 1 decl, got " ++ show (length ds)
