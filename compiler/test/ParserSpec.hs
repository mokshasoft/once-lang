module ParserSpec (parserTests) where

import qualified Data.Text as T
import Test.Tasty
import Test.Tasty.HUnit

import Once.Parser (parseModule)
import Once.Syntax
import Once.Type (Encoding (..))

parserTests :: TestTree
parserTests = testGroup "Parser"
  [ importParserTests
  , testGroup "Types"
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

      , testCase "Buffer type" $
          parseType' "Buffer" @?= Right STBuffer

      , testCase "String type (default Utf8)" $
          parseType' "String" @?= Right (STString Utf8)

      , testCase "String Utf8" $
          parseType' "String Utf8" @?= Right (STString Utf8)

      , testCase "String Ascii" $
          parseType' "String Ascii" @?= Right (STString Ascii)

      , testCase "String Utf16" $
          parseType' "String Utf16" @?= Right (STString Utf16)

      , testCase "puts signature" $
          parseType' "String Utf8 -> Unit" @?=
            Right (STArrow (STString Utf8) STUnit)
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

      , testCase "string literal" $
          parseExpr' "\"hello\"" @?= Right (EStringLit "hello")

      , testCase "string literal with escape" $
          parseExpr' "\"hello\\nworld\"" @?= Right (EStringLit "hello\nworld")

      , testCase "function applied to string literal" $
          parseExpr' "puts \"hello\"" @?=
            Right (EApp (EVar "puts") (EStringLit "hello"))

      , testCase "composition with ." $
          parseExpr' "f . g" @?=
            Right (EApp (EApp (EVar "compose") (EVar "f")) (EVar "g"))

      , testCase "composition is right-associative" $
          parseExpr' "f . g . h" @?=
            Right (EApp (EApp (EVar "compose") (EVar "f"))
                       (EApp (EApp (EVar "compose") (EVar "g")) (EVar "h")))

      , testCase "application binds tighter than composition" $
          parseExpr' "f x . g y" @?=
            Right (EApp (EApp (EVar "compose") (EApp (EVar "f") (EVar "x")))
                       (EApp (EVar "g") (EVar "y")))
      ]

  , testGroup "Declarations"
      [ testCase "type signature" $
          parseDecl' "swap : A * B -> B * A" @?=
            Right (TypeSig "swap"
                    (STArrow (STProduct (STVar "A") (STVar "B"))
                            (STProduct (STVar "B") (STVar "A"))))

      , testCase "function definition" $
          parseDecl' "swap = pair snd fst" @?=
            Right (FunDef "swap" Nothing
                    (EApp (EApp (EVar "pair") (EVar "snd")) (EVar "fst")))

      , testCase "function definition with @heap" $
          parseDecl' "concat @heap = pair snd fst" @?=
            Right (FunDef "concat" (Just AllocHeap)
                    (EApp (EApp (EVar "pair") (EVar "snd")) (EVar "fst")))

      , testCase "function definition with @stack" $
          parseDecl' "f @stack = id" @?=
            Right (FunDef "f" (Just AllocStack) (EVar "id"))
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
            Right (Module _ decls) -> do
              length decls @?= 2
              case decls of
                [TypeSig name1 _, FunDef name2 _ _] -> do
                  name1 @?= "swap"
                  name2 @?= "swap"
                _ -> assertFailure "Expected type sig and fun def"
      ]
  ]

-- -----------------------------------------------------------------------------
-- Import Tests
-- -----------------------------------------------------------------------------

importParserTests :: TestTree
importParserTests = testGroup "imports"
  [ testCase "simple import" $ do
      let input = "import Canonical.Product"
      case parseModule input of
        Left err -> assertFailure $ "Parse error: " ++ show err
        Right (Module [Import modPath Nothing] []) -> do
          modPath @?= ["Canonical", "Product"]
        Right other -> assertFailure $ "Unexpected: " ++ show other

  , testCase "aliased import" $ do
      let input = "import Canonical.Product as P"
      case parseModule input of
        Left err -> assertFailure $ "Parse error: " ++ show err
        Right (Module [Import modPath (Just alias)] []) -> do
          modPath @?= ["Canonical", "Product"]
          alias @?= "P"
        Right other -> assertFailure $ "Unexpected: " ++ show other

  , testCase "multiple imports" $ do
      let input = T.unlines
            [ "import Canonical.Product"
            , "import Canonical.Coproduct as C"
            , ""
            , "swap : A * B -> B * A"
            , "swap = pair snd fst"
            ]
      case parseModule input of
        Left err -> assertFailure $ "Parse error: " ++ show err
        Right (Module imports decls) -> do
          length imports @?= 2
          length decls @?= 2
        Right other -> assertFailure $ "Unexpected: " ++ show other

  , testCase "single-component module path" $ do
      let input = "import Prelude"
      case parseModule input of
        Left err -> assertFailure $ "Parse error: " ++ show err
        Right (Module [Import ["Prelude"] Nothing] []) -> pure ()
        Right other -> assertFailure $ "Unexpected: " ++ show other

  , testCase "qualified access (name@Module)" $ do
      let input = "f = swap@Canonical.Product"
      case parseModule input of
        Left err -> assertFailure $ "Parse error: " ++ show err
        Right (Module _ [FunDef _ _ (EQualified "swap" ["Canonical", "Product"])]) -> pure ()
        Right other -> assertFailure $ "Unexpected: " ++ show other

  , testCase "qualified access in application" $ do
      let input = "f = swap@Product x"
      case parseModule input of
        Left err -> assertFailure $ "Parse error: " ++ show err
        Right (Module _ [FunDef _ _ (EApp (EQualified "swap" ["Product"]) (EVar "x"))]) -> pure ()
        Right other -> assertFailure $ "Unexpected: " ++ show other
  ]

-- Helper to parse a single type from a type signature
parseType' :: T.Text -> Either String SType
parseType' input = case parseModule ("x : " <> input) of
  Left err -> Left (show err)
  Right (Module _ [TypeSig _ ty]) -> Right ty
  Right _ -> Left "Unexpected parse result"

-- Helper to parse a single expression from a function definition
parseExpr' :: T.Text -> Either String Expr
parseExpr' input = case parseModule ("x = " <> input) of
  Left err -> Left (show err)
  Right (Module _ [FunDef _ _ e]) -> Right e
  Right _ -> Left "Unexpected parse result"

-- Helper to parse a single declaration
parseDecl' :: T.Text -> Either String Decl
parseDecl' input = case parseModule input of
  Left err -> Left (show err)
  Right (Module _ [d]) -> Right d
  Right (Module _ ds) -> Left $ "Expected 1 decl, got " ++ show (length ds)
