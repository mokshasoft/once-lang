-- | Tests for the arithmetic compiler (OCP-0001)
--
-- Note: Many tests were removed when transitioning from Haskell ArithIR
-- to MAlonzo-extracted types. The native backend tests now use the
-- MAlonzo modules directly.
module Arith.Spec (arithTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Set as Set

import MAlonzo.RTE (coe)
import Once.Arith.Recognize
import Once.Arith.CodeGen.C
import Once.IR (IR (..))
import Once.Type (Type (..))
import Once.Syntax (Expr (..))
import Once.Elaborate (elaborateExpr)
import qualified MAlonzo.Code.Once.Arith.IR as MA
import qualified MAlonzo.Code.Once.Arith.Type as MT

arithTests :: TestTree
arithTests = testGroup "Arithmetic Compiler (OCP-0001)"
  [ testGroup "NumType"
      [ testCase "bitwidth I8 = 8" $
          MT.d_bitwidth_20 MT.C_I8_8 @?= 8
      , testCase "bitwidth I64 = 64" $
          MT.d_bitwidth_20 MT.C_I64_14 @?= 64
      , testCase "bitwidth F64 = 64" $
          MT.d_bitwidth_20 MT.C_F64_18 @?= 64
      ]
  , testGroup "IR Recognition"
      [ testCase "recognize Id TInt as input variable" $ do
          let result = recognizeArith (Id TInt)
          case result of
            Just (_, MA.C_Var_84 "_input" _) -> return ()
            _ -> assertFailure "Expected Var _input"
      , testCase "recognize Id TFloat as input variable" $ do
          let result = recognizeArith (Id TFloat)
          case result of
            Just (_, MA.C_Var_84 "_input" _) -> return ()
            _ -> assertFailure "Expected Var _input"
      , testCase "recognize integer literal" $ do
          let result = recognizeArith (Prim "__int_42" TUnit TInt)
          case result of
            Just (MT.C_I64_14, MA.C_Lit_76 _) -> return ()
            _ -> assertFailure "Expected Lit 42"
      , testCase "reject Case (branching)" $
          case recognizeArith (Case (Id TInt) (Id TInt)) of
            Nothing -> return ()
            Just _ -> assertFailure "Expected Nothing for Case"
      , testCase "reject Curry (closures)" $
          case recognizeArith (Curry "_" (Id TInt)) of
            Nothing -> return ()
            Just _ -> assertFailure "Expected Nothing for Curry"
      , testCase "isArithPrim __add_i64" $
          isArithPrim "__add_i64" @?= True
      , testCase "isArithPrim __mul_f64" $
          isArithPrim "__mul_f64" @?= True
      , testCase "isArithPrim unknown" $
          isArithPrim "__print" @?= False
      , testCase "isArithType TInt" $
          isArithType TInt @?= True
      , testCase "isArithType TFloat" $
          isArithType TFloat @?= True
      , testCase "isArithType TUnit" $
          isArithType TUnit @?= False
      ]
  , testGroup "C code generation"
      [ testCase "literal int" $
          arithToC MT.C_I64_14 (MA.C_Lit_76 (coe (42 :: Integer))) @?= "42"
      , testCase "negative literal" $
          arithToC MT.C_I64_14 (MA.C_Lit_76 (coe ((-5) :: Integer))) @?= "(-5)"
      , testCase "literal float" $
          arithToC MT.C_F64_18 (MA.C_Lit_76 (coe (3.14 :: Double))) @?= "3.14"
      , testCase "variable" $
          arithToC MT.C_I64_14 (MA.C_Var_84 "x" MA.C_here_40) @?= "x"
      , testCase "addition" $ do
          let x = MA.C_Var_84 "x" MA.C_here_40
              y = MA.C_Var_84 "y" MA.C_here_40
              add = MA.C_Add_92 MA.d_'8709'_20 MA.d_'8709'_20 x y
          arithToC MT.C_I64_14 add @?= "(x + y)"
      , testCase "subtraction" $ do
          let a = MA.C_Var_84 "a" MA.C_here_40
              one = MA.C_Lit_76 (coe (1 :: Integer))
              sub = MA.C_Sub_100 MA.d_'8709'_20 MA.d_'8709'_20 a one
          arithToC MT.C_I32_12 sub @?= "(a - 1)"
      , testCase "multiplication" $ do
          let x = MA.C_Var_84 "x" MA.C_here_40
              y = MA.C_Var_84 "y" MA.C_here_40
              mul = MA.C_Mul_108 MA.d_'8709'_20 MA.d_'8709'_20 x y
          arithToC MT.C_I64_14 mul @?= "(x * y)"
      , testCase "negation" $ do
          let x = MA.C_Var_84 "x" MA.C_here_40
              neg = MA.C_Neg_130 x
          arithToC MT.C_I64_14 neg @?= "(-x)"
      , testCase "comparison lt" $ do
          let x = MA.C_Var_84 "x" MA.C_here_40
              y = MA.C_Var_84 "y" MA.C_here_40
              cmp = MA.C_Cmp_138 MA.d_'8709'_20 MA.d_'8709'_20 MA.C_CmpLt_60 x y
          arithToC MT.C_I32_12 cmp @?= "(x < y)"
      , testCase "comparison eq" $ do
          let a = MA.C_Var_84 "a" MA.C_here_40
              zero = MA.C_Lit_76 (coe (0 :: Integer))
              cmp = MA.C_Cmp_138 MA.d_'8709'_20 MA.d_'8709'_20 MA.C_CmpEq_68 a zero
          arithToC MT.C_I64_14 cmp @?= "(a == 0)"
      ]
  , testGroup "NumType to C"
      [ testCase "I8 -> int8_t" $
          numTypeToC MT.C_I8_8 @?= "int8_t"
      , testCase "I64 -> int64_t" $
          numTypeToC MT.C_I64_14 @?= "int64_t"
      , testCase "F32 -> float" $
          numTypeToC MT.C_F32_16 @?= "float"
      , testCase "F64 -> double" $
          numTypeToC MT.C_F64_18 @?= "double"
      ]
  , testGroup "Sugar-level recognition"
      [ testCase "add_i64 (3, 5) elaborates to Arith" $
          let expr = EApp (EVar "add_i64") (EPair (EInt 3) (EInt 5))
          in case elaborateExpr expr of
               Right (Arith _ _) -> return ()
               Right _ -> assertFailure "Expected Arith"
               Left err -> assertFailure $ "Elaboration failed: " ++ show err
      , testCase "mul_i64 (4, 7) elaborates to Arith" $
          let expr = EApp (EVar "mul_i64") (EPair (EInt 4) (EInt 7))
          in case elaborateExpr expr of
               Right (Arith _ _) -> return ()
               Right _ -> assertFailure "Expected Arith"
               Left err -> assertFailure $ "Elaboration failed: " ++ show err
      , testCase "neg_i64 42 elaborates to Arith" $
          let expr = EApp (EVar "neg_i64") (EInt 42)
          in case elaborateExpr expr of
               Right (Arith _ _) -> return ()
               Right _ -> assertFailure "Expected Arith"
               Left err -> assertFailure $ "Elaboration failed: " ++ show err
      , testCase "non-arithmetic function falls back to Compose" $
          let expr = EApp (EVar "my_func") (EInt 42)
          in case elaborateExpr expr of
               Right (Compose (Var "my_func") _) -> return ()
               Right _ -> assertFailure "Expected Compose"
               Left err -> assertFailure $ "Elaboration failed: " ++ show err
      ]
  ]
