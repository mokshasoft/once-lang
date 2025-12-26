-- | Tests for the arithmetic compiler (OCP-0001)
module Arith.Spec (arithTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Set as Set

import Once.Arith.IR
import Once.Arith.CodeGen.C

arithTests :: TestTree
arithTests = testGroup "Arithmetic Compiler (OCP-0001)"
  [ testGroup "NumType"
      [ testCase "bitwidth I8 = 8" $
          bitwidth I8 @?= 8
      , testCase "bitwidth I64 = 64" $
          bitwidth I64 @?= 64
      , testCase "bitwidth F64 = 64" $
          bitwidth F64 @?= 64
      , testCase "isFloat F32" $
          isFloat F32 @?= True
      , testCase "isFloat I32" $
          isFloat I32 @?= False
      , testCase "isInteger I64" $
          isInteger I64 @?= True
      ]
  , testGroup "ArithIR structure"
      [ testCase "arithType of literal" $
          arithType (ALitInt I64 42) @?= I64
      , testCase "arithType of variable" $
          arithType (AVar "x" F64) @?= F64
      , testCase "arithType of addition" $
          arithType (AAdd (ALitInt I32 1) (ALitInt I32 2)) @?= I32
      , testCase "freeVars of literal is empty" $
          freeVars (ALitInt I64 42) @?= Set.empty
      , testCase "freeVars of variable" $
          freeVars (AVar "x" I64) @?= Set.singleton ("x", I64)
      , testCase "freeVars of binary op" $
          freeVars (AAdd (AVar "x" I64) (AVar "y" I64))
            @?= Set.fromList [("x", I64), ("y", I64)]
      ]
  , testGroup "C code generation"
      [ testCase "literal int" $
          arithToC (ALitInt I64 42) @?= "42"
      , testCase "negative literal" $
          arithToC (ALitInt I64 (-5)) @?= "(-5)"
      , testCase "literal float" $
          arithToC (ALitFloat F64 3.14) @?= "3.14"
      , testCase "variable" $
          arithToC (AVar "x" I64) @?= "x"
      , testCase "addition" $
          arithToC (AAdd (AVar "x" I64) (AVar "y" I64)) @?= "(x + y)"
      , testCase "subtraction" $
          arithToC (ASub (AVar "a" I32) (ALitInt I32 1)) @?= "(a - 1)"
      , testCase "multiplication" $
          arithToC (AMul (AVar "x" I64) (AVar "y" I64)) @?= "(x * y)"
      , testCase "division" $
          arithToC (ADiv (AVar "n" I32) (ALitInt I32 2)) @?= "(n / 2)"
      , testCase "modulo" $
          arithToC (AMod (AVar "n" I32) (ALitInt I32 10)) @?= "(n % 10)"
      , testCase "negation" $
          arithToC (ANeg (AVar "x" I64)) @?= "(-x)"
      , testCase "comparison lt" $
          arithToC (ACmp CmpLt (AVar "x" I32) (AVar "y" I32)) @?= "(x < y)"
      , testCase "comparison eq" $
          arithToC (ACmp CmpEq (AVar "a" I64) (ALitInt I64 0)) @?= "(a == 0)"
      , testCase "nested expression" $
          arithToC (AAdd (AMul (AVar "a" I64) (AVar "b" I64))
                         (AMul (AVar "c" I64) (AVar "d" I64)))
            @?= "((a * b) + (c * d))"
      , testCase "quadratic: x*x + 2*x + 1" $
          let x = AVar "x" I64
              expr = AAdd (AAdd (AMul x x) (AMul (ALitInt I64 2) x)) (ALitInt I64 1)
          in arithToC expr @?= "(((x * x) + (2 * x)) + 1)"
      ]
  , testGroup "NumType to C"
      [ testCase "I8 -> int8_t" $
          numTypeToC I8 @?= "int8_t"
      , testCase "I64 -> int64_t" $
          numTypeToC I64 @?= "int64_t"
      , testCase "F32 -> float" $
          numTypeToC F32 @?= "float"
      , testCase "F64 -> double" $
          numTypeToC F64 @?= "double"
      ]
  ]
