-- | Tests for the arithmetic compiler (OCP-0001)
module Arith.Spec (arithTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Set as Set

import Once.Arith.IR
import Once.Arith.CodeGen.C
import Once.Arith.Backend.X86.Syntax
import Once.Arith.Backend.X86.CodeGen
import Once.Arith.Backend.X86.Emit
import qualified Once.Arith.Backend.AArch64.Syntax as A64
import qualified Once.Arith.Backend.AArch64.CodeGen as A64
import qualified Once.Arith.Backend.AArch64.Emit as A64

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
  , testGroup "x86-64 code generation"
      [ testCase "literal generates mov" $
          let prog = compileArith (ALitInt I64 42)
          in length prog @?= 2  -- mov to r8, mov to rax
      , testCase "literal value in mov instruction" $
          let prog = compileArith (ALitInt I64 42)
          in case prog of
               [IntI (MovI R8 (ImmI 42)), IntI (MovI RAX (RegI R8))] -> return ()
               _ -> assertFailure $ "Unexpected: " ++ show prog
      , testCase "addition generates 3 instructions" $
          let prog = compileArith (AAdd (ALitInt I64 1) (ALitInt I64 2))
          in length prog @?= 4  -- mov r8, mov r9, add, mov rax
      , testCase "subtraction generates sub instruction" $
          let prog = compileArith (ASub (ALitInt I64 10) (ALitInt I64 3))
              hasSubI = any isSubI prog
              isSubI (IntI (SubI _ _)) = True
              isSubI _ = False
          in hasSubI @?= True
      , testCase "multiplication generates imul instruction" $
          let prog = compileArith (AMul (ALitInt I64 5) (ALitInt I64 6))
              hasIMulI = any isIMulI prog
              isIMulI (IntI (IMulI _ _)) = True
              isIMulI _ = False
          in hasIMulI @?= True
      , testCase "negation generates neg instruction" $
          let prog = compileArith (ANeg (ALitInt I64 7))
              hasNegI = any isNegI prog
              isNegI (IntI (NegI _)) = True
              isNegI _ = False
          in hasNegI @?= True
      , testCase "division generates idiv instruction" $
          let prog = compileArith (ADiv (ALitInt I64 100) (ALitInt I64 10))
              hasIDivI = any isIDivI prog
              isIDivI (IntI (IDivI _)) = True
              isIDivI _ = False
          in hasIDivI @?= True
      , testCase "nested expression" $
          let x = ALitInt I64 2
              expr = AAdd (AMul x x) (ALitInt I64 1)  -- 2*2 + 1
              prog = compileArith expr
          in length prog > 0 @?= True
      ]
  , testGroup "x86-64 assembly emission"
      [ testCase "mov instruction format" $
          emitIntInstr (MovI RAX (ImmI 42)) @?= "    movq $42, %rax"
      , testCase "add instruction format" $
          emitIntInstr (AddI R8 (RegI R9)) @?= "    addq %r9, %r8"
      , testCase "sub instruction format" $
          emitIntInstr (SubI RBX (ImmI 1)) @?= "    subq $1, %rbx"
      , testCase "imul instruction format" $
          emitIntInstr (IMulI RAX (RegI RCX)) @?= "    imulq %rcx, %rax"
      , testCase "neg instruction format" $
          emitIntInstr (NegI RDX) @?= "    negq %rdx"
      , testCase "cqo instruction format" $
          emitIntInstr Cqo @?= "    cqo"
      , testCase "idiv instruction format" $
          emitIntInstr (IDivI (RegI R10)) @?= "    idivq %r10"
      , testCase "memory operand format" $
          emitIntInstr (MovI RAX (MemI (Base RDI))) @?= "    movq (%rdi), %rax"
      , testCase "memory with displacement" $
          emitIntInstr (MovI RAX (MemI (BaseDisp RSI 8))) @?= "    movq 8(%rsi), %rax"
      , testCase "float movsd format" $
          emitFloatInstr (Movsd XMM0 (RegF XMM1)) @?= "    movsd %xmm1, %xmm0"
      , testCase "float addsd format" $
          emitFloatInstr (Addsd XMM0 (RegF XMM1)) @?= "    addsd %xmm1, %xmm0"
      , testCase "full program emission" $
          let prog = compileArith (ALitInt I64 42)
              asm = emitProgram prog
          in T.isInfixOf "movq" asm @?= True
      ]
  , testGroup "x86-64 register names"
      [ testCase "gprName RAX" $
          gprName RAX @?= "rax"
      , testCase "gprName R11" $
          gprName R11 @?= "r11"
      , testCase "gprName32 RAX" $
          gprName32 RAX @?= "eax"
      , testCase "gprName32 R8" $
          gprName32 R8 @?= "r8d"
      , testCase "xmmName XMM0" $
          xmmName XMM0 @?= "xmm0"
      , testCase "xmmName XMM15" $
          xmmName XMM15 @?= "xmm15"
      ]
  , testGroup "AArch64 code generation"
      [ testCase "literal generates movz" $
          let prog = A64.compileArith (ALitInt I64 42)
          in length prog @?= 2  -- movz x9, mov x0
      , testCase "addition generates add instruction" $
          let prog = A64.compileArith (AAdd (ALitInt I64 1) (ALitInt I64 2))
              hasAdd = any isA64Add prog
              isA64Add (A64.IntI (A64.Add _ _ _)) = True
              isA64Add _ = False
          in hasAdd @?= True
      , testCase "subtraction generates sub instruction" $
          let prog = A64.compileArith (ASub (ALitInt I64 10) (ALitInt I64 3))
              hasSub = any isA64Sub prog
              isA64Sub (A64.IntI (A64.Sub _ _ _)) = True
              isA64Sub _ = False
          in hasSub @?= True
      , testCase "multiplication generates mul instruction" $
          let prog = A64.compileArith (AMul (ALitInt I64 5) (ALitInt I64 6))
              hasMul = any isA64Mul prog
              isA64Mul (A64.IntI (A64.Mul _ _ _)) = True
              isA64Mul _ = False
          in hasMul @?= True
      , testCase "division generates sdiv instruction" $
          let prog = A64.compileArith (ADiv (ALitInt I64 100) (ALitInt I64 10))
              hasSdiv = any isA64Sdiv prog
              isA64Sdiv (A64.IntI (A64.Sdiv _ _ _)) = True
              isA64Sdiv _ = False
          in hasSdiv @?= True
      , testCase "negation generates neg instruction" $
          let prog = A64.compileArith (ANeg (ALitInt I64 7))
              hasNeg = any isA64Neg prog
              isA64Neg (A64.IntI (A64.Neg _ _)) = True
              isA64Neg _ = False
          in hasNeg @?= True
      ]
  , testGroup "AArch64 assembly emission"
      [ testCase "movz instruction format" $
          A64.emitIntInstr (A64.Movz A64.X0 42 0) @?= "    movz x0, #42"
      , testCase "movz with shift" $
          A64.emitIntInstr (A64.Movz A64.X1 0xFFFF 16) @?= "    movz x1, #65535, lsl #16"
      , testCase "add instruction format" $
          A64.emitIntInstr (A64.Add A64.X0 A64.X1 (A64.RegOp A64.X2)) @?= "    add x0, x1, x2"
      , testCase "add immediate format" $
          A64.emitIntInstr (A64.Add A64.X0 A64.X1 (A64.ImmOp 42)) @?= "    add x0, x1, #42"
      , testCase "sub instruction format" $
          A64.emitIntInstr (A64.Sub A64.X3 A64.X4 (A64.RegOp A64.X5)) @?= "    sub x3, x4, x5"
      , testCase "mul instruction format" $
          A64.emitIntInstr (A64.Mul A64.X0 A64.X1 A64.X2) @?= "    mul x0, x1, x2"
      , testCase "sdiv instruction format" $
          A64.emitIntInstr (A64.Sdiv A64.X0 A64.X1 A64.X2) @?= "    sdiv x0, x1, x2"
      , testCase "neg instruction format" $
          A64.emitIntInstr (A64.Neg A64.X0 A64.X1) @?= "    neg x0, x1"
      , testCase "fadd instruction format" $
          A64.emitFPInstr (A64.Fadd A64.D0 A64.D1 A64.D2) @?= "    fadd d0, d1, d2"
      , testCase "full program emission" $
          let prog = A64.compileArith (ALitInt I64 42)
              asm = A64.emitProgram prog
          in T.isInfixOf "movz" asm @?= True
      ]
  , testGroup "AArch64 register names"
      [ testCase "gprName X0" $
          A64.gprName A64.X0 @?= "x0"
      , testCase "gprName X15" $
          A64.gprName A64.X15 @?= "x15"
      , testCase "gprName32 X0" $
          A64.gprName32 A64.X0 @?= "w0"
      , testCase "fpRegName D0" $
          A64.fpRegName A64.D0 @?= "d0"
      , testCase "fpRegNameS D0" $
          A64.fpRegNameS A64.D0 @?= "s0"
      ]
  ]
