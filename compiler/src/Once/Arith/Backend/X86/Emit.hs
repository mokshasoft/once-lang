-- | x86-64 assembly emission
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
--
-- This module converts x86-64 instructions to assembly text (AT&T syntax).
module Once.Arith.Backend.X86.Emit
  ( -- * Emission
    emitProgram
  , emitInstr
  , emitIntInstr
  , emitFloatInstr
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import Once.Arith.Backend.X86.Syntax

------------------------------------------------------------------------
-- Assembly emission (AT&T syntax)
------------------------------------------------------------------------

-- | Emit a complete program as assembly text
emitProgram :: ArithProgram -> Text
emitProgram instrs = T.unlines (map emitInstr instrs)

-- | Emit a single instruction
emitInstr :: ArithInstr -> Text
emitInstr (IntI i)   = emitIntInstr i
emitInstr (FloatI f) = emitFloatInstr f

------------------------------------------------------------------------
-- Integer instruction emission
------------------------------------------------------------------------

-- | Emit an integer instruction (AT&T syntax: src, dst)
emitIntInstr :: IntInstr -> Text
emitIntInstr (MovI dst src) =
  T.concat ["    movq ", emitIntOp src, ", ", emitGPR dst]
emitIntInstr (AddI dst src) =
  T.concat ["    addq ", emitIntOp src, ", ", emitGPR dst]
emitIntInstr (SubI dst src) =
  T.concat ["    subq ", emitIntOp src, ", ", emitGPR dst]
emitIntInstr (IMulI dst src) =
  T.concat ["    imulq ", emitIntOp src, ", ", emitGPR dst]
emitIntInstr (NegI dst) =
  T.concat ["    negq ", emitGPR dst]
emitIntInstr Cqo =
  "    cqo"
emitIntInstr (IDivI src) =
  T.concat ["    idivq ", emitIntOp src]

-- | Emit a GPR register name (AT&T: %reg)
emitGPR :: GPReg -> Text
emitGPR r = T.pack ("%" ++ gprName r)

-- | Emit an integer operand
emitIntOp :: IntOperand -> Text
emitIntOp (RegI r)   = emitGPR r
emitIntOp (ImmI n)   = T.pack ("$" ++ show n)
emitIntOp (MemI mem) = emitMem mem

-- | Emit a memory operand
emitMem :: ArithMem -> Text
emitMem (Base r)        = T.concat ["(", emitGPR r, ")"]
emitMem (BaseDisp r d)  = T.concat [T.pack (show d), "(", emitGPR r, ")"]

------------------------------------------------------------------------
-- Float instruction emission
------------------------------------------------------------------------

-- | Emit a floating-point instruction
emitFloatInstr :: FloatInstr -> Text
emitFloatInstr (Movss dst src) =
  T.concat ["    movss ", emitFloatOp src, ", ", emitXMM dst]
emitFloatInstr (Movsd dst src) =
  T.concat ["    movsd ", emitFloatOp src, ", ", emitXMM dst]
emitFloatInstr (Addss dst src) =
  T.concat ["    addss ", emitFloatOp src, ", ", emitXMM dst]
emitFloatInstr (Addsd dst src) =
  T.concat ["    addsd ", emitFloatOp src, ", ", emitXMM dst]
emitFloatInstr (Subss dst src) =
  T.concat ["    subss ", emitFloatOp src, ", ", emitXMM dst]
emitFloatInstr (Subsd dst src) =
  T.concat ["    subsd ", emitFloatOp src, ", ", emitXMM dst]
emitFloatInstr (Mulss dst src) =
  T.concat ["    mulss ", emitFloatOp src, ", ", emitXMM dst]
emitFloatInstr (Mulsd dst src) =
  T.concat ["    mulsd ", emitFloatOp src, ", ", emitXMM dst]
emitFloatInstr (Divss dst src) =
  T.concat ["    divss ", emitFloatOp src, ", ", emitXMM dst]
emitFloatInstr (Divsd dst src) =
  T.concat ["    divsd ", emitFloatOp src, ", ", emitXMM dst]
emitFloatInstr (Xorps dst src) =
  T.concat ["    xorps ", emitXMM src, ", ", emitXMM dst]
emitFloatInstr (Xorpd dst src) =
  T.concat ["    xorpd ", emitXMM src, ", ", emitXMM dst]
emitFloatInstr (MovqToXMM xmm gpr) =
  T.concat ["    movq ", emitGPR gpr, ", ", emitXMM xmm]

-- | Emit an XMM register name
emitXMM :: XMMReg -> Text
emitXMM r = T.pack ("%" ++ xmmName r)

-- | Emit a float operand
emitFloatOp :: FloatOperand -> Text
emitFloatOp (RegF r)   = emitXMM r
emitFloatOp (MemF mem) = emitMem mem
