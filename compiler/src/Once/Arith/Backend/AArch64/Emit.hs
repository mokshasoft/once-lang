-- | AArch64 assembly emission
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
--
-- This module converts AArch64 instructions to assembly text.
module Once.Arith.Backend.AArch64.Emit
  ( -- * Emission
    emitProgram
  , emitInstr
  , emitIntInstr
  , emitFPInstr
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import Once.Arith.Backend.AArch64.Syntax

------------------------------------------------------------------------
-- Assembly emission
------------------------------------------------------------------------

-- | Emit a complete program as assembly text
emitProgram :: ArithProgram -> Text
emitProgram instrs = T.unlines (map emitInstr instrs)

-- | Emit a single instruction
emitInstr :: ArithInstr -> Text
emitInstr (IntI i) = emitIntInstr i
emitInstr (FPI f)  = emitFPInstr f

------------------------------------------------------------------------
-- Integer instruction emission
------------------------------------------------------------------------

-- | Emit an integer instruction
emitIntInstr :: IntInstr -> Text

-- Data movement
emitIntInstr (Mov dst (RegOp src)) =
  T.concat ["    mov ", emitGPR dst, ", ", emitGPR src]
emitIntInstr (Mov dst (ImmOp n)) =
  T.concat ["    mov ", emitGPR dst, ", #", T.pack (show n)]

emitIntInstr (Movz dst imm shift)
  | shift == 0 = T.concat ["    movz ", emitGPR dst, ", #", T.pack (show imm)]
  | otherwise  = T.concat ["    movz ", emitGPR dst, ", #", T.pack (show imm),
                           ", lsl #", T.pack (show shift)]

emitIntInstr (Movk dst imm shift)
  | shift == 0 = T.concat ["    movk ", emitGPR dst, ", #", T.pack (show imm)]
  | otherwise  = T.concat ["    movk ", emitGPR dst, ", #", T.pack (show imm),
                           ", lsl #", T.pack (show shift)]

-- Arithmetic
emitIntInstr (Add dst src1 (RegOp src2)) =
  T.concat ["    add ", emitGPR dst, ", ", emitGPR src1, ", ", emitGPR src2]
emitIntInstr (Add dst src1 (ImmOp n)) =
  T.concat ["    add ", emitGPR dst, ", ", emitGPR src1, ", #", T.pack (show n)]

emitIntInstr (Sub dst src1 (RegOp src2)) =
  T.concat ["    sub ", emitGPR dst, ", ", emitGPR src1, ", ", emitGPR src2]
emitIntInstr (Sub dst src1 (ImmOp n)) =
  T.concat ["    sub ", emitGPR dst, ", ", emitGPR src1, ", #", T.pack (show n)]

emitIntInstr (Mul dst src1 src2) =
  T.concat ["    mul ", emitGPR dst, ", ", emitGPR src1, ", ", emitGPR src2]

emitIntInstr (Sdiv dst src1 src2) =
  T.concat ["    sdiv ", emitGPR dst, ", ", emitGPR src1, ", ", emitGPR src2]

emitIntInstr (Msub dst mul1 mul2 acc) =
  T.concat ["    msub ", emitGPR dst, ", ", emitGPR mul1, ", ",
            emitGPR mul2, ", ", emitGPR acc]

emitIntInstr (Neg dst src) =
  T.concat ["    neg ", emitGPR dst, ", ", emitGPR src]

-- | Emit a GPR register name
emitGPR :: GPReg -> Text
emitGPR r = T.pack (gprName r)

------------------------------------------------------------------------
-- Floating-point instruction emission
------------------------------------------------------------------------

-- | Emit a floating-point instruction
emitFPInstr :: FPInstr -> Text

-- Data movement
emitFPInstr (Fmov dst (FPRegOp src)) =
  T.concat ["    fmov ", emitFP dst, ", ", emitFP src]
emitFPInstr (FmovFromGPR dst gpr) =
  T.concat ["    fmov ", emitFP dst, ", ", emitGPR gpr]

-- Double-precision
emitFPInstr (Fadd dst src1 src2) =
  T.concat ["    fadd ", emitFP dst, ", ", emitFP src1, ", ", emitFP src2]
emitFPInstr (Fsub dst src1 src2) =
  T.concat ["    fsub ", emitFP dst, ", ", emitFP src1, ", ", emitFP src2]
emitFPInstr (Fmul dst src1 src2) =
  T.concat ["    fmul ", emitFP dst, ", ", emitFP src1, ", ", emitFP src2]
emitFPInstr (Fdiv dst src1 src2) =
  T.concat ["    fdiv ", emitFP dst, ", ", emitFP src1, ", ", emitFP src2]
emitFPInstr (Fneg dst src) =
  T.concat ["    fneg ", emitFP dst, ", ", emitFP src]

-- Single-precision (use S register names)
emitFPInstr (FaddS dst src1 src2) =
  T.concat ["    fadd ", emitFPS dst, ", ", emitFPS src1, ", ", emitFPS src2]
emitFPInstr (FsubS dst src1 src2) =
  T.concat ["    fsub ", emitFPS dst, ", ", emitFPS src1, ", ", emitFPS src2]
emitFPInstr (FmulS dst src1 src2) =
  T.concat ["    fmul ", emitFPS dst, ", ", emitFPS src1, ", ", emitFPS src2]
emitFPInstr (FdivS dst src1 src2) =
  T.concat ["    fdiv ", emitFPS dst, ", ", emitFPS src1, ", ", emitFPS src2]
emitFPInstr (FnegS dst src) =
  T.concat ["    fneg ", emitFPS dst, ", ", emitFPS src]

-- | Emit a double-precision FP register name
emitFP :: FPReg -> Text
emitFP r = T.pack (fpRegName r)

-- | Emit a single-precision FP register name
emitFPS :: FPReg -> Text
emitFPS r = T.pack (fpRegNameS r)
