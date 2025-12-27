-- | RISC-V assembly emission for arithmetic programs.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
module Once.Arith.Backend.RiscV.Emit
  ( emitProgram
  , emitIntInstr
  , emitFPInstr
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import Once.Arith.Backend.RiscV.Syntax

------------------------------------------------------------------------
-- Program Emission
------------------------------------------------------------------------

-- | Emit a complete arithmetic program as RISC-V assembly
emitProgram :: ArithProgram -> Text
emitProgram instrs = T.unlines $ map emitInstr instrs

-- | Emit a single instruction
emitInstr :: ArithInstr -> Text
emitInstr (IntI i) = emitIntInstr i
emitInstr (FPI f) = emitFPInstr f

------------------------------------------------------------------------
-- Integer Instruction Emission
------------------------------------------------------------------------

-- | Emit an integer instruction
emitIntInstr :: IntInstr -> Text
emitIntInstr (Li rd imm) =
  "    li " <> gprName rd <> ", " <> T.pack (show imm)
emitIntInstr (Mv rd rs) =
  "    mv " <> gprName rd <> ", " <> gprName rs
emitIntInstr (Add rd rs1 rs2) =
  "    add " <> gprName rd <> ", " <> gprName rs1 <> ", " <> gprName rs2
emitIntInstr (Addi rd rs1 imm) =
  "    addi " <> gprName rd <> ", " <> gprName rs1 <> ", " <> T.pack (show imm)
emitIntInstr (Sub rd rs1 rs2) =
  "    sub " <> gprName rd <> ", " <> gprName rs1 <> ", " <> gprName rs2
emitIntInstr (Mul rd rs1 rs2) =
  "    mul " <> gprName rd <> ", " <> gprName rs1 <> ", " <> gprName rs2
emitIntInstr (Div rd rs1 rs2) =
  "    div " <> gprName rd <> ", " <> gprName rs1 <> ", " <> gprName rs2
emitIntInstr (Rem rd rs1 rs2) =
  "    rem " <> gprName rd <> ", " <> gprName rs1 <> ", " <> gprName rs2
emitIntInstr (Neg rd rs) =
  "    neg " <> gprName rd <> ", " <> gprName rs

------------------------------------------------------------------------
-- Floating-point Instruction Emission
------------------------------------------------------------------------

-- | Emit a floating-point instruction
emitFPInstr :: FPInstr -> Text
emitFPInstr (FmvD rd rs) =
  "    fmv.d " <> fpRegName rd <> ", " <> fpRegName rs
emitFPInstr (FaddD rd rs1 rs2) =
  "    fadd.d " <> fpRegName rd <> ", " <> fpRegName rs1 <> ", " <> fpRegName rs2
emitFPInstr (FsubD rd rs1 rs2) =
  "    fsub.d " <> fpRegName rd <> ", " <> fpRegName rs1 <> ", " <> fpRegName rs2
emitFPInstr (FmulD rd rs1 rs2) =
  "    fmul.d " <> fpRegName rd <> ", " <> fpRegName rs1 <> ", " <> fpRegName rs2
emitFPInstr (FdivD rd rs1 rs2) =
  "    fdiv.d " <> fpRegName rd <> ", " <> fpRegName rs1 <> ", " <> fpRegName rs2
emitFPInstr (FnegD rd rs) =
  "    fneg.d " <> fpRegName rd <> ", " <> fpRegName rs
emitFPInstr (FaddS rd rs1 rs2) =
  "    fadd.s " <> fpRegName rd <> ", " <> fpRegName rs1 <> ", " <> fpRegName rs2
emitFPInstr (FsubS rd rs1 rs2) =
  "    fsub.s " <> fpRegName rd <> ", " <> fpRegName rs1 <> ", " <> fpRegName rs2
emitFPInstr (FmulS rd rs1 rs2) =
  "    fmul.s " <> fpRegName rd <> ", " <> fpRegName rs1 <> ", " <> fpRegName rs2
emitFPInstr (FdivS rd rs1 rs2) =
  "    fdiv.s " <> fpRegName rd <> ", " <> fpRegName rs1 <> ", " <> fpRegName rs2
emitFPInstr (FnegS rd rs) =
  "    fneg.s " <> fpRegName rd <> ", " <> fpRegName rs
