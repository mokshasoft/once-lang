------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV.Emit
--
-- Assembly text emission for RISC-V arithmetic instructions.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV.Emit where

open import Once.Arith.Backend.RiscV.Syntax

open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer using (ℤ)
open import Data.Integer.Show renaming (show to showℤ)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; map)

------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------

unlines : List String → String
unlines [] = ""
unlines (x ∷ []) = x
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

------------------------------------------------------------------------
-- GPR emission
------------------------------------------------------------------------

gprToText : GPReg → String
gprToText x0  = "x0"
gprToText x1  = "x1"
gprToText x2  = "x2"
gprToText x3  = "x3"
gprToText x4  = "x4"
gprToText x5  = "x5"
gprToText x6  = "x6"
gprToText x7  = "x7"
gprToText x8  = "x8"
gprToText x9  = "x9"
gprToText x10 = "x10"
gprToText x11 = "x11"
gprToText x12 = "x12"
gprToText x13 = "x13"
gprToText x14 = "x14"
gprToText x15 = "x15"
gprToText x16 = "x16"
gprToText x17 = "x17"
gprToText x18 = "x18"
gprToText x19 = "x19"
gprToText x20 = "x20"
gprToText x21 = "x21"
gprToText x22 = "x22"
gprToText x23 = "x23"
gprToText x24 = "x24"
gprToText x25 = "x25"
gprToText x26 = "x26"
gprToText x27 = "x27"
gprToText x28 = "x28"
gprToText x29 = "x29"
gprToText x30 = "x30"
gprToText x31 = "x31"

------------------------------------------------------------------------
-- FP register emission
------------------------------------------------------------------------

fpToText : FPReg → String
fpToText f0  = "f0"
fpToText f1  = "f1"
fpToText f2  = "f2"
fpToText f3  = "f3"
fpToText f4  = "f4"
fpToText f5  = "f5"
fpToText f6  = "f6"
fpToText f7  = "f7"
fpToText f8  = "f8"
fpToText f9  = "f9"
fpToText f10 = "f10"
fpToText f11 = "f11"
fpToText f12 = "f12"
fpToText f13 = "f13"
fpToText f14 = "f14"
fpToText f15 = "f15"
fpToText f16 = "f16"
fpToText f17 = "f17"
fpToText f18 = "f18"
fpToText f19 = "f19"
fpToText f20 = "f20"
fpToText f21 = "f21"
fpToText f22 = "f22"
fpToText f23 = "f23"
fpToText f24 = "f24"
fpToText f25 = "f25"
fpToText f26 = "f26"
fpToText f27 = "f27"
fpToText f28 = "f28"
fpToText f29 = "f29"
fpToText f30 = "f30"
fpToText f31 = "f31"

------------------------------------------------------------------------
-- Integer instruction emission
------------------------------------------------------------------------

intInstrToText : IntInstr → String
intInstrToText (li rd imm) =
  "    li " ++ gprToText rd ++ ", " ++ showℤ imm
intInstrToText (mv rd rs) =
  "    mv " ++ gprToText rd ++ ", " ++ gprToText rs
intInstrToText (add rd rs1 rs2) =
  "    add " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ gprToText rs2
intInstrToText (addi rd rs1 imm) =
  "    addi " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ showℤ imm
intInstrToText (sub rd rs1 rs2) =
  "    sub " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ gprToText rs2
intInstrToText (mul rd rs1 rs2) =
  "    mul " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ gprToText rs2
intInstrToText (div rd rs1 rs2) =
  "    div " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ gprToText rs2
intInstrToText (rem rd rs1 rs2) =
  "    rem " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ gprToText rs2
intInstrToText (neg rd rs) =
  "    neg " ++ gprToText rd ++ ", " ++ gprToText rs
intInstrToText (sd rs offset) =
  "    sd " ++ gprToText rs ++ ", " ++ showℤ offset ++ "(sp)"
intInstrToText (ld rd offset) =
  "    ld " ++ gprToText rd ++ ", " ++ showℤ offset ++ "(sp)"
-- Comparison
intInstrToText (slt rd rs1 rs2) =
  "    slt " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ gprToText rs2
intInstrToText (sltu rd rs1 rs2) =
  "    sltu " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ gprToText rs2
intInstrToText (slti rd rs1 imm) =
  "    slti " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ showℤ imm
intInstrToText (sltiu rd rs1 imm) =
  "    sltiu " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ showℤ imm
intInstrToText (xori rd rs1 imm) =
  "    xori " ++ gprToText rd ++ ", " ++ gprToText rs1 ++ ", " ++ showℤ imm
intInstrToText (seqz rd rs) =
  "    seqz " ++ gprToText rd ++ ", " ++ gprToText rs
intInstrToText (snez rd rs) =
  "    snez " ++ gprToText rd ++ ", " ++ gprToText rs

------------------------------------------------------------------------
-- FP instruction emission
------------------------------------------------------------------------

fpInstrToText : FPInstr → String
fpInstrToText (fmvD rd rs) =
  "    fmv.d " ++ fpToText rd ++ ", " ++ fpToText rs
fpInstrToText (faddD rd rs1 rs2) =
  "    fadd.d " ++ fpToText rd ++ ", " ++ fpToText rs1 ++ ", " ++ fpToText rs2
fpInstrToText (fsubD rd rs1 rs2) =
  "    fsub.d " ++ fpToText rd ++ ", " ++ fpToText rs1 ++ ", " ++ fpToText rs2
fpInstrToText (fmulD rd rs1 rs2) =
  "    fmul.d " ++ fpToText rd ++ ", " ++ fpToText rs1 ++ ", " ++ fpToText rs2
fpInstrToText (fdivD rd rs1 rs2) =
  "    fdiv.d " ++ fpToText rd ++ ", " ++ fpToText rs1 ++ ", " ++ fpToText rs2
fpInstrToText (fnegD rd rs) =
  "    fneg.d " ++ fpToText rd ++ ", " ++ fpToText rs
-- Single-precision
fpInstrToText (faddS rd rs1 rs2) =
  "    fadd.s " ++ fpToText rd ++ ", " ++ fpToText rs1 ++ ", " ++ fpToText rs2
fpInstrToText (fsubS rd rs1 rs2) =
  "    fsub.s " ++ fpToText rd ++ ", " ++ fpToText rs1 ++ ", " ++ fpToText rs2
fpInstrToText (fmulS rd rs1 rs2) =
  "    fmul.s " ++ fpToText rd ++ ", " ++ fpToText rs1 ++ ", " ++ fpToText rs2
fpInstrToText (fdivS rd rs1 rs2) =
  "    fdiv.s " ++ fpToText rd ++ ", " ++ fpToText rs1 ++ ", " ++ fpToText rs2
fpInstrToText (fnegS rd rs) =
  "    fneg.s " ++ fpToText rd ++ ", " ++ fpToText rs
-- Type conversion
fpInstrToText (fcvtDS rd rs) =
  "    fcvt.d.s " ++ fpToText rd ++ ", " ++ fpToText rs

------------------------------------------------------------------------
-- Unified instruction emission
------------------------------------------------------------------------

instrToText : ArithInstr → String
instrToText (intI i) = intInstrToText i
instrToText (fpI f)  = fpInstrToText f

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

emitProgram : ArithProgram → String
emitProgram instrs = unlines (map instrToText instrs)
