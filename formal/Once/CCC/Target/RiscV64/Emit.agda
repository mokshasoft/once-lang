-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.Emit
--
-- Emit RISC-V 64 assembly text from instruction representation.
-- Mirror of Once.CCC.Target.X86-64.Emit, adapted for RV64 mnemonics.
-- Output is GAS-compatible RV64 assembly.
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.Emit where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.Integer using (ℤ; +_)
open import Data.Integer.Show using () renaming (show to showInt)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; foldr)

open import Once.CCC.Target.RiscV64.Syntax

------------------------------------------------------------------------
-- Register names (RV64 standard ABI)
------------------------------------------------------------------------

showReg : Reg → String
showReg zero = "zero"
showReg ra   = "ra"
showReg sp   = "sp"
showReg fp   = "fp"
showReg a0   = "a0"
showReg a1   = "a1"
showReg a2   = "a2"
showReg a3   = "a3"
showReg a4   = "a4"
showReg a5   = "a5"
showReg a6   = "a6"
showReg a7   = "a7"
showReg s1   = "s1"
showReg s2   = "s2"
showReg s3   = "s3"
showReg s4   = "s4"
showReg t0   = "t0"
showReg t1   = "t1"
showReg t2   = "t2"
showReg t3   = "t3"
showReg t4   = "t4"

------------------------------------------------------------------------
-- Instructions
------------------------------------------------------------------------

showInstr : Instr → String
showInstr (ld   rd rs o)      = "    ld "    ++ showReg rd ++ ", " ++ showNat o ++ "(" ++ showReg rs ++ ")"
showInstr (sd   rs rd o)      = "    sd "    ++ showReg rs ++ ", " ++ showNat o ++ "(" ++ showReg rd ++ ")"
showInstr (add  rd rs1 rs2)   = "    add "   ++ showReg rd ++ ", " ++ showReg rs1 ++ ", " ++ showReg rs2
showInstr (sub  rd rs1 rs2)   = "    sub "   ++ showReg rd ++ ", " ++ showReg rs1 ++ ", " ++ showReg rs2
showInstr (addi rd rs i)      = "    addi "  ++ showReg rd ++ ", " ++ showReg rs  ++ ", " ++ showInt i
showInstr (li   rd i)         = "    li "    ++ showReg rd ++ ", " ++ showInt i
showInstr (auipc rd i)        = "    auipc " ++ showReg rd ++ ", " ++ showNat i
showInstr (lla  rd n)         = "    lla "   ++ showReg rd ++ ", .L_thunk_" ++ showNat n
showInstr (mv   rd rs)        = "    mv "    ++ showReg rd ++ ", " ++ showReg rs
showInstr (beq  rs1 rs2 o)    = "    beq "   ++ showReg rs1 ++ ", " ++ showReg rs2 ++ ", .L" ++ showNat o
showInstr (bne  rs1 rs2 o)    = "    bne "   ++ showReg rs1 ++ ", " ++ showReg rs2 ++ ", .L" ++ showNat o
showInstr (jal  rd o)         = "    jal "   ++ showReg rd ++ ", .L" ++ showNat o
showInstr (jalr rd rs o)      = "    jalr "  ++ showReg rd ++ ", " ++ showReg rs ++ ", " ++ showNat o
showInstr (j    o)            = "    j .L"   ++ showNat o
showInstr ret                 = "    ret"
showInstr (call o)            = "    call "  ++ showNat o
showInstr (call-sym name)     = "    call "  ++ name
showInstr nop                 = "    nop"
showInstr unimp               = "    unimp"
showInstr (label n)           = ".L" ++ showNat n ++ ":"

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

instrToLine : Instr → String
instrToLine i = showInstr i ++ "\n"

programToText : Program → String
programToText = foldr (λ i acc → instrToLine i ++ acc) ""
