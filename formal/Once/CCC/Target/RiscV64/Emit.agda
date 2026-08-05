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

-- Register rendering is shared with the arith backend (Plan 0.55).
open import Once.Target.RiscV64.PhysReg using (showReg)

------------------------------------------------------------------------
-- Labels (Plan 0.63) — BYTE-IDENTICAL to the x86-64 / x86-32 `showLabel`.
-- Provenance keeps compiler jumps, SigOp symbols and closure-body entries in
-- separate namespaces (D033, D082); rendering them identically on every target
-- is what lets the naming be reasoned about once rather than per arch.
------------------------------------------------------------------------

showLabel : Label → String
showLabel (once n)     = "once_" ++ showNat n
showLabel (sigop nm k) = "sigops_" ++ nm ++ "_" ++ showNat k
showLabel (thunk n)    = "_thunk_" ++ showNat n

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
showInstr (beq  rs1 rs2 o)    = "    beq "   ++ showReg rs1 ++ ", " ++ showReg rs2 ++ ", .L" ++ showLabel o
showInstr (bne  rs1 rs2 o)    = "    bne "   ++ showReg rs1 ++ ", " ++ showReg rs2 ++ ", .L" ++ showLabel o
showInstr (jal  rd o)         = "    jal "   ++ showReg rd ++ ", .L" ++ showLabel o
showInstr (jalr rd rs o)      = "    jalr "  ++ showReg rd ++ ", " ++ showReg rs ++ ", " ++ showNat o
showInstr (j    o)            = "    j .L"   ++ showLabel o
showInstr ret                 = "    ret"
showInstr (call o)            = "    call "  ++ showNat o
showInstr (call-sym name)     = "    call "  ++ name
showInstr nop                 = "    nop"
showInstr unimp               = "    unimp"
showInstr (label n)           = ".L" ++ showLabel n ++ ":"

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

instrToLine : Instr → String
instrToLine i = showInstr i ++ "\n"

programToText : Program → String
programToText = foldr (λ i acc → instrToLine i ++ acc) ""
