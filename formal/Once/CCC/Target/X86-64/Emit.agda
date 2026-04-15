-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.Emit
--
-- Emit x86-64 assembly text from instruction representation.
-- This module converts the abstract instruction syntax to
-- GNU assembler (GAS) text format.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.Emit where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; foldr)

-- Import X86-64 syntax
open import Once.CCC.Target.X86-64.Syntax

------------------------------------------------------------------------
-- Register names
------------------------------------------------------------------------

showReg : Reg → String
showReg rax = "%rax"
showReg rbx = "%rbx"
showReg rcx = "%rcx"
showReg rdx = "%rdx"
showReg rsi = "%rsi"
showReg rdi = "%rdi"
showReg rbp = "%rbp"
showReg rsp = "%rsp"
showReg r8  = "%r8"
showReg r9  = "%r9"
showReg r10 = "%r10"
showReg r11 = "%r11"
showReg r12 = "%r12"
showReg r13 = "%r13"
showReg r14 = "%r14"
showReg r15 = "%r15"

------------------------------------------------------------------------
-- Memory operands (AT&T syntax)
------------------------------------------------------------------------

showMem : Mem → String
showMem (base r) = "(" ++ showReg r ++ ")"
showMem (base+disp r n) = showNat n ++ "(" ++ showReg r ++ ")"
showMem (rip+disp n) = showNat n ++ "(%rip)"

------------------------------------------------------------------------
-- Operands (AT&T syntax: $ for immediates)
------------------------------------------------------------------------

showOperand : Operand → String
showOperand (reg r) = showReg r
showOperand (mem m) = showMem m
showOperand (imm n) = "$" ++ showNat n

------------------------------------------------------------------------
-- Instructions (AT&T syntax: src, dst order)
------------------------------------------------------------------------

showInstr : Instr → String
showInstr (mov dst src) =
  "    movq " ++ showOperand src ++ ", " ++ showOperand dst
showInstr (lea r m) =
  "    leaq " ++ showMem m ++ ", " ++ showReg r
showInstr (add dst src) =
  "    addq " ++ showOperand src ++ ", " ++ showOperand dst
showInstr (sub dst src) =
  "    subq " ++ showOperand src ++ ", " ++ showOperand dst
showInstr (cmp op1 op2) =
  "    cmpq " ++ showOperand op2 ++ ", " ++ showOperand op1
showInstr (test op1 op2) =
  "    testq " ++ showOperand op2 ++ ", " ++ showOperand op1
showInstr (jmp n) =
  "    jmp .L" ++ showNat n
showInstr (je n) =
  "    je .L" ++ showNat n
showInstr (jne n) =
  "    jne .L" ++ showNat n
showInstr (call (reg r)) =
  "    call *" ++ showReg r
showInstr (call (mem m)) =
  "    call *" ++ showMem m
showInstr (call (imm n)) =
  "    call " ++ showNat n
showInstr ret =
  "    ret"
showInstr (push (reg r)) =
  "    pushq " ++ showReg r
showInstr (push (mem m)) =
  "    pushq " ++ showMem m
showInstr (push (imm n)) =
  "    pushq $" ++ showNat n
showInstr (pop r) =
  "    popq " ++ showReg r
showInstr nop =
  "    nop"
showInstr ud2 =
  "    ud2"
showInstr (label n) =
  ".L" ++ showNat n ++ ":"

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

-- | Convert a single instruction to a line of assembly
instrToLine : Instr → String
instrToLine i = showInstr i ++ "\n"

-- | Convert a program (list of instructions) to assembly text
programToText : Program → String
programToText = foldr (λ i acc → instrToLine i ++ acc) ""
