-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Once.CCC.Label using (Label; once; sigop; thunk; showLabelId)

------------------------------------------------------------------------
-- Register names
------------------------------------------------------------------------

-- Register rendering is shared with the arith backend (Plan 0.55).
open import Once.Target.X86-64.PhysReg using (showReg)

------------------------------------------------------------------------
-- Memory operands (AT&T syntax)
------------------------------------------------------------------------

showMem : Mem → String
showMem (base r) = "(" ++ showReg r ++ ")"
showMem (base+disp r n) = showNat n ++ "(" ++ showReg r ++ ")"
showMem (rip+disp n) = showNat n ++ "(%rip)"
showMem (rip+label n) = ".L_thunk_" ++ showLabelId n ++ "(%rip)"

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

-- Plan 0.33: render provenance into the assembly symbol so compiler
-- (`once`) and SigOp (`sigop`) labels never collide in the object file.
showLabel : Label → String
showLabel (once n)       = "once_" ++ showLabelId n
showLabel (sigop nm k)   = "sigops_" ++ nm ++ "_" ++ showNat k
-- Plan 0.63 (D082): a closure-body entry. The ".L" prefix is added by the
-- call sites, so this renders exactly the `.L_thunk_<n>` that
-- `emit-thunk-body` and the `rip+label` operand already use.
showLabel (thunk n)      = "_thunk_" ++ showLabelId n

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
  "    jmp .L" ++ showLabel n
showInstr (je n) =
  "    je .L" ++ showLabel n
showInstr (jne n) =
  "    jne .L" ++ showLabel n
showInstr (call (reg r)) =
  "    call *" ++ showReg r
showInstr (call (mem m)) =
  "    call *" ++ showMem m
showInstr (call (imm n)) =
  "    call " ++ showNat n
showInstr (call-sym name) =
  "    call " ++ name
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
showInstr syscall =
  "    syscall"
showInstr (label n) =
  ".L" ++ showLabel n ++ ":"

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

-- | Convert a single instruction to a line of assembly
instrToLine : Instr → String
instrToLine i = showInstr i ++ "\n"

-- | Convert a program (list of instructions) to assembly text
programToText : Program → String
programToText = foldr (λ i acc → instrToLine i ++ acc) ""
