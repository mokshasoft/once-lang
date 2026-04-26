-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.Emit
--
-- Emit x86-32 assembly text from instruction representation.
-- Mirror of Once.CCC.Target.X86-64.Emit, adapted for x86-32 register
-- names and the GAS `l` (long, 32-bit) suffix.
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.Emit where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; foldr)

open import Once.CCC.Target.X86-32.Syntax

------------------------------------------------------------------------
-- Register names
------------------------------------------------------------------------

showReg : Reg → String
showReg eax = "%eax"
showReg ebx = "%ebx"
showReg ecx = "%ecx"
showReg edx = "%edx"
showReg esi = "%esi"
showReg edi = "%edi"
showReg ebp = "%ebp"
showReg esp = "%esp"

------------------------------------------------------------------------
-- Memory operands (AT&T syntax)
------------------------------------------------------------------------

showMem : Mem → String
showMem (base r)        = "(" ++ showReg r ++ ")"
showMem (base+disp r n) = showNat n ++ "(" ++ showReg r ++ ")"
showMem (label-rel n)   = ".L" ++ showNat n

------------------------------------------------------------------------
-- Operands
------------------------------------------------------------------------

showOperand : Operand → String
showOperand (reg r) = showReg r
showOperand (mem m) = showMem m
showOperand (imm n) = "$" ++ showNat n

------------------------------------------------------------------------
-- Instructions (AT&T syntax: src, dst order; `l` = 32-bit operand size)
------------------------------------------------------------------------

showInstr : Instr → String
showInstr (mov dst src)  = "    movl " ++ showOperand src ++ ", " ++ showOperand dst
showInstr (lea r m)      = "    leal " ++ showMem m ++ ", " ++ showReg r
showInstr (add dst src)  = "    addl " ++ showOperand src ++ ", " ++ showOperand dst
showInstr (sub dst src)  = "    subl " ++ showOperand src ++ ", " ++ showOperand dst
showInstr (cmp op1 op2)  = "    cmpl " ++ showOperand op2 ++ ", " ++ showOperand op1
showInstr (test op1 op2) = "    testl " ++ showOperand op2 ++ ", " ++ showOperand op1
showInstr (jmp (reg r))  = "    jmp *" ++ showReg r
showInstr (jmp (mem m))  = "    jmp *" ++ showMem m
showInstr (jmp (imm n))  = "    jmp " ++ showNat n
showInstr (jne n)        = "    jne .L" ++ showNat n
showInstr (je n)         = "    je .L"  ++ showNat n
showInstr (call (reg r)) = "    call *" ++ showReg r
showInstr (call (mem m)) = "    call *" ++ showMem m
showInstr (call (imm n)) = "    call "  ++ showNat n
showInstr ret            = "    ret"
showInstr (push (reg r)) = "    pushl " ++ showReg r
showInstr (push (mem m)) = "    pushl " ++ showMem m
showInstr (push (imm n)) = "    pushl $" ++ showNat n
showInstr (pop r)        = "    popl "  ++ showReg r
showInstr nop            = "    nop"
showInstr ud2            = "    ud2"
showInstr (label n)      = ".L" ++ showNat n ++ ":"

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

instrToLine : Instr → String
instrToLine i = showInstr i ++ "\n"

programToText : Program → String
programToText = foldr (λ i acc → instrToLine i ++ acc) ""
