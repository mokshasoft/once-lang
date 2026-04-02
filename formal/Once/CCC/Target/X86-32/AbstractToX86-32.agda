-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.AbstractToX86-32
--
-- Compilation from AbstractInstr to x86-32 instructions.
--
-- Each AbstractInstr compiles to a short sequence of x86-32 instructions.
-- This module provides the mapping; simulation proofs would go in
-- DirectSimulation.agda.
--
-- x86-32 calling convention (cdecl):
--   - Arguments pushed on stack right-to-left
--   - Return value in eax (or eax:edx for 64-bit)
--   - Callee-saved: ebx, esi, edi, ebp
--   - Caller-saved: eax, ecx, edx
--
-- Once's mapping:
--   - eax: Output register (return value)
--   - ecx: Input register (first logical argument)
--   - ebp: frame pointer
--   - ebx: closure/environment pointer (callee-saved)
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.AbstractToX86-32 where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.List using (List; []; _∷_; _++_)

-- Import x86-32 syntax
open import Once.CCC.Target.X86-32.Syntax
  using (Reg; eax; ebx; ecx; edx; esi; edi; ebp; esp;
         Mem; base; base+disp; label-rel;
         Operand; reg; mem; imm;
         Instr; mov; lea; add; sub; cmp; test; push; pop; call; ret; jmp; jne; je; nop; ud2; label;
         Program; slot-size; slots)

-- Import AbstractInstr from SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; Slot;
         mov-to-output; mov-to-input; load-indirect; load-indirect-suc;
         load-from-slot; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input;
         instr-alloc-stack; instr-dealloc-stack;
         instr-push-frame; instr-pop-frame; instr-call-closure)

------------------------------------------------------------------------
-- Slot to displacement conversion
--
-- Convert a logical slot number to an x86-32 displacement.
-- Slots are indexed from current frame, growing upward (higher addresses).
------------------------------------------------------------------------

slot-to-disp : Slot → ℕ
slot-to-disp n = n *ℕ slot-size

------------------------------------------------------------------------
-- AbstractInstr → x86-32 Program
--
-- Each AbstractInstr compiles to a short x86-32 instruction sequence.
-- The mapping follows the SlotMachine operational semantics.
--
-- Key register mapping:
--   Input  → ecx
--   Output → eax
--   Frame  → ebp
--   Closure → ebx (environment pointer)
------------------------------------------------------------------------

compile-abstract : AbstractInstr → Program

-- mov-to-output: Output := Input
-- x86-32: mov eax, ecx
compile-abstract mov-to-output =
  mov (reg eax) (reg ecx) ∷ []

-- mov-to-input: Input := Output (compose bridge)
-- x86-32: mov ecx, eax
compile-abstract mov-to-input =
  mov (reg ecx) (reg eax) ∷ []

-- load-indirect: Output := *Input
-- x86-32: mov eax, [ecx]
compile-abstract load-indirect =
  mov (reg eax) (mem (base ecx)) ∷ []

-- load-indirect-suc: Output := *(sucLoc Input)
-- x86-32: mov eax, [ecx + 4]
compile-abstract load-indirect-suc =
  mov (reg eax) (mem (base+disp ecx slot-size)) ∷ []

-- load-from-slot: Output := stack[slot]
-- x86-32: mov eax, [ebp + slot*4]
compile-abstract (load-from-slot n) =
  mov (reg eax) (mem (base+disp ebp (slot-to-disp n))) ∷ []

-- store-at-slot: stack[slot] := Output
-- x86-32: mov [ebp + slot*4], eax
compile-abstract (store-at-slot n) =
  mov (mem (base+disp ebp (slot-to-disp n))) (reg eax) ∷ []

-- store-indirect: *Input := Output
-- x86-32: mov [ecx], eax
compile-abstract store-indirect =
  mov (mem (base ecx)) (reg eax) ∷ []

-- store-indirect-suc: *(sucLoc Input) := Output
-- x86-32: mov [ecx + 4], eax
compile-abstract store-indirect-suc =
  mov (mem (base+disp ecx slot-size)) (reg eax) ∷ []

-- lea-slot: Output := &stack[slot]
-- x86-32: lea eax, [ebp + slot*4]
compile-abstract (lea-slot n) =
  lea eax (base+disp ebp (slot-to-disp n)) ∷ []

-- restore-input: Input := stack[slot]
-- x86-32: mov ecx, [ebp + slot*4]
compile-abstract (restore-input n) =
  mov (reg ecx) (mem (base+disp ebp (slot-to-disp n))) ∷ []

-- instr-alloc-stack: allocate N slots on stack
-- x86-32: sub esp, N*4
compile-abstract (instr-alloc-stack n) =
  sub (reg esp) (imm (slots n)) ∷ []

-- instr-dealloc-stack: deallocate N slots from stack
-- x86-32: add esp, N*4
compile-abstract (instr-dealloc-stack n) =
  add (reg esp) (imm (slots n)) ∷ []

-- instr-push-frame: push new frame with capacity N
-- x86-32: push ebp; mov ebp, esp; sub esp, N*4
compile-abstract (instr-push-frame n) =
  push (reg ebp) ∷
  mov (reg ebp) (reg esp) ∷
  sub (reg esp) (imm (slots n)) ∷ []

-- instr-pop-frame: restore caller frame
-- x86-32: mov esp, ebp; pop ebp
compile-abstract instr-pop-frame =
  mov (reg esp) (reg ebp) ∷
  pop ebp ∷ []

-- instr-call-closure: jump to closure code (via indirect call)
-- Closure in ebx, code-ptr at [ebx + 4]
-- x86-32: call [ebx + 4]
compile-abstract instr-call-closure =
  call (mem (base+disp ebx slot-size)) ∷ []

------------------------------------------------------------------------
-- Trace compilation: compile a whole trace to x86-32
------------------------------------------------------------------------

compile-trace : AbstractTrace → Program
compile-trace [] = []
compile-trace (i ∷ is) = compile-abstract i ++ compile-trace is