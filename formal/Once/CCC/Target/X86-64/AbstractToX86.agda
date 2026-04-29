-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.AbstractToX86
--
-- Compilation from AbstractInstr to x86 instructions.
--
-- Each AbstractInstr compiles to a short sequence of x86 instructions.
-- This module provides the mapping; simulation proofs are in
-- AbstractSimulation.agda.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.AbstractToX86 where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.List using (List; []; _∷_; _++_)

-- Plan 0.10 Phase B: SigOp dispatch.
import Once.CCC.Target.X86-64.CodeGen.Compile as CompileX86-64

-- Import X86 syntax
open import Once.CCC.Target.X86-64.Syntax
  using (Reg; rax; rbx; rcx; rdx; rdi; rsi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         Mem; base; base+disp; rip+disp; rip+label;
         Operand; reg; mem; imm;
         Instr; mov; lea; add; sub; cmp; push; pop; call; ret; jmp; jne; label; ud2;
         Program; slot-size; slots)

-- Import AbstractInstr from SMCore
open import Once.CCC.Machine.SMCore
open import Once.CCC.SigOp.Info using (SigOpInfo)
  using (AbstractInstr; AbstractTrace; Slot;
         mov-to-output; mov-to-input; load-indirect; load-indirect-suc;
         load-from-slot; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input;
         instr-alloc-stack; instr-dealloc-stack;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         worklist-init; worklist-push; worklist-pop; worklist-check;
         instr-reclaim-to; instr-sigop; instr-save-closure-reg)

------------------------------------------------------------------------
-- Slot to displacement conversion
--
-- Convert a logical slot number to an x86 displacement.
-- Slots are indexed from current frame, growing upward (higher addresses).
------------------------------------------------------------------------

slot-to-disp : Slot → ℕ
slot-to-disp n = n *ℕ slot-size

------------------------------------------------------------------------
-- AbstractInstr → x86 Program
--
-- Each AbstractInstr compiles to a short x86 instruction sequence.
-- The mapping follows the SlotMachine operational semantics.
------------------------------------------------------------------------

compile-abstract : AbstractInstr → Program

-- mov-to-output: Output := Input
-- x86: mov rax, rdi
compile-abstract mov-to-output =
  mov (reg rax) (reg rdi) ∷ []

-- mov-to-input: Input := Output (compose bridge)
-- x86: mov rdi, rax
compile-abstract mov-to-input =
  mov (reg rdi) (reg rax) ∷ []

-- load-indirect: Output := *Input
-- x86: mov rax, [rdi]
compile-abstract load-indirect =
  mov (reg rax) (mem (base rdi)) ∷ []

-- load-indirect-suc: Output := *(sucLoc Input)
-- x86: mov rax, [rdi + 8]
compile-abstract load-indirect-suc =
  mov (reg rax) (mem (base+disp rdi slot-size)) ∷ []

-- load-from-slot: Output := stack[slot]
-- x86: mov rax, [rbp + slot*8]
compile-abstract (load-from-slot n) =
  mov (reg rax) (mem (base+disp rbp (slot-to-disp n))) ∷ []

-- store-at-slot: stack[slot] := Output
-- x86: mov [rbp + slot*8], rax
compile-abstract (store-at-slot n) =
  mov (mem (base+disp rbp (slot-to-disp n))) (reg rax) ∷ []

-- store-indirect: *Input := Output
-- x86: mov [rdi], rax
compile-abstract store-indirect =
  mov (mem (base rdi)) (reg rax) ∷ []

-- store-indirect-suc: *(sucLoc Input) := Output
-- x86: mov [rdi + 8], rax
compile-abstract store-indirect-suc =
  mov (mem (base+disp rdi slot-size)) (reg rax) ∷ []

-- lea-slot: Output := &stack[slot]
-- x86: lea rax, [rbp + slot*8]
compile-abstract (lea-slot n) =
  lea rax (base+disp rbp (slot-to-disp n)) ∷ []

-- restore-input: Input := stack[slot]
-- x86: mov rdi, [rbp + slot*8]
compile-abstract (restore-input n) =
  mov (reg rdi) (mem (base+disp rbp (slot-to-disp n))) ∷ []

-- instr-alloc-stack: allocate N slots on stack
-- x86: sub rsp, N*8
compile-abstract (instr-alloc-stack n) =
  sub (reg rsp) (imm (slots n)) ∷ []

-- instr-dealloc-stack: deallocate N slots from stack
-- x86: add rsp, N*8
compile-abstract (instr-dealloc-stack n) =
  add (reg rsp) (imm (slots n)) ∷ []

-- instr-push-frame: push new frame with capacity N
-- x86: push rbp; mov rbp, rsp; sub rsp, N*8
compile-abstract (instr-push-frame n) =
  push (reg rbp) ∷
  mov (reg rbp) (reg rsp) ∷
  sub (reg rsp) (imm (slots n)) ∷ []

-- instr-pop-frame: restore caller frame
-- x86: mov rsp, rbp; pop rbp
compile-abstract instr-pop-frame =
  mov (reg rsp) (reg rbp) ∷
  pop rbp ∷ []

-- instr-call-closure: jump to closure code (via indirect call)
-- Closure in r12, code-ptr at [r12 + 8]
-- x86: call [r12 + 8]
compile-abstract instr-call-closure =
  call (mem (base+disp r12 slot-size)) ∷ []

------------------------------------------------------------------------
-- OCP-0003: Worklist Instructions
--
-- Worklist operations support loop-based tree traversal at runtime.
-- These are simplified implementations matching the abstract semantics.
-- A full implementation would include counter management.
------------------------------------------------------------------------

-- worklist-init: Initialize worklist (no-op in simplified model)
-- x86: (empty - no runtime effect)
compile-abstract (worklist-init n) = []

-- worklist-push: Push Output to worklist at slot
-- x86: mov [rbp + slot*8], rax  (same as store-at-slot)
compile-abstract (worklist-push n) =
  mov (mem (base+disp rbp (slot-to-disp n))) (reg rax) ∷ []

-- worklist-pop: Pop from worklist at slot to Output
-- x86: mov rax, [rbp + slot*8]  (same as load-from-slot)
compile-abstract (worklist-pop n) =
  mov (reg rax) (mem (base+disp rbp (slot-to-disp n))) ∷ []

-- worklist-check: Check if worklist is empty (no-op in simplified model)
-- x86: (empty - proofs use Star-based reasoning, not loop mechanics)
compile-abstract (worklist-check n) = []

-- instr-reclaim-to: set next-slot to n (allocation bookkeeping only)
-- x86: (empty - pure AllocState update, no machine effect)
compile-abstract (instr-reclaim-to n) = []

-- Plan 0.10 Phase B: SigOp dispatch.
-- Delegates to the existing per-name handler in CodeGen/Compile.
compile-abstract (instr-sigop si) =
  CompileX86-64.compile-sigOp (SigOpInfo.name si)

-- Plan 0.11: const literal codegen (per-primitive immediate load).
-- Delegates to the per-primitive helper in CodeGen/Compile.
compile-abstract (instr-load-const p v) =
  CompileX86-64.compile-const p v

-- Plan 0.2.4.2 Phase A: load closure-body label address into rax.
-- `lea .L_thunk_<n>(%rip), %rax` — RIP-relative load of the body's
-- absolute address. The body label is emitted by per-function
-- codegen (Phase B + C) inside the same parent function symbol.
compile-abstract (instr-load-code-addr n) =
  lea rax (rip+label n) ∷ []

-- Plan 0.2.4.2 Phase D follow-up: save Input register to the
-- closure register. On x86-64 SysV: rdi holds the apply argument
-- (Input), r12 is reserved as the closure pointer for the indirect
-- call `call *0x8(%r12)`.
compile-abstract instr-save-closure-reg =
  mov (reg r12) (reg rdi) ∷ []

------------------------------------------------------------------------
-- Trace compilation: compile a whole trace to x86
------------------------------------------------------------------------

compile-trace : AbstractTrace → Program
compile-trace [] = []
compile-trace (i ∷ is) = compile-abstract i ++ compile-trace is