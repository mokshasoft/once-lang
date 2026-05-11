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

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.List using (List; []; _∷_; _++_)

-- Plan 0.10 Phase B: SigOp dispatch.
import Once.CCC.Target.X86-64.CodeGen.Compile as CompileX86-64

open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- Import X86 syntax
open import Once.CCC.Target.X86-64.Syntax
  using (Reg; rax; rbx; rcx; rdx; rdi; rsi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         Mem; base; base+disp; rip+disp; rip+label;
         Operand; reg; mem; imm;
         Instr; mov; lea; add; sub; cmp; push; pop; call; ret; jmp; je; jne; label; ud2;
         Program; slot-size; slots)

-- Import AbstractInstr from SMCore
open import Once.CCC.Machine.SMCore
open import Once.CCC.SigOp.Info using (SigOpInfo)
  using (AbstractInstr; AbstractTrace; Slot;
         mov-to-output; mov-to-input;
         mov-output-to-input2; mov-input2-to-output;
         load-indirect; load-indirect-suc;
         load-from-slot; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input;
         instr-alloc-stack; instr-dealloc-stack;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         worklist-init; worklist-push; worklist-pop; worklist-check;
         instr-reclaim-to; instr-sigop; instr-save-closure-reg;
         instr-load-tag-lit)

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

-- mov-to-output: Output := Input1
-- x86: mov rax, rdi
compile-abstract mov-to-output =
  mov (reg rax) (reg rdi) ∷ []

-- mov-to-input: Input1 := Output (compose bridge)
-- x86: mov rdi, rax
compile-abstract mov-to-input =
  mov (reg rdi) (reg rax) ∷ []

-- mov-output-to-input2: Input2 := Output (Stage C split-input setup)
-- x86 SysV calling convention: rsi = second integer argument register
compile-abstract mov-output-to-input2 =
  mov (reg rsi) (reg rax) ∷ []

-- mov-input2-to-output: Output := Input2 (Stage C body-side snd)
compile-abstract mov-input2-to-output =
  mov (reg rax) (reg rsi) ∷ []

-- load-indirect: Output := *Input1
-- x86: mov rax, [rdi]
compile-abstract load-indirect =
  mov (reg rax) (mem (base rdi)) ∷ []

-- load-indirect-suc: Output := *(sucLoc Input1)
-- x86: mov rax, [rdi + 8]
compile-abstract load-indirect-suc =
  mov (reg rax) (mem (base+disp rdi slot-size)) ∷ []

-- load-from-slot: Output := stack[slot]
-- x86: mov rax, [rsp + slot*8]
-- Plan 0.2.4.5 D1 (frameless): all slot accesses are %rsp-relative.
-- Each compiled IR function shifts %rsp by its own stack-budget at
-- entry (sub) and back at exit (add), so slot offsets are private to
-- that function's frame. %rbp is no longer used.
compile-abstract (load-from-slot n) =
  mov (reg rax) (mem (base+disp rsp (slot-to-disp n))) ∷ []

-- store-at-slot: stack[slot] := Output
-- x86: mov [rsp + slot*8], rax
compile-abstract (store-at-slot n) =
  mov (mem (base+disp rsp (slot-to-disp n))) (reg rax) ∷ []

-- store-indirect: *Input1 := Output
-- x86: mov [rdi], rax
compile-abstract store-indirect =
  mov (mem (base rdi)) (reg rax) ∷ []

-- store-indirect-suc: *(sucLoc Input1) := Output
-- x86: mov [rdi + 8], rax
compile-abstract store-indirect-suc =
  mov (mem (base+disp rdi slot-size)) (reg rax) ∷ []

-- lea-slot: Output := &stack[slot]
-- x86: lea rax, [rsp + slot*8]
compile-abstract (lea-slot n) =
  lea rax (base+disp rsp (slot-to-disp n)) ∷ []

-- restore-input: Input1 := stack[slot]
-- x86: mov rdi, [rsp + slot*8]
compile-abstract (restore-input n) =
  mov (reg rdi) (mem (base+disp rsp (slot-to-disp n))) ∷ []

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
-- x86: mov [rsp + slot*8], rax  (same as store-at-slot)
compile-abstract (worklist-push n) =
  mov (mem (base+disp rsp (slot-to-disp n))) (reg rax) ∷ []

-- worklist-pop: Pop from worklist at slot to Output
-- x86: mov rax, [rsp + slot*8]  (same as load-from-slot)
compile-abstract (worklist-pop n) =
  mov (reg rax) (mem (base+disp rsp (slot-to-disp n))) ∷ []

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

-- Plan 0.2.4.2 Phase D follow-up: save Input1 register to the
-- closure register. On x86-64 SysV: rdi holds the apply argument
-- (Input1), r12 is reserved as the closure pointer for the indirect
-- call `call *0x8(%r12)`.
compile-abstract instr-save-closure-reg =
  mov (reg r12) (reg rdi) ∷ []

-- Plan 0.13.1 Phase 1: tag literal — write SV-Tag n to Output (rax).
-- x86: mov $n, %rax (loads the small natural-number tag into rax as
-- an immediate; the StoredValue's SV-Tag wrapper is type-level only).
compile-abstract (instr-load-tag-lit n) =
  mov (reg rax) (imm n) ∷ []

-- Plan 0.13.1 Phase 1: case-on-tag — single-instruction view only.
-- The real lowering with cmp/je/jmp/labels for the sub-traces is in
-- compile-trace-cnt below (which has the label counter to thread).
-- This single-instruction view emits ud2 as a sentinel — it should
-- never appear in the output of compile-trace-cnt (which intercepts
-- the instruction before delegating here). If it does, runtime traps.
compile-abstract (instr-case-on-tag _ _) =
  ud2 ∷ []

------------------------------------------------------------------------
-- Trace compilation: compile a whole trace to x86
--
-- Plan 0.13.1 Phase 5: label-threading variant. case-on-tag in the
-- abstract trace expands to a 5-line dispatch sequence:
--
--   cmpq $0, (%rdi)        ; sum value at *Input1; tag at offset 0
--   je .L<inl-lbl>
--   <g-trace compiled>
--   jmp .L<end-lbl>
--   .L<inl-lbl>:
--   <f-trace compiled>
--   .L<end-lbl>:
--
-- Each case consumes 2 fresh labels. compile-trace-cnt threads a
-- counter through the trace; case-on-tag's sub-traces recurse with
-- the updated counter so nested cases get unique labels.
------------------------------------------------------------------------

compile-trace-cnt : ℕ → AbstractTrace → ℕ × Program

compile-trace-cnt n [] = n , []
compile-trace-cnt n (instr-case-on-tag f g ∷ rest) =
  let lbl-inl = n
      lbl-end = suc n
      (n1 , pf) = compile-trace-cnt (suc (suc n)) f
      (n2 , pg) = compile-trace-cnt n1 g
      (n3 , pr) = compile-trace-cnt n2 rest
      dispatch  = cmp (mem (base+disp rdi 0)) (imm 0) ∷
                  je lbl-inl ∷
                  pg ++
                  jmp lbl-end ∷
                  label lbl-inl ∷
                  pf ++
                  label lbl-end ∷ []
  in n3 , dispatch ++ pr
compile-trace-cnt n (i ∷ rest) =
  let (n1 , pr) = compile-trace-cnt n rest
  in n1 , compile-abstract i ++ pr

-- Backward-compatible non-threaded variant — direct foldr.
-- Doesn't dispatch case-on-tag (emits ud2 for it via compile-abstract).
-- For Layer 2 use compile-trace-cnt with proper label threading.
compile-trace : AbstractTrace → Program
compile-trace [] = []
compile-trace (i ∷ is) = compile-abstract i ++ compile-trace is