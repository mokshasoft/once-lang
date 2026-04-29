-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.AbstractToRiscV
--
-- Compilation from AbstractInstr to RISC-V 64 instructions.
--
-- Each AbstractInstr compiles to a short sequence of RV64 instructions.
-- This module provides the mapping; simulation proofs are in
-- DirectSimulation.agda.
--
-- RISC-V calling convention (LP64):
--   - a0-a7: argument registers
--   - s0 (fp): frame pointer (callee-saved)
--   - s1-s11: callee-saved registers
--   - sp: stack pointer
--   - ra: return address
--
-- Once's register mapping:
--   - a0: Input AND Output register
--     (RISC-V LP64 uses a0 for both first argument and return value.
--      This means id, fold, unfold, arr compile to ZERO instructions!)
--   - s0 (fp): frame pointer
--   - s1: closure/environment pointer (callee-saved)
--   - t0-t2: scratch registers for complex operations
--
-- NOTE: Unlike x86 (separate rdi/rax), RISC-V can use a0 for both
-- input and output because they're the same in the LP64 ABI.
-- For operations that need both an address AND a value (like
-- store-indirect), we use t0 as a temporary.
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.AbstractToRiscV where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_)

-- Import RISC-V syntax
open import Once.CCC.Target.RiscV64.Syntax
  using (Reg; zero; ra; sp; fp; a0; a1; a2; a3; a4; a5; a6; a7;
         s1; s2; s3; s4; t0; t1; t2; t3; t4;
         Instr; ld; sd; add; sub; addi; li; auipc; mv;
         beq; bne; jal; jalr; j; ret; call; call-sym; nop; unimp; label;
         Program; slot-size; slots)
open import Once.CCC.SigOp.Info using (SigOpInfo)

-- Import AbstractInstr from SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; Slot;
         mov-to-output; mov-to-input; load-indirect; load-indirect-suc;
         load-from-slot; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input;
         instr-alloc-stack; instr-dealloc-stack;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         worklist-init; worklist-push; worklist-pop; worklist-check;
         instr-reclaim-to; instr-sigop)

------------------------------------------------------------------------
-- Slot to displacement conversion
--
-- Convert a logical slot number to a RISC-V displacement.
-- Slots are indexed from current frame, growing upward (higher addresses).
------------------------------------------------------------------------

slot-to-disp : Slot → ℕ
slot-to-disp n = n *ℕ slot-size

------------------------------------------------------------------------
-- AbstractInstr → RISC-V Program
--
-- Each AbstractInstr compiles to a short RV64 instruction sequence.
-- The mapping follows the SlotMachine operational semantics.
--
-- Register mapping (optimized for RISC-V LP64):
--   Input  → a0 (primary value register)
--   Output → a0 (same! a0 serves both roles)
--   Frame  → fp (s0)
--   Closure → s1 (environment pointer, callee-saved)
--   Temp   → t0 (when we need separate addr/value)
------------------------------------------------------------------------

compile-abstract : AbstractInstr → Program

-- mov-to-output: Output := Input
-- Copy t0 (Input) to a0 (Output)
compile-abstract mov-to-output =
  mv a0 t0 ∷ []

-- mov-to-input: Input := Output
-- Copy a0 (Output) to t0 (Input)
compile-abstract mov-to-input =
  mv t0 a0 ∷ []

-- load-indirect: Output := *Input
-- t0 holds address (Input), load value into a0 (Output)
-- RV64: ld a0, 0(t0)
compile-abstract load-indirect =
  ld a0 t0 0 ∷ []

-- load-indirect-suc: Output := *(sucLoc Input)
-- RV64: ld a0, 8(t0)
compile-abstract load-indirect-suc =
  ld a0 t0 slot-size ∷ []

-- load-from-slot: Output := stack[slot]
-- RV64: ld a0, slot*8(fp)
compile-abstract (load-from-slot n) =
  ld a0 fp (slot-to-disp n) ∷ []

-- store-at-slot: stack[slot] := Output
-- RV64: sd a0, slot*8(fp)
compile-abstract (store-at-slot n) =
  sd a0 fp (slot-to-disp n) ∷ []

-- store-indirect: *Input := Output
-- Need address and value, but both are a0!
-- Solution: address was saved to t0 by preceding instruction
-- RV64: sd a0, 0(t0)
compile-abstract store-indirect =
  sd a0 t0 0 ∷ []

-- store-indirect-suc: *(sucLoc Input) := Output
-- RV64: sd a0, 8(t0)
compile-abstract store-indirect-suc =
  sd a0 t0 slot-size ∷ []

-- lea-slot: Output := &stack[slot]
-- RV64: addi a0, fp, slot*8
compile-abstract (lea-slot n) =
  addi a0 fp (+ (slot-to-disp n)) ∷ []

-- restore-input: Input := stack[slot]
-- This restores a saved address for use by store-indirect
-- We load into t0 (not a0) to preserve current value
-- RV64: ld t0, slot*8(fp)
compile-abstract (restore-input n) =
  ld t0 fp (slot-to-disp n) ∷ []

-- instr-alloc-stack: allocate N slots on stack
-- RV64: addi sp, sp, -N*8
compile-abstract (instr-alloc-stack n) =
  addi sp sp (Data.Integer.-_ (+ (slots n))) ∷ []
  where import Data.Integer

-- instr-dealloc-stack: deallocate N slots from stack
-- RV64: addi sp, sp, N*8
compile-abstract (instr-dealloc-stack n) =
  addi sp sp (+ (slots n)) ∷ []

-- instr-push-frame: push new frame with capacity N
-- RV64: addi sp, sp, -8    (reserve space for old fp)
--       sd fp, 0(sp)       (save old fp)
--       mv fp, sp          (set new fp)
--       addi sp, sp, -N*8  (reserve space for N slots)
compile-abstract (instr-push-frame n) =
  addi sp sp (Data.Integer.-_ (+ slot-size)) ∷
  sd fp sp 0 ∷
  mv fp sp ∷
  addi sp sp (Data.Integer.-_ (+ (slots n))) ∷ []
  where import Data.Integer

-- instr-pop-frame: restore caller frame
-- RV64: mv sp, fp         (restore sp to frame pointer)
--       ld fp, 0(sp)      (restore old fp)
--       addi sp, fp, 8    (set sp to fp+8, popping saved fp)
-- Note: we use fp as base (not sp) to distinguish from dealloc-stack
compile-abstract instr-pop-frame =
  mv sp fp ∷
  ld fp sp 0 ∷
  addi sp fp (+ slot-size) ∷ []

-- instr-call-closure: jump to closure code (via indirect call)
-- Closure in s1, code-ptr at [s1 + 8]
-- RV64: ld t0, 8(s1)      (load code pointer)
--       jalr ra, t0, 0    (call through t0)
compile-abstract instr-call-closure =
  ld t0 s1 slot-size ∷
  jalr ra t0 0 ∷ []

------------------------------------------------------------------------
-- Worklist operations (for Cata/recursion scheme support)
--
-- These are placeholders for the recursive worklist-based iteration.
-- A full implementation would include counter management.
------------------------------------------------------------------------

-- worklist-init: Initialize worklist (no-op in simplified model)
-- RV64: (empty - no runtime effect)
compile-abstract (worklist-init n) = []

-- worklist-push: Push Output to worklist at slot
-- RV64: sd a0, slot*8(fp)  (same as store-at-slot)
compile-abstract (worklist-push n) =
  sd a0 fp (slot-to-disp n) ∷ []

-- worklist-pop: Pop from worklist at slot to Output
-- RV64: ld a0, slot*8(fp)  (same as load-from-slot)
compile-abstract (worklist-pop n) =
  ld a0 fp (slot-to-disp n) ∷ []

-- worklist-check: Check if worklist is empty (no-op in simplified model)
-- RV64: (empty - proofs use Star-based reasoning, not loop mechanics)
compile-abstract (worklist-check n) = []

-- instr-reclaim-to: set next-slot to n (allocation bookkeeping only)
-- RV64: (empty - pure AllocState update, no machine effect)
compile-abstract (instr-reclaim-to n) = []

-- Plan 0.11: name-agnostic SigOp codegen.
-- Emit a single symbolic call; linker resolves the name at build time
-- to the externally-defined function body. CCC stays name-agnostic.
compile-abstract (instr-sigop si) = call-sym (SigOpInfo.name si) ∷ []

------------------------------------------------------------------------
-- Trace compilation: compile a whole trace to RISC-V
------------------------------------------------------------------------

compile-trace : AbstractTrace → Program
compile-trace [] = []
compile-trace (i ∷ is) = compile-abstract i ++ compile-trace is