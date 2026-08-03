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
--   - a0: Input1 AND Output register
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

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Product using (_×_; _,_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_)
open import Once.Target.Symbol using (once-symbol; once-symbol-path)

-- Import RISC-V syntax
open import Once.CCC.Target.RiscV64.Syntax
  using (Reg; zero; ra; sp; fp; a0; a1; a2; a3; a4; a5; a6; a7;
         s1; s2; s3; s4; t0; t1; t2; t3; t4;
         Instr; ld; sd; add; sub; addi; li; auipc; lla; mv;
         beq; bne; jal; jalr; j; ret; call; call-sym; nop; unimp; label;
         Program; slot-size; slots)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Type using (fits-int; fits-float)

-- Import AbstractInstr from SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; Slot;
         mov-to-output; mov-to-input;
         mov-output-to-input2; mov-input2-to-output;
         load-indirect; load-indirect-suc;
         load-from-slot; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input; lea-indexed;
         instr-alloc-stack; instr-alloc-heap; instr-dealloc-stack;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         worklist-init; worklist-push; worklist-pop; worklist-check;
         instr-reclaim-to; instr-sigop; instr-load-const; instr-load-code-addr;
         instr-save-closure-reg;
         instr-load-tag-lit; instr-case-on-tag; instr-loop; instr-reg-op; instr-ctrl;
         -- RegOp constructors (Plan 0.53 reg-op lowering)
         scratch-one; scratch-zero; scratch-dec; scratch-load-count; count-zero; count-inc;
         -- FlatCtrl constructors (Plan 0.53 flat-control lowering)
         c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero; c-thunk; c-ret)

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
--   Input1  → a0 (primary value register)
--   Output → a0 (same! a0 serves both roles)
--   Frame  → fp (s0)
--   Closure → s1 (environment pointer, callee-saved)
--   Temp   → t0 (when we need separate addr/value)
------------------------------------------------------------------------

compile-abstract : AbstractInstr → Program

-- mov-to-output: Output := Input1
-- Copy t0 (Input1) to a0 (Output)
compile-abstract mov-to-output =
  mv a0 t0 ∷ []

-- mov-to-input: Input1 := Output
-- Copy a0 (Output) to t0 (Input1)
compile-abstract mov-to-input =
  mv t0 a0 ∷ []

-- mov-output-to-input2: Input2 := Output (Stage C split-input setup)
-- RV64 LP64 calling convention: a1 = second integer argument register
compile-abstract mov-output-to-input2 =
  mv a1 a0 ∷ []

-- mov-input2-to-output: Output := Input2 (Stage C body-side snd)
compile-abstract mov-input2-to-output =
  mv a0 a1 ∷ []

-- load-indirect: Output := *Input1
-- t0 holds address (Input1), load value into a0 (Output)
-- RV64: ld a0, 0(t0)
compile-abstract load-indirect =
  ld a0 t0 0 ∷ []

-- load-indirect-suc: Output := *(sucLoc Input1)
-- RV64: ld a0, 8(t0)
compile-abstract load-indirect-suc =
  ld a0 t0 slot-size ∷ []

-- load-from-slot: Output := stack[slot]
-- Plan 0.53: frameless, sp-relative (match x86-64's %rsp model).
-- RV64: ld a0, slot*8(sp)
compile-abstract (load-from-slot n) =
  ld a0 sp (slot-to-disp n) ∷ []

-- store-at-slot: stack[slot] := Output
-- RV64: sd a0, slot*8(sp)
compile-abstract (store-at-slot n) =
  sd a0 sp (slot-to-disp n) ∷ []

-- store-indirect: *Input1 := Output
-- Need address and value, but both are a0!
-- Solution: address was saved to t0 by preceding instruction
-- RV64: sd a0, 0(t0)
compile-abstract store-indirect =
  sd a0 t0 0 ∷ []

-- store-indirect-suc: *(sucLoc Input1) := Output
-- RV64: sd a0, 8(t0)
compile-abstract store-indirect-suc =
  sd a0 t0 slot-size ∷ []

-- lea-slot: Output := &stack[slot]
-- RV64: addi a0, sp, slot*8  (Plan 0.53 frameless)
compile-abstract (lea-slot n) =
  addi a0 sp (+ (slot-to-disp n)) ∷ []

-- restore-input: Input1 := stack[slot]
-- This restores a saved address for use by store-indirect
-- We load into t0 (not a0) to preserve current value
-- RV64: ld t0, slot*8(sp)  (Plan 0.53 frameless)
compile-abstract (restore-input n) =
  ld t0 sp (slot-to-disp n) ∷ []

-- lea-indexed: Input1 := &(base + 8*idx). base = SV-Ptr at slot n, idx =
-- Scratch (s3). Plan 0.53: mirror x86-64 — no shift instr in this model, so
-- synthesize 8*idx by three doublings in t1, then add to the base pointer.
-- Result lands in t0 (Input1). RV64:
--   ld  t0, n*8(sp)   ; t0 := base ptr
--   mv  t1, s3        ; t1 := idx (Scratch)
--   add t1, t1, t1    ; ×2
--   add t1, t1, t1    ; ×4
--   add t1, t1, t1    ; ×8  → t1 = 8*idx
--   add t0, t0, t1    ; t0 := base + 8*idx
compile-abstract (lea-indexed n) =
  ld t0 sp (slot-to-disp n) ∷
  mv t1 s3 ∷
  add t1 t1 t1 ∷
  add t1 t1 t1 ∷
  add t1 t1 t1 ∷
  add t0 t0 t1 ∷ []

-- instr-alloc-stack: allocate N slots on stack
-- RV64: addi sp, sp, -N*8
compile-abstract (instr-alloc-stack n) =
  addi sp sp (Data.Integer.-_ (+ (slots n))) ∷ []
  where import Data.Integer

-- instr-alloc-heap: allocate a heap cell.
-- Plan 0.53: mirror x86-64's r15 bump allocator. s2 holds the heap top
-- pointer (initialized by _start to once_heap_base). To allocate n slots:
--   mv   a0, s2       ; Output := current heap top
--   addi s2, s2, n*8  ; bump heap top by n words
-- The freshly-allocated block lives at the OLD s2 value (now in a0).
compile-abstract (instr-alloc-heap n) =
  mv a0 s2 ∷
  addi s2 s2 (+ (slots n)) ∷ []

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

-- instr-call-closure: jump to closure code (via indirect call).
-- Closure in s1, code-ptr at [s1 + 8]. Plan 0.53: load the code pointer
-- into t1 (NOT t0) — t0 carries the Input1/argument pointer that the callee
-- reads via `ld a0, 8(t0)`, and it must survive the call. This mirrors
-- x86-64's `call *0x8(%r12)`, a memory-indirect call that never clobbers the
-- argument register %rdi.
-- RV64: ld t1, 8(s1)      (load code pointer into scratch t1)
--       jalr ra, t1, 0    (call through t1; t0 preserved for the callee)
compile-abstract instr-call-closure =
  ld t1 s1 slot-size ∷
  jalr ra t1 0 ∷ []

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
-- RV64: sd a0, slot*8(sp)  (same as store-at-slot)
compile-abstract (worklist-push n) =
  sd a0 sp (slot-to-disp n) ∷ []

-- worklist-pop: Pop from worklist at slot to Output
-- RV64: ld a0, slot*8(sp)  (same as load-from-slot)
compile-abstract (worklist-pop n) =
  ld a0 sp (slot-to-disp n) ∷ []

-- worklist-check: Check if worklist is empty (no-op in simplified model)
-- RV64: (empty - proofs use Star-based reasoning, not loop mechanics)
compile-abstract (worklist-check n) = []

-- instr-reclaim-to: set next-slot to n (allocation bookkeeping only)
-- RV64: (empty - pure AllocState update, no machine effect)
compile-abstract (instr-reclaim-to n) = []

-- Plan 0.11: name-agnostic SigOp codegen.
-- Emit a single symbolic call; linker resolves the name at build time
-- to the externally-defined function body. CCC stays name-agnostic.
compile-abstract (instr-sigop si) = call-sym (once-symbol-path (SigOpInfo.name si)) ∷ []
-- Plan 0.53: const literal. Mirror x86-64's compile-const:
-- fits-int loads the immediate into Output (a0); float still trapped.
compile-abstract (instr-load-const fits-int   v) = li a0 (+ v) ∷ []
compile-abstract (instr-load-const fits-float _) = unimp ∷ []
-- Plan 0.53: closure-body code-addr load. Mirror x86-64's
-- `lea .L_thunk_n(%rip), %rax` — load the body label address into Output.
compile-abstract (instr-load-code-addr n) = lla a0 n ∷ []
-- Plan 0.2.4.2: save closure-register. On RV64 the closure pointer
-- lives in s1; Input1 is in t0. Move t0 into s1 so the subsequent
-- `ld t0, 8(s1); jalr ra, t0, 0` resolves correctly.
compile-abstract instr-save-closure-reg =
  mv s1 t0 ∷ []

-- Plan 0.53: tag literal — write the tag n to Output (a0). Mirror x86-64's
-- `mov rax, imm n`.
compile-abstract (instr-load-tag-lit n) = li a0 (+ n) ∷ []
-- case-on-tag / loop are STRUCTURED nodes carrying sub-traces; they are
-- expanded (with fresh labels + branches) by `compile-trace-cnt` below, not
-- here. This single-instruction view is a sentinel (should never be reached
-- once irToAsm/irToBodies route through compile-trace-cnt).
compile-abstract (instr-case-on-tag _ _) = unimp ∷ []
compile-abstract (instr-loop _) = unimp ∷ []
-- Plan 0.53 (mirror x86-64 M5): register pokes. Scratch = s3, Input2 = s4
-- (callee-saved, otherwise unused by this codegen).
compile-abstract (instr-reg-op scratch-one)        = li s3 (+ 1) ∷ []
compile-abstract (instr-reg-op scratch-zero)       = li s3 (+ 0) ∷ []
compile-abstract (instr-reg-op scratch-dec)        = addi s3 s3 (Data.Integer.-_ (+ 1)) ∷ []
  where import Data.Integer
compile-abstract (instr-reg-op scratch-load-count) = mv s3 s4 ∷ []
compile-abstract (instr-reg-op count-zero)        = li s4 (+ 0) ∷ []
compile-abstract (instr-reg-op count-inc)         = addi s4 s4 (+ 1) ∷ []
-- Plan 0.53 (mirror x86-64 M3/0.34): flat control lowers 1-to-1. Labels/jumps
-- reuse RV64's `.L<n>` label space; the conditional branches are single
-- compare-and-branch (no flags on RISC-V). Input1 pointer = t0; Scratch = s3.
compile-abstract (instr-ctrl (c-label n))               = label n ∷ []
compile-abstract (instr-ctrl (c-jmp n))                 = j n ∷ []
-- Plan 0.63: closure-body entry / return. As on x86-32, this target's
-- labels are bare ℕ; step 2 reconciles the body-entry name with
-- `.L_thunk_<n>` when `c-thunk` gains a producer.
compile-abstract (instr-ctrl (c-thunk n b))             = label n ∷ addi sp sp (Data.Integer.-_ (+ (slots b))) ∷ []
  where import Data.Integer
compile-abstract (instr-ctrl (c-ret b))                 = addi sp sp (+ (slots b)) ∷ ret ∷ []
compile-abstract (instr-ctrl (c-branch-scratch-zero n)) = beq s3 zero n ∷ []
compile-abstract (instr-ctrl (c-branch-tag-zero n))     = ld t1 t0 0 ∷ beq t1 zero n ∷ []

------------------------------------------------------------------------
-- Trace compilation: compile a whole trace to RISC-V
------------------------------------------------------------------------

-- Plan 0.53: label-threading trace compiler (mirror x86-64's
-- compile-trace-cnt). Structured `case-on-tag` / `instr-loop` nodes carry
-- sub-traces that must be recursively compiled and bracketed by fresh labels
-- + branches; the plain `compile-trace` foldr would DROP the sub-traces (it
-- maps compile-abstract, which sees only the sentinel). Each case/loop
-- consumes 2 fresh labels; the counter threads through so nested structures
-- get unique labels. Input1 pointer = t0 (tag at 0(t0)); loop counter = s3.
compile-trace-cnt : ℕ → AbstractTrace → ℕ × Program
compile-trace-cnt n [] = n , []
compile-trace-cnt n (instr-loop body ∷ rest) =
  let l-top = n
      l-end = suc n
      (n1 , pbody) = compile-trace-cnt (suc (suc n)) body
      (n2 , pr)    = compile-trace-cnt n1 rest
      -- Scratch (s3) is the loop counter; break when it hits 0.
      loop = label l-top ∷
             beq s3 zero l-end ∷
             pbody ++
             (j l-top ∷
              label l-end ∷ [])
  in n2 , loop ++ pr
compile-trace-cnt n (instr-case-on-tag f g ∷ rest) =
  let lbl-inl = n
      lbl-end = suc n
      (n1 , pf) = compile-trace-cnt (suc (suc n)) f
      (n2 , pg) = compile-trace-cnt n1 g
      (n3 , pr) = compile-trace-cnt n2 rest
      -- tag at 0(t0); tag ≡ 0 ⇒ inl (f), else inr (g). Fall-through is g.
      dispatch  = ld t1 t0 0 ∷
                  beq t1 zero lbl-inl ∷
                  pg ++
                  (j lbl-end ∷
                   label lbl-inl ∷ []) ++
                  pf ++
                  (label lbl-end ∷ [])
  in n3 , dispatch ++ pr
compile-trace-cnt n (i ∷ rest) =
  let (n1 , pr) = compile-trace-cnt n rest
  in n1 , compile-abstract i ++ pr