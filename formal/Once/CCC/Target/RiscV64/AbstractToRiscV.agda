-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_)
open import Once.Target.Symbol using (once-symbol; once-symbol-path)

-- Import RISC-V syntax
open import Once.Float.Dyadic using (Dyadic; encode; binary32; binary64)
import Once.Word as OnceWord
module IntW = OnceWord.Width 64
open import Once.CCC.Target.RiscV64.Syntax
  using (Reg; zero; ra; sp; fp; a0; a1; a2; a3; a4; a5; a6; a7;
         s1; s2; s3; s4; t0; t1; t2; t3; t4;
         Instr; ld; sd; add; sub; addi; li; auipc; lla; mv;
         beq; bne; jal; jalr; j; ret; call; call-sym; nop; unimp; label;
         Label; once; thunk;
         Program; slot-size; slots)
open import Once.CanonicalName using (CanonicalName)
open import Once.CCC.Label using (ℓ)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Type using (fits-int; fits-float)

-- Import AbstractInstr from SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; Slot;
         mov-to-output; mov-to-input;
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
open import Once.CCC.Machine.NoNested public

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
-- RV64: ld   t1, 8(s1)     (load code pointer into scratch t1)
--       addi sp, sp, -8   (reserve THIS CALL'S return-address slot)
--       jalr ra, t1, 0    (call through t1; t0 preserved for the callee)
--
-- WHY THE CALLER RESERVES THE SLOT (plan 0.65 G2, 2026-08-16). The abstract
-- `instr-call-closure` is `enter-call`: it descends the frame by ONE slot,
-- because D086 says the CALL owns the return-address slot. x86-64's `call`
-- does exactly that in hardware. RISC-V's `jalr` does not move `sp` at all, so
-- until this line the reservation was folded into the callee's marker
-- (`slots (suc b)`) — arithmetically right at the END of the pair, and wrong
-- in BETWEEN: at the callee's entry, one abstract instruction after the call,
-- the concrete `sp` was one slot above the abstract frame base and `sp-eq`
-- was simply false. That window is the correspondence's granularity, so a
-- fact true only across two instructions is not available to it.
--
-- Splitting the reservation the way the model splits it costs one `addi` per
-- call site and makes the concrete call's FRAME effect equal the abstract
-- one on both arches. What is left over is the genuine ABI difference — RISC-V
-- leaves the return ADDRESS in `ra` until the callee spills it — and that one
-- no emitter change can erase; it is what `FlatState.flink` models.
compile-abstract instr-call-closure =
  ld t1 s1 slot-size ∷
  addi sp sp (Data.Integer.-_ (+ slot-size)) ∷
  jalr ra t1 0 ∷ []
  where import Data.Integer

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
-- Plan 0.53: const literal. Mirrors x86-64's `compile-const`.
-- D079 APPLIED TO riscv64 (2026-08-13, plan 0.65 G2): a float CONSTANT is a
-- 64-bit PATTERN, so it loads as an ordinary immediate — no FPU needed. This
-- was `unimp`, a TRAP, which made the machines diverge on this route exactly as
-- x86-64's `ud2` did before D079. `li` is the assembler's pseudo-instruction
-- and expands to the `lui`/`addi` sequence, which is the same trust seam as gas
-- promoting `movq $big` to `movabs`.
-- D115: an `Int` literal's payload is a `ℤ` (source syntax), so the emitter
-- MATERIALISES it at this target's width — two's complement, 64 bits. Exactly
-- what the float case beside it does with `encode`; before D115 the int case
-- could skip this only because literals were never negative.
compile-abstract (instr-load-const fits-int   v) = li a0 (+ (IntW.fromℤ v)) ∷ []
compile-abstract (instr-load-const fits-float v) = li a0 (+ (encode binary64 v)) ∷ []
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
-- Plan 0.53 (mirror x86-64 M5): register pokes. Scratch = s3, Count = s4
-- (callee-saved, otherwise unused by this codegen).
compile-abstract (instr-reg-op scratch-one)        = li s3 (+ 1) ∷ []
compile-abstract (instr-reg-op scratch-zero)       = li s3 (+ 0) ∷ []
compile-abstract (instr-reg-op scratch-dec)        = addi s3 s3 (Data.Integer.-_ (+ 1)) ∷ []
  where import Data.Integer
compile-abstract (instr-reg-op scratch-load-count) = mv s3 s4 ∷ []
compile-abstract (instr-reg-op count-zero)        = li s4 (+ 0) ∷ []
compile-abstract (instr-reg-op count-inc)         = addi s4 s4 (+ 1) ∷ []
-- Plan 0.53 (mirror x86-64 M3/0.34): flat control lowers 1-to-1. Labels/jumps
-- use the SHARED provenance-typed label space (Plan 0.63, D082 — `once` for a
-- compiler jump); the conditional branches are single compare-and-branch (no
-- flags on RISC-V). Input1 pointer = t0; Scratch = s3.
compile-abstract (instr-ctrl (c-label n))               = label (once n) ∷ []
compile-abstract (instr-ctrl (c-jmp n))                 = j (once n) ∷ []
-- Plan 0.63: closure-body entry / return, and the provenance that makes the
-- entry NAMEABLE. `instr-load-code-addr n` lowers to `lla rd, .L_thunk_<n>`,
-- so the body's entry marker must emit that symbol — hence `thunk`, the same
-- choice x86-64 makes, for the same definitional-disjointness reason.
--
-- Until the flip (2026-08-05) this emitted a bare `label n` while
-- `emit-thunk-body` defined `.L_thunk_<n>` as separate TEXT. With the bodies
-- inline that text is gone, so the `lla` referenced an undefined symbol — a
-- link failure caught by the exit tests and invisible to the proofs.
--
-- Plan 0.69: THE BODY MUST SPILL `ra`. On x86 the return address is on the
-- stack, so a body that calls something cannot lose it. On RISC-V it lives in
-- a REGISTER, and `instr-call-closure` lowers to `jalr ra t1 0` — so a body
-- that performs any call overwrites its own return address, and its `ret`
-- (= `jalr zero, ra, 0`) jumps back into itself. That is the hang the exit
-- tests saw. The dead `emit-thunk-body` path (`Once.Target.RiscV64`) always
-- did this; the flip inlined the body and left the spill behind.
--
-- One extra slot on top of the body's own budget holds it, and THE CALLER NOW
-- RESERVES THAT SLOT (2026-08-16 — see `instr-call-closure`). So this marker
-- reserves the body's own `slots b` and the spill lands at `slots b (sp)`,
-- which is the caller-reserved word just above the body's slots 0 … b-1 —
-- the same cell as before the split, since the total descent is unchanged.
-- `c-ret` releases `slots (suc b)` for the same reason and is untouched.
compile-abstract (instr-ctrl (c-thunk n b))             = label (thunk n) ∷ addi sp sp (Data.Integer.-_ (+ (slots b))) ∷ sd ra sp (slots b) ∷ []
  where import Data.Integer
compile-abstract (instr-ctrl (c-ret b))                 = ld ra sp (slots b) ∷ addi sp sp (+ (slots (suc b))) ∷ ret ∷ []
compile-abstract (instr-ctrl (c-branch-scratch-zero n)) = beq s3 zero (once n) ∷ []
compile-abstract (instr-ctrl (c-branch-tag-zero n))     = ld t1 t0 0 ∷ beq t1 zero (once n) ∷ []

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
-- Plan 0.65 (G1 validation): the plain block-wise lowering, which riscv64 did
-- not have. `FlatCore.FlatComposition` is stated over it — every abstract
-- instruction lowers to a contiguous block and the machine pc is the sum of the
-- block lengths before it — so the correspondence needs it whether or not the
-- emitter's own entry point is `compile-trace-cnt`. Mirrors x86-64's exactly.
compile-trace : AbstractTrace → Program
compile-trace [] = []
compile-trace (i ∷ is) = compile-abstract i ++ compile-trace is

compile-trace-cnt : CanonicalName → ℕ → AbstractTrace → ℕ × Program
compile-trace-cnt o n [] = n , []
compile-trace-cnt o n (instr-loop body ∷ rest) =
  let l-top = n
      l-end = suc n
      (n1 , pbody) = compile-trace-cnt o (suc (suc n)) body
      (n2 , pr)    = compile-trace-cnt o n1 rest
      -- Scratch (s3) is the loop counter; break when it hits 0.
      loop = label (once (ℓ o l-top)) ∷
             beq s3 zero (once (ℓ o l-end)) ∷
             pbody ++
             (j (once (ℓ o l-top)) ∷
              label (once (ℓ o l-end)) ∷ [])
  in n2 , loop ++ pr
compile-trace-cnt o n (instr-case-on-tag f g ∷ rest) =
  let lbl-inl = n
      lbl-end = suc n
      (n1 , pf) = compile-trace-cnt o (suc (suc n)) f
      (n2 , pg) = compile-trace-cnt o n1 g
      (n3 , pr) = compile-trace-cnt o n2 rest
      -- tag at 0(t0); tag ≡ 0 ⇒ inl (f), else inr (g). Fall-through is g.
      dispatch  = ld t1 t0 0 ∷
                  beq t1 zero (once (ℓ o lbl-inl)) ∷
                  pg ++
                  (j (once (ℓ o lbl-end)) ∷
                   label (once (ℓ o lbl-inl)) ∷ []) ++
                  pf ++
                  (label (once (ℓ o lbl-end)) ∷ [])
  in n3 , dispatch ++ pr
compile-trace-cnt o n (i ∷ rest) =
  let (n1 , pr) = compile-trace-cnt o n rest
  in n1 , compile-abstract i ++ pr

------------------------------------------------------------------------
-- WHERE THE TWO LOWERINGS AGREE (plan 0.65, 2026-08-12).
--
-- x86-64 has had this since plan 0.54 rung D and riscv64 had NONE of it —
-- found by porting the correspondence core to a second arch. It matters: the
-- correspondence is stated over `compile-trace`, the plain fold, while
-- `Once.Target.RiscV64` emits `compile-trace-cnt`. Without this theorem a
-- riscv64 correspondence would be about a program the compiler does not emit,
-- which is the same class of gap as the ones this plan keeps finding.
--
-- The `NoNested` predicate itself is SHARED (`Once.CCC.Machine.NoNested`) — it
-- mentions no target at all. What is per-arch is only this agreement, which
-- names this module's own two lowerings, and it is clause-for-clause x86-64's.
------------------------------------------------------------------------
compile-trace-cnt-agrees : ∀ (o : CanonicalName) (n : ℕ) (t : AbstractTrace) → NoNested t
                         → compile-trace-cnt o n t ≡ (n , compile-trace t)
compile-trace-cnt-agrees o n [] _ = refl
compile-trace-cnt-agrees o n (mov-to-output ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract mov-to-output ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (mov-to-input ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract mov-to-input ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (load-indirect ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract load-indirect ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (load-indirect-suc ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract load-indirect-suc ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((load-from-slot k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (load-from-slot k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((store-at-slot k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (store-at-slot k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (store-indirect ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract store-indirect ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (store-indirect-suc ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract store-indirect-suc ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((lea-slot k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (lea-slot k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((restore-input k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (restore-input k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((lea-indexed k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (lea-indexed k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-alloc-stack k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-alloc-stack k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-dealloc-stack k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-dealloc-stack k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-reclaim-to k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-reclaim-to k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-push-frame k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-push-frame k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (instr-pop-frame ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract instr-pop-frame ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (instr-call-closure ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract instr-call-closure ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((worklist-init k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-init k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((worklist-push k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-push k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((worklist-pop k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-pop k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((worklist-check k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (worklist-check k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-sigop si) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-sigop si) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-load-const fit v) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-load-const fit v) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-load-code-addr k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-load-code-addr k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n (instr-save-closure-reg ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract instr-save-closure-reg ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-load-tag-lit k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-load-tag-lit k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-alloc-heap k) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-alloc-heap k) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-reg-op op) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-reg-op op) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
compile-trace-cnt-agrees o n ((instr-ctrl c) ∷ rest) (_ , nn) =
  cong (λ p → proj₁ p , compile-abstract (instr-ctrl c) ++ proj₂ p)
       (compile-trace-cnt-agrees o n rest nn)
-- the two the emitters disagree on are excluded by `NoNested`
compile-trace-cnt-agrees o n (instr-case-on-tag f g ∷ rest) (() , _)
compile-trace-cnt-agrees o n (instr-loop body ∷ rest)       (() , _)
