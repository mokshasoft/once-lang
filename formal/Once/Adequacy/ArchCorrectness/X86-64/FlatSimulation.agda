-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation
--
-- Plan 0.32 Phase D, Stage 2: the abstract↔x86 plus-simulation over the
-- flat machine. `CompiledCorr hv prog fs s` relates a FlatState `fs` (flat
-- pc/fuel machine, typed StoredValues) to an x86 `State s` running the
-- compiled program `compile-trace prog`, where:
--   * the DATA agrees (registers under enc-sv, heap under enc-hl, flags,
--     halt) — exactly the FlatCorrespondence.FlatCorr data fields, and
--   * the CONTROL agrees up to the block offset: x86.pc = x86-off prog
--     (fpc fs)  (one flat instruction ↦ a contiguous x86 BLOCK; NOT 1-to-1
--     lockstep — see [[feedback-injectivity-not-lockstep]]).
--
-- The jump correspondence rides `FlatComposition.find-label-corr`. The
-- per-instruction DATA effects ride the FlatCorrespondence `sim-*` lemmas.
-- This module composes them under fuel.
--
-- ROADMAP (this file, in progress):
--   [x] CompiledCorr relation (data ⊕ block-offset pc)
--   [ ] block-step: one flat step ↔ `exec (x86-len i)` of its x86 block,
--       preserving CompiledCorr (uses sim-* for data, find-label-corr for
--       jumps, x86-off for the pc advance). Needs the per-x86-instr
--       "execInstr reduces to the sim-* post-state" facts (the deferred
--       (B) obligations).
--   [ ] fuel induction: exec-flat fuel prog fs ↔ exec (bound) (compile-
--       trace prog) s, lifting block-step; fuel bound = Σ x86-len.
--   [ ] wire into Correct.agda (retires compile-ir).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; shift-frame; frame-word; frame-base; shift-base; slot-addr; slot-addr-linear)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-ref; ref-id)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Once.Type using (fits-int)
open import Once.Word using (Carrier)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≡ᵇ_; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open import Once.CCC.Machine.FlatStoreWF FS using (sv-below; svm-below; StoreWF; FlatWF; flat-wf-step; wf-regs; wf-heap; wf-stack; wf-fresh)
import Once.CCC.Target.X86-64.Semantics as X
open X using (mkstate; execInstr; mkflags; _<ᵇ_; writeMem; updateFlags)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax
  using (rax; rbx; rsi; rdi; rsp; rbp; r15; rcx; Reg; Operand; Program; reg; imm; mem; mov; add; sub; cmp; label; jmp; je; push; pop; lea; rip+label; r12; base; base+disp; slots; slot-size)
open import Data.Maybe using (just; nothing)
open import Data.Bool using (true; false)
open import Data.List using (_∷_; []; _++_; drop; length)
open import Relation.Binary.PropositionalEquality using (refl)

import Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence as FC
module C = FC FS word-eq   -- HeapView / enc-sv / FlatCorr data fields
open C using (HeapView; haddr; HDom; hfront)
open import Once.CCC.Label using (once)
open import Once.Adequacy.ArchCorrectness.X86-64.FlatComposition FS
  using (x86-off; x86-len; x86-off-suc; fetch-block-head; find-label-corr; fetch-block-2nd; fetch-block-3rd; fetch-block-4th; fetch-block-5th; fetch-block-6th)
open import Once.Adequacy.ArchCorrectness.X86-64.StepLemmas using (exec-1; step-mov-rr; step-mov-ri; step-label; step-jmp; step-mov-rm; step-mov-mr; step-add-ri; step-add-rr; step-sub-ri; step-cmp-ri; step-cmp-mi; step-je-taken; step-je-not; step-push; step-pop; step-lea)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace; compile-abstract; slot-to-disp)
open import Data.Empty using (⊥)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-comm; ∸-+-assoc; *-suc; *-identityʳ; *-assoc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)
open MemOps {FS} using (writeLoc; writeLocToHeap; readLoc)

------------------------------------------------------------------------
-- The compiled correspondence = the DATA correspondence (FlatCorr, now
-- pc-free) ⊕ the block-offset pc relation. block-step gets the data from
-- the sim-* lemmas (which produce FlatCorr) and the pc from x86-off-suc /
-- find-label-corr — cleanly separated. (Plan 0.34: no zf-eq.)
------------------------------------------------------------------------
record CompiledCorr (hv : HeapView) (prog : AbstractTrace) (fs : FlatState) (s : X.State) : Set where
  field
    dataCorr : C.FlatCorr hv fs s
    -- CONTROL: x86 pc sits at the block offset of the flat pc (NOT fpc fs).
    pc-off   : X.State.pc s ≡ x86-off prog (fpc fs)
open CompiledCorr public

------------------------------------------------------------------------
-- (B) execInstr-reduces facts. For each x86 instruction the codegen
-- emits, `execInstr` reduces to the exact post-state the FlatCorrespondence
-- `sim-*` lemmas assume. The PURE ones (register/imm/arith/cmp) are stated
-- standalone here; the memory ones (loads/stores) depend on the heap
-- correspondence and are discharged inside block-step.
------------------------------------------------------------------------
-- mov (reg dst) (reg src): rax↔rdi register shuffles (mov-to-output, …).
b-mov-reg-reg : ∀ (prog : Program) (s : X.State) (dst src : Reg)
  → execInstr prog s (mov (reg dst) (reg src))
    ≡ just (mkstate (xwriteReg (xregs s) dst (xreadReg (xregs s) src))
                    (memory s) (flags s) (pc s + 1) (xhalted s))
b-mov-reg-reg prog s dst src = refl

-- mov (reg dst) (imm n): tag/reg-op immediate loads (load-tag-lit, …).
b-mov-reg-imm : ∀ (prog : Program) (s : X.State) (dst : Reg) (n : ℕ)
  → execInstr prog s (mov (reg dst) (imm n))
    ≡ just (mkstate (xwriteReg (xregs s) dst n)
                    (memory s) (flags s) (pc s + 1) (xhalted s))
b-mov-reg-imm prog s dst n = refl

-- cmp (reg dst) (imm n): the control test (c-test-scratch). Like the flat
-- test, it SETS zf (= the dst≟n result) — so it preserves zf-eq, unlike
-- the arithmetic ops below.
b-cmp-reg-imm : ∀ (prog : Program) (s : X.State) (dst : Reg) (n : ℕ)
  → execInstr prog s (cmp (reg dst) (imm n))
    ≡ just (mkstate (xregs s) (memory s)
                    (mkflags (xreadReg (xregs s) dst ≡ᵇ n) (xreadReg (xregs s) dst <ᵇ n) false)
                    (pc s + 1) (xhalted s))
b-cmp-reg-imm prog s dst n = refl

------------------------------------------------------------------------
-- block-step (Plan 0.32 Stage 2): one flat step ↔ X.exec (x86-len i) of
-- its compiled block, preserving CompiledCorr. Result type abbreviation:
------------------------------------------------------------------------
-- A step may EXTEND the heap view (only `instr-alloc-heap` does); `BlockStep`
-- is the same-view case, `BlockStepAt hv hv'` the general one.
BlockStepAt : HeapView → HeapView → AbstractTrace → FlatState → X.State → AbstractInstr → Set
BlockStepAt hv hv' prog fs s i =
  Σ X.State (λ s' → (X.exec (x86-len i) (compile-trace prog) s ≡ just s')
                  × CompiledCorr hv' prog (flat-exec-instr i prog fs) s')

BlockStep : HeapView → AbstractTrace → FlatState → X.State → AbstractInstr → Set
BlockStep hv = BlockStepAt hv hv

-- Generic single-`mov reg,reg` block-step: any straight-line instruction
-- whose x86 block is one `mov (reg dst) (reg src)`. The caller supplies the
-- compile-abstract shape (refl) + the DATA correspondence (a sim-* lemma).
-- Assembly: fetch-block-head + step-mov-rr + exec-1 (x86), then pc via
-- pc-off + x86-off-suc. No flags (Plan 0.34).
block-step-mov-rr : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : X.State)
    (i : AbstractInstr) (dst src : Reg)
  → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just i
  → compile-abstract i ≡ mov (reg dst) (reg src) ∷ []
  → fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)         -- i is straight-line
  → C.FlatCorr hv (flat-exec-instr i prog fs)
               (record s { regs = xwriteReg (xregs s) dst (xreadReg (xregs s) src) ; pc = pc s + 1 })
  → BlockStep hv prog fs s i
block-step-mov-rr {hv} prog fs s i dst src cc h-flat ft ca fpc-eq dataPost =
  post , exec-eq-len , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h-flat
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg dst) (reg src))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (trans (fetch-block-head prog (fpc fs) i ft)
                             (cong (λ b → X.fetch (b ++ compile-trace (drop (suc (fpc fs)) prog)) 0) ca))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) dst (xreadReg (xregs s) src) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rr {compile-trace prog} {s} {dst} {src} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    exec-eq-len : X.exec (x86-len i) (compile-trace prog) s ≡ just post
    exec-eq-len = trans (cong (λ m → X.exec m (compile-trace prog) s) (cong length ca)) exec-eq
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr i prog fs))
    pco' rewrite fpc-eq =
      trans (cong (_+ 1) po)
            (trans (sym (cong (x86-off prog (fpc fs) +_) (cong length ca)))
                   (sym (x86-off-suc prog (fpc fs) i ft)))

-- The four register shuffles (mov-to-output ↔ rax/rdi, …) — one-liners.
block-step-mov-to-output : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-to-output → BlockStep hv prog fs s mov-to-output
block-step-mov-to-output {hv} prog fs s cc h ft =
  block-step-mov-rr prog fs s mov-to-output rax rdi cc h ft refl refl (C.sim-mov-to-output fs s (dataCorr cc))

block-step-mov-to-input : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-to-input → BlockStep hv prog fs s mov-to-input
block-step-mov-to-input {hv} prog fs s cc h ft =
  block-step-mov-rr prog fs s mov-to-input rdi rax cc h ft refl refl (C.sim-mov-to-input fs s (dataCorr cc))

block-step-mov-input2-to-output : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-input2-to-output → BlockStep hv prog fs s mov-input2-to-output
block-step-mov-input2-to-output {hv} prog fs s cc h ft =
  block-step-mov-rr prog fs s mov-input2-to-output rax rsi cc h ft refl refl (C.sim-mov-input2-to-output fs s (dataCorr cc))

block-step-mov-output-to-input2 : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-output-to-input2 → BlockStep hv prog fs s mov-output-to-input2
block-step-mov-output-to-input2 {hv} prog fs s cc h ft =
  block-step-mov-rr prog fs s mov-output-to-input2 rsi rax cc h ft refl refl (C.sim-mov-output-to-input2 fs s (dataCorr cc))

-- Generic single-`mov reg,imm` block-step (load-tag-lit, reg-op imm loads).
block-step-mov-ri : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : X.State)
    (i : AbstractInstr) (dst : Reg) (n : ℕ)
  → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just i
  → compile-abstract i ≡ mov (reg dst) (imm n) ∷ []
  → fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)
  → C.FlatCorr hv (flat-exec-instr i prog fs)
               (record s { regs = xwriteReg (xregs s) dst n ; pc = pc s + 1 })
  → BlockStep hv prog fs s i
block-step-mov-ri {hv} prog fs s i dst n cc h-flat ft ca fpc-eq dataPost =
  post , exec-eq-len , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h-flat
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg dst) (imm n))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (trans (fetch-block-head prog (fpc fs) i ft)
                             (cong (λ b → X.fetch (b ++ compile-trace (drop (suc (fpc fs)) prog)) 0) ca))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) dst n ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-ri {compile-trace prog} {s} {dst} {n} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    exec-eq-len : X.exec (x86-len i) (compile-trace prog) s ≡ just post
    exec-eq-len = trans (cong (λ m → X.exec m (compile-trace prog) s) (cong length ca)) exec-eq
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr i prog fs))
    pco' rewrite fpc-eq =
      trans (cong (_+ 1) po)
            (trans (sym (cong (x86-off prog (fpc fs) +_) (cong length ca)))
                   (sym (x86-off-suc prog (fpc fs) i ft)))

block-step-load-tag-lit : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-tag-lit n) → BlockStep hv prog fs s (instr-load-tag-lit n)
block-step-load-tag-lit {hv} prog fs s n cc h ft =
  block-step-mov-ri prog fs s (instr-load-tag-lit n) rax n cc h ft refl refl (C.sim-load-tag-lit n fs s (dataCorr cc))

block-step-scratch-one : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-one) → BlockStep hv prog fs s (instr-reg-op scratch-one)
block-step-scratch-one {hv} prog fs s cc h ft =
  block-step-mov-ri prog fs s (instr-reg-op scratch-one) rbx 1 cc h ft refl refl (C.sim-reg-scratch-one fs s (dataCorr cc))

block-step-scratch-zero : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-zero) → BlockStep hv prog fs s (instr-reg-op scratch-zero)
block-step-scratch-zero {hv} prog fs s cc h ft =
  block-step-mov-ri prog fs s (instr-reg-op scratch-zero) rbx 0 cc h ft refl refl (C.sim-reg-scratch-zero fs s (dataCorr cc))

block-step-input2-zero : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op input2-zero) → BlockStep hv prog fs s (instr-reg-op input2-zero)
block-step-input2-zero {hv} prog fs s cc h ft =
  block-step-mov-ri prog fs s (instr-reg-op input2-zero) rsi 0 cc h ft refl refl (C.sim-reg-input2-zero fs s (dataCorr cc))

block-step-scratch-load-count : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-load-count) → BlockStep hv prog fs s (instr-reg-op scratch-load-count)
block-step-scratch-load-count {hv} prog fs s cc h ft =
  block-step-mov-rr prog fs s (instr-reg-op scratch-load-count) rbx rsi cc h ft refl refl (C.sim-reg-scratch-load-count fs s (dataCorr cc))

-- c-label: pc passes through (x86 `label` is a 1-instr no-op). The flat
-- step only bumps fpc, so the DATA correspondence transports unchanged
-- (no sim-* needed — floc/regs are untouched on both sides).
block-step-c-label : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-label n)) → BlockStep hv prog fs s (instr-ctrl (c-label n))
block-step-c-label {hv} prog fs s n cc h ft = post , exec-eq , record
  { dataCorr = record { rdi-eq = C.rdi-eq (dataCorr cc) ; rsi-eq = C.rsi-eq (dataCorr cc)
                      ; rax-eq = C.rax-eq (dataCorr cc) ; rbx-eq = C.rbx-eq (dataCorr cc)
                      ; halt-eq = C.halt-eq (dataCorr cc) ; heap-eq = C.heap-eq (dataCorr cc)
                      ; rsp-eq = C.rsp-eq (dataCorr cc)
                      ; rsp-eq = C.rsp-eq (dataCorr cc) ; r15-eq = C.r15-eq (dataCorr cc) ; dom-fresh = C.dom-fresh (dataCorr cc)
                      ; stack-eq = C.stack-eq (dataCorr cc) }
  ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (label (once n))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-label n)) ft)
    post : X.State
    post = record s { pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-label {compile-trace prog} {s} {once n} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (instr-ctrl (c-label n)) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (instr-ctrl (c-label n)) ft))

-- worklist-init / worklist-check: pure cata bookkeeping — compile to [] (x86-len 0),
-- flat step is identity (exec-abstract = s,alloc) mod fpc, x86 does nothing. FlatCorr
-- copied (floc/falloc unchanged); pc-off shifts by x86-len 0 (+-identityʳ). The
-- cleanest possible block-step: `X.exec 0 = just s` is refl.
block-step-worklist-init : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-init n) → BlockStep hv prog fs s (worklist-init n)
block-step-worklist-init {hv} prog fs s n cc h ft = s , refl , record
  { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                      ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; rsp-eq = C.rsp-eq dc ; r15-eq = C.r15-eq dc ; dom-fresh = C.dom-fresh dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
  ; pc-off = trans (pc-off cc)
             (sym (trans (x86-off-suc prog (fpc fs) (worklist-init n) ft) (+-identityʳ _))) }
  where dc = dataCorr cc

block-step-worklist-check : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-check n) → BlockStep hv prog fs s (worklist-check n)
block-step-worklist-check {hv} prog fs s n cc h ft = s , refl , record
  { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                      ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; rsp-eq = C.rsp-eq dc ; r15-eq = C.r15-eq dc ; dom-fresh = C.dom-fresh dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
  ; pc-off = trans (pc-off cc)
             (sym (trans (x86-off-suc prog (fpc fs) (worklist-check n) ft) (+-identityʳ _))) }
  where dc = dataCorr cc

-- instr-reclaim-to: allocation bookkeeping — compile to [] (x86-len 0), flat step
-- lowers `next-slot` (floc + heapMem unchanged). The heap correspondence is carried
-- by the VIEW (not indexed by the abstract alloc state), so it copies through
-- unchanged — this is what retired the old `LiveIn-reclaim` allocator postulate.
block-step-reclaim-to : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reclaim-to n) → BlockStep hv prog fs s (instr-reclaim-to n)
block-step-reclaim-to {hv} prog fs s n cc h ft = s , refl , record
  { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                      ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; rsp-eq = C.rsp-eq dc ; r15-eq = C.r15-eq dc ; dom-fresh = C.dom-fresh dc
                      ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }   -- reclaim-to changes next-slot, not stackSlot ⇒ bound stable
  ; pc-off = trans (pc-off cc)
             (sym (trans (x86-off-suc prog (fpc fs) (instr-reclaim-to n) ft) (+-identityʳ _))) }
  where dc = dataCorr cc

-- c-jmp: unconditional jump. find-label-corr maps the flat label index to
-- the x86 block-offset, so the x86 `jmp` lands at the same place. Data
-- unchanged (jmp touches only the pc). Hypothesis: the target exists.
block-step-c-jmp : ∀ {hv : HeapView} prog fs s n j → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp n))
  → find-label prog n ≡ just j
  → BlockStep hv prog fs s (instr-ctrl (c-jmp n))
block-step-c-jmp {hv} prog fs s n j cc h ft fl-eq = block-step
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (jmp (once n))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-jmp n)) ft)
    fl-x86 : X.find-label (compile-trace prog) (once n) ≡ just (x86-off prog j)
    fl-x86 = find-label-corr prog n 0 j fl-eq
    post : X.State
    post = record s { pc = x86-off prog j }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-jmp {compile-trace prog} {s} {once n} {x86-off prog j} fetch-x86 fl-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    block-step : BlockStep hv prog fs s (instr-ctrl (c-jmp n))
    block-step rewrite fl-eq = post , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc
                          ; rax-eq = C.rax-eq dc ; rbx-eq = C.rbx-eq dc
                          ; halt-eq = C.halt-eq dc ; rsp-eq = C.rsp-eq dc ; r15-eq = C.r15-eq dc ; dom-fresh = C.dom-fresh dc ; heap-eq = C.heap-eq dc
                          ; stack-eq = C.stack-eq dc }
      ; pc-off = refl }

-- load-indirect: Output := *Input1 ↔ `mov rax, [rdi]`. The read VALUE comes
-- from heap-eq (memory s at haddr hv hl = enc-sv w), the ADDRESS from rdi-eq
-- (rdi = haddr hv hl since Input1 = SV-Ptr (AtDynamic hl)).
block-step-load-indirect : ∀ {hv : HeapView} prog fs s hl w → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl        -- the loaded pointer is live (store-WF)
  → heapMem (floc fs) hl ≡ just w
  → BlockStep hv prog fs s load-indirect
block-step-load-indirect {hv} prog fs s hl w cc h ft i-eq live-hl h-eq =
  post , exec-eq , record { dataCorr = C.sim-load-indirect hl w fs s dc i-eq h-eq ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg rax) (mem (base rdi)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect ft)
    rdi-val : xreadReg (xregs s) rdi ≡ haddr hv hl
    rdi-val = trans (C.rdi-eq dc) (cong (C.enc-sv hv) i-eq)
    rd : X.readMem (memory s) (X.effectiveAddr s (base rdi)) ≡ just (C.enc-sv hv w)
    rd = trans (cong (X.readMem (memory s)) rdi-val) (trans (C.heap-eq dc hl live-hl) (cong (C.enc-maybe hv) h-eq))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rax} {base rdi} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr load-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) load-indirect ft))

-- load-indirect-suc: Output := *(sucLoc Input1) ↔ `mov rax, [rdi + slot]`.
-- The address law C.haddr-suc hv bridges the x86 effective address (haddr hv hl +
-- slot-size) to the heap cell at sucHL hl (haddr hv (sucHL hl)).
block-step-load-indirect-suc : ∀ {hv : HeapView} prog fs s hl w → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)     -- the loaded second cell is live (store-WF)
  → heapMem (floc fs) (sucHL hl) ≡ just w
  → BlockStep hv prog fs s load-indirect-suc
block-step-load-indirect-suc {hv} prog fs s hl w cc h ft i-eq live-shl h-eq =
  post , exec-eq , record { dataCorr = C.sim-load-indirect-suc hl w fs s dc i-eq h-eq ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg rax) (mem (base+disp rdi slot-size)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect-suc ft)
    rdi-val : xreadReg (xregs s) rdi ≡ haddr hv hl
    rdi-val = trans (C.rdi-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-eq : X.effectiveAddr s (base+disp rdi slot-size) ≡ haddr hv (sucHL hl)
    addr-eq = trans (cong (_+ slot-size) rdi-val) (sym (C.haddr-suc hv hl))
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rdi slot-size)) ≡ just (C.enc-sv hv w)
    rd = trans (cong (X.readMem (memory s)) addr-eq) (trans (C.heap-eq dc (sucHL hl) live-shl) (cong (C.enc-maybe hv) h-eq))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rax} {base+disp rdi slot-size} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr load-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) load-indirect-suc ft))

-- load-from-slot: Output := stack[current-frame, slot] ↔ `mov rax, [rsp + disp]`.
-- The read VALUE comes from the NEW stack-eq field (memory s at rsp+disp = enc-maybe
-- of the slot's abstract value); with the slot holding `just w`, that pins the x86
-- read to `just (enc-sv w)` — feeding step-mov-rm exactly as load-indirect uses heap-eq.
-- FIRST consumer of stack-eq: deleting the field breaks `rd`.
block-step-load-from-slot : ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (load-from-slot slot)
  → slot < stackSlot (regs (floc fs))   -- the read slot is within the runtime frame (WF)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep hv prog fs s (load-from-slot slot)
block-step-load-from-slot {hv} prog fs s slot w cc h ft slot<ns st-eq =
  post , exec-eq , record { dataCorr = C.sim-load-from-slot slot w fs s dc st-eq ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg rax) (mem (base+disp rsp (slot-to-disp slot))))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (load-from-slot slot) ft)
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rsp (slot-to-disp slot))) ≡ just (C.enc-sv hv w)
    rd = trans (C.stack-eq dc slot slot<ns) (cong (C.enc-maybe hv) st-eq)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rax} {base+disp rsp (slot-to-disp slot)} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (load-from-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (load-from-slot slot) ft))

-- restore-input: Input1 := stack[current-frame, slot] ↔ `mov rdi, [rsp+disp]`.
-- Identical to load-from-slot but the destination register is rdi (Input1).
block-step-restore-input : ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (restore-input slot)
  → slot < stackSlot (regs (floc fs))   -- the read slot is within the runtime frame (WF)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep hv prog fs s (restore-input slot)
block-step-restore-input {hv} prog fs s slot w cc h ft slot<ns st-eq =
  post , exec-eq , record { dataCorr = C.sim-restore-input slot w fs s dc st-eq ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg rdi) (mem (base+disp rsp (slot-to-disp slot))))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (restore-input slot) ft)
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rsp (slot-to-disp slot))) ≡ just (C.enc-sv hv w)
    rd = trans (C.stack-eq dc slot slot<ns) (cong (C.enc-maybe hv) st-eq)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rdi (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rdi} {base+disp rsp (slot-to-disp slot)} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (restore-input slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (restore-input slot) ft))

-- alloc-stack: reserve n slots ↔ `sub rsp, n*8`. Uses step-sub-ri; the flag
-- clobber is invisible (FlatCorr flag-free). The 3 fresh-frame facts (entry,
-- fresh-abs, fresh-x86) are threaded to sim-alloc-stack; heap liveness now rides
-- the carried view, so the old `liveinv` premise is gone.
block-step-alloc-stack : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-alloc-stack n)
  → stackSlot (regs (floc fs)) ≡ 0
  -- Plan 0.61: the reservation MOVES into the callee frame, so the freshness is
  -- about the SHIFTED frame (a weaker premise than the caller-frame one).
  → (∀ k → k < n → stackMem (floc fs) (shift-frame FS (current-frame (falloc fs)) n) k ≡ nothing)
  → (∀ k → k < n → X.readMem (memory s) ((X.readReg (xregs s) rsp ∸ slots n) + slot-to-disp k) ≡ nothing)
  → BlockStep hv prog fs s (instr-alloc-stack n)
block-step-alloc-stack {hv} prog fs s n cc h ft entry fresh-abs fresh-x86 =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (sub (reg rsp) (imm (slots n)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-alloc-stack n) ft)
    newFlags : X.Flags
    newFlags = updateFlags (xreadReg (xregs s) rsp ∸ slots n) (xreadReg (xregs s) rsp)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rsp (xreadReg (xregs s) rsp ∸ slots n)
                    ; flags = newFlags ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-sub-ri {compile-trace prog} {s} {rsp} {slots n} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr (instr-alloc-stack n) prog fs) post
    dataPost = C.sim-alloc-stack n newFlags fs s dc entry fresh-abs fresh-x86
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (instr-alloc-stack n) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (instr-alloc-stack n) ft))

-- dealloc-stack: free n slots ↔ `add rsp, n*8`. At a full-frame exit
-- (stackSlot ≡ n), sim-dealloc-stack's post bound is vacuous. Uses step-add-ri.
block-step-dealloc-stack : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-dealloc-stack n)
  → stackSlot (regs (floc fs)) ≡ n
  -- matched pairing: the restored (caller) frame's base is where %rsp lands
  → X.readReg (xregs s) rsp + slots n
      ≡ frame-base FS (current-frame (leave-frame (falloc fs)))
  → BlockStep hv prog fs s (instr-dealloc-stack n)
block-step-dealloc-stack {hv} prog fs s n cc h ft full restores =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (add (reg rsp) (imm (slots n)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-dealloc-stack n) ft)
    newFlags : X.Flags
    newFlags = updateFlags (xreadReg (xregs s) rsp + slots n) (xreadReg (xregs s) rsp)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rsp (xreadReg (xregs s) rsp + slots n)
                    ; flags = newFlags ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-add-ri {compile-trace prog} {s} {rsp} {slots n} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr (instr-dealloc-stack n) prog fs) post
    dataPost = C.sim-dealloc-stack n newFlags fs s dc full restores
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (instr-dealloc-stack n) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (instr-dealloc-stack n) ft))

-- push-frame: `push rbp; mov rbp,rsp; sub rsp,cap*8` (3 steps). The abstract
-- resets the runtime depth (stackSlot:=0) ⇒ vacuous stack-eq (sim-push-frame). The
-- prologue touches only rbp/rsp (4 tracked regs preserved: refl) and writes ONE
-- cell (saved rbp at [rsp−8]); heap-eq is preserved by a disjointness residual.
block-step-push-frame : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-push-frame n)
  → (∀ hl → HDom hv hl → (X.readReg (xregs s) rsp ∸ slot-size ≡ haddr hv hl) → ⊥)
  → BlockStep hv prog fs s (instr-push-frame n)
block-step-push-frame {hv} prog fs s n cc h ft disj =
  post-sub , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-push : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (push (reg rbp))
    fetch-push = trans (cong (X.fetch (compile-trace prog)) po)
                       (fetch-block-head prog (fpc fs) (instr-push-frame n) ft)
    post-push : X.State
    post-push = record s { regs = xwriteReg (xregs s) rsp (xreadReg (xregs s) rsp ∸ slot-size)
                         ; memory = writeMem (memory s) (xreadReg (xregs s) rsp ∸ slot-size) (xreadReg (xregs s) rbp)
                         ; pc = pc s + 1 }
    step1 : X.step-not-halted (compile-trace prog) s ≡ just post-push
    step1 = step-push {compile-trace prog} {s} {rbp} fetch-push
    fetch-mov : X.fetch (compile-trace prog) (X.State.pc post-push) ≡ just (mov (reg rbp) (reg rsp))
    fetch-mov = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                      (fetch-block-2nd prog (fpc fs) (instr-push-frame n) ft)
    post-mov : X.State
    post-mov = record post-push { regs = xwriteReg (xregs post-push) rbp (xreadReg (xregs post-push) rsp)
                                ; pc = pc post-push + 1 }
    step2 : X.step-not-halted (compile-trace prog) post-push ≡ just post-mov
    step2 = step-mov-rr {compile-trace prog} {post-push} {rbp} {rsp} fetch-mov
    fetch-sub : X.fetch (compile-trace prog) (X.State.pc post-mov) ≡ just (sub (reg rsp) (imm (slots n)))
    fetch-sub = trans (cong (λ p → X.fetch (compile-trace prog) ((p + 1) + 1)) po)
                (trans (cong (X.fetch (compile-trace prog)) (+-assoc (x86-off prog (fpc fs)) 1 1))
                       (fetch-block-3rd prog (fpc fs) (instr-push-frame n) ft))
    post-sub : X.State
    post-sub = record post-mov { regs = xwriteReg (xregs post-mov) rsp (xreadReg (xregs post-mov) rsp ∸ slots n)
                               ; flags = updateFlags (xreadReg (xregs post-mov) rsp ∸ slots n) (xreadReg (xregs post-mov) rsp)
                               ; pc = pc post-mov + 1 }
    step3 : X.step-not-halted (compile-trace prog) post-mov ≡ just post-sub
    step3 = step-sub-ri {compile-trace prog} {post-mov} {rsp} {slots n} fetch-sub
    exec-eq : X.exec 3 (compile-trace prog) s ≡ just post-sub
    exec-eq = trans (exec-1 {compile-trace prog} {2} {s} {post-push} halt-s step1 halt-s)
              (trans (exec-1 {compile-trace prog} {1} {post-push} {post-mov} halt-s step2 halt-s)
                     (exec-1 {compile-trace prog} {0} {post-mov} {post-sub} halt-s step3 halt-s))
    heap-p : ∀ hl → HDom hv hl
           → X.readMem (X.State.memory post-sub) (haddr hv hl) ≡ X.readMem (X.State.memory s) (haddr hv hl)
    heap-p hl live rewrite C.≢→≡ᵇfalse {haddr hv hl} {xreadReg (xregs s) rsp ∸ slot-size}
                             (λ eq → disj hl live (sym eq)) = refl
    -- the prologue lands %rsp on the CALLEE frame's base: `push rbp` takes one
    -- slot, `sub rsp, n·8` the rest — exactly `shift-frame cf (suc n)`.
    rsp-p : xreadReg (xregs post-sub) rsp
          ≡ frame-base FS (shift-frame FS (current-frame (falloc fs)) (suc n))
    rsp-p = trans (cong (λ b → (b ∸ slot-size) ∸ slots n) (C.rsp-eq dc))
            (trans (∸-+-assoc (frame-base FS (current-frame (falloc fs))) slot-size (slots n))
            (trans (cong (λ w → frame-base FS (current-frame (falloc fs)) ∸ (w + n * w)) (sym word-eq))
                   (sym (shift-base FS (current-frame (falloc fs)) (suc n)))))
    dataPost : C.FlatCorr hv (flat-exec-instr (instr-push-frame n) prog fs) post-sub
    dataPost = C.sim-push-frame n fs s post-sub dc refl refl refl refl refl refl rsp-p heap-p
    pco' : X.State.pc post-sub ≡ x86-off prog (fpc (flat-exec-instr (instr-push-frame n) prog fs))
    pco' = trans (trans (cong (λ p → ((p + 1) + 1) + 1) po) assoc)
                 (sym (x86-off-suc prog (fpc fs) (instr-push-frame n) ft))
      where m = x86-off prog (fpc fs)
            assoc : ((m + 1) + 1) + 1 ≡ m + 3
            assoc = trans (cong (_+ 1) (+-assoc m 1 1)) (+-assoc m 2 1)

-- pop-frame: `mov rsp,rbp; pop rbp` (2 steps). Abstract identity; at a frame
-- teardown stackSlot ≡ 0 ⇒ vacuous stack-eq (sim-pop-frame). mov/pop touch only
-- rsp/rbp (4 tracked regs preserved: refl) and pop only READS memory (heap-eq =
-- refl). `v` + `saved` witness the saved-rbp cell for pop to succeed.
block-step-pop-frame : ∀ {hv : HeapView} prog fs s (v : X.Word) → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just instr-pop-frame
  → stackSlot (regs (floc fs)) ≡ 0
  → X.readMem (memory s) (xreadReg (xregs s) rbp) ≡ just v
  -- matched pairing: `mov rsp,rbp; pop rbp` lands %rsp on the caller frame's base
  → xreadReg (xregs s) rbp + slot-size
      ≡ frame-base FS (current-frame (leave-frame (falloc fs)))
  → BlockStep hv prog fs s instr-pop-frame
block-step-pop-frame {hv} prog fs s v cc h ft ss0 saved restores =
  post-pop , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-mov : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg rsp) (reg rbp))
    fetch-mov = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) instr-pop-frame ft)
    post-mov : X.State
    post-mov = record s { regs = xwriteReg (xregs s) rsp (xreadReg (xregs s) rbp) ; pc = pc s + 1 }
    step1 : X.step-not-halted (compile-trace prog) s ≡ just post-mov
    step1 = step-mov-rr {compile-trace prog} {s} {rsp} {rbp} fetch-mov
    fetch-pop : X.fetch (compile-trace prog) (X.State.pc post-mov) ≡ just (pop rbp)
    fetch-pop = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                      (fetch-block-2nd prog (fpc fs) instr-pop-frame ft)
    rd : X.readMem (memory post-mov) (xreadReg (xregs post-mov) rsp) ≡ just v
    rd = saved
    post-pop : X.State
    post-pop = record post-mov { regs = xwriteReg (xwriteReg (xregs post-mov) rbp v) rsp
                                          (xreadReg (xregs post-mov) rsp + slot-size)
                               ; pc = pc post-mov + 1 }
    step2 : X.step-not-halted (compile-trace prog) post-mov ≡ just post-pop
    step2 = step-pop {compile-trace prog} {post-mov} {rbp} {v} fetch-pop rd
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-pop
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-mov} halt-s step1 halt-s)
                    (exec-1 {compile-trace prog} {0} {post-mov} {post-pop} halt-s step2 halt-s)
    heap-p : ∀ hl → HDom hv hl
           → X.readMem (X.State.memory post-pop) (haddr hv hl) ≡ X.readMem (X.State.memory s) (haddr hv hl)
    heap-p hl live = refl
    dataPost : C.FlatCorr hv (flat-exec-instr instr-pop-frame prog fs) post-pop
    dataPost = C.sim-pop-frame fs s post-pop dc ss0 refl refl refl refl refl refl restores heap-p
    pco' : X.State.pc post-pop ≡ x86-off prog (fpc (flat-exec-instr instr-pop-frame prog fs))
    pco' = trans (trans (cong (λ p → (p + 1) + 1) po) (+-assoc (x86-off prog (fpc fs)) 1 1))
                 (sym (x86-off-suc prog (fpc fs) instr-pop-frame ft))

-- load-const (int): Output := SV-Lit fits-int v ↔ `mov rax, imm v` (1 step).
-- With the enc-sv fix the immediate matches exactly (sim-load-const's rax-eq = refl).
block-step-load-const : ∀ {hv : HeapView} prog fs s (v : Carrier) → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-const fits-int v)
  → BlockStep hv prog fs s (instr-load-const fits-int v)
block-step-load-const {hv} prog fs s v cc h ft =
  post , exec-eq , record { dataCorr = C.sim-load-const v fs s dc ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg rax) (imm v))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-load-const fits-int v) ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax v ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-ri {compile-trace prog} {s} {rax} {v} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (instr-load-const fits-int v) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (instr-load-const fits-int v) ft))

-- load-code-addr: Output := SV-Code n ↔ `lea rax, [rip+label n]` (1 step). The
-- effective address of a label is n, and enc-sv(SV-Code n)=n ⇒ rax-eq = refl.
block-step-load-code-addr : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-code-addr n)
  → BlockStep hv prog fs s (instr-load-code-addr n)
block-step-load-code-addr {hv} prog fs s n cc h ft =
  post , exec-eq , record { dataCorr = C.sim-load-code-addr n fs s dc ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (lea rax (rip+label n))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-load-code-addr n) ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (X.effectiveAddr s (rip+label n)) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-lea {compile-trace prog} {s} {rax} {rip+label n} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (instr-load-code-addr n) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (instr-load-code-addr n) ft))

-- save-closure-reg: abstract identity ↔ `mov r12, rdi`. r12 is untracked, so the
-- whole FlatCorr copies through (sim-save-closure-reg).
block-step-save-closure-reg : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just instr-save-closure-reg
  → BlockStep hv prog fs s instr-save-closure-reg
block-step-save-closure-reg {hv} prog fs s cc h ft =
  post , exec-eq , record { dataCorr = C.sim-save-closure-reg fs s dc ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg r12) (reg rdi))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) instr-save-closure-reg ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) r12 (xreadReg (xregs s) rdi) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rr {compile-trace prog} {s} {r12} {rdi} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr instr-save-closure-reg prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) instr-save-closure-reg ft))

-- worklist-push / worklist-pop: their abstract semantics + x86 lowering are
-- IDENTICAL to store-at-slot / load-from-slot respectively (SMCore/AbstractToX86),
-- so flat-exec-instr reduces the same way and the sim-* lemmas are reused verbatim.
block-step-worklist-push : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-push slot)
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) rsp + slot-to-disp slot ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s (worklist-push slot)
block-step-worklist-push {hv} prog fs s slot cc h ft disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (mem (base+disp rsp (slot-to-disp slot))) (reg rax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (worklist-push slot) ft)
    post : X.State
    post = record s { memory = writeMem (memory s) (X.effectiveAddr s (base+disp rsp (slot-to-disp slot)))
                                        (xreadReg (xregs s) rax)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-mr {compile-trace prog} {s} {base+disp rsp (slot-to-disp slot)} {rax} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    post-eq : post ≡ mkstate (xregs s)
                             (writeMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp slot)
                                       (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ v → mkstate (xregs s)
                            (writeMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp slot) v)
                            (flags s) (pc s + 1) (xhalted s))
                   (C.rax-eq dc)
    dataPost : C.FlatCorr hv (flat-exec-instr (worklist-push slot) prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr (worklist-push slot) prog fs)) (sym post-eq)
                     (C.sim-store-at-slot slot fs s dc disj)
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (worklist-push slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (worklist-push slot) ft))

block-step-worklist-pop : ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-pop slot)
  → slot < stackSlot (regs (floc fs))   -- the read slot is within the runtime frame (WF)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep hv prog fs s (worklist-pop slot)
block-step-worklist-pop {hv} prog fs s slot w cc h ft slot<ns st-eq =
  post , exec-eq , record { dataCorr = C.sim-load-from-slot slot w fs s dc st-eq ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg rax) (mem (base+disp rsp (slot-to-disp slot))))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (worklist-pop slot) ft)
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rsp (slot-to-disp slot))) ≡ just (C.enc-sv hv w)
    rd = trans (C.stack-eq dc slot slot<ns) (cong (C.enc-maybe hv) st-eq)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rax} {base+disp rsp (slot-to-disp slot)} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (worklist-pop slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (worklist-pop slot) ft))

-- store-indirect: *Input1 := Output ↔ `mov [rdi], rax`. step-mov-mr writes
-- the RAW register values (readReg rdi / readReg rax); sim-store-indirect's
-- post has the ENCODED values (haddr hv hl / enc-sv Output) — bridge the two
-- post-states via rdi-eq + rax-eq, then transport the data correspondence.
block-step-store-indirect : ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl        -- the store target is live (store-WF)
  → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ haddr hv hl) → ⊥)   -- heap/stack disjoint
  → BlockStep hv prog fs s store-indirect
block-step-store-indirect {hv} prog fs s hl cc h ft i-eq live-hl guard disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (mem (base rdi)) (reg rax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) store-indirect ft)
    rdi-val : xreadReg (xregs s) rdi ≡ haddr hv hl
    rdi-val = trans (C.rdi-eq dc) (cong (C.enc-sv hv) i-eq)
    post : X.State
    post = record s { memory = writeMem (memory s) (X.effectiveAddr s (base rdi)) (xreadReg (xregs s) rax)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-mr {compile-trace prog} {s} {base rdi} {rax} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    -- bridge post (raw) ≡ sim-post (encoded)
    post-eq : post ≡ mkstate (xregs s) (writeMem (memory s) (haddr hv hl) (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ m → mkstate (xregs s) m (flags s) (pc s + 1) (xhalted s))
                   (cong₂ (writeMem (memory s)) rdi-val (C.rax-eq dc))
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr store-indirect prog fs)) (sym post-eq)
                     (C.sim-store-indirect hl fs s dc i-eq live-hl guard disj)
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr store-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) store-indirect ft))

-- store-indirect-suc: *(sucLoc Input1) := Output ↔ `mov [rdi+slot], rax`.
-- Like store-indirect + the address law C.haddr-suc hv for the +slot offset.
block-step-store-indirect-suc : ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)     -- the store target (second cell) is live (store-WF)
  → writeLoc (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) (sucHL hl) (readReg (regs (floc fs)) Output)
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ haddr hv (sucHL hl)) → ⊥)   -- heap/stack disjoint
  → BlockStep hv prog fs s store-indirect-suc
block-step-store-indirect-suc {hv} prog fs s hl cc h ft i-eq live-shl guard disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (mem (base+disp rdi slot-size)) (reg rax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) store-indirect-suc ft)
    rdi-val : xreadReg (xregs s) rdi ≡ haddr hv hl
    rdi-val = trans (C.rdi-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-val : xreadReg (xregs s) rdi + slot-size ≡ haddr hv (sucHL hl)
    addr-val = trans (cong (_+ slot-size) rdi-val) (sym (C.haddr-suc hv hl))
    post : X.State
    post = record s { memory = writeMem (memory s) (X.effectiveAddr s (base+disp rdi slot-size)) (xreadReg (xregs s) rax)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-mr {compile-trace prog} {s} {base+disp rdi slot-size} {rax} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    post-eq : post ≡ mkstate (xregs s) (writeMem (memory s) (haddr hv (sucHL hl)) (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ m → mkstate (xregs s) m (flags s) (pc s + 1) (xhalted s))
                   (cong₂ (writeMem (memory s)) addr-val (C.rax-eq dc))
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect-suc prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr store-indirect-suc prog fs)) (sym post-eq)
                     (C.sim-store-indirect-suc hl fs s dc i-eq live-shl guard disj)
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr store-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) store-indirect-suc ft))

-- store-at-slot: stack[current-frame, slot] := Output ↔ `mov [rsp+disp], rax`.
-- step-mov-mr writes the RAW rax; sim-store-at-slot's post has enc-sv Output —
-- bridge via rax-eq (the address is rsp+disp, definitional, no register bridge).
-- The stack/heap disjointness (`disj`) is threaded to sim-store-at-slot.
block-step-store-at-slot : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (store-at-slot slot)
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) rsp + slot-to-disp slot ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s (store-at-slot slot)
block-step-store-at-slot {hv} prog fs s slot cc h ft disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (mem (base+disp rsp (slot-to-disp slot))) (reg rax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (store-at-slot slot) ft)
    post : X.State
    post = record s { memory = writeMem (memory s) (X.effectiveAddr s (base+disp rsp (slot-to-disp slot)))
                                        (xreadReg (xregs s) rax)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-mr {compile-trace prog} {s} {base+disp rsp (slot-to-disp slot)} {rax} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    post-eq : post ≡ mkstate (xregs s)
                             (writeMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp slot)
                                       (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ v → mkstate (xregs s)
                            (writeMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp slot) v)
                            (flags s) (pc s + 1) (xhalted s))
                   (C.rax-eq dc)
    dataPost : C.FlatCorr hv (flat-exec-instr (store-at-slot slot) prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr (store-at-slot slot) prog fs)) (sym post-eq)
                     (C.sim-store-at-slot slot fs s dc disj)
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (store-at-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (store-at-slot slot) ft))

-- Arithmetic reg-ops: input2-inc (add rsi,1) / scratch-dec (sub rbx,1).
-- x86 add/sub set flags as a side effect, but CompiledCorr/FlatCorr are
-- flag-free (Plan 0.34), so the flag clobber is invisible — the sim-* lemma
-- is parametric over the post flags (instantiated with updateFlags here).
block-step-input2-inc : ∀ {hv : HeapView} prog fs s k → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op input2-inc)
  → readReg (regs (floc fs)) Input2 ≡ SV-Tag k
  → BlockStep hv prog fs s (instr-reg-op input2-inc)
block-step-input2-inc {hv} prog fs s k cc h ft i2-eq =
  post , exec-eq , record
    { dataCorr = C.sim-reg-input2-inc k (updateFlags (xreadReg (xregs s) rsi + 1) (xreadReg (xregs s) rsi)) fs s dc i2-eq
    ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (add (reg rsi) (imm 1))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-reg-op input2-inc) ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rsi (xreadReg (xregs s) rsi + 1)
                    ; flags = updateFlags (xreadReg (xregs s) rsi + 1) (xreadReg (xregs s) rsi) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-add-ri {compile-trace prog} {s} {rsi} {1} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (instr-reg-op input2-inc) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (instr-reg-op input2-inc) ft))

block-step-scratch-dec : ∀ {hv : HeapView} prog fs s k → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-dec)
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → BlockStep hv prog fs s (instr-reg-op scratch-dec)
block-step-scratch-dec {hv} prog fs s k cc h ft sc-eq =
  post , exec-eq , record
    { dataCorr = C.sim-reg-scratch-dec k (updateFlags (xreadReg (xregs s) rbx ∸ 1) (xreadReg (xregs s) rbx)) fs s dc sc-eq
    ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (sub (reg rbx) (imm 1))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-reg-op scratch-dec) ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rbx (xreadReg (xregs s) rbx ∸ 1)
                    ; flags = updateFlags (xreadReg (xregs s) rbx ∸ 1) (xreadReg (xregs s) rbx) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-sub-ri {compile-trace prog} {s} {rbx} {1} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (instr-reg-op scratch-dec) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (instr-reg-op scratch-dec) ft))

-- c-branch-scratch-zero: cmp rbx,0 ; je n. Two x86 steps; the je branch
-- depends on whether Scratch ≟ 0. With Scratch = SV-Tag k, the flat
-- condition sv-is-zero and the x86 zf (rbx≡ᵇ0, rbx = k) agree by case on k.
-- Data unchanged (control only).
block-step-c-branch-scratch-zero : ∀ {hv : HeapView} prog fs s n k j → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero n))
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → find-label prog n ≡ just j
  → BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
block-step-c-branch-scratch-zero {hv} prog fs s n zero j cc h ft sc-eq fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (reg rbx) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (xreadReg (xregs s) rbx ≡ᵇ 0) (xreadReg (xregs s) rbx <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    step-cmp = step-cmp-ri {compile-trace prog} {s} {rbx} {0} fetch-cmp
    rbx-val : xreadReg (xregs s) rbx ≡ 0
    rbx-val = trans (C.rbx-eq dc) (cong (C.enc-sv hv) sc-eq)
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    zf-true : X.Flags.zf (flags post-cmp) ≡ true
    zf-true = cong (_≡ᵇ 0) rbx-val
    fl-x86 : X.find-label (compile-trace prog) (once n) ≡ just (x86-off prog j)
    fl-x86 = find-label-corr prog n 0 j fl-eq
    post-je : X.State
    post-je = record post-cmp { pc = x86-off prog j }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-taken {compile-trace prog} {post-cmp} {once n} {x86-off prog j} fetch-je zf-true fl-x86
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq | fl-eq = post-je , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                          ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; rsp-eq = C.rsp-eq dc ; r15-eq = C.r15-eq dc ; dom-fresh = C.dom-fresh dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
      ; pc-off = refl }
block-step-c-branch-scratch-zero {hv} prog fs s n (suc m) j cc h ft sc-eq fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (reg rbx) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (xreadReg (xregs s) rbx ≡ᵇ 0) (xreadReg (xregs s) rbx <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    step-cmp = step-cmp-ri {compile-trace prog} {s} {rbx} {0} fetch-cmp
    rbx-val : xreadReg (xregs s) rbx ≡ suc m
    rbx-val = trans (C.rbx-eq dc) (cong (C.enc-sv hv) sc-eq)
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    zf-false : X.Flags.zf (flags post-cmp) ≡ false
    zf-false = cong (_≡ᵇ 0) rbx-val
    post-je : X.State
    post-je = record post-cmp { pc = X.State.pc post-cmp + 1 }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-not {compile-trace prog} {post-cmp} {once n} fetch-je zf-false
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    pco' : X.State.pc post-je ≡ x86-off prog (suc (fpc fs))
    pco' = trans (+-assoc (pc s) 1 1) (trans (cong (_+ 2) po) (sym (x86-off-suc prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)))
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq = post-je , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                          ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; rsp-eq = C.rsp-eq dc ; r15-eq = C.r15-eq dc ; dom-fresh = C.dom-fresh dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
      ; pc-off = pco' }

-- c-branch-tag-zero: cmp [rdi],0 ; je n. Like scratch-zero but the condition
-- is the heap tag at *Input1 (cond-eq reduces it to sv-is-zero (SV-Tag k)
-- like sim-test-tag); the x86 cmp reads the same value via heap-eq. The
-- address is base+disp rdi 0, so effectiveAddr carries a +0.
block-step-c-branch-tag-zero : ∀ {hv : HeapView} prog fs s n hl k j → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero n))
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl        -- the branch reads the tag at a live cell (store-WF)
  → heapMem (floc fs) hl ≡ just (SV-Tag k)
  → find-label prog n ≡ just j
  → BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
block-step-c-branch-tag-zero {hv} prog fs s n hl zero j cc h ft i-eq live-hl h-eq fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (mem (base+disp rdi 0)) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    addr-val : xreadReg (xregs s) rdi + 0 ≡ haddr hv hl
    addr-val = trans (+-identityʳ (xreadReg (xregs s) rdi)) (trans (C.rdi-eq dc) (cong (C.enc-sv hv) i-eq))
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rdi 0)) ≡ just 0
    rd = trans (cong (X.readMem (memory s)) addr-val) (trans (C.heap-eq dc hl live-hl) (cong (C.enc-maybe hv) h-eq))
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (0 ≡ᵇ 0) (0 <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    step-cmp = step-cmp-mi {compile-trace prog} {s} {base+disp rdi 0} {0} {0} fetch-cmp rd
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    fl-x86 : X.find-label (compile-trace prog) (once n) ≡ just (x86-off prog j)
    fl-x86 = find-label-corr prog n 0 j fl-eq
    post-je : X.State
    post-je = record post-cmp { pc = x86-off prog j }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-taken {compile-trace prog} {post-cmp} {once n} {x86-off prog j} fetch-je refl fl-x86
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    cond-eq : tag-zf (flat-read-tag (floc fs)) ≡ sv-is-zero (SV-Tag {FS} zero)
    cond-eq = cong tag-zf (trans (cong (flat-read-at (floc fs)) (cong sv-as-loc i-eq)) h-eq)
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
    result rewrite cond-eq | fl-eq = post-je , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                          ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; rsp-eq = C.rsp-eq dc ; r15-eq = C.r15-eq dc ; dom-fresh = C.dom-fresh dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
      ; pc-off = refl }
block-step-c-branch-tag-zero {hv} prog fs s n hl (suc m) j cc h ft i-eq live-hl h-eq fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (mem (base+disp rdi 0)) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    addr-val : xreadReg (xregs s) rdi + 0 ≡ haddr hv hl
    addr-val = trans (+-identityʳ (xreadReg (xregs s) rdi)) (trans (C.rdi-eq dc) (cong (C.enc-sv hv) i-eq))
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rdi 0)) ≡ just (suc m)
    rd = trans (cong (X.readMem (memory s)) addr-val) (trans (C.heap-eq dc hl live-hl) (cong (C.enc-maybe hv) h-eq))
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (suc m ≡ᵇ 0) (suc m <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    step-cmp = step-cmp-mi {compile-trace prog} {s} {base+disp rdi 0} {0} {suc m} fetch-cmp rd
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post-je : X.State
    post-je = record post-cmp { pc = X.State.pc post-cmp + 1 }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-not {compile-trace prog} {post-cmp} {once n} fetch-je refl
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    cond-eq : tag-zf (flat-read-tag (floc fs)) ≡ sv-is-zero (SV-Tag {FS} (suc m))
    cond-eq = cong tag-zf (trans (cong (flat-read-at (floc fs)) (cong sv-as-loc i-eq)) h-eq)
    pco' : X.State.pc post-je ≡ x86-off prog (suc (fpc fs))
    pco' = trans (+-assoc (pc s) 1 1) (trans (cong (_+ 2) po) (sym (x86-off-suc prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)))
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
    result rewrite cond-eq = post-je , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                          ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; rsp-eq = C.rsp-eq dc ; r15-eq = C.r15-eq dc ; dom-fresh = C.dom-fresh dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
      ; pc-off = pco' }

-- alloc-heap: `mov rax, r15 ; add r15, n*8` (2 steps) ↔ the abstract fresh block.
-- THE view-EXTENDING step: the post-state correspondence holds at
-- `C.extend-view hv (next-heap-ref …) n (dom-fresh …)`, where the fresh block sits
-- exactly at the old `%r15`. The store-WF premises (nothing references the not-yet-
-- allocated ref) and the fresh-cell premises are the routing site's obligations.
block-step-alloc-heap : ∀ {hv : HeapView} prog fs s n → (cc : CompiledCorr hv prog fs s)
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-alloc-heap n)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Input1)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Input2)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Scratch)
  → (∀ hl → HDom hv hl → svm-below (next-heap-ref (falloc fs)) (heapMem (floc fs) hl))
  → (∀ k → k < stackSlot (regs (floc fs))
         → svm-below (next-heap-ref (falloc fs)) (stackMem (floc fs) (current-frame (falloc fs)) k))
  → (∀ hl → ref-id (heap-ref hl) ≡ next-heap-ref (falloc fs) → heapMem (floc fs) hl ≡ nothing)
  → (∀ i → i < n → X.readMem (memory s) (xreadReg (xregs s) r15 + slot-to-disp i) ≡ nothing)
  → BlockStep (C.extend-view hv (next-heap-ref (falloc fs)) n (C.dom-fresh (dataCorr cc)))
              prog fs s (instr-alloc-heap n)
block-step-alloc-heap {hv} prog fs s n cc h ft wf1 wf2 wfs wf-heap wf-stack fresh-abs fresh-x86 =
  post-add , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-mov : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg rax) (reg r15))
    fetch-mov = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-alloc-heap n) ft)
    post-mov : X.State
    post-mov = record s { regs = xwriteReg (xregs s) rax (xreadReg (xregs s) r15) ; pc = pc s + 1 }
    step1 : X.step-not-halted (compile-trace prog) s ≡ just post-mov
    step1 = step-mov-rr {compile-trace prog} {s} {rax} {r15} fetch-mov
    fetch-add : X.fetch (compile-trace prog) (X.State.pc post-mov) ≡ just (add (reg r15) (imm (slots n)))
    fetch-add = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                      (fetch-block-2nd prog (fpc fs) (instr-alloc-heap n) ft)
    post-add : X.State
    post-add = record post-mov { regs = xwriteReg (xregs post-mov) r15 (xreadReg (xregs post-mov) r15 + slots n)
                               ; flags = updateFlags (xreadReg (xregs post-mov) r15 + slots n)
                                                     (xreadReg (xregs post-mov) r15)
                               ; pc = pc post-mov + 1 }
    step2 : X.step-not-halted (compile-trace prog) post-mov ≡ just post-add
    step2 = step-add-ri {compile-trace prog} {post-mov} {r15} {slots n} fetch-add
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-add
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-mov} halt-s step1 halt-s)
                    (exec-1 {compile-trace prog} {0} {post-mov} {post-add} halt-s step2 halt-s)
    dataPost : C.FlatCorr (C.extend-view hv (next-heap-ref (falloc fs)) n (C.dom-fresh dc))
                          (flat-exec-instr (instr-alloc-heap n) prog fs) post-add
    fresh-x86' : ∀ i → i < n → X.readMem (memory s) (hfront hv + slot-to-disp i) ≡ nothing
    fresh-x86' i i<n = subst (λ a → X.readMem (memory s) (a + slot-to-disp i) ≡ nothing)
                             (C.r15-eq dc) (fresh-x86 i i<n)
    dataPost = C.sim-alloc-heap n (X.State.flags post-add) (pc post-mov + 1) fs s dc
                 wf1 wf2 wfs wf-heap wf-stack fresh-abs fresh-x86'
    pco' : X.State.pc post-add ≡ x86-off prog (fpc (flat-exec-instr (instr-alloc-heap n) prog fs))
    pco' = trans (trans (cong (λ p → (p + 1) + 1) po) (+-assoc (x86-off prog (fpc fs)) 1 1))
                 (sym (x86-off-suc prog (fpc fs) (instr-alloc-heap n) ft))

-- lea-slot: Output := &stack[frame, slot] ↔ `lea rax, [rsp + slot-to-disp slot]`.
-- Plan 0.61's payoff: `X.effectiveAddr s (base+disp rsp d) = readReg rsp + d`, and
-- `rsp-eq` anchors %rsp to the current frame's base, so the computed address IS
-- the abstract slot's address (`sim-lea-slot`).
block-step-lea-slot : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (lea-slot slot)
  → BlockStep hv prog fs s (lea-slot slot)
block-step-lea-slot {hv} prog fs s slot cc h ft =
  post , exec-eq , record { dataCorr = C.sim-lea-slot slot fs s dc ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (lea rax (base+disp rsp (slot-to-disp slot)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (lea-slot slot) ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax
                               (X.effectiveAddr s (base+disp rsp (slot-to-disp slot)))
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-lea {compile-trace prog} {s} {rax} {base+disp rsp (slot-to-disp slot)} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (lea-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (lea-slot slot) ft))

-- lea-indexed: Input1 := &(base + idx) ↔ the 6-instruction chain
--   mov rdi,[rsp+8·slot] ; mov rcx,rbx ; add rcx,rcx ×3 ; add rdi,rcx
-- The three doublings compute 8·idx (`dbl`), %rcx and the flags are untracked,
-- and memory is only read — so the whole correspondence rides `sim-lea-indexed`.
dbl : ∀ (n : ℕ) → n + n ≡ n * 2
dbl n = sym (trans (*-suc n 1) (cong (n +_) (*-identityʳ n)))

block-step-lea-indexed : ∀ {hv : HeapView} prog fs s slot loc idx
  → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (lea-indexed slot)
  → readLoc (floc fs) (AtStack (current-frame (falloc fs)) slot) ≡ just (SV-Ptr loc)
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag idx
  → slot < stackSlot (regs (floc fs))          -- the base slot is frame-live (WF)
  → BlockStep hv prog fs s (lea-indexed slot)
block-step-lea-indexed {hv} prog fs s slot loc idx cc h ft slot-eq sc-eq slot<ss =
  s₆ , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    baseA : X.Word
    baseA = C.enc-sv hv (SV-Ptr loc)
    -- (1) mov rdi, [rsp + 8·slot]
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rsp (slot-to-disp slot))) ≡ just baseA
    rd = trans (C.stack-eq dc slot slot<ss) (cong (C.enc-maybe hv) slot-eq)
    f₁ : X.fetch (compile-trace prog) (X.State.pc s)
       ≡ just (mov (reg rdi) (mem (base+disp rsp (slot-to-disp slot))))
    f₁ = trans (cong (X.fetch (compile-trace prog)) po)
               (fetch-block-head prog (fpc fs) (lea-indexed slot) ft)
    s₁ = record s { regs = xwriteReg (xregs s) rdi baseA ; pc = pc s + 1 }
    st₁ : X.step-not-halted (compile-trace prog) s ≡ just s₁
    st₁ = step-mov-rm {compile-trace prog} {s} {rdi} {base+disp rsp (slot-to-disp slot)} {baseA} f₁ rd
    -- (2) mov rcx, rbx
    f₂ : X.fetch (compile-trace prog) (X.State.pc s₁) ≡ just (mov (reg rcx) (reg rbx))
    f₂ = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
               (fetch-block-2nd prog (fpc fs) (lea-indexed slot) ft)
    s₂ = record s₁ { regs = xwriteReg (xregs s₁) rcx (xreadReg (xregs s₁) rbx) ; pc = pc s₁ + 1 }
    st₂ : X.step-not-halted (compile-trace prog) s₁ ≡ just s₂
    st₂ = step-mov-rr {compile-trace prog} {s₁} {rcx} {rbx} f₂
    -- (3-5) add rcx, rcx  ×3
    f₃ : X.fetch (compile-trace prog) (X.State.pc s₂) ≡ just (add (reg rcx) (reg rcx))
    f₃ = trans (cong (λ p → X.fetch (compile-trace prog) ((p + 1) + 1)) po)
          (trans (cong (X.fetch (compile-trace prog)) (+-assoc (x86-off prog (fpc fs)) 1 1))
                 (fetch-block-3rd prog (fpc fs) (lea-indexed slot) ft))
    s₃ = record s₂ { regs = xwriteReg (xregs s₂) rcx (xreadReg (xregs s₂) rcx + xreadReg (xregs s₂) rcx)
                   ; flags = updateFlags (xreadReg (xregs s₂) rcx + xreadReg (xregs s₂) rcx)
                                         (xreadReg (xregs s₂) rcx)
                   ; pc = pc s₂ + 1 }
    st₃ : X.step-not-halted (compile-trace prog) s₂ ≡ just s₃
    st₃ = step-add-rr {compile-trace prog} {s₂} {rcx} {rcx} f₃
    f₄ : X.fetch (compile-trace prog) (X.State.pc s₃) ≡ just (add (reg rcx) (reg rcx))
    f₄ = trans (cong (λ p → X.fetch (compile-trace prog) (((p + 1) + 1) + 1)) po)
          (trans (cong (X.fetch (compile-trace prog))
                       (trans (cong (_+ 1) (+-assoc (x86-off prog (fpc fs)) 1 1))
                              (+-assoc (x86-off prog (fpc fs)) 2 1)))
                 (fetch-block-4th prog (fpc fs) (lea-indexed slot) ft))
    s₄ = record s₃ { regs = xwriteReg (xregs s₃) rcx (xreadReg (xregs s₃) rcx + xreadReg (xregs s₃) rcx)
                   ; flags = updateFlags (xreadReg (xregs s₃) rcx + xreadReg (xregs s₃) rcx)
                                         (xreadReg (xregs s₃) rcx)
                   ; pc = pc s₃ + 1 }
    st₄ : X.step-not-halted (compile-trace prog) s₃ ≡ just s₄
    st₄ = step-add-rr {compile-trace prog} {s₃} {rcx} {rcx} f₄
    f₅ : X.fetch (compile-trace prog) (X.State.pc s₄) ≡ just (add (reg rcx) (reg rcx))
    f₅ = trans (cong (λ p → X.fetch (compile-trace prog) ((((p + 1) + 1) + 1) + 1)) po)
          (trans (cong (X.fetch (compile-trace prog))
                       (trans (cong (λ z → (z + 1) + 1) (+-assoc (x86-off prog (fpc fs)) 1 1))
                              (trans (cong (_+ 1) (+-assoc (x86-off prog (fpc fs)) 2 1))
                                     (+-assoc (x86-off prog (fpc fs)) 3 1))))
                 (fetch-block-5th prog (fpc fs) (lea-indexed slot) ft))
    s₅ = record s₄ { regs = xwriteReg (xregs s₄) rcx (xreadReg (xregs s₄) rcx + xreadReg (xregs s₄) rcx)
                   ; flags = updateFlags (xreadReg (xregs s₄) rcx + xreadReg (xregs s₄) rcx)
                                         (xreadReg (xregs s₄) rcx)
                   ; pc = pc s₄ + 1 }
    st₅ : X.step-not-halted (compile-trace prog) s₄ ≡ just s₅
    st₅ = step-add-rr {compile-trace prog} {s₄} {rcx} {rcx} f₅
    -- (6) add rdi, rcx
    f₆ : X.fetch (compile-trace prog) (X.State.pc s₅) ≡ just (add (reg rdi) (reg rcx))
    f₆ = trans (cong (λ p → X.fetch (compile-trace prog) (((((p + 1) + 1) + 1) + 1) + 1)) po)
          (trans (cong (X.fetch (compile-trace prog))
                       (trans (cong (λ z → ((z + 1) + 1) + 1) (+-assoc (x86-off prog (fpc fs)) 1 1))
                              (trans (cong (λ z → (z + 1) + 1) (+-assoc (x86-off prog (fpc fs)) 2 1))
                                     (trans (cong (_+ 1) (+-assoc (x86-off prog (fpc fs)) 3 1))
                                            (+-assoc (x86-off prog (fpc fs)) 4 1)))))
                 (fetch-block-6th prog (fpc fs) (lea-indexed slot) ft))
    s₆ = record s₅ { regs = xwriteReg (xregs s₅) rdi (xreadReg (xregs s₅) rdi + xreadReg (xregs s₅) rcx)
                   ; flags = updateFlags (xreadReg (xregs s₅) rdi + xreadReg (xregs s₅) rcx)
                                         (xreadReg (xregs s₅) rdi)
                   ; pc = pc s₅ + 1 }
    st₆ : X.step-not-halted (compile-trace prog) s₅ ≡ just s₆
    st₆ = step-add-rr {compile-trace prog} {s₅} {rdi} {rcx} f₆
    exec-eq : X.exec 6 (compile-trace prog) s ≡ just s₆
    exec-eq = trans (exec-1 {compile-trace prog} {5} {s} {s₁} halt-s st₁ halt-s)
              (trans (exec-1 {compile-trace prog} {4} {s₁} {s₂} halt-s st₂ halt-s)
              (trans (exec-1 {compile-trace prog} {3} {s₂} {s₃} halt-s st₃ halt-s)
              (trans (exec-1 {compile-trace prog} {2} {s₃} {s₄} halt-s st₄ halt-s)
              (trans (exec-1 {compile-trace prog} {1} {s₄} {s₅} halt-s st₅ halt-s)
                     (exec-1 {compile-trace prog} {0} {s₅} {s₆} halt-s st₆ halt-s)))))
    -- %rcx holds 8·idx after the doublings; %rbx (Scratch) is `idx` by rbx-eq.
    idx-eq : xreadReg (xregs s₁) rbx ≡ idx
    idx-eq = trans (C.rbx-eq dc) (cong (C.enc-sv hv) sc-eq)
    rcx-eq : xreadReg (xregs s₅) rcx ≡ idx * slot-size
    rcx-eq = trans (cong (λ z → ((z + z) + (z + z)) + ((z + z) + (z + z))) idx-eq) (eight idx)
      where eight : ∀ n → ((n + n) + (n + n)) + ((n + n) + (n + n)) ≡ n * slot-size
            eight n = trans (cong (λ z → (z + z) + (z + z)) (dbl n))
                      (trans (cong (λ z → z + z) (dbl (n * 2)))
                      (trans (dbl ((n * 2) * 2))
                      (trans (cong (_* 2) (*-assoc n 2 2)) (*-assoc n 4 2))))
    rdi-p : xreadReg (xregs s₆) rdi ≡ baseA + idx * slot-size
    rdi-p = cong (baseA +_) rcx-eq
    dataPost : C.FlatCorr hv (flat-exec-instr (lea-indexed slot) prog fs) s₆
    dataPost = C.sim-lea-indexed slot loc idx fs s s₆ dc slot-eq sc-eq
                 rdi-p refl refl refl refl refl refl refl
    pco' : X.State.pc s₆ ≡ x86-off prog (fpc (flat-exec-instr (lea-indexed slot) prog fs))
    pco' = trans (trans (cong (λ p → (((((p + 1) + 1) + 1) + 1) + 1) + 1) po) assoc)
                 (sym (x86-off-suc prog (fpc fs) (lea-indexed slot) ft))
      where m = x86-off prog (fpc fs)
            assoc : (((((m + 1) + 1) + 1) + 1) + 1) + 1 ≡ m + 6
            assoc = trans (cong (λ z → (((z + 1) + 1) + 1) + 1) (+-assoc m 1 1))
                    (trans (cong (λ z → ((z + 1) + 1) + 1) (+-assoc m 2 1))
                    (trans (cong (λ z → (z + 1) + 1) (+-assoc m 3 1))
                    (trans (cong (_+ 1) (+-assoc m 4 1))
                           (+-assoc m 5 1))))


-- c-branch NOT TAKEN (`Scratch ≡ SV-Tag (suc m)`): the `je` falls through, so the
-- jump target is never consulted — no label premise, which is what lets the
-- MISSING-label case of a not-taken branch be an ordinary step rather than a
-- residual. (The taken case still needs `find-label ≡ just j`.)
block-step-c-branch-nz : ∀ {hv : HeapView} prog fs s n m → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero n))
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag (suc m)
  → BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
block-step-c-branch-nz {hv} prog fs s n m cc h ft sc-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (reg rbx) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (xreadReg (xregs s) rbx ≡ᵇ 0) (xreadReg (xregs s) rbx <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    step-cmp = step-cmp-ri {compile-trace prog} {s} {rbx} {0} fetch-cmp
    rbx-val : xreadReg (xregs s) rbx ≡ suc m
    rbx-val = trans (C.rbx-eq dc) (cong (C.enc-sv hv) sc-eq)
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    zf-false : X.Flags.zf (flags post-cmp) ≡ false
    zf-false = cong (_≡ᵇ 0) rbx-val
    post-je : X.State
    post-je = record post-cmp { pc = X.State.pc post-cmp + 1 }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-not {compile-trace prog} {post-cmp} {once n} fetch-je zf-false
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    pco' : X.State.pc post-je ≡ x86-off prog (suc (fpc fs))
    pco' = trans (+-assoc (pc s) 1 1) (trans (cong (_+ 2) po) (sym (x86-off-suc prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)))
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq = post-je , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                          ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; rsp-eq = C.rsp-eq dc ; r15-eq = C.r15-eq dc ; dom-fresh = C.dom-fresh dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
      ; pc-off = pco' }


-- load-indirect through a STACK pointer ↔ `mov rax, [rdi]`. `rdi-eq` gives
-- rdi ≡ slot-addr f k; for the CURRENT frame `rsp-eq` + `slot-addr-linear` turn
-- that into `rsp + slot-to-disp k`, which is exactly the address `stack-eq`
-- speaks about — so the loaded value is the slot's. Unprovable before plan 0.61,
-- when a stack pointer encoded to the placeholder `0`.
block-step-load-indirect-stack : ∀ {hv : HeapView} prog fs s f k w → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → f ≡ current-frame (falloc fs)
  → k < stackSlot (regs (floc fs))
  → stackMem (floc fs) (current-frame (falloc fs)) k ≡ just w
  → BlockStep hv prog fs s load-indirect
block-step-load-indirect-stack {hv} prog fs s f k w cc h ft i-eq f-eq k<ss st-eq =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg rax) (mem (base rdi)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect ft)
    -- rdi is the slot's ADDRESS, and for the current frame that is rsp-relative
    rdi-val : xreadReg (xregs s) rdi ≡ xreadReg (xregs s) rsp + slot-to-disp k
    rdi-val = trans (C.rdi-eq dc)
              (trans (cong (C.enc-sv hv) i-eq)
              (trans (cong (λ fr → slot-addr FS fr k) f-eq)
              (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                     (cong₂ (λ b w' → b + k * w') (sym (C.rsp-eq dc)) word-eq))))
    rd : X.readMem (memory s) (X.effectiveAddr s (base rdi)) ≡ just (C.enc-sv hv w)
    rd = trans (cong (X.readMem (memory s)) rdi-val)
               (trans (C.stack-eq dc k k<ss) (cong (C.enc-maybe hv) st-eq))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rax} {base rdi} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr load-indirect prog fs) post
    dataPost = C.sim-load-indirect-stack f k w fs s dc i-eq
                 (trans (cong (λ fr → stackMem (floc fs) fr k) f-eq) st-eq)
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr load-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) load-indirect ft))

-- load-indirect-suc through a stack pointer ↔ `mov rax, [rdi + 8]`. The x86
-- address is `slot-addr f k + 8`, which for the current frame is
-- `rsp + slot-to-disp (suc k)` — the cell `stack-eq` relates to slot `suc k`.
block-step-load-indirect-suc-stack : ∀ {hv : HeapView} prog fs s f k w → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → f ≡ current-frame (falloc fs)
  → suc k < stackSlot (regs (floc fs))
  → stackMem (floc fs) (current-frame (falloc fs)) (suc k) ≡ just w
  → BlockStep hv prog fs s load-indirect-suc
block-step-load-indirect-suc-stack {hv} prog fs s f k w cc h ft i-eq f-eq sk<ss st-eq =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg rax) (mem (base+disp rdi slot-size)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect-suc ft)
    -- rdi + 8 = (rsp + 8·k) + 8 = rsp + 8·(suc k)
    addr-eq : xreadReg (xregs s) rdi + slot-size
            ≡ xreadReg (xregs s) rsp + slot-to-disp (suc k)
    addr-eq = trans (cong (_+ slot-size)
                      (trans (C.rdi-eq dc)
                      (trans (cong (C.enc-sv hv) i-eq)
                      (trans (cong (λ fr → slot-addr FS fr k) f-eq)
                      (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                             (cong₂ (λ b w' → b + k * w') (sym (C.rsp-eq dc)) word-eq))))))
                    (trans (+-assoc (xreadReg (xregs s) rsp) (k * slot-size) slot-size)
                           (cong (xreadReg (xregs s) rsp +_)
                                 (+-comm (k * slot-size) slot-size)))
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rdi slot-size)) ≡ just (C.enc-sv hv w)
    rd = trans (cong (X.readMem (memory s)) addr-eq)
               (trans (C.stack-eq dc (suc k) sk<ss) (cong (C.enc-maybe hv) st-eq))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rax} {base+disp rdi slot-size} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr load-indirect-suc prog fs) post
    dataPost = C.sim-load-indirect-suc-stack f k w fs s dc i-eq
                 (trans (cong (λ fr → stackMem (floc fs) fr (suc k)) f-eq) st-eq)
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr load-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) load-indirect-suc ft))

-- store-indirect through a stack pointer ↔ `mov [rdi], rax`, where rdi is the
-- slot's address. Same shape as `block-step-store-at-slot`, with the address
-- coming from Input1 (`rdi-eq` + `slot-addr-linear` + `rsp-eq`).
block-step-store-indirect-stack : ∀ {hv : HeapView} prog fs s f k → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → f ≡ current-frame (falloc fs)
  → k < stackSlot (regs (floc fs))
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) rsp + slot-to-disp k ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s store-indirect
block-step-store-indirect-stack {hv} prog fs s f k cc h ft i-eq f-eq k<ss disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    Out = readReg (regs (floc fs)) Output
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (mem (base rdi)) (reg rax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) store-indirect ft)
    rdi-val : xreadReg (xregs s) rdi ≡ xreadReg (xregs s) rsp + slot-to-disp k
    rdi-val = trans (C.rdi-eq dc)
              (trans (cong (C.enc-sv hv) i-eq)
              (trans (cong (λ fr → slot-addr FS fr k) f-eq)
              (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                     (cong₂ (λ b w' → b + k * w') (sym (C.rsp-eq dc)) word-eq))))
    i-eq' : readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
    i-eq' = trans i-eq (cong (λ fr → SV-Ptr (AtStack fr k)) f-eq)
    post : X.State
    post = record s { memory = writeMem (memory s) (xreadReg (xregs s) rsp + slot-to-disp k)
                                        (C.enc-sv hv Out)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = trans (step-mov-mr {compile-trace prog} {s} {base rdi} {rax} fetch-x86)
                (cong just (cong₂ (λ a v → record s { memory = writeMem (memory s) a v ; pc = pc s + 1 })
                                  rdi-val (C.rax-eq dc)))
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect prog fs) post
    dataPost = C.sim-store-indirect-stack k fs s dc i-eq' disj
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr store-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) store-indirect ft))
