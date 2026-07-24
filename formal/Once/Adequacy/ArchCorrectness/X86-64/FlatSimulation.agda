-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation
--
-- Plan 0.32 Phase D, Stage 2: the abstract↔x86 plus-simulation over the
-- flat machine. `CompiledCorr prog fs s` relates a FlatState `fs` (flat
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

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Data.Nat using (ℕ; _+_; _∸_; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation
  (FS : FrameSemantics)
  (enc-hl : HeapLocation → ℕ)
  -- CompCert memory injection on LIVE cells + the allocator's live-block
  -- distinctness (see FlatCorrespondence). Replaces the (unsatisfiable) global
  -- `enc-hl-inj`.
  (LiveIn : AllocState {FS} → HeapLocation → Set)
  (enc-hl-inj-live : ∀ (as : AllocState {FS}) {a b : HeapLocation}
                   → LiveIn as a → LiveIn as b → enc-hl a ≡ enc-hl b → a ≡ b)
  -- heap layout successor law: a cell's successor sits one slot higher.
  (enc-hl-suc : ∀ (hl : HeapLocation) → enc-hl (sucHL hl) ≡ enc-hl hl + slot-size)
  where

open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X
open X using (mkstate; execInstr; mkflags; _<ᵇ_; writeMem; updateFlags)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax
  using (rax; rbx; rsi; rdi; rsp; Reg; Operand; Program; reg; imm; mem; mov; add; sub; cmp; label; jmp; je; base; base+disp)
open import Data.Maybe using (just)
open import Data.Bool using (true; false)
open import Data.List using (_∷_; []; _++_; drop; length)
open import Relation.Binary.PropositionalEquality using (refl)

import Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence as FC
module C = FC FS enc-hl LiveIn enc-hl-inj-live   -- enc-sv / FlatCorr data fields
open import Once.CCC.Label using (once)
open import Once.Adequacy.ArchCorrectness.X86-64.FlatComposition FS
  using (x86-off; x86-len; x86-off-suc; fetch-block-head; find-label-corr; fetch-block-2nd)
open import Once.Adequacy.ArchCorrectness.X86-64.StepLemmas using (exec-1; step-mov-rr; step-mov-ri; step-label; step-jmp; step-mov-rm; step-mov-mr; step-add-ri; step-sub-ri; step-cmp-ri; step-cmp-mi; step-je-taken; step-je-not)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace; compile-abstract; slot-to-disp)
open import Data.Empty using (⊥)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)
open MemOps {FS} using (writeLoc; writeLocToHeap)

------------------------------------------------------------------------
-- The compiled correspondence = the DATA correspondence (FlatCorr, now
-- pc-free) ⊕ the block-offset pc relation. block-step gets the data from
-- the sim-* lemmas (which produce FlatCorr) and the pc from x86-off-suc /
-- find-label-corr — cleanly separated. (Plan 0.34: no zf-eq.)
------------------------------------------------------------------------
record CompiledCorr (prog : AbstractTrace) (fs : FlatState) (s : X.State) : Set where
  field
    dataCorr : C.FlatCorr fs s
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
BlockStep : AbstractTrace → FlatState → X.State → AbstractInstr → Set
BlockStep prog fs s i =
  Σ X.State (λ s' → (X.exec (x86-len i) (compile-trace prog) s ≡ just s')
                  × CompiledCorr prog (flat-exec-instr i prog fs) s')

-- Generic single-`mov reg,reg` block-step: any straight-line instruction
-- whose x86 block is one `mov (reg dst) (reg src)`. The caller supplies the
-- compile-abstract shape (refl) + the DATA correspondence (a sim-* lemma).
-- Assembly: fetch-block-head + step-mov-rr + exec-1 (x86), then pc via
-- pc-off + x86-off-suc. No flags (Plan 0.34).
block-step-mov-rr : ∀ (prog : AbstractTrace) (fs : FlatState) (s : X.State)
    (i : AbstractInstr) (dst src : Reg)
  → CompiledCorr prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just i
  → compile-abstract i ≡ mov (reg dst) (reg src) ∷ []
  → fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)         -- i is straight-line
  → C.FlatCorr (flat-exec-instr i prog fs)
               (record s { regs = xwriteReg (xregs s) dst (xreadReg (xregs s) src) ; pc = pc s + 1 })
  → BlockStep prog fs s i
block-step-mov-rr prog fs s i dst src cc h-flat ft ca fpc-eq dataPost =
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
block-step-mov-to-output : ∀ prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-to-output → BlockStep prog fs s mov-to-output
block-step-mov-to-output prog fs s cc h ft =
  block-step-mov-rr prog fs s mov-to-output rax rdi cc h ft refl refl (C.sim-mov-to-output fs s (dataCorr cc))

block-step-mov-to-input : ∀ prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-to-input → BlockStep prog fs s mov-to-input
block-step-mov-to-input prog fs s cc h ft =
  block-step-mov-rr prog fs s mov-to-input rdi rax cc h ft refl refl (C.sim-mov-to-input fs s (dataCorr cc))

block-step-mov-input2-to-output : ∀ prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-input2-to-output → BlockStep prog fs s mov-input2-to-output
block-step-mov-input2-to-output prog fs s cc h ft =
  block-step-mov-rr prog fs s mov-input2-to-output rax rsi cc h ft refl refl (C.sim-mov-input2-to-output fs s (dataCorr cc))

block-step-mov-output-to-input2 : ∀ prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-output-to-input2 → BlockStep prog fs s mov-output-to-input2
block-step-mov-output-to-input2 prog fs s cc h ft =
  block-step-mov-rr prog fs s mov-output-to-input2 rsi rax cc h ft refl refl (C.sim-mov-output-to-input2 fs s (dataCorr cc))

-- Generic single-`mov reg,imm` block-step (load-tag-lit, reg-op imm loads).
block-step-mov-ri : ∀ (prog : AbstractTrace) (fs : FlatState) (s : X.State)
    (i : AbstractInstr) (dst : Reg) (n : ℕ)
  → CompiledCorr prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just i
  → compile-abstract i ≡ mov (reg dst) (imm n) ∷ []
  → fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)
  → C.FlatCorr (flat-exec-instr i prog fs)
               (record s { regs = xwriteReg (xregs s) dst n ; pc = pc s + 1 })
  → BlockStep prog fs s i
block-step-mov-ri prog fs s i dst n cc h-flat ft ca fpc-eq dataPost =
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

block-step-load-tag-lit : ∀ prog fs s n → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-tag-lit n) → BlockStep prog fs s (instr-load-tag-lit n)
block-step-load-tag-lit prog fs s n cc h ft =
  block-step-mov-ri prog fs s (instr-load-tag-lit n) rax n cc h ft refl refl (C.sim-load-tag-lit n fs s (dataCorr cc))

block-step-scratch-one : ∀ prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-one) → BlockStep prog fs s (instr-reg-op scratch-one)
block-step-scratch-one prog fs s cc h ft =
  block-step-mov-ri prog fs s (instr-reg-op scratch-one) rbx 1 cc h ft refl refl (C.sim-reg-scratch-one fs s (dataCorr cc))

block-step-scratch-zero : ∀ prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-zero) → BlockStep prog fs s (instr-reg-op scratch-zero)
block-step-scratch-zero prog fs s cc h ft =
  block-step-mov-ri prog fs s (instr-reg-op scratch-zero) rbx 0 cc h ft refl refl (C.sim-reg-scratch-zero fs s (dataCorr cc))

block-step-input2-zero : ∀ prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op input2-zero) → BlockStep prog fs s (instr-reg-op input2-zero)
block-step-input2-zero prog fs s cc h ft =
  block-step-mov-ri prog fs s (instr-reg-op input2-zero) rsi 0 cc h ft refl refl (C.sim-reg-input2-zero fs s (dataCorr cc))

block-step-scratch-load-count : ∀ prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-load-count) → BlockStep prog fs s (instr-reg-op scratch-load-count)
block-step-scratch-load-count prog fs s cc h ft =
  block-step-mov-rr prog fs s (instr-reg-op scratch-load-count) rbx rsi cc h ft refl refl (C.sim-reg-scratch-load-count fs s (dataCorr cc))

-- c-label: pc passes through (x86 `label` is a 1-instr no-op). The flat
-- step only bumps fpc, so the DATA correspondence transports unchanged
-- (no sim-* needed — floc/regs are untouched on both sides).
block-step-c-label : ∀ prog fs s n → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-label n)) → BlockStep prog fs s (instr-ctrl (c-label n))
block-step-c-label prog fs s n cc h ft = post , exec-eq , record
  { dataCorr = record { rdi-eq = C.rdi-eq (dataCorr cc) ; rsi-eq = C.rsi-eq (dataCorr cc)
                      ; rax-eq = C.rax-eq (dataCorr cc) ; rbx-eq = C.rbx-eq (dataCorr cc)
                      ; halt-eq = C.halt-eq (dataCorr cc) ; heap-eq = C.heap-eq (dataCorr cc)
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
block-step-worklist-init : ∀ prog fs s n → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-init n) → BlockStep prog fs s (worklist-init n)
block-step-worklist-init prog fs s n cc h ft = s , refl , record
  { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                      ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
  ; pc-off = trans (pc-off cc)
             (sym (trans (x86-off-suc prog (fpc fs) (worklist-init n) ft) (+-identityʳ _))) }
  where dc = dataCorr cc

block-step-worklist-check : ∀ prog fs s n → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-check n) → BlockStep prog fs s (worklist-check n)
block-step-worklist-check prog fs s n cc h ft = s , refl , record
  { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                      ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
  ; pc-off = trans (pc-off cc)
             (sym (trans (x86-off-suc prog (fpc fs) (worklist-check n) ft) (+-identityʳ _))) }
  where dc = dataCorr cc

-- instr-reclaim-to: allocation bookkeeping — compile to [] (x86-len 0), flat step
-- lowers `next-slot` (floc + heapMem unchanged). heap-eq copies EXCEPT the LiveIn
-- quantifier shifts to `next-slot := n`; reclaiming only SHRINKS the live set, so the
-- new witness maps back (LiveIn-reclaim, an allocator property discharged offline).
postulate
  LiveIn-reclaim : ∀ (alloc : AllocState {FS}) (n : ℕ) (hl : HeapLocation)
                 → LiveIn (record alloc { next-slot = n }) hl → LiveIn alloc hl

block-step-reclaim-to : ∀ prog fs s n → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reclaim-to n) → BlockStep prog fs s (instr-reclaim-to n)
block-step-reclaim-to prog fs s n cc h ft = s , refl , record
  { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                      ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc
                      ; heap-eq = λ hl live → C.heap-eq dc hl (LiveIn-reclaim (falloc fs) n hl live)
                      ; stack-eq = C.stack-eq dc }
  ; pc-off = trans (pc-off cc)
             (sym (trans (x86-off-suc prog (fpc fs) (instr-reclaim-to n) ft) (+-identityʳ _))) }
  where dc = dataCorr cc

-- c-jmp: unconditional jump. find-label-corr maps the flat label index to
-- the x86 block-offset, so the x86 `jmp` lands at the same place. Data
-- unchanged (jmp touches only the pc). Hypothesis: the target exists.
block-step-c-jmp : ∀ prog fs s n j → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp n))
  → find-label prog n ≡ just j
  → BlockStep prog fs s (instr-ctrl (c-jmp n))
block-step-c-jmp prog fs s n j cc h ft fl-eq = block-step
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
    block-step : BlockStep prog fs s (instr-ctrl (c-jmp n))
    block-step rewrite fl-eq = post , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc
                          ; rax-eq = C.rax-eq dc ; rbx-eq = C.rbx-eq dc
                          ; halt-eq = C.halt-eq dc ; heap-eq = C.heap-eq dc
                          ; stack-eq = C.stack-eq dc }
      ; pc-off = refl }

-- load-indirect: Output := *Input1 ↔ `mov rax, [rdi]`. The read VALUE comes
-- from heap-eq (memory s at enc-hl hl = enc-sv w), the ADDRESS from rdi-eq
-- (rdi = enc-hl hl since Input1 = SV-Ptr (AtDynamic hl)).
block-step-load-indirect : ∀ prog fs s hl w → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → LiveIn (falloc fs) hl        -- the loaded pointer is live (store-WF)
  → heapMem (floc fs) hl ≡ just w
  → BlockStep prog fs s load-indirect
block-step-load-indirect prog fs s hl w cc h ft i-eq live-hl h-eq =
  post , exec-eq , record { dataCorr = C.sim-load-indirect hl w fs s dc i-eq h-eq ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg rax) (mem (base rdi)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect ft)
    rdi-val : xreadReg (xregs s) rdi ≡ enc-hl hl
    rdi-val = trans (C.rdi-eq dc) (cong C.enc-sv i-eq)
    rd : X.readMem (memory s) (X.effectiveAddr s (base rdi)) ≡ just (C.enc-sv w)
    rd = trans (cong (X.readMem (memory s)) rdi-val) (trans (C.heap-eq dc hl live-hl) (cong C.enc-maybe h-eq))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (C.enc-sv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rax} {base rdi} {C.enc-sv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr load-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) load-indirect ft))

-- load-indirect-suc: Output := *(sucLoc Input1) ↔ `mov rax, [rdi + slot]`.
-- The address law enc-hl-suc bridges the x86 effective address (enc-hl hl +
-- slot-size) to the heap cell at sucHL hl (enc-hl (sucHL hl)).
block-step-load-indirect-suc : ∀ prog fs s hl w → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → LiveIn (falloc fs) (sucHL hl)     -- the loaded second cell is live (store-WF)
  → heapMem (floc fs) (sucHL hl) ≡ just w
  → BlockStep prog fs s load-indirect-suc
block-step-load-indirect-suc prog fs s hl w cc h ft i-eq live-shl h-eq =
  post , exec-eq , record { dataCorr = C.sim-load-indirect-suc hl w fs s dc i-eq h-eq ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg rax) (mem (base+disp rdi slot-size)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect-suc ft)
    rdi-val : xreadReg (xregs s) rdi ≡ enc-hl hl
    rdi-val = trans (C.rdi-eq dc) (cong C.enc-sv i-eq)
    addr-eq : X.effectiveAddr s (base+disp rdi slot-size) ≡ enc-hl (sucHL hl)
    addr-eq = trans (cong (_+ slot-size) rdi-val) (sym (enc-hl-suc hl))
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rdi slot-size)) ≡ just (C.enc-sv w)
    rd = trans (cong (X.readMem (memory s)) addr-eq) (trans (C.heap-eq dc (sucHL hl) live-shl) (cong C.enc-maybe h-eq))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (C.enc-sv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rax} {base+disp rdi slot-size} {C.enc-sv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr load-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) load-indirect-suc ft))

-- load-from-slot: Output := stack[current-frame, slot] ↔ `mov rax, [rsp + disp]`.
-- The read VALUE comes from the NEW stack-eq field (memory s at rsp+disp = enc-maybe
-- of the slot's abstract value); with the slot holding `just w`, that pins the x86
-- read to `just (enc-sv w)` — feeding step-mov-rm exactly as load-indirect uses heap-eq.
-- FIRST consumer of stack-eq: deleting the field breaks `rd`.
block-step-load-from-slot : ∀ prog fs s slot w → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (load-from-slot slot)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep prog fs s (load-from-slot slot)
block-step-load-from-slot prog fs s slot w cc h ft st-eq =
  post , exec-eq , record { dataCorr = C.sim-load-from-slot slot w fs s dc st-eq ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg rax) (mem (base+disp rsp (slot-to-disp slot))))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (load-from-slot slot) ft)
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rsp (slot-to-disp slot))) ≡ just (C.enc-sv w)
    rd = trans (C.stack-eq dc slot) (cong C.enc-maybe st-eq)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (C.enc-sv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rax} {base+disp rsp (slot-to-disp slot)} {C.enc-sv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (load-from-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (load-from-slot slot) ft))

-- restore-input: Input1 := stack[current-frame, slot] ↔ `mov rdi, [rsp+disp]`.
-- Identical to load-from-slot but the destination register is rdi (Input1).
block-step-restore-input : ∀ prog fs s slot w → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (restore-input slot)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep prog fs s (restore-input slot)
block-step-restore-input prog fs s slot w cc h ft st-eq =
  post , exec-eq , record { dataCorr = C.sim-restore-input slot w fs s dc st-eq ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg rdi) (mem (base+disp rsp (slot-to-disp slot))))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (restore-input slot) ft)
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rsp (slot-to-disp slot))) ≡ just (C.enc-sv w)
    rd = trans (C.stack-eq dc slot) (cong C.enc-maybe st-eq)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rdi (C.enc-sv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rdi} {base+disp rsp (slot-to-disp slot)} {C.enc-sv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (restore-input slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (restore-input slot) ft))

-- worklist-push / worklist-pop: their abstract semantics + x86 lowering are
-- IDENTICAL to store-at-slot / load-from-slot respectively (SMCore/AbstractToX86),
-- so flat-exec-instr reduces the same way and the sim-* lemmas are reused verbatim.
block-step-worklist-push : ∀ prog fs s slot → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-push slot)
  → (∀ hl' → LiveIn (falloc fs) hl' → (X.readReg (xregs s) rsp + slot-to-disp slot ≡ enc-hl hl') → ⊥)
  → BlockStep prog fs s (worklist-push slot)
block-step-worklist-push prog fs s slot cc h ft disj =
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
                                       (C.enc-sv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ v → mkstate (xregs s)
                            (writeMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp slot) v)
                            (flags s) (pc s + 1) (xhalted s))
                   (C.rax-eq dc)
    dataPost : C.FlatCorr (flat-exec-instr (worklist-push slot) prog fs) post
    dataPost = subst (C.FlatCorr (flat-exec-instr (worklist-push slot) prog fs)) (sym post-eq)
                     (C.sim-store-at-slot slot fs s dc disj)
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (worklist-push slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (worklist-push slot) ft))

block-step-worklist-pop : ∀ prog fs s slot w → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-pop slot)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep prog fs s (worklist-pop slot)
block-step-worklist-pop prog fs s slot w cc h ft st-eq =
  post , exec-eq , record { dataCorr = C.sim-load-from-slot slot w fs s dc st-eq ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg rax) (mem (base+disp rsp (slot-to-disp slot))))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (worklist-pop slot) ft)
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rsp (slot-to-disp slot))) ≡ just (C.enc-sv w)
    rd = trans (C.stack-eq dc slot) (cong C.enc-maybe st-eq)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) rax (C.enc-sv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {rax} {base+disp rsp (slot-to-disp slot)} {C.enc-sv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (worklist-pop slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (worklist-pop slot) ft))

-- store-indirect: *Input1 := Output ↔ `mov [rdi], rax`. step-mov-mr writes
-- the RAW register values (readReg rdi / readReg rax); sim-store-indirect's
-- post has the ENCODED values (enc-hl hl / enc-sv Output) — bridge the two
-- post-states via rdi-eq + rax-eq, then transport the data correspondence.
block-step-store-indirect : ∀ prog fs s hl → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → LiveIn (falloc fs) hl        -- the store target is live (store-WF)
  → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ enc-hl hl) → ⊥)   -- heap/stack disjoint
  → BlockStep prog fs s store-indirect
block-step-store-indirect prog fs s hl cc h ft i-eq live-hl guard disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (mem (base rdi)) (reg rax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) store-indirect ft)
    rdi-val : xreadReg (xregs s) rdi ≡ enc-hl hl
    rdi-val = trans (C.rdi-eq dc) (cong C.enc-sv i-eq)
    post : X.State
    post = record s { memory = writeMem (memory s) (X.effectiveAddr s (base rdi)) (xreadReg (xregs s) rax)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-mr {compile-trace prog} {s} {base rdi} {rax} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    -- bridge post (raw) ≡ sim-post (encoded)
    post-eq : post ≡ mkstate (xregs s) (writeMem (memory s) (enc-hl hl) (C.enc-sv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ m → mkstate (xregs s) m (flags s) (pc s + 1) (xhalted s))
                   (cong₂ (writeMem (memory s)) rdi-val (C.rax-eq dc))
    dataPost : C.FlatCorr (flat-exec-instr store-indirect prog fs) post
    dataPost = subst (C.FlatCorr (flat-exec-instr store-indirect prog fs)) (sym post-eq)
                     (C.sim-store-indirect hl fs s dc i-eq live-hl guard disj)
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr store-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) store-indirect ft))

-- store-indirect-suc: *(sucLoc Input1) := Output ↔ `mov [rdi+slot], rax`.
-- Like store-indirect + the address law enc-hl-suc for the +slot offset.
block-step-store-indirect-suc : ∀ prog fs s hl → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → LiveIn (falloc fs) (sucHL hl)     -- the store target (second cell) is live (store-WF)
  → writeLoc (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) (sucHL hl) (readReg (regs (floc fs)) Output)
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ enc-hl (sucHL hl)) → ⊥)   -- heap/stack disjoint
  → BlockStep prog fs s store-indirect-suc
block-step-store-indirect-suc prog fs s hl cc h ft i-eq live-shl guard disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (mem (base+disp rdi slot-size)) (reg rax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) store-indirect-suc ft)
    rdi-val : xreadReg (xregs s) rdi ≡ enc-hl hl
    rdi-val = trans (C.rdi-eq dc) (cong C.enc-sv i-eq)
    addr-val : xreadReg (xregs s) rdi + slot-size ≡ enc-hl (sucHL hl)
    addr-val = trans (cong (_+ slot-size) rdi-val) (sym (enc-hl-suc hl))
    post : X.State
    post = record s { memory = writeMem (memory s) (X.effectiveAddr s (base+disp rdi slot-size)) (xreadReg (xregs s) rax)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-mr {compile-trace prog} {s} {base+disp rdi slot-size} {rax} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    post-eq : post ≡ mkstate (xregs s) (writeMem (memory s) (enc-hl (sucHL hl)) (C.enc-sv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ m → mkstate (xregs s) m (flags s) (pc s + 1) (xhalted s))
                   (cong₂ (writeMem (memory s)) addr-val (C.rax-eq dc))
    dataPost : C.FlatCorr (flat-exec-instr store-indirect-suc prog fs) post
    dataPost = subst (C.FlatCorr (flat-exec-instr store-indirect-suc prog fs)) (sym post-eq)
                     (C.sim-store-indirect-suc hl fs s dc i-eq live-shl guard disj)
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr store-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) store-indirect-suc ft))

-- store-at-slot: stack[current-frame, slot] := Output ↔ `mov [rsp+disp], rax`.
-- step-mov-mr writes the RAW rax; sim-store-at-slot's post has enc-sv Output —
-- bridge via rax-eq (the address is rsp+disp, definitional, no register bridge).
-- The stack/heap disjointness (`disj`) is threaded to sim-store-at-slot.
block-step-store-at-slot : ∀ prog fs s slot → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (store-at-slot slot)
  → (∀ hl' → LiveIn (falloc fs) hl' → (X.readReg (xregs s) rsp + slot-to-disp slot ≡ enc-hl hl') → ⊥)
  → BlockStep prog fs s (store-at-slot slot)
block-step-store-at-slot prog fs s slot cc h ft disj =
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
                                       (C.enc-sv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ v → mkstate (xregs s)
                            (writeMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp slot) v)
                            (flags s) (pc s + 1) (xhalted s))
                   (C.rax-eq dc)
    dataPost : C.FlatCorr (flat-exec-instr (store-at-slot slot) prog fs) post
    dataPost = subst (C.FlatCorr (flat-exec-instr (store-at-slot slot) prog fs)) (sym post-eq)
                     (C.sim-store-at-slot slot fs s dc disj)
    pco' : X.State.pc post ≡ x86-off prog (fpc (flat-exec-instr (store-at-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (x86-off-suc prog (fpc fs) (store-at-slot slot) ft))

-- Arithmetic reg-ops: input2-inc (add rsi,1) / scratch-dec (sub rbx,1).
-- x86 add/sub set flags as a side effect, but CompiledCorr/FlatCorr are
-- flag-free (Plan 0.34), so the flag clobber is invisible — the sim-* lemma
-- is parametric over the post flags (instantiated with updateFlags here).
block-step-input2-inc : ∀ prog fs s k → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op input2-inc)
  → readReg (regs (floc fs)) Input2 ≡ SV-Tag k
  → BlockStep prog fs s (instr-reg-op input2-inc)
block-step-input2-inc prog fs s k cc h ft i2-eq =
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

block-step-scratch-dec : ∀ prog fs s k → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-dec)
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → BlockStep prog fs s (instr-reg-op scratch-dec)
block-step-scratch-dec prog fs s k cc h ft sc-eq =
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
block-step-c-branch-scratch-zero : ∀ prog fs s n k j → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero n))
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → find-label prog n ≡ just j
  → BlockStep prog fs s (instr-ctrl (c-branch-scratch-zero n))
block-step-c-branch-scratch-zero prog fs s n zero j cc h ft sc-eq fl-eq = result
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
    rbx-val = trans (C.rbx-eq dc) (cong C.enc-sv sc-eq)
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
    result : BlockStep prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq | fl-eq = post-je , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                          ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
      ; pc-off = refl }
block-step-c-branch-scratch-zero prog fs s n (suc m) j cc h ft sc-eq fl-eq = result
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
    rbx-val = trans (C.rbx-eq dc) (cong C.enc-sv sc-eq)
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
    result : BlockStep prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq = post-je , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                          ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
      ; pc-off = pco' }

-- c-branch-tag-zero: cmp [rdi],0 ; je n. Like scratch-zero but the condition
-- is the heap tag at *Input1 (cond-eq reduces it to sv-is-zero (SV-Tag k)
-- like sim-test-tag); the x86 cmp reads the same value via heap-eq. The
-- address is base+disp rdi 0, so effectiveAddr carries a +0.
block-step-c-branch-tag-zero : ∀ prog fs s n hl k j → CompiledCorr prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero n))
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → LiveIn (falloc fs) hl        -- the branch reads the tag at a live cell (store-WF)
  → heapMem (floc fs) hl ≡ just (SV-Tag k)
  → find-label prog n ≡ just j
  → BlockStep prog fs s (instr-ctrl (c-branch-tag-zero n))
block-step-c-branch-tag-zero prog fs s n hl zero j cc h ft i-eq live-hl h-eq fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (mem (base+disp rdi 0)) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    addr-val : xreadReg (xregs s) rdi + 0 ≡ enc-hl hl
    addr-val = trans (+-identityʳ (xreadReg (xregs s) rdi)) (trans (C.rdi-eq dc) (cong C.enc-sv i-eq))
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rdi 0)) ≡ just 0
    rd = trans (cong (X.readMem (memory s)) addr-val) (trans (C.heap-eq dc hl live-hl) (cong C.enc-maybe h-eq))
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
    result : BlockStep prog fs s (instr-ctrl (c-branch-tag-zero n))
    result rewrite cond-eq | fl-eq = post-je , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                          ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
      ; pc-off = refl }
block-step-c-branch-tag-zero prog fs s n hl (suc m) j cc h ft i-eq live-hl h-eq fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (mem (base+disp rdi 0)) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    addr-val : xreadReg (xregs s) rdi + 0 ≡ enc-hl hl
    addr-val = trans (+-identityʳ (xreadReg (xregs s) rdi)) (trans (C.rdi-eq dc) (cong C.enc-sv i-eq))
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp rdi 0)) ≡ just (suc m)
    rd = trans (cong (X.readMem (memory s)) addr-val) (trans (C.heap-eq dc hl live-hl) (cong C.enc-maybe h-eq))
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
    result : BlockStep prog fs s (instr-ctrl (c-branch-tag-zero n))
    result rewrite cond-eq = post-je , exec-eq , record
      { dataCorr = record { rdi-eq = C.rdi-eq dc ; rsi-eq = C.rsi-eq dc ; rax-eq = C.rax-eq dc
                          ; rbx-eq = C.rbx-eq dc ; halt-eq = C.halt-eq dc ; heap-eq = C.heap-eq dc
                      ; stack-eq = C.stack-eq dc }
      ; pc-off = pco' }
