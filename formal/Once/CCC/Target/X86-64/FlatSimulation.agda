-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.FlatSimulation
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
open import Once.Memory.HeapAddress using (HeapLocation)
open import Data.Nat using (ℕ; _+_; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.CCC.Target.X86-64.FlatSimulation
  (FS : FrameSemantics)
  (enc-hl : HeapLocation → ℕ)
  (enc-hl-inj : ∀ {a b : HeapLocation} → enc-hl a ≡ enc-hl b → a ≡ b)
  where

open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X
open X using (mkstate; execInstr; mkflags; _<ᵇ_)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax
  using (rax; rbx; rsi; rdi; Reg; Operand; Program; reg; imm; mem; mov; add; sub; cmp)
open import Data.Maybe using (just)
open import Data.Bool using (false)
open import Data.List using (_∷_; []; _++_; drop; length)
open import Relation.Binary.PropositionalEquality using (refl)

import Once.CCC.Target.X86-64.FlatCorrespondence as FC
module C = FC FS enc-hl enc-hl-inj          -- enc-sv / FlatCorr data fields
open import Once.CCC.Target.X86-64.FlatComposition FS
  using (x86-off; x86-len; x86-off-suc; fetch-block-head)
open import Once.CCC.Target.X86-64.StepLemmas using (exec-1; step-mov-rr; step-mov-ri)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace; compile-abstract)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

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
  Σ X.State (λ s' → (X.exec 1 (compile-trace prog) s ≡ just s')
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
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
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
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' }
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
