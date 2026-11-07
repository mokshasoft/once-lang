-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterCont
--
-- plan 0.119 D5: THE LOOP CONTINUES. A round returned `inr a′`: from the
-- round's end the machine runs
--
--   mov-to-input ∷ c-branch-tag-zero (ℓ o (suc l)) ∷ get A 1 ∷   -- read a′
--   <⟨_,_⟩'s tail, `Pair.Build`>                                -- build (e , a′)
--   mov-to-input ∷ c-jmp (ℓ o l) ∷ … c-label (ℓ o l)              -- back edge
--
-- — and arrives at the next round's entry with the pair `(e , a′)` in
-- `Input1`. The tail IS `⟨_,_⟩`'s (`PairBuildC.Tail`), at the same stashes:
-- `e` from the prologue (its `fsF`/`placeF`, kept by every round since —
-- `bkF0`), `a′` where the read placed it.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.IterCont (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore using (ending)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore
  using (instr-ctrl; c-branch-tag-zero; c-jmp; c-label; AllocState; AbstractTrace; AbstractInstr;
         load-indirect-suc; mov-to-input; store-at-slot; instr-alloc-heap; load-from-slot;
         store-indirect; store-indirect-suc; LocState; StoredValue; readReg; Input1; Output; SV-Ptr;
         sv-as-loc; writeReg-same; module LocState; module AllocState)
open AllocState using (next-slot; current-frame; saved-frames; next-heap-ref)
open LocState using (halted; regs)
open import Data.Product using (Σ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (s≤s; z≤n)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)
open import Once.IRTy using (IRTy)
import Once.IRTy as IRT

open import Once.CCC.Codegen.IRObsCorrect.CaseShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterRun o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterInv o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterExit o tbl
open import Once.CCC.Codegen.IRObsCorrect.Pair.Build o tbl using (module PairBuildC)
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.FlatLayout using (get)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Codegen.StraightRun
open import Once.CCC.Machine.Locations using (AtDynamic)
open import Data.List.Properties using (++-identityʳ)

module IterContC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-tag-branch-not; flat-jmp)
  open ShapeC {FS} using (tag-inr; payload-r)
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem)
  open IterShapeC {FS}
  open IterRunC {FS}
  open IterInvC {FS}
  open IterExitC {FS} using (ev-step1)
  module SR = Once.CCC.Codegen.StraightRun.StraightRunAPI {FS}

  -- `chain-ctrls` does not look at the end state either.
  ctrls-subst-end : ∀ {prog k fs fs′ fs″} (eq : fs′ ≡ fs″) (c : FlatSteps prog k fs fs′)
                  → chain-ctrls (subst (FlatSteps prog k fs) eq c) ≡ chain-ctrls c
  ctrls-subst-end refl c = refl

  -- A `step-at` link's events: its instruction's, then the rest's — by
  -- matching the link's equation, so nothing is normalized.
  ev-step-at : ∀ {prog k fs fs″} {i : AbstractInstr} (fs′ : FlatState)
                 (h : halted (floc fs) ≡ false × fetch prog (fpc fs) ≡ just i)
                 (eq : flat-exec-instr i prog fs ≡ fs′) (rest : FlatSteps prog k fs′ fs″)
             → chain-events (step-at fs′ h eq rest) ≡ event-of i fs ++ chain-events rest
  ev-step-at fs′ h refl rest = refl

  module Cont {E A B : IRTy} (body : IR (E IRT.* A) (B IRT.+ A))
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (emitted n l (Iter body)))
    (la : LabelsAt prog base (emitted n l (Iter body)))
    (Z : Loop.Anchor body n l base prog)
    (S0 : FlatState) (a′ : ⟦ A ⟧)
    (nh0 : halted (floc S0) ≡ false)
    (pc0 : fpc S0 ≡ (3 + length (IterShape.bt body n l) + 0) + base)
    (cf0 : current-frame (falloc S0) ≡ Loop.FR body n l base Z)
    (sf0 : saved-frames (falloc S0) ≡ Loop.SF body n l base Z)
    (ns0 : next-slot (falloc S0) ≡ next-slot (Loop.Anchor.alloc₀ Z))
    (hr0 : next-heap-ref (falloc (Loop.Anchor.fsF Z)) ≤ next-heap-ref (falloc S0))
    (memF0 : ∀ (loc : ValueLocation FS) → BeforeFrontier (falloc (Loop.Anchor.fsF Z)) loc
           → SMCore.MemOps.readLoc (floc S0) loc ≡ SMCore.MemOps.readLoc (floc (Loop.Anchor.fsF Z)) loc)
    (env0 : SMCore.MemOps.readLoc (floc S0) (AtStack (Loop.FR body n l base Z) (suc n)) ≡ just (Loop.fv body n l base Z))
    (ret0 : fret S0 ≡ Loop.Anchor.rs₀ Z) (lnk0 : flink S0 ≡ nothing)
    (mem00 : ∀ (loc : ValueLocation FS) → BeforeFrontier (record (Loop.Anchor.alloc₀ Z) { next-slot = n }) loc
           → SMCore.MemOps.readLoc (floc S0) loc ≡ SMCore.MemOps.readLoc (Loop.Anchor.s₀ Z) loc)
    (bf00 : ∀ (m : ℕ) (loc : ValueLocation FS) → BeforeFrontier (record (Loop.Anchor.alloc₀ Z) { next-slot = m }) loc
          → BeforeFrontier (record (falloc S0) { next-slot = m }) loc)
    (left0 : ending (floc S0) ≡ ending (Loop.Anchor.s₀ Z))
    (bkF0 : BlocksKept (falloc (Loop.Anchor.fsF Z)) (falloc S0))
    (bk00 : BlocksKept (Loop.Anchor.alloc₀ Z) (falloc S0))
    {m : AllocMode} (loc : ValueLocation FS)
    (vS : ValidAtWF {prog = prog} m (falloc S0) {B IRT.+ A} (inj₂ a′) loc (floc S0))
    (bef : Live (falloc S0) loc)
    (rax : readReg (regs (floc S0)) Output ≡ SV-Ptr loc)
    where

    open IterShape body n l
    open IterRun body n l prog base span
    open Loop body n l base
    open Anchor Z

    c1 c2 : FlatState
    c1 = flat-exec-instr mov-to-input prog S0
    c2 = record c1 { fpc = suc (fpc c1) }

    rd1 : readReg (regs (floc c1)) Input1 ≡ SV-Ptr loc
    rd1 = trans (writeReg-same (regs (floc S0)) Input1 (readReg (regs (floc S0)) Output)) rax

    mem1 : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc c1) lc ≡ SMCore.MemOps.readLoc (floc S0) lc
    mem1 lc = mem-untouched mov-to-input (floc S0) (falloc S0) lc nhw-mov-to-input refl

    v1 : ValidAtWF {prog = prog} m (falloc c1) {B IRT.+ A} (inj₂ a′) loc (floc c1)
    v1 = validityWF-mem-preserved (inj₂ a′) loc (floc S0) (floc c1) (live→bf bef) (λ lc _ → mem1 lc) vS

    nh1 : halted (floc c1) ≡ false
    nh1 = exec-abstract-preserves-halted-WF mov-to-input (floc S0) (falloc S0) nh0 tt

    cond : tag-test (flat-read-tag (floc c1)) ≡ just false
    cond = tag-inr v1 rd1

    pc-shift : ∀ (r b k : ℕ) → k + ((r + 0) + b) ≡ (r + k) + b
    pc-shift = solve 3 (λ r b k → k :+ ((r :+ con 0) :+ b) := (r :+ k) :+ b) refl

    pc-shift3 : ∀ (r b k : ℕ) → k + ((r + 3) + b) ≡ (r + (3 + k)) + b
    pc-shift3 = solve 3 (λ r b k → k :+ ((r :+ con 3) :+ b) := (r :+ (con 3 :+ k)) :+ b) refl

    pc1 : fpc c1 ≡ (rend + 1) + base
    pc1 = trans (cong suc pc0) (pc-shift rend base 1)

    pc2 : fpc c2 ≡ (rend + 2) + base
    pc2 = trans (cong (2 +_) pc0) (pc-shift rend base 2)

    ------------------------------------------------------------------
    -- the payload `a′`, read at word 1 of the sum (`Get.get-run`)
    ------------------------------------------------------------------
    gA : GetOut {prog = prog} A a′ c2
    gA = get-run A 1 c2 loc nh1 (λ i e → subst (λ z → fetch prog z ≡ just i) (sym pc2) (at-geta i e))
                 rd1 bef (payload-r v1)

    gs : FlatState
    gs = setOut c2 (GetOut.out gA)

    nhG : halted (floc gs) ≡ false
    nhG = nh1

    memG : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc gs) lc ≡ SMCore.MemOps.readLoc (floc S0) lc
    memG lc = trans (out-mem c2 (GetOut.out gA) lc) (mem1 lc)

    pcG : fpc gs ≡ (rend + 3) + base
    pcG = trans (cong (3 +_) pc0) (pc-shift rend base 3)

    ------------------------------------------------------------------
    -- the pair `(e , a′)` (`Pair.Build`): `e` where the prologue read it,
    -- kept by every round since; `a′` where the read placed it
    ------------------------------------------------------------------
    keepFG : ∀ l → Live (falloc fsF) l → SMCore.MemOps.readLoc (floc gs) l ≡ SMCore.MemOps.readLoc (floc fsF) l
    keepFG l lv = trans (memG l) (memF0 l (live→bf lv))

    bftB : ∀ l → Live (falloc fsF) l → Live (falloc gs) l
    bftB (AtDynamic hl) (BeforeFrontier.heap-before p) = BeforeFrontier.heap-before (<-≤-trans p hr0)

    srcB = FlatPut.src-tr {FS} {prog} keepFG (PairBuildC.src-of-place {FS} {prog} placeF)
    srcC = PairBuildC.src-of-place {FS} {prog} (GetOut.place gA)

    rsB : SMCore.MemOps.readLoc (floc gs) (AtStack (current-frame (falloc gs)) (suc n)) ≡ just (fv Z)
    rsB = subst (λ fr → SMCore.MemOps.readLoc (floc gs) (AtStack fr (suc n)) ≡ just (fv Z)) (sym cf0)
                (trans (memG (AtStack (FR Z) (suc n))) env0)

    at-T : SR.At prog (fpc gs) T
    at-T j i e = subst (λ z → fetch prog z ≡ just i)
                       (sym (trans (cong (j +_) pcG) (pc-shift3 rend base j))) (at-tail j i e)

    module TT = PairBuildC.Tail {FS} {prog} n E A gs at-T nhG (fv Z) (falloc fsF) bftB bkF0 srcB rsB srcC

    u10 u11 u12 σ′ : FlatState
    u10 = TT.settle
    u11 = flat-exec-instr mov-to-input prog u10
    u12 = record u11 { fpc = top-at + base }
    σ′  = record u12 { fpc = suc (top-at + base) }

    nhU10 : halted (floc u10) ≡ false
    nhU10 = TT.hfin

    nhU11 : halted (floc u11) ≡ false
    nhU11 = exec-abstract-preserves-halted-WF mov-to-input (floc u10) (falloc u10) nhU10 tt

    after-eq : ∀ k → k + fpc u10 ≡ (rend + (3 + (LT + k))) + base
    after-eq k = trans (cong (λ z → k + (LT + z)) pcG)
                       (solve 4 (λ k t r b → k :+ (t :+ ((r :+ con 3) :+ b)) := (r :+ (con 3 :+ (t :+ k))) :+ b) refl k LT rend base)

    fMov2 : fetch prog (fpc u10) ≡ just mov-to-input
    fMov2 = subst (λ z → fetch prog z ≡ just mov-to-input) (sym (after-eq 0)) at-movin2

    fJmp : fetch prog (fpc u11) ≡ just (instr-ctrl (c-jmp (ℓ o l)))
    fJmp = subst (λ z → fetch prog z ≡ just (instr-ctrl (c-jmp (ℓ o l)))) (sym (after-eq 1)) at-jmp

    eqJmp : flat-exec-instr (instr-ctrl (c-jmp (ℓ o l))) prog u11 ≡ u12
    eqJmp = trans (flat-jmp prog u11 (ℓ o l)) (cong (λ mj → do-jump mj u11) (top-target prog base la))
    jmpStep : FlatSteps prog 1 u11 u12
    jmpStep = flat-step1 nhU11 fJmp eqJmp

    labelStep : FlatSteps prog 1 u12 σ′
    labelStep = flat-step1 nhU11 at-top refl

    fBranch : fetch prog (fpc c1) ≡ just (instr-ctrl (c-branch-tag-zero (ℓ o (suc l))))
    fBranch = trans (cong (fetch prog) pc1) at-branch
    eqBranch : flat-exec-instr (instr-ctrl (c-branch-tag-zero (ℓ o (suc l)))) prog c1 ≡ c2
    eqBranch = flat-tag-branch-not prog c1 (ℓ o (suc l)) cond
    branchStep : FlatSteps prog 1 c1 c2
    branchStep = flat-step1 nh1 fBranch eqBranch

    rest3 : FlatSteps prog 3 u10 σ′
    rest3 = (nhU10 , fMov2) ∷ FlatSteps-++ jmpStep labelStep

    rest-t : FlatSteps prog (length T + 3) gs σ′
    rest-t = FlatSteps-++ TT.run rest3

    rest2 : FlatSteps prog (1 + (length T + 3)) c2 σ′
    rest2 = FlatSteps-++ (GetOut.step gA) rest-t

    rest1 : FlatSteps prog (1 + (1 + (length T + 3))) c1 σ′
    rest1 = FlatSteps-++ branchStep rest2

    chain : FlatSteps prog (1 + (1 + (1 + (length T + 3)))) S0 σ′
    chain = (nh0 , trans (cong (fetch prog) pc0) at-movin1) ∷ rest1

    ------------------------------------------------------------------
    -- WHAT THE ROWS DO: no event, the log unchanged, at least one
    -- control step, and the next round's invariant.
    ------------------------------------------------------------------
    ev-rest3 : chain-events rest3 ≡ []
    ev-rest3 =
      trans (chain-events-++ jmpStep labelStep)
            (cong₂ _++_ (ev-step1 {prog} u11 nhU11 fJmp eqJmp refl) (ev-step1 {prog} u12 nhU11 at-top refl refl))

    ev-rest2 : chain-events rest2 ≡ []
    ev-rest2 = trans (chain-events-++ (GetOut.step gA) rest-t)
                     (cong₂ _++_ (GetOut.silent gA)
                       (trans (chain-events-++ TT.run rest3) (cong₂ _++_ TT.silent ev-rest3)))

    ev-branch : chain-events branchStep ≡ []
    ev-branch = ev-step1 {prog} c1 nh1 fBranch eqBranch refl

    ev-chain : chain-events chain ≡ []
    ev-chain = trans (chain-events-++ branchStep rest2) (cong₂ _++_ ev-branch ev-rest2)

    ctrls-chain : 1 ≤ chain-ctrls chain
    ctrls-chain =
      subst (1 ≤_) (sym (chain-ctrls-++ branchStep rest2))
        (subst (λ z → 1 ≤ z + chain-ctrls rest2) (sym (ctrls-subst-end eqBranch ((nh1 , fBranch) ∷ [])))
               (s≤s z≤n))

    log-chain : SMCore.LocState.ev-log (floc σ′) ≡ SMCore.LocState.ev-log (floc S0)
    log-chain = trans (log-of chain ev-chain) (++-identityʳ _)

    ------------------------------------------------------------------
    -- THE NEXT ROUND'S ENTRY.
    ------------------------------------------------------------------
    mem11 : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc σ′) lc ≡ SMCore.MemOps.readLoc (floc u10) lc
    mem11 lc = mem-untouched mov-to-input (floc u10) (falloc u10) lc nhw-mov-to-input refl

    aT : AllocState {FS}
    aT = record (falloc gs) { next-slot = suc (suc n) }

    bfEnv : BeforeFrontier aT (AtStack (FR Z) (suc n))
    bfEnv = BeforeFrontier.stack-before (sym cf0) (n<1+n (suc n))

    bfA : ∀ (lc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = n }) lc → BeforeFrontier aT lc
    bfA = frontier-monotone (record alloc₀ { next-slot = n }) aT (sym cf0)
            (≤-trans (n≤1+n n) (n≤1+n (suc n))) (≤-trans hr-F hr0)

    bfF : ∀ (lc : ValueLocation FS) → BeforeFrontier (falloc fsF) lc → BeforeFrontier aT lc
    bfF = frontier-monotone (falloc fsF) aT (trans cf-F (sym cf0))
            (≤-trans (≤-reflexive ns-F) (≤-trans n≤₀ (≤-trans (n≤1+n n) (n≤1+n (suc n))))) hr0

    live0S : ∀ l → Live alloc₀ l → Live (falloc S0) l
    live0S (AtDynamic hl) (BeforeFrontier.heap-before p) with bf00 0 (AtDynamic hl) (BeforeFrontier.heap-before p)
    ... | BeforeFrontier.heap-before q = BeforeFrontier.heap-before q

    next-inv : RoundInv Z σ′ a′
    next-inv = record
      { pc   = refl
      ; ret  = ret0
      ; lnk  = lnk0
      ; nh   = nhU11
      ; mode = Heap
      ; inp  = in-loc TT.L
                 (validityWF-mem-preserved (e , a′) TT.L (floc u10) (floc σ′) (live→bf TT.live-L)
                    (λ lc _ → mem11 lc) TT.val)
                 TT.live-L
                 (writeReg-same (regs (floc u10)) Input1 (readReg (regs (floc u10)) Output))
      ; cf   = trans TT.cf-tail cf0
      ; sf   = trans TT.sf-tail sf0
      ; ns   = ns0
      ; hr   = ≤-trans hr0 (n≤1+n _)
      ; memF = λ lc bf → trans (mem11 lc) (trans (TT.keep lc (bfF lc bf)) (trans (memG lc) (memF0 lc bf)))
      ; env  = trans (mem11 (AtStack (FR Z) (suc n)))
                     (trans (TT.keep (AtStack (FR Z) (suc n)) bfEnv) (trans (memG (AtStack (FR Z) (suc n))) env0))
      ; mem0 = λ lc bf → trans (mem11 lc) (trans (TT.keep lc (bfA lc bf)) (trans (memG lc) (mem00 lc bf)))
      ; bf0  = λ m lc bf → TT.bf-tail m lc (bf00 m lc bf)
      ; left = trans (chain-left chain nhU11) left0
      ; bkF  = bk-trans {a = falloc fsF} {b = falloc S0} {c = TT.A₁} bkF0 TT.bk-tail bftB
      ; bk0  = bk-trans {a = alloc₀} {b = falloc S0} {c = TT.A₁} bk00 TT.bk-tail live0S
      }
