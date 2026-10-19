-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterCont
--
-- plan 0.119 D5: THE LOOP CONTINUES. A round returned `inr a′`: from the
-- round's end the machine runs fifteen rows —
--
--   mov-to-input ∷ c-branch-tag-zero (ℓ o (suc l)) ∷ load-indirect-suc ∷   -- unpack a′
--   <⟨_,_⟩'s nine-row tail>                                                 -- build (e , a′)
--   mov-to-input ∷ c-jmp (ℓ o l) ∷ … c-label (ℓ o l)                        -- back edge
--
-- — and arrives at the next round's entry with the pair `(e , a′)` in
-- `Input1`. The nine rows ARE `⟨_,_⟩`'s, at the same stashes, so the node's
-- validity is `PairPlace`'s, instantiated with the prologue's `e` (its
-- `fsF`/`placeF`, carried by the invariant) and the round's `a′`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.IterCont (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore
  using (instr-ctrl; c-branch-tag-zero; c-jmp; c-label; AllocState; AbstractTrace; AbstractInstr;
         load-indirect-suc; mov-to-input; store-at-slot; instr-alloc-heap; load-from-slot;
         store-indirect; store-indirect-suc; LocState; StoredValue; readReg; Input1; Output; SV-Ptr;
         sv-as-loc; writeReg-same; module LocState; module AllocState)
open AllocState using (next-slot; current-frame; next-heap-ref)
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
open import Once.CCC.Codegen.IRObsCorrect.Pair.Place o tbl

module IterContC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-tag-branch-not; flat-jmp)
  open ShapeC {FS} using (tag-inr; unpack-wf; mem-unpack)
  open IterShapeC {FS}
  open IterRunC {FS}
  open IterInvC {FS}
  open IterExitC {FS} using (payload-place-r; ev-step1)
  open PairPlaceC {FS}

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
    (Z : Loop.Anchor body n l base)
    (S0 : FlatState) (a′ : ⟦ A ⟧)
    (nh0 : halted (floc S0) ≡ false)
    (pc0 : fpc S0 ≡ (3 + length (IterShape.bt body n l) + 0) + base)
    (cf0 : current-frame (falloc S0) ≡ Loop.FR body n l base Z)
    (ns0 : next-slot (falloc S0) ≡ next-slot (Loop.Anchor.alloc₀ Z))
    (hr0 : next-heap-ref (falloc (Loop.Anchor.fsF Z)) ≤ next-heap-ref (falloc S0))
    (memF0 : ∀ (loc : ValueLocation FS) → BeforeFrontier (falloc (Loop.Anchor.fsF Z)) loc
           → SMCore.MemOps.readLoc (floc S0) loc ≡ SMCore.MemOps.readLoc (floc (Loop.Anchor.fsF Z)) loc)
    (env0 : SMCore.MemOps.readLoc (floc S0) (AtStack (Loop.FR body n l base Z) (suc n)) ≡ just (Loop.fv body n l base Z))
    (ret0 : fret S0 ≡ []) (lnk0 : flink S0 ≡ nothing)
    (mem00 : ∀ (loc : ValueLocation FS) → BeforeFrontier (record (Loop.Anchor.alloc₀ Z) { next-slot = n }) loc
           → SMCore.MemOps.readLoc (floc S0) loc ≡ SMCore.MemOps.readLoc (Loop.Anchor.s₀ Z) loc)
    (bf00 : ∀ (m : ℕ) (loc : ValueLocation FS) → BeforeFrontier (record (Loop.Anchor.alloc₀ Z) { next-slot = m }) loc
          → BeforeFrontier (record (falloc S0) { next-slot = m }) loc)
    (left0 : LocState.left (floc S0) ≡ LocState.left (Loop.Anchor.s₀ Z))
    {m : AllocMode} (loc : ValueLocation FS)
    (vS : ValidAtWF m (falloc S0) {B IRT.+ A} (inj₂ a′) loc (floc S0))
    (bef : BeforeFrontier (falloc S0) loc)
    (rax : readReg (regs (floc S0)) Output ≡ SV-Ptr loc)
    where

    open IterShape body n l
    open IterRun body n l prog base span
    open Loop body n l base
    open Anchor Z

    c1 c2 gs : FlatState
    c1 = flat-exec-instr mov-to-input prog S0
    c2 = record c1 { fpc = suc (fpc c1) }
    gs = flat-exec-instr load-indirect-suc prog c2

    rd1 : readReg (regs (floc c1)) Input1 ≡ SV-Ptr loc
    rd1 = trans (writeReg-same (regs (floc S0)) Input1 (readReg (regs (floc S0)) Output)) rax

    mem1 : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc c1) lc ≡ SMCore.MemOps.readLoc (floc S0) lc
    mem1 lc = mem-untouched mov-to-input (floc S0) (falloc S0) lc nhw-mov-to-input refl

    memG : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc gs) lc ≡ SMCore.MemOps.readLoc (floc S0) lc
    memG lc = trans (mem-unpack (floc c1) (falloc c1) lc) (mem1 lc)

    v1 : ValidAtWF m (falloc c1) {B IRT.+ A} (inj₂ a′) loc (floc c1)
    v1 = validityWF-mem-preserved (inj₂ a′) loc (floc S0) (floc c1) bef (λ lc _ → mem1 lc) vS

    nh1 : halted (floc c1) ≡ false
    nh1 = exec-abstract-preserves-halted-WF mov-to-input (floc S0) (falloc S0) nh0 tt

    cond : tag-zf (flat-read-tag (floc c1)) ≡ false
    cond = tag-inr v1 rd1

    nhG : halted (floc gs) ≡ false
    nhG = exec-abstract-preserves-halted-WF load-indirect-suc (floc c2) (falloc c2) nh1 (unpack-wf v1 rd1)

    mg : AllocMode
    mg = proj₁ (payload-place-r v1 rd1)

    placeG : ResultPlace A mg (falloc gs) (falloc gs) a′ (floc gs)
    placeG = proj₂ (payload-place-r v1 rd1)

    ------------------------------------------------------------------
    -- `⟨_,_⟩`'s tail, at the prologue's `e` and the round's `a′`.
    ------------------------------------------------------------------
    mem-F→G : ∀ (lc : ValueLocation FS) → BeforeFrontier (falloc fsF) lc
            → SMCore.MemOps.readLoc (floc gs) lc ≡ SMCore.MemOps.readLoc (floc fsF) lc
    mem-F→G lc bf = trans (memG lc) (memF0 lc bf)

    fst-cell-gs : SMCore.MemOps.readLoc (floc gs) (AtStack (current-frame alloc₀) (suc n))
                ≡ just (readReg (regs (floc fsF)) Output)
    fst-cell-gs = trans (memG (AtStack (current-frame alloc₀) (suc n))) env0

    module PP = PairPlace {E} {A} n alloc₀ n≤₀ fsF gs cf-F cf0 ns-F ns0 hr0
                  e a′ mf mg caf (falloc gs) placeF placeG mem-F→G fst-cell-gs

    ------------------------------------------------------------------
    -- THE PCS. Everything past the round is `rend + j`; the tail's rows are
    -- `k` steps past `gs`.
    ------------------------------------------------------------------
    pc-shift : ∀ (r b k : ℕ) → k + ((r + 0) + b) ≡ (r + k) + b
    pc-shift = solve 3 (λ r b k → k :+ ((r :+ con 0) :+ b) := (r :+ k) :+ b) refl

    pc-shift3 : ∀ (r b k : ℕ) → k + ((r + 3) + b) ≡ (r + (3 + k)) + b
    pc-shift3 = solve 3 (λ r b k → k :+ ((r :+ con 3) :+ b) := (r :+ (con 3 :+ k)) :+ b) refl

    pc1 : fpc c1 ≡ (rend + 1) + base
    pc1 = trans (cong suc pc0) (pc-shift rend base 1)

    pcG : fpc gs ≡ (rend + 3) + base
    pcG = trans (cong (3 +_) pc0) (pc-shift rend base 3)

    tfetch : ∀ (k : ℕ) (i : AbstractInstr) → fetch post (3 + k) ≡ just i → fetch prog (k + fpc gs) ≡ just i
    tfetch k i e = subst (λ z → fetch prog z ≡ just i)
                         (sym (trans (cong (k +_) pcG) (pc-shift3 rend base k))) (post-at (3 + k) i e)

    ------------------------------------------------------------------
    -- THE TAIL'S `halted ≡ false`s, spending `PairPlace`'s row witnesses.
    ------------------------------------------------------------------
    nhU2 : halted (floc PP.u2) ≡ false
    nhU2 = exec-abstract-preserves-halted-WF (store-at-slot (suc (suc n))) (floc gs) (falloc gs) nhG tt
    nhU3 : halted (floc PP.u3) ≡ false
    nhU3 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc PP.u2) (falloc PP.u2) nhU2 tt
    nhU4 : halted (floc PP.u4) ≡ false
    nhU4 = exec-abstract-preserves-halted-WF (store-at-slot (suc (suc (suc n)))) (floc PP.u3) (falloc PP.u3) nhU3 tt
    nhU5 : halted (floc PP.u5) ≡ false
    nhU5 = exec-abstract-preserves-halted-WF mov-to-input (floc PP.u4) (falloc PP.u4) nhU4 tt
    nhU6 : halted (floc PP.u6) ≡ false
    nhU6 = exec-abstract-preserves-halted-WF (load-from-slot (suc n)) (floc PP.u5) (falloc PP.u5) nhU5 PP.wf-load-fst
    nhU7 : halted (floc PP.u7) ≡ false
    nhU7 = exec-abstract-preserves-halted-WF store-indirect (floc PP.u6) (falloc PP.u6) nhU6 (PP.pair-loc , PP.rdi-u6)
    nhU8 : halted (floc PP.u8) ≡ false
    nhU8 = exec-abstract-preserves-halted-WF (load-from-slot (suc (suc n))) (floc PP.u7) (falloc PP.u7) nhU7 PP.wf-load-snd
    nhU9 : halted (floc PP.u9) ≡ false
    nhU9 = exec-abstract-preserves-halted-WF store-indirect-suc (floc PP.u8) (falloc PP.u8) nhU8 (PP.pair-loc , PP.rdi-u8)
    nhU10 : halted (floc PP.u10) ≡ false
    nhU10 = exec-abstract-preserves-halted-WF (load-from-slot (suc (suc (suc n)))) (floc PP.u9) (falloc PP.u9) nhU9 PP.wf-load-pair

    tail9 : FlatSteps prog 9 gs PP.u10
    tail9 =
        step-at PP.u2  (nhG  , tfetch 0 _ refl) refl
      ( step-at PP.u3  (nhU2 , tfetch 1 _ refl) refl
      ( step-at PP.u4  (nhU3 , tfetch 2 _ refl) refl
      ( step-at PP.u5  (nhU4 , tfetch 3 _ refl) refl
      ( step-at PP.u6  (nhU5 , tfetch 4 _ refl) refl
      ( step-at PP.u7  (nhU6 , tfetch 5 _ refl) refl
      ( step-at PP.u8  (nhU7 , tfetch 6 _ refl) refl
      ( step-at PP.u9  (nhU8 , tfetch 7 _ refl) refl
      ( step-at PP.u10 (nhU9 , tfetch 8 _ refl) refl
        [] ))))))))

    ------------------------------------------------------------------
    -- THE BACK EDGE: the node into `Input1`, the jump to the top, the label.
    ------------------------------------------------------------------
    u11 u12 σ′ : FlatState
    u11 = flat-exec-instr mov-to-input prog PP.u10
    u12 = record u11 { fpc = top-at + base }
    σ′  = record u12 { fpc = suc (top-at + base) }

    nhU11 : halted (floc u11) ≡ false
    nhU11 = exec-abstract-preserves-halted-WF mov-to-input (floc PP.u10) (falloc PP.u10) nhU10 tt

    fJmp : fetch prog (fpc u11) ≡ just (instr-ctrl (c-jmp (ℓ o l)))
    fJmp = tfetch 10 (instr-ctrl (c-jmp (ℓ o l))) refl
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

    fUnpack : fetch prog (fpc c2) ≡ just load-indirect-suc
    fUnpack = trans (cong (fetch prog) (trans (cong (2 +_) pc0) (pc-shift rend base 2))) (post-at 2 _ refl)
    fMov2 : fetch prog (fpc PP.u10) ≡ just mov-to-input
    fMov2 = tfetch 9 mov-to-input refl

    rest3 : FlatSteps prog 3 PP.u10 σ′
    rest3 = step-at u11 (nhU10 , fMov2) refl (FlatSteps-++ jmpStep labelStep)

    rest2 : FlatSteps prog 13 c2 σ′
    rest2 = step-at gs (nh1 , fUnpack) refl (FlatSteps-++ tail9 rest3)

    chain : FlatSteps prog 15 S0 σ′
    chain = step-at c1 (nh0 , trans (cong (fetch prog) pc0) at-movin1) refl (FlatSteps-++ branchStep rest2)

    ------------------------------------------------------------------
    -- WHAT THE FIFTEEN ROWS DO: no event, the log unchanged, at least one
    -- control step, and the next round's invariant.
    ------------------------------------------------------------------
    ev-rest3 : chain-events rest3 ≡ []
    ev-rest3 =
      trans (chain-events-++ jmpStep labelStep)
            (cong₂ _++_ (ev-step1 {prog} u11 nhU11 fJmp eqJmp refl) (ev-step1 {prog} u12 nhU11 at-top refl refl))

    ev-tail9 : chain-events tail9 ≡ []
    ev-tail9 = refl

    ev-rest2 : chain-events rest2 ≡ []
    ev-rest2 = trans (ev-step-at {prog} {fs = c2} {i = load-indirect-suc} gs (nh1 , fUnpack) refl (FlatSteps-++ tail9 rest3))
                     (trans (chain-events-++ tail9 rest3) (cong₂ _++_ ev-tail9 ev-rest3))

    ev-branch : chain-events branchStep ≡ []
    ev-branch = ev-step1 {prog} c1 nh1 fBranch eqBranch refl

    ev-chain : chain-events chain ≡ []
    ev-chain = trans (ev-step-at {prog} {fs = S0} {i = mov-to-input} c1 (nh0 , trans (cong (fetch prog) pc0) at-movin1) refl (FlatSteps-++ branchStep rest2))
                     (trans (chain-events-++ branchStep rest2) (cong₂ _++_ ev-branch ev-rest2))

    ctrls-chain : 1 ≤ chain-ctrls chain
    ctrls-chain =
      subst (1 ≤_) (sym (chain-ctrls-++ branchStep rest2))
        (subst (λ z → 1 ≤ z + chain-ctrls rest2) (sym (ctrls-subst-end eqBranch ((nh1 , fBranch) ∷ [])))
               (s≤s z≤n))

    log-chain : SMCore.LocState.ev-log (floc σ′) ≡ SMCore.LocState.ev-log (floc S0)
    log-chain =
      trans (log-abstract mov-to-input tt (floc PP.u10) (falloc PP.u10))
     (trans (log-abstract (load-from-slot (suc (suc (suc n)))) tt (floc PP.u9) (falloc PP.u9))
     (trans (log-abstract store-indirect-suc tt (floc PP.u8) (falloc PP.u8))
     (trans (log-abstract (load-from-slot (suc (suc n))) tt (floc PP.u7) (falloc PP.u7))
     (trans (log-abstract store-indirect tt (floc PP.u6) (falloc PP.u6))
     (trans (log-abstract (load-from-slot (suc n)) tt (floc PP.u5) (falloc PP.u5))
     (trans (log-abstract mov-to-input tt (floc PP.u4) (falloc PP.u4))
     (trans (log-abstract (store-at-slot (suc (suc (suc n)))) tt (floc PP.u3) (falloc PP.u3))
     (trans (log-abstract (instr-alloc-heap 2) tt (floc PP.u2) (falloc PP.u2))
     (trans (log-abstract (store-at-slot (suc (suc n))) tt (floc gs) (falloc gs))
     (trans (log-abstract load-indirect-suc tt (floc c2) (falloc c2))
            (log-abstract mov-to-input tt (floc S0) (falloc S0))))))))))))

    ------------------------------------------------------------------
    -- THE NEXT ROUND'S ENTRY.
    ------------------------------------------------------------------
    mem11 : ∀ (lc : ValueLocation FS) → SMCore.MemOps.readLoc (floc σ′) lc ≡ SMCore.MemOps.readLoc (floc PP.u10) lc
    mem11 lc = mem-untouched mov-to-input (floc PP.u10) (falloc PP.u10) lc nhw-mov-to-input refl

    bfEnv : BeforeFrontier PP.a' (AtStack (current-frame alloc₀) (suc n))
    bfEnv = BeforeFrontier.stack-before (sym cf0) ≤-refl

    bfA : ∀ (lc : ValueLocation FS) → BeforeFrontier (record alloc₀ { next-slot = n }) lc → BeforeFrontier PP.a' lc
    bfA = frontier-monotone (record alloc₀ { next-slot = n }) PP.a' (sym cf0)
            (≤-trans (n≤1+n n) (n≤1+n (suc n))) (≤-trans hr-F hr0)

    next-inv : RoundInv Z σ′ a′
    next-inv = record
      { pc   = refl
      ; ret  = ret0
      ; lnk  = lnk0
      ; nh   = nhU11
      ; mode = Heap
      ; inp  = in-loc PP.pair-loc
                 (validityWF-mem-preserved (e , a′) PP.pair-loc (floc PP.u10) (floc σ′) PP.before
                    (λ lc _ → mem11 lc) PP.validity)
                 PP.before
                 (trans (writeReg-same (regs (floc PP.u10)) Input1 (readReg (regs (floc PP.u10)) Output)) PP.out-u10)
      ; cf   = PP.cf-u10
      ; ns   = trans PP.nextslot-u10 ns0
      ; hr   = ≤-trans hr0 PP.gs≤u10
      ; memF = λ lc bf → trans (mem11 lc) (PP.mem-F→u10 lc bf)
      ; env  = trans (mem11 (AtStack (current-frame alloc₀) (suc n)))
                     (trans (PP.tail-pres (AtStack (current-frame alloc₀) (suc n)) bfEnv) fst-cell-gs)
      ; mem0 = λ lc bf → trans (mem11 lc) (trans (PP.tail-pres lc (bfA lc bf)) (trans (memG lc) (mem00 lc bf)))
      ; bf0  = λ m lc bf → frontier-monotone (record (falloc S0) { next-slot = m }) (record (falloc σ′) { next-slot = m })
                             (trans cf0 (sym PP.cf-u10)) ≤-refl PP.gs≤u10 lc (bf00 m lc bf)
      ; left = trans (chain-left chain nhU11) left0
      }
