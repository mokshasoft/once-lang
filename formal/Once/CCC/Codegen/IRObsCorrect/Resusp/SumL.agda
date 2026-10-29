-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.SumL
--
-- Part of `Resusp.Sum`, split for the per-module memory cap: the `inl` arm (`ArmL`).
--
-- plan 0.125 S3: a SUM layer of the re-suspension (shape: `SumShape`).
-- The branch reads the input's own tag. The `inl` arm jumps to the mid
-- row's label, loads the payload, re-suspends it (`tF`), builds a fresh
-- `[0 , result]` node (`SumTail`) and falls through the join label; the
-- `inr` arm falls through, does the same with `tG` and tag 1, and jumps to
-- the join label. Both land one past the join.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.SumL (o : CanonicalName) (tbl : DL.List IRFun) where


open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumTail o tbl
open import Once.CCC.Codegen.IRObsCorrect.CaseShape o tbl using (module ShapeC)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.SlotBudget o using (resuspend-mono)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue
        ; readReg; Output; Input1; SV-Code; SV-Ptr; sucLoc; instr-ctrl; c-branch-tag-zero; c-jmp; c-label
        ; store-at-slot; restore-input; load-indirect-suc; sv-as-loc)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; wf-Sum; _⊕_)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
open import Once.CCC.Machine.SMPrimitives using (nhw-restore-input)
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot)
open import Once.Memory.HeapAddress using (sucHL)
open import Data.Nat using (z≤n; s≤s)
open import Data.Sum using (inj₁; inj₂)
import Once.CCC.Machine.ClosureWellFormed o tbl as CWF
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumPro o tbl using (module ResuspSumProC)
module ResuspSumLC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open ResuspSumShapeC {FS}
  open ResuspSumTailC {FS}
  open ShapeC {FS} using (tag-inl; tag-inr)
  open CWF.ClosureWellFormedBase {FS} using (CellAtP)
  open FlatStepsAPI {FS} using (flat-tag-branch-yes; flat-tag-branch-not)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)

  private
    cfx : ∀ i (t : FlatState) → current-frame (falloc (St i t)) ≡ current-frame (falloc t)
    cfx i t = exec-abstract-preserves-frame i (floc t) (falloc t)

    sfx : ∀ i (t : FlatState) → saved-frames (falloc (St i t)) ≡ saved-frames (falloc t)
    sfx i t = exec-abstract-preserves-saved i (floc t) (falloc t)

    lgx : ∀ i (t : FlatState) → LogFree i → LocState.ev-log (floc (St i t)) ≡ LocState.ev-log (floc t)
    lgx i t lf = log-abstract i lf (floc t) (falloc t)

    ev-++ : ∀ {prog k₁ k₂} {x y z : FlatState} (r₁ : FlatSteps prog k₁ x y) (r₂ : FlatSteps prog k₂ y z)
          → chain-events r₁ ≡ [] → chain-events r₂ ≡ [] → chain-events (FlatSteps-++ r₁ r₂) ≡ []
    ev-++ r₁ r₂ e₁ e₂ = trans (chain-events-++ r₁ r₂) (cong₂ _++_ e₁ e₂)

  module RSumL {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
              (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (e : ValueDomain.⟦ E ⟧ᴰᴵ)
              (prog : AbstractTrace) (lbl-n : ℕ)
              (R : VTy (ν-type F))
              (mk-child : ∀ {alloc ν-loc s} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                        → LocMatchesMode Heap ν-loc
                        → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o lbl-n))
                        → Live alloc (sucLoc ν-loc)
                        → CellAt {prog = prog} alloc (E IRTy′.* A) (e , a′) ν-loc s
                        → R Heap alloc (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc s)
              where

    open RBase wf coalg e prog lbl-n R mk-child

    ------------------------------------------------------------------
    -- THE SHARED PROLOGUE: stash the sum pointer, put it in Input1.
    ------------------------------------------------------------------
    open ResuspSumProC.RSumPro {FS} wf coalg e prog lbl-n R mk-child

    module ArmL {G₁ G₂ : IRFunctor} (wF : WellFormedFI G₁) (wG : WellFormedFI G₂) (ihF : Resusp′ wF)
               (n l : ℕ) (σ : FlatState) (y₁ : ValueDomain.⟦ ⟦ G₁ ⟧TI A ⟧ᴰᴵ) (pl : ValueLocation FS)
               (b : AllocState {FS}) (hb : next-heap-ref b ≤ next-heap-ref (falloc σ))
               (span : SpanAt prog (fpc σ) (rtrace (wf-Sum wF wG) n l))
               (lab : LabelsAt prog (fpc σ) (rtrace (wf-Sum wF wG) n l))
               (nh0 : halted (floc σ) ≡ false) (lk : flink σ ≡ nothing)
               (ns0 : next-slot (falloc σ) ≡ 0) (n≥1 : 1 ≤ n)
               (sl0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) 0) ≡ just (SV-Ptr pl))
               (lpl : Live b pl) (cE : CellAt {prog = prog} b E e pl (floc σ))
               {m₀ : AllocMode} (sloc : ValueLocation FS)
               (v : ValidAtWF {prog = prog} m₀ b {⟦ G₁ ⟧TI A IRTy′.+ ⟦ G₂ ⟧TI A} (inj₁ y₁) sloc (floc σ))
               (cP : CellAt {prog = prog} b (⟦ G₁ ⟧TI A) y₁ (sucLoc sloc) (floc σ))
               (slb : Live b (sucLoc sloc))
               (lsloc : Live b sloc) (rax : readReg (regs (floc σ)) Output ≡ SV-Ptr sloc)
               where

      open Pro wF wG n l σ pl b hb span lab nh0 n≥1 sl0 sloc rax

      preSeg2 : SegA a₀ n σ p2
      preSeg2 = record
        { mem  = pm2 ; cf = cfp2
        ; sf   = trans (sfx (restore-input n) p1) (sfx (store-at-slot n) σ)
        ; ns   = trans (exec-abstract-preserves-next-slot (restore-input n) (floc p1) (falloc p1) tt)
                       (exec-abstract-preserves-next-slot (store-at-slot n) s₀ a₀ tt)
        ; href = ≤-reflexive (sym (trans (exec-abstract-preserves-heap-ref (restore-input n) (floc p1) (falloc p1) tt)
                                          (exec-abstract-preserves-heap-ref (store-at-slot n) s₀ a₀ tt)))
        }

      cond : tag-zf (flat-read-tag (floc p2)) ≡ true
      cond = tag-inl {prog = prog} (v-tr (kp-base bl preSeg2) lsloc v) in2

      eqbr : flat-exec-instr (instr-ctrl (c-branch-tag-zero (ℓ o l))) prog p2 ≡ record p2 { fpc = AT.P }
      eqbr = trans (flat-tag-branch-yes prog p2 (ℓ o l) cond) (cong (λ mj → do-jump mj p2) AT.inl-target)

      module U = Unpack (suc AT.P)

      i1 : FlatState
      i1 = record p2 { fpc = AT.P }

      rsp : readLoc (floc U.x2) (sucLoc sloc) ≡ just (cell-sv cP)
      rsp = trans (mem-untouched (restore-input n) (floc p2) (falloc p2) (sucLoc sloc) nhw-restore-input refl)
                  (trans (pm2 (sucLoc sloc) (live-ns n (bl (sucLoc sloc) slb))) (cell-read cP))

      outF : readReg (regs (floc U.x3)) Output ≡ cell-sv cP
      outF = out-lind-suc (floc U.x2) (falloc U.x2) sloc (cell-sv cP) U.inx2 rsp

      nhF : halted (floc U.x3) ≡ false
      nhF = exec-abstract-preserves-halted-WF load-indirect-suc (floc U.x2) (falloc U.x2) U.nhx2
              (sloc , cong sv-as-loc U.inx2 , _ , rsp)

      branchS : SRun prog 4 p2 U.x3
      branchS = s-at i1 (nhp2 , span 2 _ refl) eqbr refl tt
               (s-at U.x1 (nhp2 , AT.spLab 0 _ refl) refl refl tt
               (s-at U.x2 (nhp2 , AT.spLab 1 _ refl) refl refl tt
               (s-at U.x3 (U.nhx2 , AT.spLab 2 _ refl) refl refl tt s-nil)))

      branch : FlatSteps prog 4 p2 U.x3
      branch = proj₁ branchS

      kF : Kp b s₀ b (floc U.x3)
      kF = kp-base bl U.seg

      rF : RRuns′ wF SS.nF (suc (suc l)) U.x3 y₁ b
      rF = ihF SS.nF (suc (suc l)) U.x3 y₁ pl b (≤-trans hb (SegA.href U.seg)) AT.spF AT.labF
             nhF lk (trans (SegA.ns U.seg) ns0) (s≤s z≤n)
             (at-cf (floc U.x3) (falloc U.x3) U.cfx3 (trans (U.um _ bf0) sl0)) lpl
             (cell-copy kF (seg-live-read U.seg pl (bl pl lpl)) cE)
             (cell→out kF cP outF)

      module RF = RRuns′ rF

      sF : FlatState
      sF = RF.settle

      segF : SegA a₀ n U.x3 sF
      segF = seg-rebase RF.seg U.cfx3 n≤nF (SegA.href U.seg)

      cfF : current-frame (falloc sF) ≡ f₀
      cfF = trans (SegA.cf RF.seg) U.cfx3

      h₀≤F : h₀ ≤ next-heap-ref (falloc sF)
      h₀≤F = ≤-trans (SegA.href U.seg) (SegA.href RF.seg)

      spT : SpanAt prog (fpc sF) (tail9 n 0 ++ SS.post)
      spT = subst (λ z → SpanAt prog z (tail9 n 0 ++ SS.post)) (sym RF.pc) AT.spFT

      module T = Tail n 0 prog sF f₀ cfF RF.nh {SS.post} spT
      module TA = T.TMem a₀ refl h₀≤F
      module TF = T.TMem (falloc sF) cfF ≤-refl

      fin : FlatState
      fin = record T.w9 { fpc = suc (fpc T.w9) }

      endS : SRun prog 1 T.w9 fin
      endS = s-at {prog} {T.w9} {0} {fin} {instr-ctrl (c-label (ℓ o (suc l)))} fin
               (T.nhw9 , spT 9 (instr-ctrl (c-label (ℓ o (suc l)))) refl) refl refl tt s-nil

      endRun : FlatSteps prog 1 T.w9 fin
      endRun = proj₁ endS

      run : FlatSteps prog (2 + (4 + (RF.steps + (9 + 1)))) σ fin
      run = FlatSteps-++ pre2 (FlatSteps-++ branch (FlatSteps-++ RF.run (FlatSteps-++ T.run endRun)))

      p-o : Prot b h₀ (falloc fin) (AtDynamic T.ohl)
      p-o = BeforeFrontier.heap-before T.o< , inj₂ h₀≤F
      p-so : Prot b h₀ (falloc fin) (AtDynamic (sucHL T.ohl))
      p-so = BeforeFrontier.heap-before T.o< , inj₂ h₀≤F

      liveF : ∀ l′ → Live (falloc sF) l′ → Live (falloc fin) l′
      liveF = live-from (falloc sF) (falloc fin) (SegA.href TA.seg)

      sumV : ∀ {a′ : AllocState {FS}} {s′ : LocState FS}
           → (∀ l′ → Live (falloc fin) l′ → Live a′ l′)
           → (∀ l′ → Prot b h₀ (falloc fin) l′ → readLoc s′ l′ ≡ readLoc (floc fin) l′)
           → LV (G₁ ⊕ G₂) Heap a′ (rsd (wf-Sum wF wG) (inj₁ y₁)) (AtDynamic T.ohl) s′
      sumV {a′} {s′} bft rd = cell→inl {G₁} {G₂} cellP tt (trans (rd _ p-o) T.how9) (bft _ (proj₁ p-so))
        where
          cellP : CellAtP {⟦ G₁ ⟧TI (ν-type F)} (LV G₁) a′ (rsd wF y₁) (sucLoc (AtDynamic T.ohl)) s′
          cellP = ro→cell RF.rout (λ l′ x → bft l′ (liveF l′ x))
                    (λ l′ p → trans (rd l′ (prot-mono (SegA.href U.seg) liveF p)) (seg-live-read TF.seg l′ (proj₁ p)))
                    (trans (rd _ p-so) T.hsw9)

      pcL : fpc fin ≡ DL.length (rtrace (wf-Sum wF wG) n l) + fpc σ
      pcL = trans (cong (λ z → suc (9 + z)) RF.pc) AT.end-l

      evL : chain-events run ≡ []
      evL = ev-++ pre2 (FlatSteps-++ branch (FlatSteps-++ RF.run (FlatSteps-++ T.run endRun))) (proj₁ (proj₂ pre2S))
              (ev-++ branch (FlatSteps-++ RF.run (FlatSteps-++ T.run endRun)) (proj₁ (proj₂ branchS))
              (ev-++ RF.run (FlatSteps-++ T.run endRun) RF.ev (ev-++ T.run endRun T.ev (proj₁ (proj₂ endS)))))

      logL : LocState.ev-log (floc fin) ≡ LocState.ev-log (floc σ)
      logL = trans (proj₂ (proj₂ endS)) (trans T.log (trans RF.log (trans (proj₂ (proj₂ branchS)) (proj₂ (proj₂ pre2S)))))

      segL : Seg n σ fin
      seg9 : SegA a₀ n σ T.w9
      seg9 = segA-∘ U.seg (segA-∘ segF TA.seg)

      segL = segA-pc {fs′ = T.w9} (suc (fpc T.w9)) seg9

      routL : ROut (G₁ ⊕ G₂) Heap b h₀ (falloc fin) (floc fin) (rsd (wf-Sum wF wG) (inj₁ y₁))
      routL = ro-loc (AtDynamic T.ohl) (proj₁ p-o) T.outw9 sumV

      result : RRuns′ (wf-Sum wF wG) n l σ (inj₁ y₁) b
      result = record
        { steps    = 2 + (4 + (RF.steps + (9 + 1)))
        ; settle   = fin
        ; run      = run
        ; nh       = T.nhw9
        ; pc       = pcL
        ; ret      = RF.ret
        ; lnk      = RF.lnk
        ; ev       = evL
        ; log      = logL
        ; left     = chain-left run T.nhw9
        ; out-mode = Heap
        ; rout     = routL
        ; seg      = segL
        }
