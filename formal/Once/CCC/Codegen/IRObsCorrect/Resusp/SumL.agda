-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.SumL
--
-- plan 0.123 alpha-7: the `inl` arm of a SUM layer of the re-suspension (the branch is
-- taken; split out of `Resusp.Sum`, see `SumCommon`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.SumL (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore using (ending)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; LocState; AllocState; module LocState; module AllocState;
         readReg; Output; Input1; SV-Ptr; SV-Code; StoredValue; sucLoc; offsetLoc;
         store-at-slot; restore-input; instr-ctrl; c-branch-tag-zero; c-jmp; c-label)
open LocState using (regs; halted)
open AllocState using (current-frame; next-slot; next-heap-ref; saved-frames)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; wf-Sum; _⊕_) renaming (_+_ to _+ᵀ_)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.SlotBudget o using (resuspend-mono)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumShape o tbl using (module ResuspSumShapeC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumArm o tbl using (module ResuspSumArmC)
open import Once.CCC.Codegen.IRObsCorrect.CaseShape o tbl using (module ShapeC)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (z≤n; s≤s; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)

open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumCommon o tbl using (module ResuspSumCommonC)

module ResuspSumLC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-tag-branch-yes; flat-tag-branch-not; flat-jmp)
  open ResuspBaseC {FS}
  open ResuspSumShapeC {FS}
  open ResuspSumArmC {FS}
  open ShapeC {FS} using (tag-inl; tag-inr; payload-l; payload-r)
  open ClosureWellFormedBase {FS} using (SumTag; Pad; CellAtP; inl-wf; inr-wf; inl-reg-wf; inr-reg-wf; inl-flat-wf; inr-flat-wf)
  import Once.CCC.Machine.SMCore as SMCore
  open ResuspSumCommonC {FS}

  module RSumL {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
              (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (e : ValueDomain.⟦ E ⟧ᴰᴵ)
              (prog : AbstractTrace) (lbl-n : ℕ) (R : VTy (ν-type F))
              (mk-child : ∀ {alloc ν-loc s pl′} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                        → LocMatchesMode Heap ν-loc
                        → readLoc s ν-loc ≡ just (SV-Ptr pl′) → Live alloc pl′
                        → ValidAtWF {prog = prog} Heap alloc {E IRTy′.* A} (e , a′) pl′ s
                        → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o lbl-n))
                        → Live alloc (sucLoc ν-loc)
                        → R Heap alloc (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc s)
              (R-tr : ∀ {a a′ : AllocState {FS}} {s s′ : LocState FS}
                    → (∀ l → Live a l → Live a′ l) → (∀ l → Live a l → readLoc s′ l ≡ readLoc s l)
                    → BlocksKept a a′
                    → ∀ {m v l} → R m a v l s → R m a′ v l s′)
              {G₁ G₂ : IRFunctor} (wF : WellFormedFI G₁) (wG : WellFormedFI G₂)
              (ihF : RBase.Resusp′ wf coalg e prog lbl-n R mk-child R-tr wF)
              (ihG : RBase.Resusp′ wf coalg e prog lbl-n R mk-child R-tr wG)
              where

    open RBase wf coalg e prog lbl-n R mk-child R-tr
    open RSum wf coalg e prog lbl-n R mk-child R-tr wF wG ihF ihG

    -- `Resusp′ (wf-Sum wF wG)` at the L tag
    ArmL : Set
    ArmL =
      ∀ (n l : ℕ) (σ : FlatState) (y₁ : ValueDomain.⟦ ⟦ G₁ ⟧TI A ⟧ᴰᴵ) (pl : ValueLocation FS)
        (b : AllocState {FS}) → next-heap-ref b ≤ next-heap-ref (falloc σ) → BlocksKept b (falloc σ)
      → SpanAt prog (fpc σ) (rtrace (wf-Sum wF wG) n l)
      → LabelsAt prog (fpc σ) (rtrace (wf-Sum wF wG) n l)
      → halted (floc σ) ≡ false → flink σ ≡ nothing
      → next-slot (falloc σ) ≡ 0 → 1 ≤ n
      → readLoc (floc σ) (AtStack (current-frame (falloc σ)) 0) ≡ just (SV-Ptr pl)
      → Live b pl
      → CellAt {prog = prog} b E e pl (floc σ)
      → OutAt′ {⟦ G₁ ⊕ G₂ ⟧TI A} b (inj₁ y₁) (floc σ)
      → RRuns′ (wf-Sum wF wG) n l σ (inj₁ y₁) b

    result-l : ArmL
    result-l n l σ y₁ pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE (out-reg () _)
    result-l n l σ y₁ pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE (out-unit ())
    result-l n l σ y₁ pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE (out-loc {m} sloc v lsl rax) = record
      { steps    = 2 + (1 + (1 + (AR.steps + 1)))
      ; settle   = σ₄
      ; run      = run
      ; nh       = AR.nh
      ; pc       = trans (cong suc (trans AR.pc AT.join-l)) AT.end
      ; ret      = AR.ret
      ; lnk      = AR.lnk
      ; ev       = ev
      ; log      = trans (log-of run ev) (++-identityʳ _)
      ; left     = chain-left run AR.nh
      ; out-mode = Heap
      ; rout     = ro-loc AR.D (AR.B.liveD 0) refl
                     (λ keep → sum-l (AR.B.cell-at keep) (AR.B.tag-at keep) AR.B.live-suc AR.B.in-suc (AR.B.pad-at keep) tt)
      ; seg      = segA-∘ (S.seg n ≤-refl) (segA-∘ (ctl σ₁ AT.P) (segA-∘ (ctl σ₂ (suc AT.P)) (segA-∘ AR.seg (ctl σE (suc (fpc σE))))))
      ; bk       = AR.bk
      }
      where
        open Common n l σ pl b hb bkb span lab nh n≥1 sl0 lpl cE sloc rax

        v₁ = vtr lsl v

        σ₂ σ₃ : FlatState
        σ₂ = record σ₁ { fpc = AT.P }
        σ₃ = record σ₂ { fpc = suc AT.P }

        eqBr : flat-exec-instr (instr-ctrl (c-branch-tag-zero (ℓ o l))) prog σ₁ ≡ σ₂
        eqBr = trans (flat-tag-branch-yes prog σ₁ (ℓ o l) (tag-inl v₁ refl)) (cong (λ mj → do-jump mj σ₁) AT.inl-target)

        br : FlatSteps prog 1 σ₁ σ₂
        br = flat-step1 nh fBr eqBr

        lb : FlatSteps prog 1 σ₂ σ₃
        lb = flat-step1 nh AT.at-lab refl

        module AF = RArm wf coalg e prog lbl-n R mk-child R-tr wF ihF 0 sz n SS.nF (suc (suc l))
        module AR = AF.Run (s≤s (m≤m⊔n (size Fν) (size Gν))) ≤-refl σ₃ AT.spF AT.labF nh lk ns n≥1
                      slotS sl0′ b hb bkb lpl cE′ lsl (payload-l v₁)

        σE = AR.settle

        fJ : fetch prog (fpc σE) ≡ just (instr-ctrl (c-label (ℓ o (suc l))))
        fJ = trans (cong (fetch prog) AR.pc) AT.at-join-l

        σ₄ : FlatState
        σ₄ = record σE { fpc = suc (fpc σE) }

        jn : FlatSteps prog 1 σE σ₄
        jn = flat-step1 AR.nh fJ refl

        run : FlatSteps prog (2 + (1 + (1 + (AR.steps + 1)))) σ σ₄
        c4 = FlatSteps-++ AR.run jn
        c3 = FlatSteps-++ lb c4
        c2 = FlatSteps-++ br c3
        run = FlatSteps-++ S.run c2

        ev : chain-events run ≡ []
        ev = trans (chain-events-++ S.run c2) (cong₂ DL._++_ S.silent
            (trans (chain-events-++ br c3) (cong₂ DL._++_ (ev-step1 {prog} σ₁ nh fBr eqBr refl)
            (trans (chain-events-++ lb c4) (cong₂ DL._++_ (ev-step1 {prog} σ₂ nh AT.at-lab refl refl)
            (trans (chain-events-++ AR.run jn) (cong₂ DL._++_ AR.ev (ev-step1 {prog} σE AR.nh fJ refl refl))))))))
