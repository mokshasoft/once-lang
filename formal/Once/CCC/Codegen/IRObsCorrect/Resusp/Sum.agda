-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.Sum
--
-- plan 0.135 S3 / plan 0.123 α2: the re-suspension at a SUM layer
-- (`wf-Sum`), by the layer's tag. The sum is kept at `src` and put back in
-- Input1; the branch reads its tag:
--
--   * `inl`: the branch jumps to `l`, the `inl` arm (tag 0) runs, and the
--     run falls into the join label;
--   * `inr`: the branch falls through, the `inr` arm (tag 1) runs, and the
--     jump lands on the join label.
--
-- Each arm (`SumArm`) leaves a fresh tagged block; this module makes it the
-- layer's `SumV`, by where the payload's re-suspension put its result.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.Sum (o : CanonicalName) (tbl : DL.List IRFun) where

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

module ResuspSumC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (flat-step1; flat-tag-branch-yes; flat-tag-branch-not; flat-jmp)
  open ResuspBaseC {FS}
  open ResuspSumShapeC {FS}
  open ResuspSumArmC {FS}
  open ShapeC {FS} using (tag-inl; tag-inr; payload-l; payload-r)
  open ClosureWellFormedBase {FS} using (SumTag; Pad; CellAtP; inl-wf; inr-wf; inl-reg-wf; inr-reg-wf; inl-flat-wf; inr-flat-wf)
  import Once.CCC.Machine.SMCore as SMCore

  -- a one-step chain emits what its instruction emits
  ev-step1 : ∀ {prog : AbstractTrace} (fs : FlatState) {fs′ : FlatState} {i : AbstractInstr}
               (h : halted (floc fs) ≡ false) (ft : fetch prog (fpc fs) ≡ just i)
               (eq : flat-exec-instr i prog fs ≡ fs′)
             → event-of i fs ≡ []
             → chain-events (flat-step1 {prog} {fs} h ft eq) ≡ []
  ev-step1 fs h ft refl e = cong (_++ []) e

  module RSum {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
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

    Fν Gν : IRTy
    Fν = ⟦ G₁ ⟧TI Xν
    Gν = ⟦ G₂ ⟧TI Xν

    -- the layer's sum, from an arm's block
    sum-l : ∀ {a v D s} → CellAtP {Fν} (LV G₁) a v (sucLoc D) s → SumTag Heap 0 s D → Live a (sucLoc D)
          → InBlk a (sucLoc D) → Pad s D (suc (size Fν)) (size Fν ⊔ size Gν ∸ size Fν)
          → LocMatchesMode Heap D
          → LV (G₁ ⊕ G₂) Heap a (inj₁ v) D s
    sum-l (cell-ptr nd r lv vv) tg slb ib pd lmm = inl-wf nd lmm tg r lv slb pd vv
    sum-l (cell-inline rep r) tg slb ib pd lmm = inl-reg-wf lmm tg rep r slb pd
    sum-l (cell-flat fl hr vv) tg slb ib pd lmm = inl-flat-wf fl lmm tg slb (λ _ → ib) pd vv

    sum-r : ∀ {a v D s} → CellAtP {Gν} (LV G₂) a v (sucLoc D) s → SumTag Heap 1 s D → Live a (sucLoc D)
          → InBlk a (sucLoc D) → Pad s D (suc (size Gν)) (size Fν ⊔ size Gν ∸ size Gν)
          → LocMatchesMode Heap D
          → LV (G₁ ⊕ G₂) Heap a (inj₂ v) D s
    sum-r (cell-ptr nd r lv vv) tg slb ib pd lmm = inr-wf nd lmm tg r lv slb pd vv
    sum-r (cell-inline rep r) tg slb ib pd lmm = inr-reg-wf lmm tg rep r slb pd
    sum-r (cell-flat fl hr vv) tg slb ib pd lmm = inr-flat-wf fl lmm tg slb (λ _ → ib) pd vv

    -- a control step moves only the pc
    ctl : ∀ {a n} (fs : FlatState) (k : ℕ) → SegA a n fs (record fs { fpc = k })
    ctl fs k = record { mem = λ _ _ → refl ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }

    ------------------------------------------------------------------
    -- WHAT BOTH TAGS SHARE: the sum kept at `src`, back in Input1
    ------------------------------------------------------------------
    module Common (n l : ℕ) (σ : FlatState) (pl : ValueLocation FS)
                  (b : AllocState {FS}) (hb : next-heap-ref b ≤ next-heap-ref (falloc σ)) (bkb : BlocksKept b (falloc σ))
                  (span : SpanAt prog (fpc σ) (rtrace (wf-Sum wF wG) n l))
                  (lab : LabelsAt prog (fpc σ) (rtrace (wf-Sum wF wG) n l))
                  (nh : halted (floc σ) ≡ false) (n≥1 : 1 ≤ n)
                  (sl0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) 0) ≡ just (SV-Ptr pl))
                  (lpl : Live b pl) (cE : CellAt {prog = prog} b E e pl (floc σ))
                  (sloc : ValueLocation FS) (rax : readReg (regs (floc σ)) Output ≡ SV-Ptr sloc)
                  where

      module SS = SumShape F E A lbl-n wF wG n l
      module AT = SS.At prog (fpc σ) span lab

      s  = floc σ
      a  = falloc σ
      cf = current-frame a

      r1 : readLoc (proj₁ (exec-abstract (store-at-slot n) s a)) (AtStack cf n) ≡ just (SV-Ptr sloc)
      r1 = trans (SMCore.MemOps.writeLoc-read-same-stack {FS} s cf n (readReg (regs s) Output)) (cong just rax)

      module S = Stash {prog} σ n n (SV-Ptr sloc) nh
                   (span-take prog (store-at-slot n ∷ restore-input n ∷ [])
                      {instr-ctrl (c-branch-tag-zero (ℓ o l)) ∷ (SS.armG DL.++ (SS.midJ DL.++ (SS.armF DL.++ SS.post)))} (fpc σ) span)
                   r1
      σ₁ = S.fs′

      fBr : fetch prog (fpc σ₁) ≡ just (instr-ctrl (c-branch-tag-zero (ℓ o l)))
      fBr = AT.at-pre 2 _ refl

      keep₁ : ∀ l′ → Live b l′ → readLoc (floc σ₁) l′ ≡ readLoc s l′
      keep₁ (AtDynamic hl) _ = refl

      slotS : readLoc (floc σ₁) (AtStack cf n) ≡ just (SV-Ptr sloc)
      slotS = trans S.slot (cong just rax)

      sl0′ : readLoc (floc σ₁) (AtStack cf 0) ≡ just (SV-Ptr pl)
      sl0′ = trans (S.other 0 (λ e′ → <-irrefl e′ n≥1)) sl0

      cE′ : CellAt {prog = prog} b E e pl (floc σ₁)
      cE′ = cellWF-heap-transport (Live b) (λ _ x → x) keep₁ (λ _ x → x) (λ _ _ ib → ib) e pl lpl cE

      vtr : ∀ {m′ y′} → Live b sloc → ValidAtWF {prog = prog} m′ b {⟦ G₁ ⟧TI A +ᵀ ⟦ G₂ ⟧TI A} y′ sloc s
          → ValidAtWF {prog = prog} m′ b {⟦ G₁ ⟧TI A +ᵀ ⟦ G₂ ⟧TI A} y′ sloc (floc σ₁)
      vtr {y′ = y′} lsl v = validityWF-heap-transport (Live b) (λ _ x → x) keep₁ (λ _ x → x) (λ _ _ ib → ib) y′ sloc lsl v

      sz = size (Fν +ᵀ Gν)

    resusp-Sum : Resusp′ (wf-Sum wF wG)
    resusp-Sum n l σ y pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE (out-reg () _)
    resusp-Sum n l σ y pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE (out-unit ())
    -- inl: the branch is taken
    resusp-Sum n l σ (inj₁ y₁) pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE (out-loc {m} sloc v lsl rax) = record
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
    -- inr: the branch falls through
    resusp-Sum n l σ (inj₂ y₂) pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE (out-loc {m} sloc v lsl rax) = record
      { steps    = 2 + (1 + (AR.steps + (1 + 1)))
      ; settle   = σ₄
      ; run      = run
      ; nh       = AR.nh
      ; pc       = AT.end
      ; ret      = AR.ret
      ; lnk      = AR.lnk
      ; ev       = ev
      ; log      = trans (log-of run ev) (++-identityʳ _)
      ; left     = chain-left run AR.nh
      ; out-mode = Heap
      ; rout     = ro-loc AR.D (AR.B.liveD 0) refl
                     (λ keep → sum-r (AR.B.cell-at keep) (AR.B.tag-at keep) AR.B.live-suc AR.B.in-suc (AR.B.pad-at keep) tt)
      ; seg      = segA-∘ (S.seg n ≤-refl) (segA-∘ (ctl σ₁ (suc (fpc σ₁))) (segA-∘ AR.seg (segA-∘ (ctl σE AT.J) (ctl σ₃ (suc AT.J)))))
      ; bk       = AR.bk
      }
      where
        open Common n l σ pl b hb bkb span lab nh n≥1 sl0 lpl cE sloc rax

        v₁ = vtr lsl v

        σ₂ : FlatState
        σ₂ = record σ₁ { fpc = suc (fpc σ₁) }

        eqBr : flat-exec-instr (instr-ctrl (c-branch-tag-zero (ℓ o l))) prog σ₁ ≡ σ₂
        eqBr = flat-tag-branch-not prog σ₁ (ℓ o l) (tag-inr v₁ refl)

        br : FlatSteps prog 1 σ₁ σ₂
        br = flat-step1 nh fBr eqBr

        module AG = RArm wf coalg e prog lbl-n R mk-child R-tr wG ihG 1 sz n SS.n2 SS.l2
        module AR = AG.Run (s≤s (m≤n⊔m (size Fν) (size Gν))) (resuspend-mono F E A SS.nF (suc (suc l)) (ℓ o lbl-n) 0 wF)
                      σ₂ AT.spG AT.labG nh lk ns n≥1 slotS sl0′ b hb bkb lpl cE′ lsl (payload-r v₁)

        σE = AR.settle

        fJm : fetch prog (fpc σE) ≡ just (instr-ctrl (c-jmp (ℓ o (suc l))))
        fJm = trans (cong (fetch prog) AR.pc) AT.at-jmp

        σ₃ σ₄ : FlatState
        σ₃ = record σE { fpc = AT.J }
        σ₄ = record σ₃ { fpc = suc AT.J }

        eqJ : flat-exec-instr (instr-ctrl (c-jmp (ℓ o (suc l)))) prog σE ≡ σ₃
        eqJ = trans (flat-jmp prog σE (ℓ o (suc l))) (cong (λ mj → do-jump mj σE) AT.join-target)

        jm : FlatSteps prog 1 σE σ₃
        jm = flat-step1 AR.nh fJm eqJ

        jn : FlatSteps prog 1 σ₃ σ₄
        jn = flat-step1 AR.nh AT.at-join refl

        run : FlatSteps prog (2 + (1 + (AR.steps + (1 + 1)))) σ σ₄
        d3 = FlatSteps-++ jm jn
        d2 = FlatSteps-++ AR.run d3
        d1 = FlatSteps-++ br d2
        run = FlatSteps-++ S.run d1

        ev : chain-events run ≡ []
        ev = trans (chain-events-++ S.run d1) (cong₂ DL._++_ S.silent
            (trans (chain-events-++ br d2) (cong₂ DL._++_ (ev-step1 {prog} σ₁ nh fBr eqBr refl)
            (trans (chain-events-++ AR.run d3) (cong₂ DL._++_ AR.ev
            (trans (chain-events-++ jm jn) (cong₂ DL._++_ (ev-step1 {prog} σE AR.nh fJm eqJ refl)
                                                         (ev-step1 {prog} σ₃ AR.nh AT.at-join refl refl))))))))
