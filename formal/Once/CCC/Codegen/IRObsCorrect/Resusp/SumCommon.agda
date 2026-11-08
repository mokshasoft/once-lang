-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.SumCommon
--
-- plan 0.123 alpha-7 (the merge with plan 0.144): what both arms of a SUM layer of
-- the re-suspension share -- the arm cells as the layer's value (`sum-l`, `sum-r`), a
-- control step (`ctl`) and the prologue that keeps the sum and reads its tag (`Common`).
-- Split out of `Resusp.Sum` so that each arm checks in its own module (`SumL`, `SumR`):
-- whole, `Sum` took 3.4 GB and no longer fit the one-process apex (`make certified`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.SumCommon (o : CanonicalName) (tbl : DL.List IRFun) where

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

module ResuspSumCommonC {FS : FrameSemantics} where

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
