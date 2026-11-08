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

open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumL o tbl using (module ResuspSumLC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumR o tbl using (module ResuspSumRC)

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

  -- the arms check in their own modules (`SumL`, `SumR`; shared: `SumCommon`)
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
    module AL = ResuspSumLC.RSumL {FS} wf coalg e prog lbl-n R mk-child R-tr wF wG ihF ihG
    module AR = ResuspSumRC.RSumR {FS} wf coalg e prog lbl-n R mk-child R-tr wF wG ihF ihG

    resusp-Sum : Resusp′ (wf-Sum wF wG)
    resusp-Sum n l σ (inj₁ y₁) = AL.result-l n l σ y₁
    resusp-Sum n l σ (inj₂ y₂) = AR.result-r n l σ y₂
