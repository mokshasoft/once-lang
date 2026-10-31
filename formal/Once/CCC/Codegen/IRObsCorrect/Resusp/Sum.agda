-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.Sum
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
module Once.CCC.Codegen.IRObsCorrect.Resusp.Sum (o : CanonicalName) (tbl : DL.List IRFun) where


open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl
open import Once.CCC.Machine.FlatLog using (LogFree)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumTail o tbl
open import Once.CCC.Codegen.IRObsCorrect.CaseShape o tbl using (module ShapeC)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.SlotBudget o using (resuspend-mono)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue
        ; readReg; Output; Input1; SV-Code; SV-Ptr; sucLoc; instr-ctrl; c-branch-tag-zero; c-jmp
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
import Once.CCC.Machine.ValueRel as CWF
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumL o tbl using (module ResuspSumLC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.SumR o tbl using (module ResuspSumRC)
module ResuspSumC {FS : FrameSemantics} where

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

  module RSum {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
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

    -- the two arms (`SumL`, `SumR`; the shared prologue is `SumPro`)
    module ArmL = ResuspSumLC.RSumL.ArmL {FS} wf coalg e prog lbl-n R mk-child
    module ArmR = ResuspSumRC.RSumR.ArmR {FS} wf coalg e prog lbl-n R mk-child

    resusp-Sum : ∀ {G₁ G₂ : IRFunctor} (wF : WellFormedFI G₁) (wG : WellFormedFI G₂)
               → Resusp′ wF → Resusp′ wG → Resusp′ (wf-Sum wF wG)
    resusp-Sum wF wG ihF ihG n l σ (inj₁ y₁) pl b hb span lab nh lk ns n≥1 sl0 lpl cE
               (out-loc sloc v@(valid-inl-wf lmm tg pp pb slb pv) lsloc rax) =
      ArmL.result wF wG ihF n l σ y₁ pl b hb span lab nh lk ns n≥1 sl0 lpl cE sloc v (cell-ptr pp pb pv) slb lsloc rax
    resusp-Sum wF wG ihF ihG n l σ (inj₁ y₁) pl b hb span lab nh lk ns n≥1 sl0 lpl cE
               (out-loc sloc v@(valid-inl-reg-wf lmm tg rep pp slb) lsloc rax) =
      ArmL.result wF wG ihF n l σ y₁ pl b hb span lab nh lk ns n≥1 sl0 lpl cE sloc v (cell-inline rep pp) slb lsloc rax
    resusp-Sum wF wG ihF ihG n l σ (inj₂ y₂) pl b hb span lab nh lk ns n≥1 sl0 lpl cE
               (out-loc sloc v@(valid-inr-wf lmm tg pp pb slb pv) lsloc rax) =
      ArmR.result wF wG ihG n l σ y₂ pl b hb span lab nh lk ns n≥1 sl0 lpl cE sloc v (cell-ptr pp pb pv) slb lsloc rax
    resusp-Sum wF wG ihF ihG n l σ (inj₂ y₂) pl b hb span lab nh lk ns n≥1 sl0 lpl cE
               (out-loc sloc v@(valid-inr-reg-wf lmm tg rep pp slb) lsloc rax) =
      ArmR.result wF wG ihG n l σ y₂ pl b hb span lab nh lk ns n≥1 sl0 lpl cE sloc v (cell-inline rep pp) slb lsloc rax
    resusp-Sum wF wG ihF ihG n l σ (inj₁ y₁) pl b hb span lab nh lk ns n≥1 sl0 lpl cE (out-reg () _)
    resusp-Sum wF wG ihF ihG n l σ (inj₂ y₂) pl b hb span lab nh lk ns n≥1 sl0 lpl cE (out-reg () _)
    resusp-Sum wF wG ihF ihG n l σ (inj₁ y₁) pl b hb span lab nh lk ns n≥1 sl0 lpl cE (out-unit ())
    resusp-Sum wF wG ihF ihG n l σ (inj₂ y₂) pl b hb span lab nh lk ns n≥1 sl0 lpl cE (out-unit ())
