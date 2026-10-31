-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.SumPro
--
-- Part of `Resusp.Sum`, split for the per-module memory cap: the shared prologue of the two arms (`Pro`).
--
-- plan 0.135 S3: a SUM layer of the re-suspension (shape: `SumShape`).
-- The branch reads the input's own tag. The `inl` arm jumps to the mid
-- row's label, loads the payload, re-suspends it (`tF`), builds a fresh
-- `[0 , result]` node (`SumTail`) and falls through the join label; the
-- `inr` arm falls through, does the same with `tG` and tag 1, and jumps to
-- the join label. Both land one past the join.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.SumPro (o : CanonicalName) (tbl : DL.List IRFun) where


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

module ResuspSumProC {FS : FrameSemantics} where

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

  module RSumPro {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
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

    module Pro {G₁ G₂ : IRFunctor} (wF : WellFormedFI G₁) (wG : WellFormedFI G₂)
               (n l : ℕ) (σ : FlatState) (pl : ValueLocation FS)
               (b : AllocState {FS}) (hb : next-heap-ref b ≤ next-heap-ref (falloc σ))
               (span : SpanAt prog (fpc σ) (rtrace (wf-Sum wF wG) n l))
               (lab : LabelsAt prog (fpc σ) (rtrace (wf-Sum wF wG) n l))
               (nh0 : halted (floc σ) ≡ false)
               (n≥1 : 1 ≤ n)
               (sl0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) 0) ≡ just (SV-Ptr pl))
               (sloc : ValueLocation FS) (rax : readReg (regs (floc σ)) Output ≡ SV-Ptr sloc)
               where

      module SS = SumShape lbl-n wF wG n l
      module AT = SS.At prog (fpc σ) span lab

      s₀ : LocState FS
      s₀ = floc σ
      a₀ : AllocState {FS}
      a₀ = falloc σ
      f₀ = current-frame a₀
      h₀ : ℕ
      h₀ = next-heap-ref a₀

      bl : ∀ l′ → Live b l′ → Live a₀ l′
      bl = live-from b a₀ hb

      a-n : AllocState {FS}
      a-n = record a₀ { next-slot = n }

      bf0 : BeforeFrontier a-n (AtStack f₀ 0)
      bf0 = BeforeFrontier.stack-before refl n≥1

      n≤nF : n ≤ SS.nF
      n≤nF = ≤-trans (≤-trans (n≤1+n n) (n≤1+n (suc n))) (n≤1+n (suc (suc n)))

      p1 p2 : FlatState
      p1 = St (store-at-slot n) σ
      p2 = St (restore-input n) p1

      cfp1 : current-frame (falloc p1) ≡ f₀
      cfp1 = cfx (store-at-slot n) σ
      cfp2 : current-frame (falloc p2) ≡ f₀
      cfp2 = trans (cfx (restore-input n) p1) cfp1

      snp1 : readLoc (floc p1) (AtStack f₀ n) ≡ just (SV-Ptr sloc)
      snp1 = trans (sl-same n s₀ a₀ f₀ refl) (cong just rax)
      snp2 : readLoc (floc p2) (AtStack f₀ n) ≡ just (SV-Ptr sloc)
      snp2 = trans (sl-keep (restore-input n) (floc p1) (falloc p1) f₀ n nhw-restore-input refl) snp1

      in2 : readReg (regs (floc p2)) Input1 ≡ SV-Ptr sloc
      in2 = in-restore n (floc p1) (falloc p1) _ (at-cf (floc p1) (falloc p1) cfp1 snp1)

      nhp1 : halted (floc p1) ≡ false
      nhp1 = exec-abstract-preserves-halted-WF (store-at-slot n) s₀ a₀ nh0 tt
      nhp2 : halted (floc p2) ≡ false
      nhp2 = exec-abstract-preserves-halted-WF (restore-input n) (floc p1) (falloc p1) nhp1 (_ , at-cf (floc p1) (falloc p1) cfp1 snp1)

      pm1 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc p1) loc ≡ readLoc s₀ loc
      pm1 loc bf = store-slot-preserves-before n s₀ a-n a₀ loc refl ≤-refl bf
      pm2 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc p2) loc ≡ readLoc s₀ loc
      pm2 loc bf = trans (mem-untouched (restore-input n) (floc p1) (falloc p1) loc nhw-restore-input refl) (pm1 loc bf)

      -- the arm's two rows, `restore-input n ∷ load-indirect-suc`, from a
      -- state with p2's memory (the branch moved only the pc)
      module Unpack (pc : ℕ) where
        x1 x2 x3 : FlatState
        x1 = record p2 { fpc = pc }
        x2 = St (restore-input n) x1
        x3 = St load-indirect-suc x2

        cfx3 : current-frame (falloc x3) ≡ f₀
        cfx3 = trans (cfx load-indirect-suc x2) (trans (cfx (restore-input n) x1) cfp2)

        inx2 : readReg (regs (floc x2)) Input1 ≡ SV-Ptr sloc
        inx2 = in-restore n (floc p2) (falloc p2) _ (at-cf (floc p2) (falloc p2) cfp2 snp2)

        nhx2 : halted (floc x2) ≡ false
        nhx2 = exec-abstract-preserves-halted-WF (restore-input n) (floc p2) (falloc p2) nhp2 (_ , at-cf (floc p2) (falloc p2) cfp2 snp2)

        um : ∀ loc → BeforeFrontier a-n loc → readLoc (floc x3) loc ≡ readLoc s₀ loc
        um loc bf = trans (mem-untouched load-indirect-suc (floc x2) (falloc x2) loc nhw-load-indirect-suc refl)
                   (trans (mem-untouched (restore-input n) (floc p2) (falloc p2) loc nhw-restore-input refl) (pm2 loc bf))

        seg : SegA a₀ n σ x3
        seg = record
          { mem  = um
          ; cf   = cfx3
          ; sf   = trans (sfx load-indirect-suc x2) (trans (sfx (restore-input n) x1)
                   (trans (sfx (restore-input n) p1) (sfx (store-at-slot n) σ)))
          ; ns   = trans (exec-abstract-preserves-next-slot load-indirect-suc (floc x2) (falloc x2) tt)
                   (trans (exec-abstract-preserves-next-slot (restore-input n) (floc p2) (falloc p2) tt)
                   (trans (exec-abstract-preserves-next-slot (restore-input n) (floc p1) (falloc p1) tt)
                          (exec-abstract-preserves-next-slot (store-at-slot n) s₀ a₀ tt)))
          ; href = ≤-reflexive (sym
                   (trans (exec-abstract-preserves-heap-ref load-indirect-suc (floc x2) (falloc x2) tt)
                   (trans (exec-abstract-preserves-heap-ref (restore-input n) (floc p2) (falloc p2) tt)
                   (trans (exec-abstract-preserves-heap-ref (restore-input n) (floc p1) (falloc p1) tt)
                          (exec-abstract-preserves-heap-ref (store-at-slot n) s₀ a₀ tt)))))
          }

        log : LocState.ev-log (floc x3) ≡ LocState.ev-log s₀
        log = trans (lgx load-indirect-suc x2 tt) (trans (lgx (restore-input n) x1 tt)
              (trans (lgx (restore-input n) p1 tt) (lgx (store-at-slot n) σ tt)))

      pre2S : SRun prog 2 σ p2
      pre2S = s-at p1 (nh0 , span 0 _ refl) refl refl tt (s-at p2 (nhp1 , span 1 _ refl) refl refl tt s-nil)

      pre2 : FlatSteps prog 2 σ p2
      pre2 = proj₁ pre2S

    ------------------------------------------------------------------
    -- THE `inl` ARM.
    ------------------------------------------------------------------
