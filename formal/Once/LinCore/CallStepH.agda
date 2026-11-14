-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.CallStepH — plan 0.146 B1.4b (D425): ★ A MANY-USE BODY'S
-- CALL, from its trampoline (beside `CallStep`).
--
-- The trampoline hands its dispatcher's area through (its one save slot,
-- 0, into `Input1`) and the body's view by pointer (the cell's contents'
-- address, already in `Output`); the body's entry saves both and reads the
-- argument from the area, the view from the cell (`SimF.enter-jh`). What
-- the return needs is `CalledH`: as `Called`, the body's first save slot
-- the area's pointer (in the dispatcher's frame, not the caller's).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.CallStepH
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
open import Once.LinCore.ImagePt fmt ans bw using (whole)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.EntriesI fmt ans bw using (module ImgE)
open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
open import Once.LinCore.CallStep fmt ans bw using (module Calls)
import Once.LinCore.Moves

------------------------------------------------------------------------
-- 1. WHAT THE CALL LEAVES FOR ITS RETURN.
------------------------------------------------------------------------

module FramesH {FS : FrameSemantics} where
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc; fret)
  open import Once.LinCore.LowerSimE {FS} using (callee-frame)
  open import Once.LinCore.Moves {FS} using (slot; Old; InBlk)

  -- the return pc `r`, the callee's budget `b`, its first save slot `sv`, the area's pointer `ap`
  record CalledH (fs fs′ : FlatState) (r b sv : ℕ) (ap : StoredValue FS) : Set where
    field
      dh-ret    : fret fs′ ≡ r ∷ fret fs
      dh-saved  : AllocState.saved-frames (falloc fs′)
                  ≡ (AllocState.current-frame (falloc fs) , AllocState.frame-slots (falloc fs)) ∷ AllocState.saved-frames (falloc fs)
      dh-frame  : AllocState.current-frame (falloc fs′) ≡ callee-frame (AllocState.current-frame (falloc fs)) b
      dh-others : ∀ f′ x → ¬ callee-frame (AllocState.current-frame (falloc fs)) b ≡ f′
                → LocState.stackMem (floc fs′) f′ x ≡ LocState.stackMem (floc fs) f′ x
      dh-area   : slot fs′ sv ≡ just ap
      dh-next   : AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs)
      dh-old    : Old (AllocState.next-heap-ref (falloc fs)) fs fs′
      dh-inb    : InBlk fs → InBlk fs′

------------------------------------------------------------------------
-- 2. ★ THE CALL.
------------------------------------------------------------------------

module CallsH {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
              (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
              (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
              (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Program ds f using (U)
  open ProgramRun ds f using (ncty)
  open Program′ ds f ldConst using (image)
  open Lowering U ncty ldConst
  open ImgE {FS} ds f ldConst ld-nl using (image-fn)
  open Rel {FS} U wordOf
  open SimF {FS} U wordOf using (enter-jh)
  open FramesH {FS}
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc; fret)
  open FlatStepsAPI {FS} using (FlatSteps; FlatSteps-++)
  open FrameSemantics FS using (_≺_; ≺-trans; ≺-irrefl)
  open Calls {FS} ds f ldConst ld-nl wordOf using (module K; module CalleeV)
  open import Once.LinCore.LowerSim fmt ans bw using (module Sim)
  open Sim {FS} U wordOf using (slots-frame)
  open import Once.LinCore.LowerSimE {FS}
    using (CallInH; call-in-h; callee-frame; callee-below; ch-frame; ch-saved; ch-ret; ch-pc; ch-in; ch-s₁; ch-s₂; ch-other; ch-heap; ch-next; ch-size; ch-halt)
  open import Once.LinCore.Moves {FS}
    using (Seg; slot; Ran; r-keep; r-pc; r-next; r-old; k-halt; k-ret; k-saved; k-frame; k-other; r-inb; inb-pt)

  private
    sv-ne : ∀ n → ¬ n ≡ suc n
    sv-ne n ()

    shuffle-v : ∀ x y p → (x + suc y) + suc (suc (suc (suc p))) ≡ p + suc (suc (suc (suc (x + suc y))))
    shuffle-v = solve-∀

    ≺-≢ : ∀ {f g} → f ≺ g → f ≡ g → ⊥
    ≺-≢ lt refl = ≺-irrefl lt

  -- ★ from the trampoline's frame (below the area's, `cf`): its save slot 0
  -- the area's pointer, the contents' address (offset `o₀` in cell `i`) in `Output`
  call-core-h : ∀ {X A B} {κ : Key (bsig (just X) A B)} (p : (bsig (just X) A B , κ) ∈ allK U)
                  (cf : FrameSemantics.Frame FS) (area o₀ : ℕ) (i : Id) {x : MV X} {a : MV A} {fs} (wx wa : List W)
              → Seg image (fpc fs) (restore-input 0 ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ [])
              → LocState.halted (floc fs) ≡ false
              → slot fs 0 ≡ just (SV-Ptr (AtStack cf area))
              → AllocState.current-frame (falloc fs) ≺ cf
              → readReg (LocState.regs (floc fs)) Output ≡ SV-Ptr (AtDynamic (cellLoc i o₀))
              → VW (LocState.heapMem (floc fs)) x wx → At (LocState.heapMem (floc fs)) i o₀ wx
              → VW (LocState.heapMem (floc fs)) a wa → SlotsAt (LocState.stackMem (floc fs) cf) (((wsz A ⊔ wsz B) ∸ wsz A) + area) wa
              → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
                  × K.Here p whole (vw x []ᵉ ∥ a ∷ˢ []ˢ) fs′
                  × CalledH fs fs′ (suc (suc (fpc fs))) (fbudget (frameOf (blockᴵ κ))) (sv₁ (frameOf (blockᴵ κ))) (SV-Ptr (AtStack cf area))
  call-core-h {X} {A} {B} {κ} p cf area o₀ i {x} {a} {fs} wx wa seg h s0 lt out px ax pa sa =
    fin (call-in-h image fs 0 ap vp (nameOf (idx p)) (e-fn (nameOf (idx p))) q b (sv₁ φ′) (sv₂ φ′)
           (sv-ne (budget φ′)) s0 out seg (image-fn p) entry-seg h)
    where
      open CalleeV p
      b = fbudget φ′
      cur = AllocState.current-frame (falloc fs)
      ap = SV-Ptr (AtStack cf area)
      vp = SV-Ptr (AtDynamic (cellLoc i o₀))
      callee≢ : ¬ callee-frame cur b ≡ cf
      callee≢ e = ≺-≢ (≺-trans (callee-below cur b) lt) e
      fin : Σ FlatState (λ fs₁ → FlatSteps image 6 fs fs₁ × CallInH fs fs₁ b (sv₁ φ′) (sv₂ φ′) q ap vp) → _
      fin (fs₁ , st₁ , CH) =
        fin₂ (enter-jh image fs₁ φ′ cf area (M ∸ wsz A) (sv₂ φ′) {X} {A} {x} {a} i o₀ wx wa ne₁ (ch-in CH) sv₂-at
                (Data.Nat.Properties.n≤1+n (budget φ′)) pa₁ sa₁ px₁ ax₁ seg₂ h₁
                (proj₁ (K.shape-fits p whole)) (proj₂ (K.shape-fits p whole)))
        where
          import Data.Nat.Properties
          ne₁ : ¬ AllocState.current-frame (falloc fs₁) ≡ cf
          ne₁ e′ = callee≢ (trans (sym (ch-frame CH)) e′)
          h₁ : LocState.halted (floc fs₁) ≡ false
          h₁ = trans (ch-halt CH) h
          sv₂-at : slot fs₁ (sv₂ φ′) ≡ just vp
          sv₂-at = subst (λ g → LocState.stackMem (floc fs₁) g (sv₂ φ′) ≡ just vp) (sym (ch-frame CH)) (ch-s₂ CH)
          pa₁ : VW (LocState.heapMem (floc fs₁)) a wa
          pa₁ = subst (λ r → VW r a wa) (sym (ch-heap CH)) pa
          px₁ : VW (LocState.heapMem (floc fs₁)) x wx
          px₁ = subst (λ r → VW r x wx) (sym (ch-heap CH)) px
          ax₁ : At (LocState.heapMem (floc fs₁)) i o₀ wx
          ax₁ = subst (λ r → At r i o₀ wx) (sym (ch-heap CH)) ax
          sa₁ : SlotsAt (LocState.stackMem (floc fs₁) cf) ((M ∸ wsz A) + area) wa
          sa₁ = slots-frame {LocState.stackMem (floc fs) cf} {LocState.stackMem (floc fs₁) cf} wa
                  (λ k _ → ch-other CH cf (k + ((M ∸ wsz A) + area)) callee≢) sa
          seg₂ : Seg image (fpc fs₁) (argMv ++ viewMv)
          seg₂ = subst (λ z → Seg image z (argMv ++ viewMv)) (sym (ch-pc CH)) pro-seg
          nE = Once.LinCore.Moves.ln {FS} (wsz A) + suc (Once.LinCore.Moves.ln {FS} (wsz X))
          fin₂ : Σ FlatState (λ fs₂ → FlatSteps image nE fs₁ fs₂
                   × CfgW (LocState.heapMem (floc fs₂)) (slot fs₂) φ′ (vw x []ᵉ ∥ a ∷ˢ []ˢ)
                   × Ran nE 0 (AllocState.next-heap-ref (falloc fs₁)) (budget φ′) fs₁ fs₂
                   × (∀ y → budget φ′ ≤ y → slot fs₂ y ≡ slot fs₁ y))
               → _
          fin₂ (fs₂ , st₂ , C₂ , Rn , top) =
            _ , fs₂ , FlatSteps-++ st₁ st₂ ,
            record { h-pc  = trans (r-pc Rn) (trans (cong (nE +_) (ch-pc CH)) (trans (shuffle-v _ _ q) (sym start-pos)))
                   ; h-run = trans (k-halt (r-keep Rn)) h₁
                   ; h-cfg = C₂ } ,
            record { dh-ret    = trans (k-ret (r-keep Rn)) (ch-ret CH)
                   ; dh-saved  = trans (k-saved (r-keep Rn)) (ch-saved CH)
                   ; dh-frame  = trans (k-frame (r-keep Rn)) (ch-frame CH)
                   ; dh-others = λ f′ y ne → trans (k-other (r-keep Rn) f′ y (λ e′ → ne (trans (sym (ch-frame CH)) (sym e′))))
                                                   (ch-other CH f′ y ne)
                   ; dh-area   = trans (top (sv₁ φ′) ≤-refl)
                                   (subst (λ g → LocState.stackMem (floc fs₁) g (sv₁ φ′) ≡ just ap) (sym (ch-frame CH)) (ch-s₁ CH))
                   ; dh-next   = trans (r-next Rn) (ch-next CH)
                   ; dh-old    = λ hl lt′ → trans (r-old Rn hl (subst (_ <_) (sym (ch-next CH)) lt′)) (cong (λ h′ → h′ hl) (ch-heap CH))
                   ; dh-inb    = λ I → r-inb Rn (inb-pt {fs} {fs₁} (λ hl → cong (λ h′ → h′ hl) (ch-heap CH)) (ch-next CH) (ch-size CH) I) }
