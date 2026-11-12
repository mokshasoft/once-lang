-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimB — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: steps built from `LowerSim`'s.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-assoc; ≤-trans; ≤-reflexive; m≤n+m)
open import Data.List using (List; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (StoredValue)
open import Data.Bool using (false)

module Once.LinCore.LowerSimB
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; mpair)
open import Once.LinCore.Machine fmt ans bw using (Stk; _∷ˢ_; Slots; _∥_)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw

module SimB {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open CfgW
  open import Once.LinCore.Moves {FS} using (Seg; slot) renaming (ln to nsteps)
  open import Once.LinCore.MoveCode using (mvSS)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; fpc)
  open import Once.CCC.Machine.SMCore using (module LocState)
  open LocState using (heapMem) renaming (halted to fhalted)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)

  -- ★ `lswap`: `swap`'s code on the pair's components, in place
  lswap-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es A B S} {es : Slots Es} {os : Stk S} {a : MV A} {b : MV B}
            → let t = budget φ ∸ ws (A ∷ B ∷ S) in
              Seg prog (fpc fs) (mvSS t (t ∸ wsz A) (wsz A) ++ mvSS (t + wsz A) t (wsz B) ++ mvSS (t ∸ wsz A) (t + wsz B) (wsz A))
            → fhalted (floc fs) ≡ false
            → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ mpair a b ∷ˢ os)
            → wsz A + ws ((A ⊗t B) ∷ S) ≤ OP φ
            → Σ FlatState λ fs₃ → FlatSteps prog (nsteps (wsz A) + (nsteps (wsz B) + nsteps (wsz A))) fs fs₃
                × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ mpair b a ∷ˢ os)
  lswap-sim prog fs φ {Es} {A} {B} {S} {es} {os} {a} {b} s h C fitT
    = finish (swap-sim prog fs φ {Es} {A} {B} {S} {es} {os} {a} {b} s h C′ fitT′)
    where
      rd = heapMem (floc fs)
      assoc : ws ((A ⊗t B) ∷ S) ≡ ws (A ∷ B ∷ S)
      assoc = +-assoc (wsz A) (wsz B) (ws S)
      fitB : ws (A ∷ B ∷ S) ≤ budget φ
      fitB = ≤-trans (subst (_≤ OP φ) assoc (c-sfit C)) (m≤n+m (OP φ) (EP φ))
      C′ : CfgW rd (slot fs) φ (es ∥ a ∷ˢ b ∷ˢ os)
      C′ = record { c-env = c-env C
                  ; c-stk = unpair-W {rd} {slot fs} {φ} {A} {B} {S} {a} {b} {os} fitB (c-stk C)
                  ; c-efit = c-efit C
                  ; c-sfit = subst (_≤ OP φ) assoc (c-sfit C) }
      fitT′ : wsz A + ws (A ∷ B ∷ S) ≤ OP φ
      fitT′ = subst (λ z → wsz A + z ≤ OP φ) assoc fitT
      t = budget φ ∸ ws (A ∷ B ∷ S)
      n = nsteps (wsz A) + (nsteps (wsz B) + nsteps (wsz A))
      finish : Σ FlatState (λ fs₃ → FlatSteps prog n fs fs₃ × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ b ∷ˢ a ∷ˢ os))
             → Σ FlatState (λ fs₃ → FlatSteps prog n fs fs₃ × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ mpair b a ∷ˢ os))
      finish (fs₃ , st , C₃) =
        fs₃ , st ,
        record { c-env = c-env C₃
               ; c-stk = pair-W {heapMem (floc fs₃)} {slot fs₃} {φ} {B} {A} {S} {b} {a} {os}
                           (≤-trans (c-sfit C₃) (m≤n+m (OP φ) (EP φ))) (c-stk C₃)
               ; c-efit = c-efit C₃
               ; c-sfit = subst (_≤ OP φ) (sym (+-assoc (wsz B) (wsz A) (ws S))) (c-sfit C₃) }
