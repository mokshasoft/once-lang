-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.StepEpop — plan 0.146 B1.4b (D425): AN `epop`'s STEP,
-- inverted. A many-use body's trampoline takes one step that stays at a
-- trampoline's point (its `epop`); the split on the step lives here, in a
-- module of its own (a split of `StepI` unifies its indices for each of its
-- constructors).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Level using (Level)
open import Data.List using (_∷_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.StepEpop
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Events fmt ans bw using (MV)
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; Slots; Cfg; _∥_; vw)
open import Once.LinCore.Image fmt ans bw using (Codeᴵ; _⨾_; epop)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; StepI; i-epop)

module _ {ℓ : Level} {T : Sh} where

  epop-inv : ∀ {E Es S U} {k : Codeᴵ (Es ∣ S) U} {r : Ret U T} {m : Cfg (E ∷ Es ∣ S)} {n t sh′ U′}
               {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
           → (P : Cfg (E ∷ Es ∣ S) → ∀ {sh′ U′} → Codeᴵ sh′ U′ → Ret U′ T → Cfg sh′ → ℕ → Set ℓ)
           → (∀ {e : MV E} {es : Slots Es} {os : Stk S} → P (vw e es ∥ os) k r (es ∥ os) n)
           → StepI (epop ⨾ k) r m n t c′ r′ m′ n′ → P m c′ r′ m′ n′
  epop-inv P h i-epop = h
