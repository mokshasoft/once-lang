-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Coherence — plan 0.116 A1: THE MEANING IS A FUNCTION OF
-- THE JUDGMENT.
--
-- SPEC (a statement; the proof is `Once.Metatheory.Coherence`). The meaning
-- `⟦_⟧` is defined on DERIVATIONS, and a judgment `Γ ⊢[ Ψ ] t ∷ A ! π` can
-- have several: the non-syntax-directed rules (`⊢sub-use`, `⊢sub-eff`,
-- `⊢coerce`) can be placed in more than one way, and some rules hide a choice
-- the judgment does not record (the bound variable's quantity in `let`, `case`
-- and `lam`). Coherence says none of these choices is observable: any two
-- derivations of one judgment mean the same, at every target format,
-- definition meaning and environment.
--
-- It is the guard against a meaning rule that drops, repeats or reorders an
-- effect depending on such a choice (plan 0.116 §0: a `let` at quantity
-- `Zero` used to drop its effectful right-hand side, while the same judgment
-- derived at `One` ran it).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Contract using (ISig)

module Once.Spec.Core.Coherence {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Type.Grade using (Purity)
open import Once.Spec.Type using (Type)
open import Once.Target.Arch using (TargetNum)
open import Once.Spec.Context using (Ctx; Usage)
open import Once.Spec.Core.Syntax S using (Tm)
open import Once.Spec.Core.Typing S using (_⊢[_]_∷_!_)
open import Once.Spec.Core.Meaning S using (⟦_⟧; DefSem; Env)

record Coherence : Set where
  field
    coherent : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {t : Tm n} {A : Type} {π : Purity}
                 (d d′ : Γ ⊢[ Ψ ] t ∷ A ! π) (fmt : TargetNum) (δ : DefSem) (x : Env Γ Ψ)
             → ⟦ d ⟧ fmt δ x ≡ ⟦ d′ ⟧ fmt δ x
