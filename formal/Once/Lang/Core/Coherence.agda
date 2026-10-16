-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Core.Coherence — plan 0.116 A1: THE MEANING IS A FUNCTION OF
-- THE JUDGMENT.
--
-- SPEC (a statement; the proof is `Once.Metatheory.Coherence`). The meaning
-- `⟦_⟧` is defined on DERIVATIONS, and a judgment `Γ ⊢[ Ψ ] t ∷ A ! π` can
-- have several: the non-syntax-directed rules (`⊢sub-use`, `⊢sub-eff`,
-- `⊢coerce`) can be placed in more than one way, and some rules hide a choice
-- the judgment does not record (the bound variable's quantity in `let`, `case`
-- and `lam`, the type of an argument or a scrutinee). Coherence says none of
-- these choices is observable: any two derivations of one judgment mean the
-- same — no finite observation tells them apart (`Spec.Equivalence`; not `≡`,
-- since two streams built differently can behave identically) — at every
-- target format, at definitions and an environment whose values are
-- themselves well-behaved (each the same as itself — a definition whatever
-- proof of its instance's kinds is passed — : a function respects
-- sameness of its arguments — the usual premise of a logical relation; an
-- arbitrary Agda function need not, and nothing in Agda proves it does).
--
-- It is the guard against a meaning rule that drops, repeats or reorders an
-- effect depending on such a choice (plan 0.116 §0: a `let` at quantity
-- `Zero` used to drop its effectful right-hand side, while the same judgment
-- derived at `One` ran it).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Lang.Core.PolyTy using (Sig)
open import Once.Lang.Contract using (ISig)

module Once.Lang.Core.Coherence {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Once.Lang.Type.Grade using (Purity)
open import Once.Lang.Type using (Type)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Lang.Context using (Ctx; Usage)
import Once.Lang.Context as SC
open import Once.Lang.Core.PolyTy using (_!!_; _⟪_⟫; module Schema)
open import Once.Lang.Core.Syntax S using (Tm)
open import Once.Lang.Core.Typing S using (_⊢[_]_∷_!_)
open import Once.Lang.Core.Meaning S using (⟦_⟧; DefSem; defs; Env)
open import Once.Lang.Equivalence using (Same; SameM)

-- The definitions' meanings are well-behaved: each the same as itself, and
-- not depending on which proof shows its instance respects the kinds (a
-- proof is not data).
SameDefs : DefSem → Set
SameDefs δ = ∀ d τ r r′ → Same (Schema.type (S !! d) ⟪ τ ⟫) (defs δ d τ r) (defs δ d τ r′)

record Coherence : Set where
  field
    coherent : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {t : Tm n} {A : Type} {π : Purity}
                 (d d′ : Γ ⊢[ Ψ ] t ∷ A ! π) (fmt : TargetNum) (δ : DefSem) → SameDefs δ
                 → (x : Env Γ Ψ) → Same SC.⟦ Γ SC.↾ Ψ ⟧ᶜ x x
             → SameM π A (⟦ d ⟧ fmt δ x) (⟦ d′ ⟧ fmt δ x)
