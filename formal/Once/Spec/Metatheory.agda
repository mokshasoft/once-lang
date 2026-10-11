-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Metatheory — WHAT THE LANGUAGE PROMISES ABOUT ITSELF (D304).
--
-- A metatheorem is a claim about the Spec ALONE: it mentions no compiler. If
-- one cannot be proved, the LANGUAGE is wrong, not the compiler — D276 made
-- the grades affine precisely so that substitution is typed. So the
-- statements are part of the Spec, read with the definition they constrain;
-- the proofs are not (D140): they live under `Once.Metatheory`, which may
-- import only the Spec and its semantic domain, never the compiler
-- (`scripts/metatheory-gate.sh`). `Once.Certified` carries the proofs, so
-- each statement is on the apex and goes red when the Spec moves.
--
-- Two parts:
--   * `term-model` — for every signature of definitions `S`, the core's TERM
--     MODEL (`Once.Spec.Core.TermModel`): substitution of terms is typed
--     (`subst-⊢`), a pure `let` means its substitution (`let-β`, referential
--     transparency), and substitution of types is typed (`ty-subst-⊢`, D303).
--   * `type-system` — the surface typing judgment (D305): subtyping and the
--     purity order are partial orders whose derivations are unique (so a
--     coercion has one meaning), and a term's usage is a property of the term,
--     not of the mode that typed it — synthesis is unique, checking agrees
--     with it, the domain-given mode is exact.
--
-- No type-safety theorem is needed in this setting: the meaning is a TOTAL
-- function on derivations, so every well-typed program means something by
-- construction.
------------------------------------------------------------------------

module Once.Spec.Metatheory where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Contract using (ISig)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Core.TermModel using (TermModel) public
open import Once.Spec.Type.Grade using (Purity; mk-kind; Many)
open import Once.Spec.Type using (Type; _⇒[_]_)
open import Once.Spec.Type.Sub using (_<:_; _⊑π_)
open import Once.Spec.Syntax using (RawExpr)
open import Once.Spec.Typing.Scope using (NamedCtx)
open import Once.Spec.Typing using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_; _⊢ᵈ_∶_⇒[_]↦_⨾_)
import Once.Spec.Context as Surface

-- The surface typing judgment's laws (D305).
record TypeSystem : Set where
  field
    -- subtyping is a preorder with unique derivations (D226: one judgment)
    <:-refl   : ∀ A → A <: A
    <:-trans  : ∀ {A B C} → A <: B → B <: C → A <: C
    <:-unique : ∀ {A B} (p q : A <: B) → p ≡ q
    -- …and so is the purity order
    ⊑π-refl   : ∀ π → π ⊑π π
    ⊑π-trans  : ∀ {π₁ π₂ π₃} → π₁ ⊑π π₂ → π₂ ⊑π π₃ → π₁ ⊑π π₃
    ⊑π-unique : ∀ {π π′} (g h : π ⊑π π′) → g ≡ h

    -- synthesis is unique
    synth-unique : ∀ {ctx : NamedCtx} {e : RawExpr} {A A′ : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                 → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′ → A ≡ A′ × Ψ ≡ Ψ′
    -- checking at one type gives one usage
    check-usage-unique : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                       → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ A ⨾ Ψ′ → Ψ ≡ Ψ′
    -- checking agrees with synthesis on usage
    check-agrees-synth : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                       → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ′ → Ψ ≡ Ψ′
    -- the domain-given mode agrees with checking at an arrow from its domain
    domain-agrees-check : ∀ {ctx : NamedCtx} {e : RawExpr} {A B B′ : Type} {π : Purity}
                            {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᶜ e ∶ (A ⇒[ mk-kind Many π ] B′) ⨾ Ψ′ → Ψ ≡ Ψ′
    -- a term that synthesizes is domain-given only through its synthesized arrow
    domain-agrees-synth : ∀ {ctx : NamedCtx} {e : RawExpr} {A B S : Type} {π : Purity}
                            {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᵢ e ∶ S ⨾ Ψ′
                        → Σ[ A′ ∈ Type ] Σ[ π′ ∈ Purity ] (S ≡ (A′ ⇒[ mk-kind Many π′ ] B)) × π′ ⊑π π × Ψ ≡ Ψ′
    -- the domain-given mode is exact: its output is determined by its input
    domain-exact : ∀ {ctx : NamedCtx} {e : RawExpr} {A B B′ : Type} {π : Purity}
                     {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                 → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B′ ⨾ Ψ′ → B ≡ B′ × Ψ ≡ Ψ′

record Metatheory : Set where
  field
    term-model  : ∀ {Fs : ISig} {s : ℕ} (S : Sig Fs s) → TermModel S
    type-system : TypeSystem
