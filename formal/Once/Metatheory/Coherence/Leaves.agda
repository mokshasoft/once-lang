{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Leaves — the leaves of the core meaning: a
-- reference to the signature, a primitive, a literal, are each the same as
-- themselves; and the small congruences the fundamental lemma and the
-- substitution lemmas share.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Coherence.Leaves (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Once.Spec.Grade
  using (Zero; One; Many; pure; act)
open import Once.Spec.Type
  using (Ty; Type; ∅ₖ; TySub; _⟨_⟩; Base; b-Unit; b-Int; b-Float; b-*; b-+; _+_)
open import Once.Spec.Signature
  using (_∶_; constant; value; operation; ⌜_⌝; ⌜_⌝ᵈ)
open import Once.Spec.Core.Syntax
open import Once.Spec.Theory using (int; float; unary; binary; compare; symDom; symCod)
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Boundary using (readAt)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; toB; fromB)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Observation Σ using (Model; module Model)
open import Once.Metatheory.Coherence.Layer Σ
open import Once.Metatheory.Coherence.Sigop Σ
open import Once.Metatheory.Coherence.Env Σ fmt S using (SlotAgree)



module _ {m : ℕ} (σ : TySub m 0) where

  sigopRefl : ∀ c t (mem : (c ∶ t) ∈ Σ) (μ₀ : Model) → Same (⌜ t ⌝ᵈ ⟨ σ ⟩) (sigopᵛ σ c t mem μ₀) (sigopᵛ σ c t mem μ₀)
  sigopRefl c (constant b) mem μ₀ = fromB-same σ b _
  sigopRefl c (value a Zero b) mem μ₀ = lamZero {π = pure} {A = ⌜ a ⌝ ⟨ σ ⟩} (relPure (fromB-same σ b _))
  sigopRefl c (value a One  b) mem μ₀ =
    lamOne {π = pure} λ {x} sa → relPure (subst (λ z → Same _ (fromB σ b (readAt fmt b (Model.valueᵐ μ₀ mem (toB σ a x)))) (fromB σ b (readAt fmt b (Model.valueᵐ μ₀ mem z))))
                                     (argEq σ a sa) (fromB-same σ b _))
  sigopRefl c (value a Many b) mem μ₀ =
    lamMany {π = pure} λ {x} sa → relPure (subst (λ z → Same _ (fromB σ b (readAt fmt b (Model.valueᵐ μ₀ mem (toB σ a x)))) (fromB σ b (readAt fmt b (Model.valueᵐ μ₀ mem z))))
                                      (argEq σ a sa) (fromB-same σ b _))
  sigopRefl c (operation a Zero b) mem μ₀ = lamZero {π = act} {A = ⌜ a ⌝ ⟨ σ ⟩} (callT′ σ mem (readAt fmt b) refl)
  sigopRefl c (operation a One  b) mem μ₀ = lamOne {π = act}  λ sa → callT′ σ mem (readAt fmt b) (argEq σ a sa)
  sigopRefl c (operation a Many b) mem μ₀ = lamMany {π = act} λ sa → callT′ σ mem (readAt fmt b) (argEq σ a sa)

  -- A symbol's types at a number type are base types.
  symBaseDom : ∀ A sh → Base ∅ₖ (symDom {m} A sh ⟨ σ ⟩)
  symBaseDom int   unary   = b-Int
  symBaseDom int   binary  = b-* b-Int b-Int
  symBaseDom int   compare = b-* b-Int b-Int
  symBaseDom float unary   = b-Float
  symBaseDom float binary  = b-* b-Float b-Float
  symBaseDom float compare = b-* b-Float b-Float

  symBaseCod : ∀ A sh → Base ∅ₖ (symCod {m} A sh ⟨ σ ⟩)
  symBaseCod int   unary   = b-Int
  symBaseCod int   binary  = b-Int
  symBaseCod int   compare = b-+ b-Unit b-Unit
  symBaseCod float unary   = b-Float
  symBaseCod float binary  = b-Float
  symBaseCod float compare = b-+ b-Unit b-Unit

  baseDom : ∀ p → Base ∅ₖ (primDom {m} p ⟨ σ ⟩)
  baseDom (num {A} {k = sh} _ _) = symBaseDom A sh
  baseDom p-i2f                  = b-Int

  baseCod : ∀ p → Base ∅ₖ (primCod {m} p ⟨ σ ⟩)
  baseCod (num {A} {k = sh} _ _) = symBaseCod A sh
  baseCod p-i2f                  = b-Float

  primSame : ∀ p {x x′} → Same (primDom p ⟨ σ ⟩) x x′ → Same (primCod p ⟨ σ ⟩) (primᵛ σ p x) (primᵛ σ p x′)
  primSame p {x} s = subst (λ z → Same _ (primᵛ σ p x) (primᵛ σ p z)) (sameBase (baseDom p) s) (reflBase (baseCod p) _)

substSame : ∀ {A B : Type} (e : A ≡ B) {x y} → Same A x y → Same B (subst ⟦_⟧ᵛ e x) (subst ⟦_⟧ᵛ e y)
substSame refl s = s

caseRel : ∀ {A B C : Type} {π π′} {l : ⟦ A ⟧ᵛ → _} {l′ r r′}
        → (∀ {a a′} → Same A a a′ → Rel π π′ C (l a) (l′ a′))
        → (∀ {b b′} → Same B b b′ → Rel π π′ C (r b) (r′ b′))
        → ∀ {w w′} → Same (A + B) w w′ → Rel π π′ C ([ l , r ]′ w) ([ l′ , r′ ]′ w′)
caseRel hl hr {inj₁ a} {inj₁ a′} s = hl s
caseRel hl hr {inj₂ b} {inj₂ b′} s = hr s
caseRel hl hr {inj₁ a} {inj₂ b′} ()
caseRel hl hr {inj₂ b} {inj₁ a′} ()

slotSame : ∀ {m} (σ : TySub m 0) (A : Ty m) q {a a′} → Same (A ⟨ σ ⟩) a a′ → SlotAgree σ A q q (slot q a) (slot q a′)
slotSame σ A Zero s = tt
slotSame σ A One  s = s
slotSame σ A Many s = s

