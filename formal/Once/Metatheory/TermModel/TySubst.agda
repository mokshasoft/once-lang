{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.TermModel.TySubst — typing survives an instance of the
-- type variables that respects their kinds (`Spec.Metatheory.TermModel.
-- ty-subst-⊢`): a polymorphic definition is typed once.
--
-- Every rule's types are built by the type formers, which substitution
-- commutes with; functors stay well formed (a base type stays base); a
-- coercion stays a coercion; the signature's types are closed.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.TermModel.TySubst (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Once.Spec.Grade using (mk-kind; Many; pure; act)
open import Once.Spec.Type
open import Once.Spec.Type.Substitution using (base-⟨⟩; respects-∘; ⟨⟩-∘)
open import Once.Spec.Sub
open import Once.Spec.Signature using (BTy; unit; void; int; float; ⌜_⌝; ⌜_⌝ᵈ; DeclType; constant; value; operation)
import Once.Spec.Signature as BT
open import Once.Spec.Context using (Ctx; ∅; _▸_; lookup; _⟨_⟩ᶜ)
open import Once.Spec.Core.Syntax
open import Once.Spec.Theory using (int; float; unary; binary; compare; symDom; symCod)
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.Types using (<:-refl)

module _ {m k : ℕ} (σ : TySub m k) where

  lookup-⟨⟩ : ∀ {n} (Γ : Ctx m n) (i : Fin n) → lookup (Γ ⟨ σ ⟩ᶜ) i ≡ lookup Γ i ⟨ σ ⟩
  lookup-⟨⟩ (Γ ▸ A) zero    = refl
  lookup-⟨⟩ (Γ ▸ A) (suc i) = lookup-⟨⟩ Γ i

  ⟦⟧F-⟨⟩ : ∀ (F : Fun m) (A : Ty m) → (⟦ F ⟧F A) ⟨ σ ⟩ ≡ ⟦ F ⟨ σ ⟩F ⟧F (A ⟨ σ ⟩)
  ⟦⟧F-⟨⟩ (K B)   A = refl
  ⟦⟧F-⟨⟩ Id      A = refl
  ⟦⟧F-⟨⟩ (F ⊕ G) A = cong₂ _+_ (⟦⟧F-⟨⟩ F A) (⟦⟧F-⟨⟩ G A)
  ⟦⟧F-⟨⟩ (F ⊗ G) A = cong₂ _*_ (⟦⟧F-⟨⟩ F A) (⟦⟧F-⟨⟩ G A)

  <:-⟨⟩ : ∀ {A B : Ty m} → A <: B → A ⟨ σ ⟩ <: B ⟨ σ ⟩
  <:-⟨⟩ sub-void        = sub-void
  <:-⟨⟩ (sub-var {i})   = <:-refl (σ i)
  <:-⟨⟩ sub-unit        = sub-unit
  <:-⟨⟩ sub-int         = sub-int
  <:-⟨⟩ sub-float       = sub-float
  <:-⟨⟩ (sub-arr a b g) = sub-arr (<:-⟨⟩ a) (<:-⟨⟩ b) g
  <:-⟨⟩ (sub-* a b)     = sub-* (<:-⟨⟩ a) (<:-⟨⟩ b)
  <:-⟨⟩ (sub-+ a b)     = sub-+ (<:-⟨⟩ a) (<:-⟨⟩ b)
  <:-⟨⟩ sub-μ           = sub-μ
  <:-⟨⟩ (sub-ν g)       = sub-ν g

  ⌜⌝-⟨⟩ : ∀ b → ⌜ b ⌝ ⟨ σ ⟩ ≡ ⌜ b ⌝
  ⌜⌝-⟨⟩ unit  = refl
  ⌜⌝-⟨⟩ void  = refl
  ⌜⌝-⟨⟩ int   = refl
  ⌜⌝-⟨⟩ float = refl
  ⌜⌝-⟨⟩ (a BT.* b) = cong₂ _*_ (⌜⌝-⟨⟩ a) (⌜⌝-⟨⟩ b)
  ⌜⌝-⟨⟩ (a BT.+ b) = cong₂ _+_ (⌜⌝-⟨⟩ a) (⌜⌝-⟨⟩ b)

  ⌜⌝ᵈ-⟨⟩ : ∀ t → ⌜ t ⌝ᵈ ⟨ σ ⟩ ≡ ⌜ t ⌝ᵈ
  ⌜⌝ᵈ-⟨⟩ (constant b)   = ⌜⌝-⟨⟩ b
  ⌜⌝ᵈ-⟨⟩ (value a q b)     = cong₂ (λ x y → x ⇒[ mk-kind q pure ] y) (⌜⌝-⟨⟩ a) (⌜⌝-⟨⟩ b)
  ⌜⌝ᵈ-⟨⟩ (operation a q b) = cong₂ (λ x y → x ⇒[ mk-kind q act ] y) (⌜⌝-⟨⟩ a) (⌜⌝-⟨⟩ b)

  -- A symbol's type at a number type has no variables.
  symDom-⟨⟩ : ∀ A sh → symDom {m} A sh ⟨ σ ⟩ ≡ symDom {k} A sh
  symDom-⟨⟩ int   unary   = refl
  symDom-⟨⟩ int   binary  = refl
  symDom-⟨⟩ int   compare = refl
  symDom-⟨⟩ float unary   = refl
  symDom-⟨⟩ float binary  = refl
  symDom-⟨⟩ float compare = refl

  symCod-⟨⟩ : ∀ A sh → symCod {m} A sh ⟨ σ ⟩ ≡ symCod {k} A sh
  symCod-⟨⟩ int   unary   = refl
  symCod-⟨⟩ int   binary  = refl
  symCod-⟨⟩ int   compare = refl
  symCod-⟨⟩ float unary   = refl
  symCod-⟨⟩ float binary  = refl
  symCod-⟨⟩ float compare = refl

  primDom-⟨⟩ : ∀ p → primDom {m} p ⟨ σ ⟩ ≡ primDom {k} p
  primDom-⟨⟩ (num {A} {k = sh} _ _) = symDom-⟨⟩ A sh
  primDom-⟨⟩ p-i2f                  = refl

  primCod-⟨⟩ : ∀ p → primCod {m} p ⟨ σ ⟩ ≡ primCod {k} p
  primCod-⟨⟩ (num {A} {k = sh} _ _) = symCod-⟨⟩ A sh
  primCod-⟨⟩ p-i2f                  = refl

  module _ {Δ : KCtx m} {Δ′ : KCtx k} (rσ : Respects Δ Δ′ σ) where

    wf-⟨⟩ : ∀ {F} → WFFun Δ F → WFFun Δ′ (F ⟨ σ ⟩F)
    wf-⟨⟩ (wf-K b)   = wf-K (base-⟨⟩ rσ b)
    wf-⟨⟩ wf-Id      = wf-Id
    wf-⟨⟩ (wf-⊕ f g) = wf-⊕ (wf-⟨⟩ f) (wf-⟨⟩ g)
    wf-⟨⟩ (wf-⊗ f g) = wf-⊗ (wf-⟨⟩ f) (wf-⟨⟩ g)

    -- The type a rule computes, moved to the one stated (public, so the
    -- substitution's transports can be reasoned about).
    retypeᵗ : ∀ {n} {Γ : Ctx k n} {Ψ t A A′ π} → A ≡ A′ → Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ A′ ! π
    retypeᵗ refl d = d

    ty-subst-⊢ : ∀ {n} {Γ : Ctx m n} {Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] t ⟪ σ ⟫ₜ ∷ A ⟨ σ ⟩ ! π
    ty-subst-⊢ {Γ = Γ} (⊢var i) = retypeᵗ (lookup-⟨⟩ Γ i) (⊢var i)
    ty-subst-⊢ (⊢lam le d) = ⊢lam le (ty-subst-⊢ d)
    ty-subst-⊢ (⊢app df dx) = ⊢app (ty-subst-⊢ df) (ty-subst-⊢ dx)
    ty-subst-⊢ (⊢let d₁ d₂) = ⊢let (ty-subst-⊢ d₁) (ty-subst-⊢ d₂)
    ty-subst-⊢ ⊢unit = ⊢unit
    ty-subst-⊢ (⊢pair da db) = ⊢pair (ty-subst-⊢ da) (ty-subst-⊢ db)
    ty-subst-⊢ (⊢fst d) = ⊢fst (ty-subst-⊢ d)
    ty-subst-⊢ (⊢snd d) = ⊢snd (ty-subst-⊢ d)
    ty-subst-⊢ (⊢inl d) = ⊢inl (ty-subst-⊢ d)
    ty-subst-⊢ (⊢inr d) = ⊢inr (ty-subst-⊢ d)
    ty-subst-⊢ (⊢case ds dl dr) = ⊢case (ty-subst-⊢ ds) (ty-subst-⊢ dl) (ty-subst-⊢ dr)
    ty-subst-⊢ (⊢absurd d) = ⊢absurd (ty-subst-⊢ d)
    ty-subst-⊢ (⊢roll {F = F} wf d) =
      ⊢roll (wf-⟨⟩ wf) (retypeᵗ (⟦⟧F-⟨⟩ F (μ F)) (ty-subst-⊢ d))
    ty-subst-⊢ (⊢fold {F = F} {A} wf da dt) =
      ⊢fold (wf-⟨⟩ wf) (retypeᵗ (cong (λ X → X ⇒[ mk-kind Many _ ] A ⟨ σ ⟩) (⟦⟧F-⟨⟩ F A)) (ty-subst-⊢ da)) (ty-subst-⊢ dt)
    ty-subst-⊢ (⊢unfold {F = F} {A} wf dc da) =
      ⊢unfold (wf-⟨⟩ wf) (retypeᵗ (cong (λ X → A ⟨ σ ⟩ ⇒[ mk-kind Many _ ] X) (⟦⟧F-⟨⟩ F A)) (ty-subst-⊢ dc)) (ty-subst-⊢ da)
    ty-subst-⊢ (⊢out {f = f} {F = F} wf d) =
      retypeᵗ (sym (⟦⟧F-⟨⟩ F (ν F f))) (⊢out (wf-⟨⟩ wf) (ty-subst-⊢ d))
    ty-subst-⊢ (⊢iter df ds) = ⊢iter (ty-subst-⊢ df) (ty-subst-⊢ ds)
    ty-subst-⊢ (⊢coerce p d) = ⊢coerce (<:-⟨⟩ p) (ty-subst-⊢ d)
    ty-subst-⊢ ⊢lit-int = ⊢lit-int
    ty-subst-⊢ ⊢lit-float = ⊢lit-float
    ty-subst-⊢ (⊢prim p d) = retypeᵗ (sym (primCod-⟨⟩ p)) (⊢prim p (retypeᵗ (primDom-⟨⟩ p) (ty-subst-⊢ d)))
    ty-subst-⊢ (⊢sigop {t = t} mem) = retypeᵗ (sym (⌜⌝ᵈ-⟨⟩ t)) (⊢sigop mem)
    ty-subst-⊢ (⊢ref d τ rd) =
      retypeᵗ (sym (⟨⟩-∘ (type (S !! d)) τ σ)) (⊢ref d (λ i → τ i ⟨ σ ⟩) (respects-∘ rd rσ))
    ty-subst-⊢ (⊢sub-use p d) = ⊢sub-use p (ty-subst-⊢ d)
    ty-subst-⊢ (⊢sub-eff g d) = ⊢sub-eff g (ty-subst-⊢ d)
