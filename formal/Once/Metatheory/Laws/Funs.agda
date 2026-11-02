{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Funs — the laws of `→` (`Spec.Metatheory.Equations`):
-- a call is a `let` of its argument (β, by value).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Funs (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; positionGrade; 0≤q)
open import Once.Spec.Type using (Ty; KCtx; _⟨_⟩; _⇒[_]_)
open import Once.Spec.Context using (Ctx; _▸_; _∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; _≈_; toT∞)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (_≅_; Pure)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; appZero; appOne; appMany)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S

≡→≈ : ∀ {X} {x y : T∞ X} → x ≡ y → x ≈ y
≡→≈ {x = x} refl = ≈-refl x

module _ {m : ℕ} {Δ : KCtx m} where

  app-lam : ∀ {n} {Γ : Ctx m n} {Ψ A B q π π′ t u}
            (d : Δ ⊩ Γ ⊢[ Ψ ] app (lam A q π′ t) u ∷ B ! π)
            (d′ : Δ ⊩ Γ ⊢[ Ψ ] let′ q u t ∷ B ! π) → _≅_ Σ fmt S d d′
  app-lam {Γ = Γ} {A = A} {B} {q} {π} {π′} d d′ δ sd σ r γ sγ =
    sameM {B ⟨ σ ⟩} {π} (rel (go (viewApp d base) (viewLet d′ base)))
    where
      open Views δ sd σ r γ sγ
      open FunV δ sd σ r γ sγ

      go : AppView d γ → LetView d′ γ → _~_ {B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (appView df dx rf sem) (letView de db rb semL) = goL (viewLam df rf)
        where
          goL : LamView df _ → _~_ {B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
          goL (lamView le dt {e₀} r₀ refl eqF) with ty-unique dx de
          ... | refl = fin q le dt r₀ eqF dx sem de db rb semL
            where
              fin : ∀ q₀ {q′ Ψ₀ Ψ₁ Ψ₂ Ψe Ψb π₁ π₂ πe πb ef eb} {e₀ : Env σ Γ Ψ₀}
                      (le : q′ Once.Spec.Grade.≤q q₀) (dt : Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ₀ ] _ ∷ B ! π′) → Res e₀
                  → {df : Δ ⊩ Γ ⊢[ Ψ₁ ] lam A q₀ π′ _ ∷ A ⇒[ mk-kind q₀ π′ ] B ! π₁}
                  → _~_ {A ⇒[ mk-kind q₀ π′ ] B} (⟪ df ⟫ ef) (return∞ (⟦ ⊢lam le dt ⟧ δ σ r e₀))
                  → (dx : Δ ⊩ Γ ⊢[ Ψ₂ ] _ ∷ A ! positionGrade q₀ π₂) → AppSem q₀ (⟪ d ⟫ γ) df dx ef
                  → (de : Δ ⊩ Γ ⊢[ Ψe ] _ ∷ A ! positionGrade q₀ πe) (db : Δ ⊩ (Γ ▸ A) ⊢[ q₀ ∷ Ψb ] _ ∷ B ! πb) → Res eb
                  → LetSem q₀ (⟪ d′ ⟫ γ) de db eb → _~_ {B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
              fin Zero {e₀ = e₀} 0≤q dt r₀ eqF dx sem de db rb semL =
                ~trans {B} sem
                  (~trans {B} (bindRel {f = λ fv → toT∞ π′ (fv tt)} {g = λ fv → toT∞ π′ (fv tt)} eqF (λ sf → runs (appZero {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf)))
                    (≈-Relatedˡ (idˡ (⟦ ⊢lam {q = Zero} 0≤q dt ⟧ δ σ r e₀) (λ fv → toT∞ π′ (fv tt)))
                      (~trans {B} (runs (fl▸ dt db r₀ rb tt)) (~sym {B} semL))))
              fin One {e₀ = e₀} le dt r₀ eqF dx (ex , rx , eqA) de db rb semL =
                ~trans {B} eqA
                  (~trans {B} (bindRel {f = K} {g = K} eqF
                                  (λ sf → bindRel (runs (fl dx dx rx rx)) (λ sa → runs (appOne {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sa))))
                    (≈-Relatedˡ (≈-trans (idˡ (⟦ ⊢lam le dt ⟧ δ σ r e₀) K)
                                  (≈-bind (≈-refl _) λ a → ≡→≈ (cong (toT∞ π′) (lamCall le dt e₀ a))))
                      (letEnd One dx rx dt r₀ de db rb semL)))
                where K : _ → T∞ _
                      K fv = ⟪ dx ⟫ ex >>=∞ λ a → toT∞ π′ (fv a)
              fin Many {e₀ = e₀} le dt r₀ eqF dx (ex , rx , eqA) de db rb semL =
                ~trans {B} eqA
                  (~trans {B} (bindRel {f = K} {g = K} eqF
                                  (λ sf → bindRel (runs (fl dx dx rx rx)) (λ sa → runs (appMany {π′} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sa))))
                    (≈-Relatedˡ (≈-trans (idˡ (⟦ ⊢lam le dt ⟧ δ σ r e₀) K)
                                  (≈-bind (≈-refl _) λ a → ≡→≈ (cong (toT∞ π′) (lamCall le dt e₀ a))))
                      (letEnd Many dx rx dt r₀ de db rb semL)))
                where K : _ → T∞ _
                      K fv = ⟪ dx ⟫ ex >>=∞ λ a → toT∞ π′ (fv a)
