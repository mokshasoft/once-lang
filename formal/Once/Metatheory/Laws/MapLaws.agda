{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapLaws — the semantic map (`Laws.MapSem`) respects
-- sameness: the same functions, applied to the same values, give the same
-- values.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Laws.MapLaws (Σ : Signature) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)
open import Once.Spec.Grade using (Zero; One; Many; mk-kind; fin)
open import Once.Spec.Type using (Ty; Type; Fun; KCtx; Base; ∅ₖ; Respects; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν;
                                  K; Id; _⊕_; _⊗_; TySub; _⟨_⟩; _⟨_⟩F; at₀; Occurs; OccursF; o-var; o-*ˡ; o-*ʳ; o-+ˡ; o-+ʳ; o-⇒ʳ; o-μ; o-ν; o-K; o-⊕ˡ; o-⊕ʳ; o-⊗ˡ; o-⊗ʳ)
open import Once.Spec.Type.Substitution using (base-⟨⟩)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF; μS; inS)
open import Once.Spec.Effect Σ using (M; fmap; νM; ana; LayerEq)
open νM using (outν)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)
open import Once.Spec.Equivalence Σ using (Same; SameM)
open import Once.Metatheory.Erase Σ using (toT∞-fmap)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (sameBase; reflBase; relatedFmap; LayerEq-∀; outRel; module Ana)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt)

module MapResp {m : ℕ} {Δ : KCtx m} (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) (A B : Ty m) where
  open MapAt Δ σ A B

  -- Two functions that take the same arguments to the same results.
  SameFn : ∀ {P : Set} → (P → ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ B ⟨ σ ⟩ ⟧ᵛ) → (P → ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ B ⟨ σ ⟩ ⟧ᵛ) → Set
  SameFn {P} φ φ′ = ∀ (o : P) a a′ → Same (A ⟨ σ ⟩) a a′ → Same (B ⟨ σ ⟩) (φ o a) (φ′ o a′)

  private
    -- An argument read at the domain the map was written at.
    substSame : ∀ {X Y : Ty m} (e e′ : X ≡ Y) {y y′ : ⟦ Y ⟨ σ ⟩ ⟧ᵛ} → Same (Y ⟨ σ ⟩) y y′
              → Same (X ⟨ σ ⟩) (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y) (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e′) y′)
    substSame refl refl s = s

    -- Base values: the same exactly when equal.
    baseEq : ∀ {C : Ty (suc m)} (b : Base Δ (C ⟨ at₀ B ⟩)) {y y′ : ⟦ C ⟨ at₀ B ⟩ ⟨ σ ⟩ ⟧ᵛ} → Same _ y y′ → y ≡ y′
    baseEq b = sameBase (base-⟨⟩ r b)

  mutual
    resp : ∀ T (c c′ : Cov T) {φ φ′ : Fn T} → SameFn φ φ′
         → ∀ {x x′} → Same (T ⟨ at₀ A ⟩ ⟨ σ ⟩) x x′ → Same (T ⟨ at₀ B ⟩ ⟨ σ ⟩) (mapS T c φ x) (mapS T c′ φ′ x′)
    resp (var zero)    c c′ h s = h o-var _ _ s
    resp (var (suc i)) c c′ h s = s
    resp Unit          c c′ h s = s
    resp Void          c c′ h s = s
    resp Int           c c′ h s = s
    resp Float         c c′ h s = s
    resp (T₁ * T₂) (c₁ , c₂) (c₁′ , c₂′) h {x₁ , x₂} {y₁ , y₂} (s₁ , s₂) =
      resp T₁ c₁ c₁′ (λ o → h (o-*ˡ o)) s₁ , resp T₂ c₂ c₂′ (λ o → h (o-*ʳ o)) s₂
    resp (T₁ + T₂) (c₁ , c₂) (c₁′ , c₂′) h {inj₁ x} {inj₁ y} s = resp T₁ c₁ c₁′ (λ o → h (o-+ˡ o)) s
    resp (T₁ + T₂) (c₁ , c₂) (c₁′ , c₂′) h {inj₂ x} {inj₂ y} s = resp T₂ c₂ c₂′ (λ o → h (o-+ʳ o)) s
    resp (T₁ + T₂) c c′ h {inj₁ x} {inj₂ y} ()
    resp (T₁ + T₂) c c′ h {inj₂ x} {inj₁ y} ()
    resp (T₁ ⇒[ mk-kind Zero π ] T₂) (e , c) (e′ , c′) h {g} {g′} s = toObserved
      (≈-Relatedˡ (toT∞-fmap π _ (g _)) (≈-Relatedʳ (toT∞-fmap π _ (g′ _))
        (relatedFmap (fromObserved s) (resp T₂ c c′ (λ o → h (o-⇒ʳ o))))))
    resp (T₁ ⇒[ mk-kind One π ] T₂) (e , c) (e′ , c′) h {g} {g′} s y y′ sy = toObserved
      (≈-Relatedˡ (toT∞-fmap π _ (g _)) (≈-Relatedʳ (toT∞-fmap π _ (g′ _))
        (relatedFmap (fromObserved (s _ _ (substSame e e′ sy))) (resp T₂ c c′ (λ o → h (o-⇒ʳ o))))))
    resp (T₁ ⇒[ mk-kind Many π ] T₂) (e , c) (e′ , c′) h {g} {g′} s y y′ sy = toObserved
      (≈-Relatedˡ (toT∞-fmap π _ (g _)) (≈-Relatedʳ (toT∞-fmap π _ (g′ _))
        (relatedFmap (fromObserved (s _ _ (substSame e e′ sy))) (resp T₂ c c′ (λ o → h (o-⇒ʳ o))))))
    resp (μ G) c c′ h {x} refl = muResp G c c′ (λ o → h (o-μ o)) x
    resp (ν G f) c c′ h {x} {x′} s n = Ana.anaRel f (CB G) ((ν (G ⟨ at₀ A ⟩F) f) ⟨ σ ⟩) _ _ coalg n s
      where
        coalg : ∀ {a a′} → Same ((ν (G ⟨ at₀ A ⟩F) f) ⟨ σ ⟩) a a′
              → Related (LayerEq (CB G) (Same ((ν (G ⟨ at₀ A ⟩F) f) ⟨ σ ⟩))) _ _
        coalg {a} {a′} sa =
          ≈-Relatedˡ (toT∞-fmap (fin f) _ (outν a)) (≈-Relatedʳ (toT∞-fmap (fin f) _ (outν a′))
            (relatedFmap (outRel f (CA G) sa)
              (λ p → nuResp G c c′ (λ o → h (o-ν o)) (LayerEq-∀ (CA G) p))))

    muResp : ∀ G (c c′ : CovF G) {φ φ′ : FnF G} → SameFn φ φ′ → ∀ x → muMap G c φ x ≡ muMap G c′ φ′ x
    muResp G c c′ h (inS l) = cong inS (muLayerResp G G c c′ h c c′ h l)

    muLayerResp : ∀ G H (cG cG′ : CovF G) {φG φG′ : FnF G} → SameFn φG φG′
                → (cH cH′ : CovF H) {φ φ′ : FnF H} → SameFn φ φ′
                → ∀ l → muLayer G H cG φG cH φ l ≡ muLayer G H cG′ φG′ cH′ φ′ l
    muLayerResp G (K C) cG cG′ hG (cC , bA , bB) (cC′ , _ , _) h l =
      baseEq {C = C} bB (resp C cC cC′ (λ o → h (o-K o)) (reflBase (base-⟨⟩ r bA) l))
    muLayerResp G Id cG cG′ hG cH cH′ h l = muResp G cG cG′ hG l
    muLayerResp G (H₁ ⊕ H₂) cG cG′ hG (c₁ , c₂) (c₁′ , c₂′) h (inj₁ l) =
      cong inj₁ (muLayerResp G H₁ cG cG′ hG c₁ c₁′ (λ o → h (o-⊕ˡ o)) l)
    muLayerResp G (H₁ ⊕ H₂) cG cG′ hG (c₁ , c₂) (c₁′ , c₂′) h (inj₂ l) =
      cong inj₂ (muLayerResp G H₂ cG cG′ hG c₂ c₂′ (λ o → h (o-⊕ʳ o)) l)
    muLayerResp G (H₁ ⊗ H₂) cG cG′ hG (c₁ , c₂) (c₁′ , c₂′) h (l₁ , l₂) =
      cong₂ _,_ (muLayerResp G H₁ cG cG′ hG c₁ c₁′ (λ o → h (o-⊗ˡ o)) l₁) (muLayerResp G H₂ cG cG′ hG c₂ c₂′ (λ o → h (o-⊗ʳ o)) l₂)

    nuResp : ∀ H (c c′ : CovF H) {φ φ′ : FnF H} → SameFn φ φ′
           → ∀ {X} {R : X → X → Set} {l l′} → LayerEq (CA H) R l l′ → LayerEq (CB H) R (nuLayer H c φ l) (nuLayer H c′ φ′ l′)
    nuResp (K C) (cC , bA , bB) (cC′ , _ , _) h {l = l} refl =
      baseEq {C = C} bB (resp C cC cC′ (λ o → h (o-K o)) (reflBase (base-⟨⟩ r bA) l))
    nuResp Id c c′ h p = p
    nuResp (H₁ ⊕ H₂) (c₁ , c₂) (c₁′ , c₂′) h {l = inj₁ x} {inj₁ y} p = nuResp H₁ c₁ c₁′ (λ o → h (o-⊕ˡ o)) p
    nuResp (H₁ ⊕ H₂) (c₁ , c₂) (c₁′ , c₂′) h {l = inj₂ x} {inj₂ y} p = nuResp H₂ c₂ c₂′ (λ o → h (o-⊕ʳ o)) p
    nuResp (H₁ ⊕ H₂) c c′ h {l = inj₁ x} {inj₂ y} ()
    nuResp (H₁ ⊕ H₂) c c′ h {l = inj₂ x} {inj₁ y} ()
    nuResp (H₁ ⊗ H₂) (c₁ , c₂) (c₁′ , c₂′) h (p₁ , p₂) = nuResp H₁ c₁ c₁′ (λ o → h (o-⊗ˡ o)) p₁ , nuResp H₂ c₂ c₂′ (λ o → h (o-⊗ʳ o)) p₂
