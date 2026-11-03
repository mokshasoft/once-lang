{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapLaws — the semantic map (`Laws.MapSem`) respects
-- sameness: the same functions, applied to the same values, give the same
-- values (`resp`); mapped by the identity, a value stays the same (`mid`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Laws.MapLaws (Σ : Signature) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)
open import Once.Spec.Grade using (Purity; Zero; One; Many; mk-kind; fin)
open import Once.Spec.Type using (Ty; Type; Fun; KCtx; Base; ∅ₖ; Respects; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν;
                                  K; Id; _⊕_; _⊗_; TySub; _⟨_⟩; _⟨_⟩F; at₀; Occurs; OccursF; o-var; o-*ˡ; o-*ʳ; o-+ˡ; o-+ʳ; o-⇒ʳ; o-μ; o-ν; o-K; o-⊕ˡ; o-⊕ʳ; o-⊗ˡ; o-⊗ʳ)
open import Once.Spec.Type.Substitution using (base-⟨⟩)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF; μS; inS)
open import Once.Spec.Effect Σ using (M; fmap; νM; ana; LayerEq; T∞; _>>=∞_; return∞; _≈_; toT∞)
open νM using (outν)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)
open import Once.Spec.Equivalence Σ using (Same; SameM; SameNu)
open import Once.Spec.Polynomial using (sfmap)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ; assoc)
open import Once.Metatheory.Unfold Σ using (module Unfold)
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
    resp (var fz)      c c′ h s = h o-var _ _ s
    resp (var (fs i))  c c′ h s = s
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

-- Two maps in a row are one bind.
fmap² : ∀ π {X Y Z : Set} (f : Y → Z) (g : X → Y) (m : M π X)
      → toT∞ π (fmap π f (fmap π g m)) ≈ (toT∞ π m >>=∞ λ x → return∞ (f (g x)))
fmap² π f g m = ≈-trans (toT∞-fmap π f (fmap π g m))
  (≈-trans (≈-bind (toT∞-fmap π g m) (λ _ → ≈-refl _)) (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ x → idˡ (g x) _))))

module MapId {m : ℕ} {Δ : KCtx m} (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) (A : Ty m) where
  open MapAt Δ σ A A

  -- A function that takes each argument to the same one.
  IsId : ∀ {P : Set} → (P → ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ A ⟨ σ ⟩ ⟧ᵛ) → Set
  IsId {P} φ = ∀ (o : P) a a′ → Same (A ⟨ σ ⟩) a a′ → Same (A ⟨ σ ⟩) (φ o a) a′

  private
    substId : ∀ {X : Ty m} (e : X ≡ X) {y y′ : ⟦ X ⟨ σ ⟩ ⟧ᵛ} → Same (X ⟨ σ ⟩) y y′
            → Same (X ⟨ σ ⟩) (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y) y′
    substId refl s = s

    funId : ∀ π {X : Type} {f : ⟦ X ⟧ᵛ → ⟦ X ⟧ᵛ} {u u′ : M π ⟦ X ⟧ᵛ}
          → (∀ {a a′} → Same X a a′ → Same X (f a) a′) → SameM π X u u′ → SameM π X (fmap π f u) u′
    funId π {u = u} {u′} h s = toObserved
      (≈-Relatedˡ (toT∞-fmap π _ u) (≈-Relatedʳ (≈-sym (idʳ (toT∞ π u′))) (relatedFmap (fromObserved s) h)))

  mutual
    mid : ∀ T (c : Cov T) {φ : Fn T} → IsId φ
        → ∀ {x x′} → Same (T ⟨ at₀ A ⟩ ⟨ σ ⟩) x x′ → Same (T ⟨ at₀ A ⟩ ⟨ σ ⟩) (mapS T c φ x) x′
    mid (var fz)      c h s = h o-var _ _ s
    mid (var (fs i))  c h s = s
    mid Unit          c h s = s
    mid Void          c h s = s
    mid Int           c h s = s
    mid Float         c h s = s
    mid (T₁ * T₂) (c₁ , c₂) h {x₁ , x₂} {y₁ , y₂} (s₁ , s₂) =
      mid T₁ c₁ (λ o → h (o-*ˡ o)) s₁ , mid T₂ c₂ (λ o → h (o-*ʳ o)) s₂
    mid (T₁ + T₂) (c₁ , c₂) h {inj₁ x} {inj₁ y} s = mid T₁ c₁ (λ o → h (o-+ˡ o)) s
    mid (T₁ + T₂) (c₁ , c₂) h {inj₂ x} {inj₂ y} s = mid T₂ c₂ (λ o → h (o-+ʳ o)) s
    mid (T₁ + T₂) c h {inj₁ x} {inj₂ y} ()
    mid (T₁ + T₂) c h {inj₂ x} {inj₁ y} ()
    mid (T₁ ⇒[ mk-kind Zero π ] T₂) (e , c) h s = funId π (mid T₂ c (λ o → h (o-⇒ʳ o))) s
    mid (T₁ ⇒[ mk-kind One π ] T₂) (e , c) h s y y′ sy = funId π (mid T₂ c (λ o → h (o-⇒ʳ o))) (s _ _ (substId e sy))
    mid (T₁ ⇒[ mk-kind Many π ] T₂) (e , c) h s y y′ sy = funId π (mid T₂ c (λ o → h (o-⇒ʳ o))) (s _ _ (substId e sy))
    mid (μ G) c h {x} refl = muId G c (λ o → h (o-μ o)) x
    mid (ν G f) c h s n = nuId G f c (λ o → h (o-ν o)) n s

    muId : ∀ G (c : CovF G) {φ : FnF G} → IsId φ → ∀ x → muMap G c φ x ≡ x
    muId G c h (inS l) = cong inS (muLayerId G G c h c h l)

    muLayerId : ∀ G H (cG : CovF G) {φG : FnF G} → IsId φG → (cH : CovF H) {φ : FnF H} → IsId φ
              → ∀ l → muLayer G H cG φG cH φ l ≡ l
    muLayerId G (K C) cG hG (cC , bA , _) h l =
      sameBase (base-⟨⟩ r bA) (mid C cC (λ o → h (o-K o)) (reflBase (base-⟨⟩ r bA) l))
    muLayerId G Id cG hG cH h l = muId G cG hG l
    muLayerId G (H₁ ⊕ H₂) cG hG (c₁ , c₂) h (inj₁ l) = cong inj₁ (muLayerId G H₁ cG hG c₁ (λ o → h (o-⊕ˡ o)) l)
    muLayerId G (H₁ ⊕ H₂) cG hG (c₁ , c₂) h (inj₂ l) = cong inj₂ (muLayerId G H₂ cG hG c₂ (λ o → h (o-⊕ʳ o)) l)
    muLayerId G (H₁ ⊗ H₂) cG hG (c₁ , c₂) h (l₁ , l₂) =
      cong₂ _,_ (muLayerId G H₁ cG hG c₁ (λ o → h (o-⊗ˡ o)) l₁) (muLayerId G H₂ cG hG c₂ (λ o → h (o-⊗ʳ o)) l₂)

    -- ν: at every depth, by the layers.
    nuId : ∀ G f (c : CovF G) {φ : FnF G} → IsId φ → ∀ n {a a′} → Same ((ν (G ⟨ at₀ A ⟩F) f) ⟨ σ ⟩) a a′
         → SameNu f (CA G) n (ana f (CA G) (λ y → fmap (fin f) (nuLayer G c φ {νM f (CA G)}) (outν y)) a) a′
    nuId G f c h zero    s = tt
    nuId G f c {φ} h (suc n) {a} {a′} s = toObserved
      (≈-Relatedˡ (≈-trans (Unfold.unfold-out≈ (CA G) f k a) (fmap² (fin f) _ _ (outν a)))
        (≈-Relatedʳ (≈-sym (idʳ (toT∞ (fin f) (outν a′))))
          (relatedFmap (outRel f (CA G) s) (λ p → nuLayerId G f c h G c h n (LayerEq-∀ (CA G) p)))))
      where k = λ y → fmap (fin f) (nuLayer G c φ {νM f (CA G)}) (outν y)

    nuLayerId : ∀ G f (cG : CovF G) {φG : FnF G} → IsId φG → ∀ H (cH : CovF H) {φ : FnF H} → IsId φ → ∀ n {l l′}
              → LayerEq (CA H) (Same ((ν (G ⟨ at₀ A ⟩F) f) ⟨ σ ⟩)) l l′
              → LayerEq (CA H) (SameNu f (CA G) n)
                  (sfmap (CA H) (ana f (CA G) (λ y → fmap (fin f) (nuLayer G cG φG {νM f (CA G)}) (outν y))) (nuLayer H cH φ l)) l′
    nuLayerId G f cG hG (K C) (cC , bA , _) h n {l} refl =
      sameBase (base-⟨⟩ r bA) (mid C cC (λ o → h (o-K o)) (reflBase (base-⟨⟩ r bA) l))
    nuLayerId G f cG hG Id cH h n p = nuId G f cG hG n p
    nuLayerId G f cG hG (H₁ ⊕ H₂) (c₁ , c₂) h n {inj₁ x} {inj₁ y} p = nuLayerId G f cG hG H₁ c₁ (λ o → h (o-⊕ˡ o)) n p
    nuLayerId G f cG hG (H₁ ⊕ H₂) (c₁ , c₂) h n {inj₂ x} {inj₂ y} p = nuLayerId G f cG hG H₂ c₂ (λ o → h (o-⊕ʳ o)) n p
    nuLayerId G f cG hG (H₁ ⊕ H₂) c h n {inj₁ x} {inj₂ y} ()
    nuLayerId G f cG hG (H₁ ⊕ H₂) c h n {inj₂ x} {inj₁ y} ()
    nuLayerId G f cG hG (H₁ ⊗ H₂) (c₁ , c₂) h n (p₁ , p₂) =
      nuLayerId G f cG hG H₁ c₁ (λ o → h (o-⊗ˡ o)) n p₁ , nuLayerId G f cG hG H₂ c₂ (λ o → h (o-⊗ʳ o)) n p₂
