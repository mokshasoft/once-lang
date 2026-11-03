{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapLaws — the semantic map (`Laws.MapSem`) respects
-- sameness: the same functions, applied to the same values, give the same
-- values (`resp`); mapped by the identity, a value stays the same (`mid`);
-- mapped by a composite, it is mapped by each part in turn (`comp`).
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
                                  K; Id; _⊕_; _⊗_; TySub; _⟨_⟩; _⟨_⟩F; at₀)
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
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt; Occ; OccF; p-var; p-*ˡ; p-*ʳ; p-+ˡ; p-+ʳ; p-⇒ʳ; p-μ; p-ν; p-K; p-⊕ˡ; p-⊕ʳ; p-⊗ˡ; p-⊗ʳ)

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
    resp (var fz)      c c′ h s = h p-var _ _ s
    resp (var (fs i))  c c′ h s = s
    resp Unit          c c′ h s = s
    resp Void          c c′ h s = s
    resp Int           c c′ h s = s
    resp Float         c c′ h s = s
    resp (T₁ * T₂) (c₁ , c₂) (c₁′ , c₂′) h {x₁ , x₂} {y₁ , y₂} (s₁ , s₂) =
      resp T₁ c₁ c₁′ (λ o → h (p-*ˡ o)) s₁ , resp T₂ c₂ c₂′ (λ o → h (p-*ʳ o)) s₂
    resp (T₁ + T₂) (c₁ , c₂) (c₁′ , c₂′) h {inj₁ x} {inj₁ y} s = resp T₁ c₁ c₁′ (λ o → h (p-+ˡ o)) s
    resp (T₁ + T₂) (c₁ , c₂) (c₁′ , c₂′) h {inj₂ x} {inj₂ y} s = resp T₂ c₂ c₂′ (λ o → h (p-+ʳ o)) s
    resp (T₁ + T₂) c c′ h {inj₁ x} {inj₂ y} ()
    resp (T₁ + T₂) c c′ h {inj₂ x} {inj₁ y} ()
    resp (T₁ ⇒[ mk-kind Zero π ] T₂) (e , c) (e′ , c′) h {g} {g′} s = toObserved
      (≈-Relatedˡ (toT∞-fmap π _ (g _)) (≈-Relatedʳ (toT∞-fmap π _ (g′ _))
        (relatedFmap (fromObserved s) (resp T₂ c c′ (λ o → h (p-⇒ʳ o))))))
    resp (T₁ ⇒[ mk-kind One π ] T₂) (e , c) (e′ , c′) h {g} {g′} s y y′ sy = toObserved
      (≈-Relatedˡ (toT∞-fmap π _ (g _)) (≈-Relatedʳ (toT∞-fmap π _ (g′ _))
        (relatedFmap (fromObserved (s _ _ (substSame e e′ sy))) (resp T₂ c c′ (λ o → h (p-⇒ʳ o))))))
    resp (T₁ ⇒[ mk-kind Many π ] T₂) (e , c) (e′ , c′) h {g} {g′} s y y′ sy = toObserved
      (≈-Relatedˡ (toT∞-fmap π _ (g _)) (≈-Relatedʳ (toT∞-fmap π _ (g′ _))
        (relatedFmap (fromObserved (s _ _ (substSame e e′ sy))) (resp T₂ c c′ (λ o → h (p-⇒ʳ o))))))
    resp (μ G) c c′ h {x} refl = muResp G c c′ (λ o → h (p-μ o)) x
    resp (ν G f) c c′ h {x} {x′} s n = Ana.anaRel f (CB G) ((ν (G ⟨ at₀ A ⟩F) f) ⟨ σ ⟩) _ _ coalg n s
      where
        coalg : ∀ {a a′} → Same ((ν (G ⟨ at₀ A ⟩F) f) ⟨ σ ⟩) a a′
              → Related (LayerEq (CB G) (Same ((ν (G ⟨ at₀ A ⟩F) f) ⟨ σ ⟩))) _ _
        coalg {a} {a′} sa =
          ≈-Relatedˡ (toT∞-fmap (fin f) _ (outν a)) (≈-Relatedʳ (toT∞-fmap (fin f) _ (outν a′))
            (relatedFmap (outRel f (CA G) sa)
              (λ p → nuResp G c c′ (λ o → h (p-ν o)) (LayerEq-∀ (CA G) p))))

    muResp : ∀ G (c c′ : CovF G) {φ φ′ : FnF G} → SameFn φ φ′ → ∀ x → muMap G c φ x ≡ muMap G c′ φ′ x
    muResp G c c′ h (inS l) = cong inS (muLayerResp G G c c′ h c c′ h l)

    muLayerResp : ∀ G H (cG cG′ : CovF G) {φG φG′ : FnF G} → SameFn φG φG′
                → (cH cH′ : CovF H) {φ φ′ : FnF H} → SameFn φ φ′
                → ∀ l → muLayer G H cG φG cH φ l ≡ muLayer G H cG′ φG′ cH′ φ′ l
    muLayerResp G (K C) cG cG′ hG (cC , bA , bB) (cC′ , _ , _) h l =
      baseEq {C = C} bB (resp C cC cC′ (λ o → h (p-K o)) (reflBase (base-⟨⟩ r bA) l))
    muLayerResp G Id cG cG′ hG cH cH′ h l = muResp G cG cG′ hG l
    muLayerResp G (H₁ ⊕ H₂) cG cG′ hG (c₁ , c₂) (c₁′ , c₂′) h (inj₁ l) =
      cong inj₁ (muLayerResp G H₁ cG cG′ hG c₁ c₁′ (λ o → h (p-⊕ˡ o)) l)
    muLayerResp G (H₁ ⊕ H₂) cG cG′ hG (c₁ , c₂) (c₁′ , c₂′) h (inj₂ l) =
      cong inj₂ (muLayerResp G H₂ cG cG′ hG c₂ c₂′ (λ o → h (p-⊕ʳ o)) l)
    muLayerResp G (H₁ ⊗ H₂) cG cG′ hG (c₁ , c₂) (c₁′ , c₂′) h (l₁ , l₂) =
      cong₂ _,_ (muLayerResp G H₁ cG cG′ hG c₁ c₁′ (λ o → h (p-⊗ˡ o)) l₁) (muLayerResp G H₂ cG cG′ hG c₂ c₂′ (λ o → h (p-⊗ʳ o)) l₂)

    nuResp : ∀ H (c c′ : CovF H) {φ φ′ : FnF H} → SameFn φ φ′
           → ∀ {X} {R : X → X → Set} {l l′} → LayerEq (CA H) R l l′ → LayerEq (CB H) R (nuLayer H c φ l) (nuLayer H c′ φ′ l′)
    nuResp (K C) (cC , bA , bB) (cC′ , _ , _) h {l = l} refl =
      baseEq {C = C} bB (resp C cC cC′ (λ o → h (p-K o)) (reflBase (base-⟨⟩ r bA) l))
    nuResp Id c c′ h p = p
    nuResp (H₁ ⊕ H₂) (c₁ , c₂) (c₁′ , c₂′) h {l = inj₁ x} {inj₁ y} p = nuResp H₁ c₁ c₁′ (λ o → h (p-⊕ˡ o)) p
    nuResp (H₁ ⊕ H₂) (c₁ , c₂) (c₁′ , c₂′) h {l = inj₂ x} {inj₂ y} p = nuResp H₂ c₂ c₂′ (λ o → h (p-⊕ʳ o)) p
    nuResp (H₁ ⊕ H₂) c c′ h {l = inj₁ x} {inj₂ y} ()
    nuResp (H₁ ⊕ H₂) c c′ h {l = inj₂ x} {inj₁ y} ()
    nuResp (H₁ ⊗ H₂) (c₁ , c₂) (c₁′ , c₂′) h (p₁ , p₂) = nuResp H₁ c₁ c₁′ (λ o → h (p-⊗ˡ o)) p₁ , nuResp H₂ c₂ c₂′ (λ o → h (p-⊗ʳ o)) p₂

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
    mid (var fz)      c h s = h p-var _ _ s
    mid (var (fs i))  c h s = s
    mid Unit          c h s = s
    mid Void          c h s = s
    mid Int           c h s = s
    mid Float         c h s = s
    mid (T₁ * T₂) (c₁ , c₂) h {x₁ , x₂} {y₁ , y₂} (s₁ , s₂) =
      mid T₁ c₁ (λ o → h (p-*ˡ o)) s₁ , mid T₂ c₂ (λ o → h (p-*ʳ o)) s₂
    mid (T₁ + T₂) (c₁ , c₂) h {inj₁ x} {inj₁ y} s = mid T₁ c₁ (λ o → h (p-+ˡ o)) s
    mid (T₁ + T₂) (c₁ , c₂) h {inj₂ x} {inj₂ y} s = mid T₂ c₂ (λ o → h (p-+ʳ o)) s
    mid (T₁ + T₂) c h {inj₁ x} {inj₂ y} ()
    mid (T₁ + T₂) c h {inj₂ x} {inj₁ y} ()
    mid (T₁ ⇒[ mk-kind Zero π ] T₂) (e , c) h s = funId π (mid T₂ c (λ o → h (p-⇒ʳ o))) s
    mid (T₁ ⇒[ mk-kind One π ] T₂) (e , c) h s y y′ sy = funId π (mid T₂ c (λ o → h (p-⇒ʳ o))) (s _ _ (substId e sy))
    mid (T₁ ⇒[ mk-kind Many π ] T₂) (e , c) h s y y′ sy = funId π (mid T₂ c (λ o → h (p-⇒ʳ o))) (s _ _ (substId e sy))
    mid (μ G) c h {x} refl = muId G c (λ o → h (p-μ o)) x
    mid (ν G f) c h s n = nuId G f c (λ o → h (p-ν o)) n s

    muId : ∀ G (c : CovF G) {φ : FnF G} → IsId φ → ∀ x → muMap G c φ x ≡ x
    muId G c h (inS l) = cong inS (muLayerId G G c h c h l)

    muLayerId : ∀ G H (cG : CovF G) {φG : FnF G} → IsId φG → (cH : CovF H) {φ : FnF H} → IsId φ
              → ∀ l → muLayer G H cG φG cH φ l ≡ l
    muLayerId G (K C) cG hG (cC , bA , _) h l =
      sameBase (base-⟨⟩ r bA) (mid C cC (λ o → h (p-K o)) (reflBase (base-⟨⟩ r bA) l))
    muLayerId G Id cG hG cH h l = muId G cG hG l
    muLayerId G (H₁ ⊕ H₂) cG hG (c₁ , c₂) h (inj₁ l) = cong inj₁ (muLayerId G H₁ cG hG c₁ (λ o → h (p-⊕ˡ o)) l)
    muLayerId G (H₁ ⊕ H₂) cG hG (c₁ , c₂) h (inj₂ l) = cong inj₂ (muLayerId G H₂ cG hG c₂ (λ o → h (p-⊕ʳ o)) l)
    muLayerId G (H₁ ⊗ H₂) cG hG (c₁ , c₂) h (l₁ , l₂) =
      cong₂ _,_ (muLayerId G H₁ cG hG c₁ (λ o → h (p-⊗ˡ o)) l₁) (muLayerId G H₂ cG hG c₂ (λ o → h (p-⊗ʳ o)) l₂)

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
      sameBase (base-⟨⟩ r bA) (mid C cC (λ o → h (p-K o)) (reflBase (base-⟨⟩ r bA) l))
    nuLayerId G f cG hG Id cH h n p = nuId G f cG hG n p
    nuLayerId G f cG hG (H₁ ⊕ H₂) (c₁ , c₂) h n {inj₁ x} {inj₁ y} p = nuLayerId G f cG hG H₁ c₁ (λ o → h (p-⊕ˡ o)) n p
    nuLayerId G f cG hG (H₁ ⊕ H₂) (c₁ , c₂) h n {inj₂ x} {inj₂ y} p = nuLayerId G f cG hG H₂ c₂ (λ o → h (p-⊕ʳ o)) n p
    nuLayerId G f cG hG (H₁ ⊕ H₂) c h n {inj₁ x} {inj₂ y} ()
    nuLayerId G f cG hG (H₁ ⊕ H₂) c h n {inj₂ x} {inj₁ y} ()
    nuLayerId G f cG hG (H₁ ⊗ H₂) (c₁ , c₂) h n (p₁ , p₂) =
      nuLayerId G f cG hG H₁ c₁ (λ o → h (p-⊗ˡ o)) n p₁ , nuLayerId G f cG hG H₂ c₂ (λ o → h (p-⊗ʳ o)) n p₂

module MapComp {m : ℕ} {Δ : KCtx m} (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) (A B C : Ty m) where
  module AB = MapAt Δ σ A B
  module BC = MapAt Δ σ B C
  module AC = MapAt Δ σ A C

  -- `φ₃` is `φ₂` after `φ₁`.
  IsComp : ∀ {P : Set} → (P → ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ C ⟨ σ ⟩ ⟧ᵛ) → (P → ⟦ B ⟨ σ ⟩ ⟧ᵛ → ⟦ C ⟨ σ ⟩ ⟧ᵛ)
         → (P → ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ B ⟨ σ ⟩ ⟧ᵛ) → Set
  IsComp {P} φ₃ φ₂ φ₁ = ∀ (o : P) a a′ → Same (A ⟨ σ ⟩) a a′ → Same (C ⟨ σ ⟩) (φ₃ o a) (φ₂ o (φ₁ o a′))

  private
    substComp : ∀ {X Y Z : Ty m} (eXZ : X ≡ Z) (eXY : X ≡ Y) (eYZ : Y ≡ Z) {y y′ : ⟦ Z ⟨ σ ⟩ ⟧ᵛ} → Same (Z ⟨ σ ⟩) y y′
              → Same (X ⟨ σ ⟩) (subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) (sym eXZ) y)
                               (subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) (sym eXY) (subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) (sym eYZ) y′))
    substComp refl refl refl s = s

    funComp : ∀ π {X Y Z : Type} {f : ⟦ X ⟧ᵛ → ⟦ Z ⟧ᵛ} {g : ⟦ Y ⟧ᵛ → ⟦ Z ⟧ᵛ} {k : ⟦ X ⟧ᵛ → ⟦ Y ⟧ᵛ} {u u′ : M π ⟦ X ⟧ᵛ}
            → (∀ {a a′} → Same X a a′ → Same Z (f a) (g (k a′))) → SameM π X u u′
            → SameM π Z (fmap π f u) (fmap π g (fmap π k u′))
    funComp π {u = u} {u′} h s = toObserved
      (≈-Relatedˡ (toT∞-fmap π _ u) (≈-Relatedʳ (fmap² π _ _ u′) (relatedFmap (fromObserved s) h)))

  mutual
    comp : ∀ T (c₃ : AC.Cov T) (c₂ : BC.Cov T) (c₁ : AB.Cov T) {φ₃ : AC.Fn T} {φ₂ : BC.Fn T} {φ₁ : AB.Fn T}
         → IsComp φ₃ φ₂ φ₁ → ∀ {x x′} → Same (T ⟨ at₀ A ⟩ ⟨ σ ⟩) x x′
         → Same (T ⟨ at₀ C ⟩ ⟨ σ ⟩) (AC.mapS T c₃ φ₃ x) (BC.mapS T c₂ φ₂ (AB.mapS T c₁ φ₁ x′))
    comp (var fz)      c₃ c₂ c₁ h s = h p-var _ _ s
    comp (var (fs i))  c₃ c₂ c₁ h s = s
    comp Unit          c₃ c₂ c₁ h s = s
    comp Void          c₃ c₂ c₁ h s = s
    comp Int           c₃ c₂ c₁ h s = s
    comp Float         c₃ c₂ c₁ h s = s
    comp (T₁ * T₂) (a₃ , b₃) (a₂ , b₂) (a₁ , b₁) h {x₁ , x₂} {y₁ , y₂} (s₁ , s₂) =
      comp T₁ a₃ a₂ a₁ (λ o → h (p-*ˡ o)) s₁ , comp T₂ b₃ b₂ b₁ (λ o → h (p-*ʳ o)) s₂
    comp (T₁ + T₂) (a₃ , b₃) (a₂ , b₂) (a₁ , b₁) h {inj₁ x} {inj₁ y} s = comp T₁ a₃ a₂ a₁ (λ o → h (p-+ˡ o)) s
    comp (T₁ + T₂) (a₃ , b₃) (a₂ , b₂) (a₁ , b₁) h {inj₂ x} {inj₂ y} s = comp T₂ b₃ b₂ b₁ (λ o → h (p-+ʳ o)) s
    comp (T₁ + T₂) c₃ c₂ c₁ h {inj₁ x} {inj₂ y} ()
    comp (T₁ + T₂) c₃ c₂ c₁ h {inj₂ x} {inj₁ y} ()
    comp (T₁ ⇒[ mk-kind Zero π ] T₂) (e₃ , c₃) (e₂ , c₂) (e₁ , c₁) h s =
      funComp π (comp T₂ c₃ c₂ c₁ (λ o → h (p-⇒ʳ o))) s
    comp (T₁ ⇒[ mk-kind One π ] T₂) (e₃ , c₃) (e₂ , c₂) (e₁ , c₁) h s y y′ sy =
      funComp π (comp T₂ c₃ c₂ c₁ (λ o → h (p-⇒ʳ o))) (s _ _ (substComp e₃ e₁ e₂ sy))
    comp (T₁ ⇒[ mk-kind Many π ] T₂) (e₃ , c₃) (e₂ , c₂) (e₁ , c₁) h s y y′ sy =
      funComp π (comp T₂ c₃ c₂ c₁ (λ o → h (p-⇒ʳ o))) (s _ _ (substComp e₃ e₁ e₂ sy))
    comp (μ G) c₃ c₂ c₁ h {x} refl = muComp G c₃ c₂ c₁ (λ o → h (p-μ o)) x
    comp (ν G f) c₃ c₂ c₁ h s n = nuComp G f c₃ c₂ c₁ (λ o → h (p-ν o)) n s

    muComp : ∀ G (c₃ : AC.CovF G) (c₂ : BC.CovF G) (c₁ : AB.CovF G) {φ₃ : AC.FnF G} {φ₂ : BC.FnF G} {φ₁ : AB.FnF G}
           → IsComp φ₃ φ₂ φ₁ → ∀ x → AC.muMap G c₃ φ₃ x ≡ BC.muMap G c₂ φ₂ (AB.muMap G c₁ φ₁ x)
    muComp G c₃ c₂ c₁ h (inS l) = cong inS (muLayerComp G G c₃ c₂ c₁ h c₃ c₂ c₁ h l)

    muLayerComp : ∀ G H (g₃ : AC.CovF G) (g₂ : BC.CovF G) (g₁ : AB.CovF G)
                  {ψ₃ : AC.FnF G} {ψ₂ : BC.FnF G} {ψ₁ : AB.FnF G} → IsComp ψ₃ ψ₂ ψ₁
                → (c₃ : AC.CovF H) (c₂ : BC.CovF H) (c₁ : AB.CovF H)
                  {φ₃ : AC.FnF H} {φ₂ : BC.FnF H} {φ₁ : AB.FnF H} → IsComp φ₃ φ₂ φ₁
                → ∀ l → AC.muLayer G H g₃ ψ₃ c₃ φ₃ l ≡ BC.muLayer G H g₂ ψ₂ c₂ φ₂ (AB.muLayer G H g₁ ψ₁ c₁ φ₁ l)
    muLayerComp G (K D) g₃ g₂ g₁ hG (d₃ , bA , bC) (d₂ , _ , _) (d₁ , _ , _) h l =
      sameBase (base-⟨⟩ r bC) (comp D d₃ d₂ d₁ (λ o → h (p-K o)) (reflBase (base-⟨⟩ r bA) l))
    muLayerComp G Id g₃ g₂ g₁ hG c₃ c₂ c₁ h l = muComp G g₃ g₂ g₁ hG l
    muLayerComp G (H₁ ⊕ H₂) g₃ g₂ g₁ hG (a₃ , b₃) (a₂ , b₂) (a₁ , b₁) h (inj₁ l) =
      cong inj₁ (muLayerComp G H₁ g₃ g₂ g₁ hG a₃ a₂ a₁ (λ o → h (p-⊕ˡ o)) l)
    muLayerComp G (H₁ ⊕ H₂) g₃ g₂ g₁ hG (a₃ , b₃) (a₂ , b₂) (a₁ , b₁) h (inj₂ l) =
      cong inj₂ (muLayerComp G H₂ g₃ g₂ g₁ hG b₃ b₂ b₁ (λ o → h (p-⊕ʳ o)) l)
    muLayerComp G (H₁ ⊗ H₂) g₃ g₂ g₁ hG (a₃ , b₃) (a₂ , b₂) (a₁ , b₁) h (l₁ , l₂) =
      cong₂ _,_ (muLayerComp G H₁ g₃ g₂ g₁ hG a₃ a₂ a₁ (λ o → h (p-⊗ˡ o)) l₁)
                (muLayerComp G H₂ g₃ g₂ g₁ hG b₃ b₂ b₁ (λ o → h (p-⊗ʳ o)) l₂)

    -- ν: at every depth, by the layers.
    nuComp : ∀ G f (c₃ : AC.CovF G) (c₂ : BC.CovF G) (c₁ : AB.CovF G) {φ₃ : AC.FnF G} {φ₂ : BC.FnF G} {φ₁ : AB.FnF G}
           → IsComp φ₃ φ₂ φ₁ → ∀ n {a a′} → Same ((ν (G ⟨ at₀ A ⟩F) f) ⟨ σ ⟩) a a′
           → SameNu f (AC.CB G) n
               (ana f (AC.CB G) (λ y → fmap (fin f) (AC.nuLayer G c₃ φ₃ {νM f (AC.CA G)}) (outν y)) a)
               (ana f (BC.CB G) (λ y → fmap (fin f) (BC.nuLayer G c₂ φ₂ {νM f (BC.CA G)}) (outν y))
                 (ana f (AB.CB G) (λ y → fmap (fin f) (AB.nuLayer G c₁ φ₁ {νM f (AB.CA G)}) (outν y)) a′))
    nuComp G f c₃ c₂ c₁ h zero    s = tt
    nuComp G f c₃ c₂ c₁ {φ₃} {φ₂} {φ₁} h (suc n) {a} {a′} s = toObserved
      (≈-Relatedˡ (≈-trans (Unfold.unfold-out≈ (AC.CB G) f k₃ a) (fmap² (fin f) _ _ (outν a)))
        (≈-Relatedʳ (≈-trans (Unfold.unfold-out≈ (BC.CB G) f k₂ (ana f (AB.CB G) k₁ a′))
                     (≈-trans (fmap² (fin f) _ _ (outν (ana f (AB.CB G) k₁ a′)))
                       (≈-trans (≈-bind (≈-trans (Unfold.unfold-out≈ (AB.CB G) f k₁ a′) (fmap² (fin f) _ _ (outν a′)))
                                        (λ _ → ≈-refl _))
                         (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ l → idˡ _ _))))))
          (relatedFmap (outRel f (AC.CA G) s) (λ p → nuLayerComp G f c₃ c₂ c₁ h G c₃ c₂ c₁ h n (LayerEq-∀ (AC.CA G) p)))))
      where
        k₃ = λ y → fmap (fin f) (AC.nuLayer G c₃ φ₃ {νM f (AC.CA G)}) (outν y)
        k₂ = λ y → fmap (fin f) (BC.nuLayer G c₂ φ₂ {νM f (BC.CA G)}) (outν y)
        k₁ = λ y → fmap (fin f) (AB.nuLayer G c₁ φ₁ {νM f (AB.CA G)}) (outν y)

    nuLayerComp : ∀ G f (g₃ : AC.CovF G) (g₂ : BC.CovF G) (g₁ : AB.CovF G)
                  {ψ₃ : AC.FnF G} {ψ₂ : BC.FnF G} {ψ₁ : AB.FnF G} → IsComp ψ₃ ψ₂ ψ₁
                → ∀ H (c₃ : AC.CovF H) (c₂ : BC.CovF H) (c₁ : AB.CovF H)
                  {φ₃ : AC.FnF H} {φ₂ : BC.FnF H} {φ₁ : AB.FnF H} → IsComp φ₃ φ₂ φ₁ → ∀ n {l l′}
                → LayerEq (AC.CA H) (Same ((ν (G ⟨ at₀ A ⟩F) f) ⟨ σ ⟩)) l l′
                → LayerEq (AC.CB H) (SameNu f (AC.CB G) n)
                    (sfmap (AC.CB H) (ana f (AC.CB G) (λ y → fmap (fin f) (AC.nuLayer G g₃ ψ₃ {νM f (AC.CA G)}) (outν y)))
                       (AC.nuLayer H c₃ φ₃ l))
                    (sfmap (BC.CB H) (ana f (BC.CB G) (λ y → fmap (fin f) (BC.nuLayer G g₂ ψ₂ {νM f (BC.CA G)}) (outν y)))
                       (BC.nuLayer H c₂ φ₂
                         (sfmap (AB.CB H) (ana f (AB.CB G) (λ y → fmap (fin f) (AB.nuLayer G g₁ ψ₁ {νM f (AB.CA G)}) (outν y)))
                            (AB.nuLayer H c₁ φ₁ l′))))
    nuLayerComp G f g₃ g₂ g₁ hG (K D) (d₃ , bA , bC) (d₂ , _ , _) (d₁ , _ , _) h n {l} refl =
      sameBase (base-⟨⟩ r bC) (comp D d₃ d₂ d₁ (λ o → h (p-K o)) (reflBase (base-⟨⟩ r bA) l))
    nuLayerComp G f g₃ g₂ g₁ hG Id c₃ c₂ c₁ h n p = nuComp G f g₃ g₂ g₁ hG n p
    nuLayerComp G f g₃ g₂ g₁ hG (H₁ ⊕ H₂) (a₃ , b₃) (a₂ , b₂) (a₁ , b₁) h n {inj₁ x} {inj₁ y} p =
      nuLayerComp G f g₃ g₂ g₁ hG H₁ a₃ a₂ a₁ (λ o → h (p-⊕ˡ o)) n p
    nuLayerComp G f g₃ g₂ g₁ hG (H₁ ⊕ H₂) (a₃ , b₃) (a₂ , b₂) (a₁ , b₁) h n {inj₂ x} {inj₂ y} p =
      nuLayerComp G f g₃ g₂ g₁ hG H₂ b₃ b₂ b₁ (λ o → h (p-⊕ʳ o)) n p
    nuLayerComp G f g₃ g₂ g₁ hG (H₁ ⊕ H₂) c₃ c₂ c₁ h n {inj₁ x} {inj₂ y} ()
    nuLayerComp G f g₃ g₂ g₁ hG (H₁ ⊕ H₂) c₃ c₂ c₁ h n {inj₂ x} {inj₁ y} ()
    nuLayerComp G f g₃ g₂ g₁ hG (H₁ ⊗ H₂) (a₃ , b₃) (a₂ , b₂) (a₁ , b₁) h n (p₁ , p₂) =
      nuLayerComp G f g₃ g₂ g₁ hG H₁ a₃ a₂ a₁ (λ o → h (p-⊗ˡ o)) n p₁ , nuLayerComp G f g₃ g₂ g₁ hG H₂ b₃ b₂ b₁ (λ o → h (p-⊗ʳ o)) n p₂
