{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.LayerSem — `layerᶜ F` means `F`'s own action on a
-- layer (`LAYER`): the semantic map at `layerT F`, read at `⟦ F ⟧F X` (`tr`),
-- is `LAYER`; and the Spec's fold maps a layer by `LAYER` of the fold.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Laws.LayerSem (Σ : Signature) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Once.Spec.Grade using (pure)
open import Once.Spec.Type using (Ty; Fun; KCtx; ∅ₖ; Respects; Base; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+;
                                  WFFun; wf-K; wf-Id; wf-⊕; wf-⊗; var; _*_; _+_; μ; K; Id; _⊕_; _⊗_;
                                  ⟦_⟧F; TySub; _⟨_⟩; _⟨_⟩F; at₀; shiftᵗ)
open import Once.Spec.Polynomial using (μS; inS)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM; layerM)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Metatheory.Laws.LayerTy using (shift-at₀; layerT; layerTy)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt; p-var; p-+ˡ; p-+ʳ; p-*ˡ; p-*ʳ)

module LayerSem {m : ℕ} (σ : TySub m 0) where

  V : Ty m → Set
  V Z = ⟦ Z ⟨ σ ⟩ ⟧ᵛ

  -- A value of `layerT F` at `X`, read at `⟦ F ⟧F X`.
  tr : ∀ F X → V (layerT F ⟨ at₀ X ⟩) → V (⟦ F ⟧F X)
  tr F X = subst V (layerTy F X)

  -- `F`'s action on a layer: `φ` at the recursive positions, the constants kept.
  LAYER : ∀ F {X Y : Ty m} → (V X → V Y) → V (⟦ F ⟧F X) → V (⟦ F ⟧F Y)
  LAYER (K C)   φ v = v
  LAYER Id      φ v = φ v
  LAYER (F ⊕ G) φ (inj₁ v) = inj₁ (LAYER F φ v)
  LAYER (F ⊕ G) φ (inj₂ v) = inj₂ (LAYER G φ v)
  LAYER (F ⊗ G) φ (v , w)  = LAYER F φ v , LAYER G φ w

  -- Reading along a sum or product equation: by parts.
  substInj₁ : ∀ {P P′ Q Q′ : Ty m} (e₁ : P ≡ P′) (e₂ : Q ≡ Q′) (a : V P) → subst V (cong₂ _+_ e₁ e₂) (inj₁ a) ≡ inj₁ (subst V e₁ a)
  substInj₁ refl refl a = refl
  substInj₂ : ∀ {P P′ Q Q′ : Ty m} (e₁ : P ≡ P′) (e₂ : Q ≡ Q′) (b : V Q) → subst V (cong₂ _+_ e₁ e₂) (inj₂ b) ≡ inj₂ (subst V e₂ b)
  substInj₂ refl refl b = refl
  substPair : ∀ {P P′ Q Q′ : Ty m} (e₁ : P ≡ P′) (e₂ : Q ≡ Q′) (a : V P) (b : V Q)
            → subst V (cong₂ _*_ e₁ e₂) (a , b) ≡ (subst V e₁ a , subst V e₂ b)
  substPair refl refl a b = refl

  -- Same-ness, rewritten on either side.
  sameRw : ∀ {Z : Ty m} {x x′ y y′ : V Z} → x ≡ x′ → y ≡ y′ → Same (Z ⟨ σ ⟩) x′ y′ → Same (Z ⟨ σ ⟩) x y
  sameRw refl refl s = s

  module _ {Δ : KCtx m} (r : Respects Δ ∅ₖ σ) (X Y : Ty m) where
    open MapAt Δ σ X Y

    -- A base constant, the variable made room for: the map leaves it.
    noVar : ∀ {C : Ty m} → Base Δ C → (c : Cov (C ⟨ shiftᵗ ⟩)) (φ : Fn (C ⟨ shiftᵗ ⟩)) → ∀ {v v′}
          → Same (C ⟨ shiftᵗ ⟩ ⟨ at₀ X ⟩ ⟨ σ ⟩) v v′
          → Same (C ⟨ σ ⟩) (subst V (shift-at₀ C Y) (mapS (C ⟨ shiftᵗ ⟩) c φ v)) (subst V (shift-at₀ C X) v′)
    noVar (b-var e) c φ s = s
    noVar b-Unit    c φ s = s
    noVar b-Void    c φ s = s
    noVar b-Int     c φ s = s
    noVar b-Float   c φ s = s
    noVar {C₁ * C₂} (b-* a b) (c₁ , c₂) φ {v₁ , v₂} {w₁ , w₂} (s₁ , s₂) =
      sameRw {Z = C₁ * C₂} (substPair (shift-at₀ C₁ Y) (shift-at₀ C₂ Y) _ _) (substPair (shift-at₀ C₁ X) (shift-at₀ C₂ X) w₁ w₂)
        (noVar a c₁ (λ o → φ (p-*ˡ o)) s₁ , noVar b c₂ (λ o → φ (p-*ʳ o)) s₂)
    noVar {C₁ + C₂} (b-+ a b) (c₁ , c₂) φ {inj₁ v} {inj₁ w} s =
      sameRw {Z = C₁ + C₂} (substInj₁ (shift-at₀ C₁ Y) (shift-at₀ C₂ Y) _) (substInj₁ (shift-at₀ C₁ X) (shift-at₀ C₂ X) w)
        (noVar a c₁ (λ o → φ (p-+ˡ o)) s)
    noVar {C₁ + C₂} (b-+ a b) (c₁ , c₂) φ {inj₂ v} {inj₂ w} s =
      sameRw {Z = C₁ + C₂} (substInj₂ (shift-at₀ C₁ Y) (shift-at₀ C₂ Y) _) (substInj₂ (shift-at₀ C₁ X) (shift-at₀ C₂ X) w)
        (noVar b c₂ (λ o → φ (p-+ʳ o)) s)
    noVar (b-+ a b) c φ {inj₁ v} {inj₂ w} ()
    noVar (b-+ a b) c φ {inj₂ v} {inj₁ w} ()

    -- The semantic map at `layerT F`, read at `⟦ F ⟧F`: `F`'s action.
    agree : ∀ F → WFFun Δ F → (c : Cov (layerT F)) (Φ : Fn (layerT F)) (φ : V X → V Y)
          → (∀ o a a′ → Same (X ⟨ σ ⟩) a a′ → Same (Y ⟨ σ ⟩) (Φ o a) (φ a′))
          → ∀ {v v′} → Same (layerT F ⟨ at₀ X ⟩ ⟨ σ ⟩) v v′
          → Same ((⟦ F ⟧F Y) ⟨ σ ⟩) (tr F Y (mapS (layerT F) c Φ v)) (LAYER F φ (tr F X v′))
    agree (K C) (wf-K b) c Φ φ h s = noVar b c Φ s
    agree Id wf c Φ φ h s = h p-var _ _ s
    agree (F ⊕ G) (wf-⊕ wF wG) (c₁ , c₂) Φ φ h {inj₁ v} {inj₁ w} s =
      sameRw {Z = ⟦ F ⊕ G ⟧F Y} (substInj₁ (layerTy F Y) (layerTy G Y) _) (cong (LAYER (F ⊕ G) φ) (substInj₁ (layerTy F X) (layerTy G X) w))
        (agree F wF c₁ (λ o → Φ (p-+ˡ o)) φ (λ o → h (p-+ˡ o)) s)
    agree (F ⊕ G) (wf-⊕ wF wG) (c₁ , c₂) Φ φ h {inj₂ v} {inj₂ w} s =
      sameRw {Z = ⟦ F ⊕ G ⟧F Y} (substInj₂ (layerTy F Y) (layerTy G Y) _) (cong (LAYER (F ⊕ G) φ) (substInj₂ (layerTy F X) (layerTy G X) w))
        (agree G wG c₂ (λ o → Φ (p-+ʳ o)) φ (λ o → h (p-+ʳ o)) s)
    agree (F ⊕ G) wf c Φ φ h {inj₁ v} {inj₂ w} ()
    agree (F ⊕ G) wf c Φ φ h {inj₂ v} {inj₁ w} ()
    agree (F ⊗ G) (wf-⊗ wF wG) (c₁ , c₂) Φ φ h {v₁ , v₂} {w₁ , w₂} (s₁ , s₂) =
      sameRw {Z = ⟦ F ⊗ G ⟧F Y} (substPair (layerTy F Y) (layerTy G Y) _ _) (cong (LAYER (F ⊗ G) φ) (substPair (layerTy F X) (layerTy G X) w₁ w₂))
        (agree F wF c₁ (λ o → Φ (p-*ˡ o)) φ (λ o → h (p-*ˡ o)) s₁ , agree G wG c₂ (λ o → Φ (p-*ʳ o)) φ (λ o → h (p-*ʳ o)) s₂)

  -- The Spec's fold maps a layer's recursive positions by the fold itself.
  foldLayer : ∀ (G : Fun m) {A : Ty m} (alg : _) H (x : V (⟦ H ⟧F (μ G)))
            → fromL σ H A (layerM pure (code (G ⟨ σ ⟩F)) (code (H ⟨ σ ⟩F)) alg (toL σ H (μ G) x))
              ≡ LAYER H (foldM pure (code (G ⟨ σ ⟩F)) alg) x
  foldLayer G alg (K C)   x = refl
  foldLayer G alg Id      x = refl
  foldLayer G alg (H₁ ⊕ H₂) (inj₁ x) = cong inj₁ (foldLayer G alg H₁ x)
  foldLayer G alg (H₁ ⊕ H₂) (inj₂ x) = cong inj₂ (foldLayer G alg H₂ x)
  foldLayer G alg (H₁ ⊗ H₂) (x , y)  = cong₂ _,_ (foldLayer G alg H₁ x) (foldLayer G alg H₂ y)
