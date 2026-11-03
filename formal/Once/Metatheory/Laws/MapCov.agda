{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapCov — what a derivation of `mapᶜ`'s body fixes
-- about the type it maps (`Laws.MapSem.Cov`): an arrow's domain is the same
-- at both ends, and a functor's constants are base types at both ends.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapCov (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Once.Spec.Grade using (Quantity; mk-kind; Purity)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; wf-K; wf-Id; wf-⊕; wf-⊗; ⟦_⟧F; _⟨_⟩; _⟨_⟩F; _⇒[_]_; _*_; _+_;
                                  var; Unit; Void; Int; Float; μ; ν; K; Id; _⊕_; _⊗_; at₀)
open import Once.Spec.Context using (Ctx; _▸_; _∷_; lookup)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (mapAtᶜ; mapLayerᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy; str)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt; Occ; OccF; p-var; p-*ˡ; p-*ʳ; p-+ˡ; p-+ʳ; p-⇒ʳ; p-μ; p-ν; p-K; p-⊕ˡ; p-⊕ʳ; p-⊗ˡ; p-⊗ʳ)

module _ {m : ℕ} {Δ : KCtx m} where

  -- Any derivation of a former: its premises, the type it has.
  lamInv : ∀ {n} {Γ : Ctx m n} {Ψ X q π Y π₀ t} → Δ ⊩ Γ ⊢[ Ψ ] lam X q π t ∷ Y ! π₀
         → Σ[ B ∈ Ty m ] Σ[ q′ ∈ Quantity ] Σ[ Ψ₀ ∈ _ ] (Y ≡ X ⇒[ mk-kind q π ] B) × (Δ ⊩ Γ ▸ X ⊢[ q′ ∷ Ψ₀ ] t ∷ B ! π)
  lamInv (⊢lam {Ψ = Ψ₀} {q′ = q′} {B = B} le d) = B , q′ , Ψ₀ , refl , d
  lamInv (⊢sub-use _ d) = lamInv d
  lamInv (⊢sub-eff _ d) = lamInv d

  letInv : ∀ {n} {Γ : Ctx m n} {Ψ q Y π e b} → Δ ⊩ Γ ⊢[ Ψ ] let′ q e b ∷ Y ! π
         → Σ[ X ∈ Ty m ] Σ[ Ψ₁ ∈ _ ] Σ[ Ψ₂ ∈ _ ] Σ[ π₁ ∈ Purity ] Σ[ π₂ ∈ Purity ]
             (Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ X ! π₁) × (Δ ⊩ Γ ▸ X ⊢[ q ∷ Ψ₂ ] b ∷ Y ! π₂)
  letInv (⊢let {A = X} de db) = X , _ , _ , _ , _ , de , db
  letInv (⊢sub-use _ d) = letInv d
  letInv (⊢sub-eff _ d) = letInv d

  inlInv : ∀ {n} {Γ : Ctx m n} {Ψ Z X Y π t} → Δ ⊩ Γ ⊢[ Ψ ] inl Z t ∷ X + Y ! π → Σ[ Ψ₀ ∈ _ ] Σ[ π₀ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ X ! π₀)
  inlInv (⊢inl d) = _ , _ , d
  inlInv (⊢sub-use _ d) = inlInv d
  inlInv (⊢sub-eff _ d) = inlInv d

  inrInv : ∀ {n} {Γ : Ctx m n} {Ψ Z X Y π t} → Δ ⊩ Γ ⊢[ Ψ ] inr Z t ∷ X + Y ! π → Σ[ Ψ₀ ∈ _ ] Σ[ π₀ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ Y ! π₀)
  inrInv (⊢inr d) = _ , _ , d
  inrInv (⊢sub-use _ d) = inrInv d
  inrInv (⊢sub-eff _ d) = inrInv d

  outInv : ∀ {n} {Γ : Ctx m n} {Ψ X π t} → Δ ⊩ Γ ⊢[ Ψ ] out t ∷ X ! π
         → Σ[ F ∈ Fun m ] Σ[ f ∈ _ ] Σ[ Ψ₀ ∈ _ ] Σ[ π₀ ∈ Purity ] (X ≡ ⟦ F ⟧F (ν F f)) × WFFun Δ F × (Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ ν F f ! π₀)
  outInv (⊢out wf d) = _ , _ , _ , _ , refl , wf , d
  outInv (⊢sub-use _ d) = outInv d
  outInv (⊢sub-eff _ d) = outInv d

  rollInv : ∀ {n} {Γ : Ctx m n} {Ψ F π t} → Δ ⊩ Γ ⊢[ Ψ ] roll F t ∷ μ F ! π
          → WFFun Δ F × Σ[ Ψ₀ ∈ _ ] Σ[ π₀ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ ⟦ F ⟧F (μ F) ! π₀)
  rollInv (⊢roll wf d) = wf , _ , _ , d
  rollInv (⊢sub-use _ d) = rollInv d
  rollInv (⊢sub-eff _ d) = rollInv d

  appInv : ∀ {n} {Γ : Ctx m n} {Ψ Y π f x} → Δ ⊩ Γ ⊢[ Ψ ] app f x ∷ Y ! π
         → Σ[ X ∈ Ty m ] Σ[ q ∈ Quantity ] Σ[ πl ∈ Purity ] Σ[ Ψ₁ ∈ _ ] Σ[ Ψ₂ ∈ _ ] Σ[ π₁ ∈ Purity ] Σ[ π₂ ∈ Purity ]
             (Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ X ⇒[ mk-kind q πl ] Y ! π₁) × (Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ X ! π₂)
  appInv (⊢app df dx) = _ , _ , _ , _ , _ , _ , _ , df , dx
  appInv (⊢sub-use _ d) = appInv d
  appInv (⊢sub-eff _ d) = appInv d

  pairInv : ∀ {n} {Γ : Ctx m n} {Ψ X Y π a b} → Δ ⊩ Γ ⊢[ Ψ ] pair a b ∷ X * Y ! π
          → Σ[ Ψ₁ ∈ _ ] Σ[ Ψ₂ ∈ _ ] Σ[ π₁ ∈ Purity ] Σ[ π₂ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψ₁ ] a ∷ X ! π₁) × (Δ ⊩ Γ ⊢[ Ψ₂ ] b ∷ Y ! π₂)
  pairInv (⊢pair da db) = _ , _ , _ , _ , da , db
  pairInv (⊢sub-use _ d) = pairInv d
  pairInv (⊢sub-eff _ d) = pairInv d

  fstInv : ∀ {n} {Γ : Ctx m n} {Ψ X π p} → Δ ⊩ Γ ⊢[ Ψ ] fst p ∷ X ! π → Σ[ Y ∈ Ty m ] Σ[ Ψ₀ ∈ _ ] Σ[ π₀ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψ₀ ] p ∷ X * Y ! π₀)
  fstInv (⊢fst d) = _ , _ , _ , d
  fstInv (⊢sub-use _ d) = fstInv d
  fstInv (⊢sub-eff _ d) = fstInv d

  sndInv : ∀ {n} {Γ : Ctx m n} {Ψ Y π p} → Δ ⊩ Γ ⊢[ Ψ ] snd p ∷ Y ! π → Σ[ X ∈ Ty m ] Σ[ Ψ₀ ∈ _ ] Σ[ π₀ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψ₀ ] p ∷ X * Y ! π₀)
  sndInv (⊢snd d) = _ , _ , _ , d
  sndInv (⊢sub-use _ d) = sndInv d
  sndInv (⊢sub-eff _ d) = sndInv d

  caseInv : ∀ {n} {Γ : Ctx m n} {Ψ qℓ qr C π s l r′} → Δ ⊩ Γ ⊢[ Ψ ] case qℓ qr s l r′ ∷ C ! π
          → Σ[ X ∈ Ty m ] Σ[ Y ∈ Ty m ] Σ[ Ψs ∈ _ ] Σ[ Ψc ∈ _ ] Σ[ π₁ ∈ Purity ] Σ[ π₂ ∈ Purity ]
              (Δ ⊩ Γ ⊢[ Ψs ] s ∷ X + Y ! π₁) × (Δ ⊩ Γ ▸ X ⊢[ qℓ ∷ Ψc ] l ∷ C ! π₂) × (Δ ⊩ Γ ▸ Y ⊢[ qr ∷ Ψc ] r′ ∷ C ! π₂)
  caseInv (⊢case ds dl dr) = _ , _ , _ , _ , _ , _ , ds , dl , dr
  caseInv (⊢sub-use _ d) = caseInv d
  caseInv (⊢sub-eff _ d) = caseInv d

  foldInv : ∀ {n} {Γ : Ctx m n} {Ψ F A′ π alg t} → Δ ⊩ Γ ⊢[ Ψ ] fold F alg t ∷ A′ ! π
          → WFFun Δ F × Σ[ Ψf ∈ _ ] Σ[ πf ∈ Purity ] Σ[ π₁ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψf ] alg ∷ ⟦ F ⟧F A′ ⇒[ mk-kind _ πf ] A′ ! π₁)
  foldInv (⊢fold wf da dt) = wf , _ , _ , _ , da
  foldInv (⊢sub-use _ d) = foldInv d
  foldInv (⊢sub-eff _ d) = foldInv d

  unfoldInv : ∀ {n} {Γ : Ctx m n} {Ψ F f π c t} → Δ ⊩ Γ ⊢[ Ψ ] unfold F c t ∷ ν F f ! π
            → WFFun Δ F × Σ[ A′ ∈ Ty m ] Σ[ Ψc ∈ _ ] Σ[ π₁ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψc ] c ∷ A′ ⇒[ mk-kind _ _ ] ⟦ F ⟧F A′ ! π₁)
  unfoldInv (⊢unfold wf dc dt) = wf , _ , _ , _ , dc
  unfoldInv (⊢sub-use _ d) = unfoldInv d
  unfoldInv (⊢sub-eff _ d) = unfoldInv d

  wf₁ : ∀ {F G : Fun m} → WFFun Δ (F ⊕ G) → WFFun Δ F
  wf₁ (wf-⊕ a b) = a
  wf₂ : ∀ {F G : Fun m} → WFFun Δ (F ⊕ G) → WFFun Δ G
  wf₂ (wf-⊕ a b) = b
  wf₁⊗ : ∀ {F G : Fun m} → WFFun Δ (F ⊗ G) → WFFun Δ F
  wf₁⊗ (wf-⊗ a b) = a
  wf₂⊗ : ∀ {F G : Fun m} → WFFun Δ (F ⊗ G) → WFFun Δ G
  wf₂⊗ (wf-⊗ a b) = b

  dom≡ : ∀ {X Y Z Z′ : Ty m} {k k′} → (Y ⇒[ k ] Z) ≡ (X ⇒[ k′ ] Z′) → Y ≡ X
  dom≡ refl = refl
  cod≡ : ∀ {X Y Z Z′ : Ty m} {k k′} → (Y ⇒[ k ] Z) ≡ (X ⇒[ k′ ] Z′) → Z ≡ Z′
  cod≡ refl = refl

  module Covs {σ} (A B : Ty m) where
    open MapAt Δ σ A B

    mutual
      covOf : ∀ {n} {Γ : Ctx m n} {Ψ π} T {h x} → Δ ⊩ Γ ⊢[ Ψ ] mapAtᶜ A B T h x ∷ T ⟨ at₀ B ⟩ ! π → Cov T
      covOf (var fz)     d = tt
      covOf (var (fs i)) d = tt
      covOf Unit  d = tt
      covOf Void  d = tt
      covOf Int   d = tt
      covOf Float d = tt
      covOf (T₁ * T₂) (⊢pair d₁ d₂) = covOf T₁ d₁ , covOf T₂ d₂
      covOf (T₁ * T₂) (⊢sub-use _ d) = covOf (T₁ * T₂) d
      covOf (T₁ * T₂) (⊢sub-eff _ d) = covOf (T₁ * T₂) d
      covOf (T₁ + T₂) (⊢case ds dl dr) with inlInv dl | inrInv dr
      ... | _ , _ , d₁ | _ , _ , d₂ = covOf T₁ d₁ , covOf T₂ d₂
      covOf (T₁ + T₂) (⊢sub-use _ d) = covOf (T₁ + T₂) d
      covOf (T₁ + T₂) (⊢sub-eff _ d) = covOf (T₁ + T₂) d
      covOf (T₁ ⇒[ mk-kind q π ] T₂) d with lamInv d
      ... | B′ , q′ , Ψ₀ , eqT , dt with cod≡ eqT
      ...   | refl with letInv dt
      ...     | _ , _ , _ , _ , _ , de , db = sym (dom≡ eqT) , covOf T₂ db
      covOf (μ G) (⊢fold wfA da dt) with lamInv da
      ... | B′ , q′ , Ψ₀ , eqT , dr with cod≡ eqT
      ...   | refl with rollInv dr
      ...     | wfB , _ , _ , dl = covL G wfA wfB dl
      covOf (μ G) (⊢sub-use _ d) = covOf (μ G) d
      covOf (μ G) (⊢sub-eff _ d) = covOf (μ G) d
      covOf (ν G f) (⊢unfold wfB dc dt) with lamInv dc
      ... | B′ , q′ , Ψ₀ , eqT , db with dom≡ eqT | cod≡ eqT
      ...   | refl | refl with letInv db
      ...     | _ , _ , _ , _ , _ , de , dl with outInv de
      ...       | _ , _ , _ , _ , refl , wfA , dv with varTy dv
      ...         | refl = covL G wfA wfB dl
      covOf (ν G f) (⊢sub-use _ d) = covOf (ν G f) d
      covOf (ν G f) (⊢sub-eff _ d) = covOf (ν G f) d

      covL : ∀ {n} {Γ : Ctx m n} {Ψ π} {R : Ty m} H {h y} → WFFun Δ (H ⟨ at₀ A ⟩F) → WFFun Δ (H ⟨ at₀ B ⟩F)
           → Δ ⊩ Γ ⊢[ Ψ ] mapLayerᶜ A B R H h y ∷ ⟦ H ⟨ at₀ B ⟩F ⟧F R ! π → CovF H
      covL (K C) (wf-K bA) (wf-K bB) d = covOf C d , bA , bB
      covL Id wfA wfB d = tt
      covL (H₁ ⊕ H₂) wfA wfB (⊢case ds dl dr) with inlInv dl | inrInv dr
      ... | _ , _ , d₁ | _ , _ , d₂ = covL H₁ (wf₁ wfA) (wf₁ wfB) d₁ , covL H₂ (wf₂ wfA) (wf₂ wfB) d₂
      covL (H₁ ⊕ H₂) wfA wfB (⊢sub-use _ d) = covL (H₁ ⊕ H₂) wfA wfB d
      covL (H₁ ⊕ H₂) wfA wfB (⊢sub-eff _ d) = covL (H₁ ⊕ H₂) wfA wfB d
      covL (H₁ ⊗ H₂) wfA wfB (⊢pair d₁ d₂) = covL H₁ (wf₁⊗ wfA) (wf₁⊗ wfB) d₁ , covL H₂ (wf₂⊗ wfA) (wf₂⊗ wfB) d₂
      covL (H₁ ⊗ H₂) wfA wfB (⊢sub-use _ d) = covL (H₁ ⊗ H₂) wfA wfB d
      covL (H₁ ⊗ H₂) wfA wfB (⊢sub-eff _ d) = covL (H₁ ⊗ H₂) wfA wfB d

    -- What a term's every derivation has as its type.
    TyOf : ∀ {n} (Γ : Ctx m n) → Tm S m n → Ty m → Set
    TyOf Γ t X = ∀ {Ψ Y π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ Y ! π → Y ≡ X

    private
      tyVar : ∀ {n} {Γ : Ctx m n} i → TyOf Γ (var i) (lookup Γ i)
      tyVar i = varTy
      tyWk : ∀ {n} {Γ : Ctx m n} {X t F} → TyOf Γ t F → TyOf (Γ ▸ X) (wk t) F
      tyWk h {_ ∷ _} d = h (str d)
      tyFst : ∀ {n} {Γ : Ctx m n} {t X₁ X₂} → TyOf Γ t (X₁ * X₂) → TyOf Γ (fst t) X₁
      tyFst h d with fstInv d
      ... | _ , _ , _ , dp with h dp
      ...   | refl = refl
      tySnd : ∀ {n} {Γ : Ctx m n} {t X₁ X₂} → TyOf Γ t (X₁ * X₂) → TyOf Γ (snd t) X₂
      tySnd h d with sndInv d
      ... | _ , _ , _ , dp with h dp
      ...   | refl = refl

    -- Where the variable occurs, the arrow is from `A` to `B`.
    mutual
      occTy : ∀ {n} {Γ : Ctx m n} {Ψ π} T {h x F} → TyOf Γ h F → TyOf Γ x (T ⟨ at₀ A ⟩)
            → Δ ⊩ Γ ⊢[ Ψ ] mapAtᶜ A B T h x ∷ T ⟨ at₀ B ⟩ ! π → Occ T
            → Σ[ q ∈ Quantity ] Σ[ π′ ∈ Purity ] (F ≡ A ⇒[ mk-kind q π′ ] B)
      occTy (var fz) hT xT d p-var with appInv d
      ... | X , q , πl , _ , _ , _ , _ , df , dx with xT dx
      ...   | refl = q , πl , sym (hT df)
      occTy (T₁ * T₂) hT xT d (p-*ˡ o) with pairInv d
      ... | _ , _ , _ , _ , d₁ , d₂ = occTy T₁ hT (tyFst xT) d₁ o
      occTy (T₁ * T₂) hT xT d (p-*ʳ o) with pairInv d
      ... | _ , _ , _ , _ , d₁ , d₂ = occTy T₂ hT (tySnd xT) d₂ o
      occTy (T₁ + T₂) hT xT d (p-+ˡ o) with caseInv d
      ... | _ , _ , _ , _ , _ , _ , ds , dl , dr with xT ds
      ...   | refl with inlInv dl
      ...     | _ , _ , d₁ = occTy T₁ (tyWk hT) (tyVar fz) d₁ o
      occTy (T₁ + T₂) hT xT d (p-+ʳ o) with caseInv d
      ... | _ , _ , _ , _ , _ , _ , ds , dl , dr with xT ds
      ...   | refl with inrInv dr
      ...     | _ , _ , d₂ = occTy T₂ (tyWk hT) (tyVar fz) d₂ o
      occTy (T₁ ⇒[ mk-kind q π ] T₂) hT xT d (p-⇒ʳ o) with lamInv d
      ... | B′ , q′ , Ψ₀ , eqT , dt with cod≡ eqT
      ...   | refl with letInv dt
      ...     | X″ , _ , _ , _ , _ , de , db with appInv de
      ...       | _ , _ , _ , _ , _ , _ , _ , df , dx with cod≡ (tyWk xT df)
      ...         | refl = occTy T₂ (tyWk (tyWk hT)) (tyVar fz) db o
      occTy (μ G) hT xT d (p-μ o) with foldInv d
      ... | wfA , _ , _ , _ , da with lamInv da
      ...   | B′ , q′ , Ψ₀ , eqT , dr with cod≡ eqT
      ...     | refl with rollInv dr
      ...       | wfB , _ , _ , dl = occL G (tyWk hT) (tyVar fz) dl o
      occTy (ν G f) hT xT d (p-ν o) with unfoldInv d
      ... | wfB , A′ , _ , _ , dc with lamInv dc
      ...   | B′ , q′ , Ψ₀ , eqT , db with dom≡ eqT | cod≡ eqT
      ...     | refl | refl with letInv db
      ...       | _ , _ , _ , _ , _ , de , dl with outInv de
      ...         | _ , _ , _ , _ , refl , wfA , dv with varTy dv
      ...           | refl = occL G (tyWk (tyWk hT)) (tyVar fz) dl o

      occL : ∀ {n} {Γ : Ctx m n} {Ψ π} {R : Ty m} H {h y F} → TyOf Γ h F → TyOf Γ y (⟦ H ⟨ at₀ A ⟩F ⟧F R)
           → Δ ⊩ Γ ⊢[ Ψ ] mapLayerᶜ A B R H h y ∷ ⟦ H ⟨ at₀ B ⟩F ⟧F R ! π → OccF H
           → Σ[ q ∈ Quantity ] Σ[ π′ ∈ Purity ] (F ≡ A ⇒[ mk-kind q π′ ] B)
      occL (K C) hT yT d (p-K o) = occTy C hT yT d o
      occL (H₁ ⊕ H₂) hT yT d (p-⊕ˡ o) with caseInv d
      ... | _ , _ , _ , _ , _ , _ , ds , dl , dr with yT ds
      ...   | refl with inlInv dl
      ...     | _ , _ , d₁ = occL H₁ (tyWk hT) (tyVar fz) d₁ o
      occL (H₁ ⊕ H₂) hT yT d (p-⊕ʳ o) with caseInv d
      ... | _ , _ , _ , _ , _ , _ , ds , dl , dr with yT ds
      ...   | refl with inrInv dr
      ...     | _ , _ , d₂ = occL H₂ (tyWk hT) (tyVar fz) d₂ o
      occL (H₁ ⊗ H₂) hT yT d (p-⊗ˡ o) with pairInv d
      ... | _ , _ , _ , _ , d₁ , d₂ = occL H₁ hT (tyFst yT) d₁ o
      occL (H₁ ⊗ H₂) hT yT d (p-⊗ʳ o) with pairInv d
      ... | _ , _ , _ , _ , d₁ , d₂ = occL H₂ hT (tySnd yT) d₂ o
