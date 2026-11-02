{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Strengthen — renaming is typed backwards too: a
-- derivation of `ren ρ t` along a thinning `θ` gives one of `t`, at the usage
-- that drops the inserted variables (`back θ`). With weakening's meaning
-- (`Views.WkV.wkRel`) this reads an arm a combinator binds under its own
-- binders as the arm itself.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Strengthen (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; act; eff; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; _≤q_; _*q_)
open import Once.Spec.Type using (Ty; KCtx)
open import Once.Spec.Context using (Ctx; ∅; _▸_; lookup; Usage; []; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊑∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-refl; ⊑ᵘ-trans; ⊑ᵘ-≡)
open import Once.Metatheory.TermModel.Subst Σ S
  using (Thin; done; keep; skip; ⟦_⟧θ; idθ; idθ-id; CThin; cdone; ckeep; cskip; cid; cthin-lookup; ext-hρ; cast; retype)

-- The usage of the variables a thinning keeps.
back : ∀ {n n′} → Thin n n′ → Usage n′ → Usage n
back done     []      = []
back (keep θ) (q ∷ Ψ) = q ∷ back θ Ψ
back (skip θ) (q ∷ Ψ) = back θ Ψ

back-+ : ∀ {n n′} (θ : Thin n n′) (Ψ₁ Ψ₂ : Usage n′) → back θ (Ψ₁ +ᵘ Ψ₂) ≡ back θ Ψ₁ +ᵘ back θ Ψ₂
back-+ done     []       []       = refl
back-+ (keep θ) (p ∷ Ψ₁) (q ∷ Ψ₂) = cong (_ ∷_) (back-+ θ Ψ₁ Ψ₂)
back-+ (skip θ) (p ∷ Ψ₁) (q ∷ Ψ₂) = back-+ θ Ψ₁ Ψ₂

back-* : ∀ {n n′} (θ : Thin n n′) q (Ψ : Usage n′) → back θ (q *ᵘ Ψ) ≡ q *ᵘ back θ Ψ
back-* done     q []      = refl
back-* (keep θ) q (p ∷ Ψ) = cong (_ ∷_) (back-* θ q Ψ)
back-* (skip θ) q (p ∷ Ψ) = back-* θ q Ψ

back-zero : ∀ {n n′} (θ : Thin n n′) → back θ zeroUsage ≡ zeroUsage
back-zero done     = refl
back-zero (keep θ) = cong (Zero ∷_) (back-zero θ)
back-zero (skip θ) = back-zero θ

back-single : ∀ {n n′} (θ : Thin n n′) (i : Fin n) → back θ (singleUse (⟦ θ ⟧θ i) One) ≡ singleUse i One
back-single (keep θ) zero    = cong (One ∷_) (back-zero θ)
back-single (keep θ) (suc i) = cong (Zero ∷_) (back-single θ i)
back-single (skip θ) i       = back-single θ i

back-mono : ∀ {n n′} (θ : Thin n n′) {Ψ Ψ′ : Usage n′} → Ψ ⊑ᵘ Ψ′ → back θ Ψ ⊑ᵘ back θ Ψ′
back-mono done     []        = []
back-mono (keep θ) (a ⊑∷ as) = a ⊑∷ back-mono θ as
back-mono (skip θ) (a ⊑∷ as) = back-mono θ as

back-id : ∀ {n} (Ψ : Usage n) → back (idθ n) Ψ ≡ Ψ
back-id []      = refl
back-id (q ∷ Ψ) = cong (q ∷_) (back-id Ψ)

pure⊑ : ∀ π → pure ⊑π π
pure⊑ pure = ⊑-pure
pure⊑ act  = ⊑-pa
pure⊑ eff  = ⊑-pe

module _ {m : ℕ} {Δ : KCtx m} where

  -- A variable's derivation is at its context type, and uses it.
  varTy : ∀ {n} {Γ : Ctx m n} {Ψ i A π} → Δ ⊩ Γ ⊢[ Ψ ] var i ∷ A ! π → A ≡ lookup Γ i
  varTy (⊢var i) = refl
  varTy (⊢sub-use _ d) = varTy d
  varTy (⊢sub-eff _ d) = varTy d

  varUse′ : ∀ {n} {Γ : Ctx m n} {Ψ i A π} → Δ ⊩ Γ ⊢[ Ψ ] var i ∷ A ! π → singleUse i One ⊑ᵘ Ψ
  varUse′ (⊢var i) = ⊑ᵘ-refl _
  varUse′ (⊢sub-use p d) = ⊑ᵘ-trans (varUse′ d) p
  varUse′ (⊢sub-eff _ d) = varUse′ d

  private
    ↑ : ∀ {n n′} → (Fin n → Fin n′) → Fin (suc n) → Fin (suc n′)
    ↑ ρ = ext {S = S} {m = m} ρ

    sum* : ∀ {n n′} (θ : Thin n n′) Ψ₁ q Ψ₂ → back θ Ψ₁ +ᵘ q *ᵘ back θ Ψ₂ ≡ back θ (Ψ₁ +ᵘ q *ᵘ Ψ₂)
    sum* θ Ψ₁ q Ψ₂ = sym (trans (back-+ θ Ψ₁ (q *ᵘ Ψ₂)) (cong (back θ Ψ₁ +ᵘ_) (back-* θ q Ψ₂)))

    *sum : ∀ {n n′} (θ : Thin n n′) q Ψ₁ Ψ₂ → q *ᵘ back θ Ψ₁ +ᵘ back θ Ψ₂ ≡ back θ (q *ᵘ Ψ₁ +ᵘ Ψ₂)
    *sum θ q Ψ₁ Ψ₂ = sym (trans (back-+ θ (q *ᵘ Ψ₁) Ψ₂) (cong (_+ᵘ back θ Ψ₂) (back-* θ q Ψ₁)))

  unren : ∀ {n n′} (θ : Thin n n′) (ρ : Fin n → Fin n′) → (∀ i → ⟦ θ ⟧θ i ≡ ρ i)
        → ∀ {Γ Γ′} → CThin θ Γ Γ′
        → ∀ {Ψ′ t A π} → Δ ⊩ Γ′ ⊢[ Ψ′ ] ren ρ t ∷ A ! π → Δ ⊩ Γ ⊢[ back θ Ψ′ ] t ∷ A ! π
  unren θ ρ h {Γ} {Γ′} c {t = var i} (⊢var _) = ⊢sub-use U (retype T (⊢var i))
    where
      T : lookup Γ i ≡ lookup Γ′ (ρ i)
      T = trans (sym (cthin-lookup c i)) (cong (lookup Γ′) (h i))
      U : singleUse i One ⊑ᵘ back θ (singleUse (ρ i) One)
      U = ⊑ᵘ-≡ (sym (trans (cong (λ j → back θ (singleUse j One)) (sym (h i))) (back-single θ i)))
  unren θ ρ h c {t = lam A q π t} (⊢lam le d) = ⊢lam le (unren (keep θ) (↑ ρ) (ext-hρ {m = m} θ ρ h) (ckeep c) d)
  unren θ ρ h c {t = app f x} (⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = q} df dx) =
    cast (sum* θ Ψ₁ q Ψ₂) (⊢app (unren θ ρ h c df) (unren θ ρ h c dx))
  unren θ ρ h c {t = let′ q e b} (⊢let {Ψ₁ = Ψ₁} {Ψ₂} d₁ d₂) =
    cast (sum* θ Ψ₂ q Ψ₁) (⊢let (unren θ ρ h c d₁) (unren (keep θ) (↑ ρ) (ext-hρ {m = m} θ ρ h) (ckeep c) d₂))
  unren θ ρ h c {t = unit} ⊢unit = cast (sym (back-zero θ)) ⊢unit
  unren θ ρ h c {t = pair a b} (⊢pair {Ψ₁ = Ψ₁} {Ψ₂} da db) =
    cast (sym (back-+ θ Ψ₁ Ψ₂)) (⊢pair (unren θ ρ h c da) (unren θ ρ h c db))
  unren θ ρ h c {t = fst p} (⊢fst d) = ⊢fst (unren θ ρ h c d)
  unren θ ρ h c {t = snd p} (⊢snd d) = ⊢snd (unren θ ρ h c d)
  unren θ ρ h c {t = inl B a} (⊢inl d) = ⊢inl (unren θ ρ h c d)
  unren θ ρ h c {t = inr A b} (⊢inr d) = ⊢inr (unren θ ρ h c d)
  unren θ ρ h c {t = case qℓ qr e l r} (⊢case {Ψs = Ψs} {Ψ} ds dl dr) =
    cast (sym (back-+ θ Ψs Ψ))
      (⊢case (unren θ ρ h c ds) (unren (keep θ) (↑ ρ) (ext-hρ {m = m} θ ρ h) (ckeep c) dl)
                                (unren (keep θ) (↑ ρ) (ext-hρ {m = m} θ ρ h) (ckeep c) dr))
  unren θ ρ h c {t = absurd A e} (⊢absurd d) = ⊢absurd (unren θ ρ h c d)
  unren θ ρ h c {t = roll F t} (⊢roll wf d) = ⊢roll wf (unren θ ρ h c d)
  unren θ ρ h c {t = fold F alg t} (⊢fold {Ψa = Ψa} {Ψt} wf da dt) =
    cast (*sum θ Many Ψa Ψt) (⊢fold wf (unren θ ρ h c da) (unren θ ρ h c dt))
  unren θ ρ h c {t = unfold F c′ a} (⊢unfold {Ψc = Ψc} {Ψs} wf dc da) =
    cast (*sum θ Many Ψc Ψs) (⊢unfold wf (unren θ ρ h c dc) (unren θ ρ h c da))
  unren θ ρ h c {t = out t} (⊢out wf d) = ⊢out wf (unren θ ρ h c d)
  unren θ ρ h c {t = iter f a} (⊢iter {Ψf = Ψf} {Ψs} df ds) =
    cast (*sum θ Many Ψf Ψs) (⊢iter (unren θ ρ h c df) (unren θ ρ h c ds))
  unren θ ρ h c {t = coerce A B t} (⊢coerce p d) = ⊢coerce p (unren θ ρ h c d)
  unren θ ρ h c {t = lit _} ⊢lit-int = cast (sym (back-zero θ)) ⊢lit-int
  unren θ ρ h c {t = lit _} ⊢lit-float = cast (sym (back-zero θ)) ⊢lit-float
  unren θ ρ h c {t = prim p t} (⊢prim .p d) = ⊢prim p (unren θ ρ h c d)
  unren θ ρ h c {t = sigop c′ t} (⊢sigop mem) = cast (sym (back-zero θ)) (⊢sigop mem)
  unren θ ρ h c {t = ref d τ} (⊢ref .d .τ r) = cast (sym (back-zero θ)) (⊢ref d τ r)
  -- the sub-rules, at every term
  {-# CATCHALL #-}
  unren θ ρ h c {t = t} (⊢sub-use p d) = ⊢sub-use (back-mono θ p) (unren θ ρ h c {t = t} d)
  {-# CATCHALL #-}
  unren θ ρ h c {t = t} (⊢sub-eff g d) = ⊢sub-eff g (unren θ ρ h c {t = t} d)

  -- Strengthening: `wk t` under a binder is `t`.
  str : ∀ {n} {Γ : Ctx m n} {X q Ψ t A π} → Δ ⊩ (Γ ▸ X) ⊢[ q ∷ Ψ ] wk t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π
  str {n} {Γ} {Ψ = Ψ} d = cast (back-id Ψ) (unren (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip (cid Γ)) d)
