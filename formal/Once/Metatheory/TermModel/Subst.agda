{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.TermModel.Subst — renaming and substitution are typed
-- (`Spec.Metatheory.TermModel.subst-⊢`).
--
-- A renaming along a thinning (variables kept, others inserted unused)
-- keeps a term's type and moves its usage; a substitution whose terms are
-- pure and typed keeps a term's type, and its usage is the usages of the
-- replacements, counted by the term's (`Usage._·ᵐ_`). Where the usage the
-- rule computes and the one the lemma states differ only by the semiring's
-- laws, `⊢sub-use` at an equality bridges them.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.TermModel.Subst (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; pure; _+q_; _*q_)
open import Once.Spec.Type using (Ty; KCtx)
open import Once.Spec.Context
  using (Ctx; ∅; _▸_; lookup; Usage; []; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊑∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.TermModel.Usage

------------------------------------------------------------------------
-- Thinnings
------------------------------------------------------------------------

data Thin : ℕ → ℕ → Set where
  done : Thin 0 0
  keep : ∀ {n n′} → Thin n n′ → Thin (suc n) (suc n′)
  skip : ∀ {n n′} → Thin n n′ → Thin n (suc n′)

⟦_⟧θ : ∀ {n n′} → Thin n n′ → Fin n → Fin n′
⟦ keep θ ⟧θ zero    = zero
⟦ keep θ ⟧θ (suc i) = suc (⟦ θ ⟧θ i)
⟦ skip θ ⟧θ i       = suc (⟦ θ ⟧θ i)

idθ : ∀ n → Thin n n
idθ zero    = done
idθ (suc n) = keep (idθ n)

idθ-id : ∀ {n} (i : Fin n) → ⟦ idθ n ⟧θ i ≡ i
idθ-id zero    = refl
idθ-id (suc i) = cong suc (idθ-id i)

-- A usage, moved along a thinning: the inserted variables are unused.
infixr 75 _θ*_
_θ*_ : ∀ {n n′} → Thin n n′ → Usage n → Usage n′
done   θ* []      = []
keep θ θ* (q ∷ Ψ) = q ∷ (θ θ* Ψ)
skip θ θ* Ψ       = Zero ∷ (θ θ* Ψ)

module _ {m : ℕ} where
  data CThin : ∀ {n n′} → Thin n n′ → Ctx m n → Ctx m n′ → Set where
    cdone : CThin done ∅ ∅
    ckeep : ∀ {n n′} {θ : Thin n n′} {Γ Γ′ A} → CThin θ Γ Γ′ → CThin (keep θ) (Γ ▸ A) (Γ′ ▸ A)
    cskip : ∀ {n n′} {θ : Thin n n′} {Γ Γ′ A} → CThin θ Γ Γ′ → CThin (skip θ) Γ (Γ′ ▸ A)

  cthin-lookup : ∀ {n n′} {θ : Thin n n′} {Γ Γ′} → CThin θ Γ Γ′ → ∀ i → lookup Γ′ (⟦ θ ⟧θ i) ≡ lookup Γ i
  cthin-lookup (ckeep c) zero    = refl
  cthin-lookup (ckeep c) (suc i) = cthin-lookup c i
  cthin-lookup (cskip c) i       = cthin-lookup c i

  cid : ∀ {n} (Γ : Ctx m n) → CThin (idθ n) Γ Γ
  cid ∅       = cdone
  cid (Γ ▸ A) = ckeep (cid Γ)

θ*-id : ∀ {n} (Ψ : Usage n) → idθ n θ* Ψ ≡ Ψ
θ*-id []      = refl
θ*-id (q ∷ Ψ) = cong (q ∷_) (θ*-id Ψ)

θ*-zero : ∀ {n n′} (θ : Thin n n′) → θ θ* zeroUsage ≡ zeroUsage
θ*-zero done     = refl
θ*-zero (keep θ) = cong (Zero ∷_) (θ*-zero θ)
θ*-zero (skip θ) = cong (Zero ∷_) (θ*-zero θ)

θ*-+ : ∀ {n n′} (θ : Thin n n′) (Ψ Ψ′ : Usage n) → θ θ* (Ψ +ᵘ Ψ′) ≡ θ θ* Ψ +ᵘ θ θ* Ψ′
θ*-+ done     []      []        = refl
θ*-+ (keep θ) (p ∷ Ψ) (q ∷ Ψ′) = cong (p +q q ∷_) (θ*-+ θ Ψ Ψ′)
θ*-+ (skip θ) Ψ       Ψ′        = cong (Zero ∷_) (θ*-+ θ Ψ Ψ′)

θ*-* : ∀ {n n′} (θ : Thin n n′) q (Ψ : Usage n) → θ θ* (q *ᵘ Ψ) ≡ q *ᵘ (θ θ* Ψ)
θ*-* done     q []      = refl
θ*-* (keep θ) q (p ∷ Ψ) = cong (q *q p ∷_) (θ*-* θ q Ψ)
θ*-* (skip θ) q Ψ       = cong₂ _∷_ (sym (*q-zeroʳ q)) (θ*-* θ q Ψ)

θ*-single : ∀ {n n′} (θ : Thin n n′) (i : Fin n) → θ θ* singleUse i One ≡ singleUse (⟦ θ ⟧θ i) One
θ*-single (keep θ) zero    = cong (One ∷_) (θ*-zero θ)
θ*-single (keep θ) (suc i) = cong (Zero ∷_) (θ*-single θ i)
θ*-single (skip θ) i       = cong (Zero ∷_) (θ*-single θ i)

θ*-mono : ∀ {n n′} (θ : Thin n n′) {Ψ Ψ′ : Usage n} → Ψ ⊑ᵘ Ψ′ → θ θ* Ψ ⊑ᵘ θ θ* Ψ′
θ*-mono done     []        = []
θ*-mono (keep θ) (a ⊑∷ as) = a ⊑∷ θ*-mono θ as
θ*-mono (skip θ) as        = ≤q-refl Zero ⊑∷ θ*-mono θ as

------------------------------------------------------------------------
-- Renaming is typed
------------------------------------------------------------------------

-- Renaming under a binder, along the kept thinning.
ext-hρ : ∀ {m n n′} (θ : Thin n n′) (ρ : Fin n → Fin n′) → (∀ i → ⟦ θ ⟧θ i ≡ ρ i) → ∀ i → ⟦ keep θ ⟧θ i ≡ ext {S = S} {m = m} ρ i
ext-hρ θ ρ h zero    = refl
ext-hρ θ ρ h (suc i) = cong suc (h i)

module _ {m : ℕ} {Δ : KCtx m} where

  -- A usage that equals the one a rule computes.
  cast : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ t A π} → Ψ ≡ Ψ′ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ A ! π
  cast e d = ⊢sub-use (⊑ᵘ-≡ e) d

  -- A type that equals the one a rule computes.
  retype : ∀ {n} {Γ : Ctx m n} {Ψ t A A′ π} → A ≡ A′ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A′ ! π
  retype refl d = d

  -- A kept variable, renamed.
  varAt : ∀ {n n′} {θ : Thin n n′} {Γ Γ′} → CThin θ Γ Γ′ → ∀ i {j} → ⟦ θ ⟧θ i ≡ j
        → Δ ⊩ Γ′ ⊢[ θ θ* singleUse i One ] var j ∷ lookup Γ i ! pure
  varAt {θ = θ} c i refl = cast (sym (θ*-single θ i)) (retype (cthin-lookup c i) (⊢var (⟦ θ ⟧θ i)))

  ren-⊢ : ∀ {n n′} (θ : Thin n n′) (ρ : Fin n → Fin n′) → (∀ i → ⟦ θ ⟧θ i ≡ ρ i)
        → ∀ {Γ Γ′} → CThin θ Γ Γ′
        → ∀ {Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ′ ⊢[ θ θ* Ψ ] ren ρ t ∷ A ! π
  ren-⊢ θ ρ h c (⊢var i) = varAt c i (h i)
  ren-⊢ θ ρ h c (⊢lam le d) = ⊢lam le (ren-⊢ (keep θ) (ext {S = S} {m = m} ρ) (ext-hρ {m = m} θ ρ h) (ckeep c) d)
  ren-⊢ θ ρ h c (⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = q} df dx) =
    cast (sym (trans (θ*-+ θ Ψ₁ (q *ᵘ Ψ₂)) (cong (θ θ* Ψ₁ +ᵘ_) (θ*-* θ q Ψ₂))))
      (⊢app (ren-⊢ θ ρ h c df) (ren-⊢ θ ρ h c dx))
  ren-⊢ θ ρ h c (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = q} d₁ d₂) =
    cast (sym (trans (θ*-+ θ Ψ₂ (q *ᵘ Ψ₁)) (cong (θ θ* Ψ₂ +ᵘ_) (θ*-* θ q Ψ₁))))
      (⊢let (ren-⊢ θ ρ h c d₁) (ren-⊢ (keep θ) (ext {S = S} {m = m} ρ) (ext-hρ {m = m} θ ρ h) (ckeep c) d₂))
  ren-⊢ θ ρ h c ⊢unit = cast (sym (θ*-zero θ)) ⊢unit
  ren-⊢ θ ρ h c (⊢pair {Ψ₁ = Ψ₁} {Ψ₂} da db) = cast (sym (θ*-+ θ Ψ₁ Ψ₂)) (⊢pair (ren-⊢ θ ρ h c da) (ren-⊢ θ ρ h c db))
  ren-⊢ θ ρ h c (⊢fst d) = ⊢fst (ren-⊢ θ ρ h c d)
  ren-⊢ θ ρ h c (⊢snd d) = ⊢snd (ren-⊢ θ ρ h c d)
  ren-⊢ θ ρ h c (⊢inl d) = ⊢inl (ren-⊢ θ ρ h c d)
  ren-⊢ θ ρ h c (⊢inr d) = ⊢inr (ren-⊢ θ ρ h c d)
  ren-⊢ θ ρ h c (⊢case {Ψs = Ψs} {Ψ} ds dl dr) =
    cast (sym (θ*-+ θ Ψs Ψ))
      (⊢case (ren-⊢ θ ρ h c ds) (ren-⊢ (keep θ) (ext {S = S} {m = m} ρ) (ext-hρ {m = m} θ ρ h) (ckeep c) dl)
                                 (ren-⊢ (keep θ) (ext {S = S} {m = m} ρ) (ext-hρ {m = m} θ ρ h) (ckeep c) dr))
  ren-⊢ θ ρ h c (⊢absurd d) = ⊢absurd (ren-⊢ θ ρ h c d)
  ren-⊢ θ ρ h c (⊢roll wf d) = ⊢roll wf (ren-⊢ θ ρ h c d)
  ren-⊢ θ ρ h c (⊢fold {Ψa = Ψa} {Ψt} wf da dt) =
    cast (sym (trans (θ*-+ θ (Many *ᵘ Ψa) Ψt) (cong (_+ᵘ θ θ* Ψt) (θ*-* θ Many Ψa))))
      (⊢fold wf (ren-⊢ θ ρ h c da) (ren-⊢ θ ρ h c dt))
  ren-⊢ θ ρ h c (⊢unfold {Ψc = Ψc} {Ψs} wf dc da) =
    cast (sym (trans (θ*-+ θ (Many *ᵘ Ψc) Ψs) (cong (_+ᵘ θ θ* Ψs) (θ*-* θ Many Ψc))))
      (⊢unfold wf (ren-⊢ θ ρ h c dc) (ren-⊢ θ ρ h c da))
  ren-⊢ θ ρ h c (⊢out wf d) = ⊢out wf (ren-⊢ θ ρ h c d)
  ren-⊢ θ ρ h c (⊢iter {Ψf = Ψf} {Ψs} df ds) =
    cast (sym (trans (θ*-+ θ (Many *ᵘ Ψf) Ψs) (cong (_+ᵘ θ θ* Ψs) (θ*-* θ Many Ψf))))
      (⊢iter (ren-⊢ θ ρ h c df) (ren-⊢ θ ρ h c ds))
  ren-⊢ θ ρ h c (⊢coerce p d) = ⊢coerce p (ren-⊢ θ ρ h c d)
  ren-⊢ θ ρ h c ⊢lit-int = cast (sym (θ*-zero θ)) ⊢lit-int
  ren-⊢ θ ρ h c ⊢lit-float = cast (sym (θ*-zero θ)) ⊢lit-float
  ren-⊢ θ ρ h c (⊢prim p d) = ⊢prim p (ren-⊢ θ ρ h c d)
  ren-⊢ θ ρ h c (⊢sigop mem) = cast (sym (θ*-zero θ)) (⊢sigop mem)
  ren-⊢ θ ρ h c (⊢ref d τ r) = cast (sym (θ*-zero θ)) (⊢ref d τ r)
  ren-⊢ θ ρ h c (⊢sub-use p d) = ⊢sub-use (θ*-mono θ p) (ren-⊢ θ ρ h c d)
  ren-⊢ θ ρ h c (⊢sub-eff g d) = ⊢sub-eff g (ren-⊢ θ ρ h c d)

  -- Weakening: one more variable, unused.
  wk-⊢ : ∀ {n} {Γ : Ctx m n} {B Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ (Γ ▸ B) ⊢[ Zero ∷ Ψ ] wk t ∷ A ! π
  wk-⊢ {n} {Γ} {Ψ = Ψ} d =
    cast (cong (Zero ∷_) (θ*-id Ψ)) (ren-⊢ (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip (cid Γ)) d)

------------------------------------------------------------------------
-- Substitution is typed
------------------------------------------------------------------------

  -- A substitution of pure, typed terms, with the usage of each.
  record TSub {n n′} (Γ : Ctx m n) (Γ′ : Ctx m n′) : Set where
    field
      term  : Fin n′ → Tm S m n
      usage : Fin n′ → Usage n
      typed : ∀ i → Δ ⊩ Γ ⊢[ usage i ] term i ∷ lookup Γ′ i ! pure
  open TSub

  extsT : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} {A} → TSub Γ Γ′ → TSub (Γ ▸ A) (Γ′ ▸ A)
  term  (extsT σ) = exts (term σ)
  usage (extsT σ) zero    = singleUse zero One
  usage (extsT σ) (suc i) = Zero ∷ usage σ i
  typed (extsT σ) zero    = ⊢var zero
  typed (extsT σ) (suc i) = wk-⊢ (typed σ i)

  ·ᵐ-wk : ∀ {n n′} (Ψ : Usage n′) (Φ : Fin n′ → Usage n) → Ψ ·ᵐ (λ i → Zero ∷ Φ i) ≡ Zero ∷ (Ψ ·ᵐ Φ)
  ·ᵐ-wk []      Φ = refl
  ·ᵐ-wk (q ∷ Ψ) Φ =
    trans (cong ((q *q Zero ∷ q *ᵘ Φ zero) +ᵘ_) (·ᵐ-wk Ψ (λ i → Φ (suc i))))
          (cong (_∷ (q *ᵘ Φ zero +ᵘ Ψ ·ᵐ (λ i → Φ (suc i)))) (trans (+q-identityʳ (q *q Zero)) (*q-zeroʳ q)))

  ·ᵐ-exts : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} {A} (σ : TSub Γ Γ′) q (Ψ : Usage n′)
          → (q ∷ Ψ) ·ᵐ usage (extsT {A = A} σ) ≡ q ∷ (Ψ ·ᵐ usage σ)
  ·ᵐ-exts σ q Ψ =
    trans (cong ((q *q One ∷ q *ᵘ zeroUsage) +ᵘ_) (·ᵐ-wk Ψ (usage σ)))
          (cong₂ _∷_ (trans (+q-identityʳ (q *q One)) (*q-identityʳ q))
                     (trans (cong (_+ᵘ (Ψ ·ᵐ usage σ)) (*ᵘ-zero q)) (+ᵘ-identityˡ (Ψ ·ᵐ usage σ))))

  sub-⊢ : ∀ {n n′} {Γ : Ctx m n} {Γ′ : Ctx m n′} (σ : TSub Γ Γ′)
        → ∀ {Ψ t A π} → Δ ⊩ Γ′ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ·ᵐ usage σ ] subₜ (term σ) t ∷ A ! π
  sub-⊢ σ (⊢var i) = cast (sym (·ᵐ-single i (usage σ))) (typed σ i)
  sub-⊢ σ (⊢lam {Ψ = Ψ} {q′ = q′} {A = A} le d) =
    ⊢lam le (cast (·ᵐ-exts {A = A} σ q′ Ψ) (sub-⊢ (extsT σ) d))
  sub-⊢ σ (⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = q} df dx) =
    cast (sym (trans (·ᵐ-+ Ψ₁ (q *ᵘ Ψ₂) (usage σ)) (cong (Ψ₁ ·ᵐ usage σ +ᵘ_) (·ᵐ-* q Ψ₂ (usage σ)))))
      (⊢app (sub-⊢ σ df) (sub-⊢ σ dx))
  sub-⊢ σ (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = q} {A = A} d₁ d₂) =
    cast (sym (trans (·ᵐ-+ Ψ₂ (q *ᵘ Ψ₁) (usage σ)) (cong (Ψ₂ ·ᵐ usage σ +ᵘ_) (·ᵐ-* q Ψ₁ (usage σ)))))
      (⊢let (sub-⊢ σ d₁) (cast (·ᵐ-exts {A = A} σ q Ψ₂) (sub-⊢ (extsT σ) d₂)))
  sub-⊢ σ ⊢unit = cast (sym (·ᵐ-zero (usage σ))) ⊢unit
  sub-⊢ σ (⊢pair {Ψ₁ = Ψ₁} {Ψ₂} da db) = cast (sym (·ᵐ-+ Ψ₁ Ψ₂ (usage σ))) (⊢pair (sub-⊢ σ da) (sub-⊢ σ db))
  sub-⊢ σ (⊢fst d) = ⊢fst (sub-⊢ σ d)
  sub-⊢ σ (⊢snd d) = ⊢snd (sub-⊢ σ d)
  sub-⊢ σ (⊢inl d) = ⊢inl (sub-⊢ σ d)
  sub-⊢ σ (⊢inr d) = ⊢inr (sub-⊢ σ d)
  sub-⊢ σ (⊢case {Ψs = Ψs} {Ψ} {qℓ} {qr} {A = A} {B} ds dl dr) =
    cast (sym (·ᵐ-+ Ψs Ψ (usage σ)))
      (⊢case (sub-⊢ σ ds) (cast (·ᵐ-exts {A = A} σ qℓ Ψ) (sub-⊢ (extsT σ) dl))
                          (cast (·ᵐ-exts {A = B} σ qr Ψ) (sub-⊢ (extsT σ) dr)))
  sub-⊢ σ (⊢absurd d) = ⊢absurd (sub-⊢ σ d)
  sub-⊢ σ (⊢roll wf d) = ⊢roll wf (sub-⊢ σ d)
  sub-⊢ σ (⊢fold {Ψa = Ψa} {Ψt} wf da dt) =
    cast (sym (trans (·ᵐ-+ (Many *ᵘ Ψa) Ψt (usage σ)) (cong (_+ᵘ Ψt ·ᵐ usage σ) (·ᵐ-* Many Ψa (usage σ)))))
      (⊢fold wf (sub-⊢ σ da) (sub-⊢ σ dt))
  sub-⊢ σ (⊢unfold {Ψc = Ψc} {Ψs} wf dc da) =
    cast (sym (trans (·ᵐ-+ (Many *ᵘ Ψc) Ψs (usage σ)) (cong (_+ᵘ Ψs ·ᵐ usage σ) (·ᵐ-* Many Ψc (usage σ)))))
      (⊢unfold wf (sub-⊢ σ dc) (sub-⊢ σ da))
  sub-⊢ σ (⊢out wf d) = ⊢out wf (sub-⊢ σ d)
  sub-⊢ σ (⊢iter {Ψf = Ψf} {Ψs} df ds) =
    cast (sym (trans (·ᵐ-+ (Many *ᵘ Ψf) Ψs (usage σ)) (cong (_+ᵘ Ψs ·ᵐ usage σ) (·ᵐ-* Many Ψf (usage σ)))))
      (⊢iter (sub-⊢ σ df) (sub-⊢ σ ds))
  sub-⊢ σ (⊢coerce p d) = ⊢coerce p (sub-⊢ σ d)
  sub-⊢ σ ⊢lit-int = cast (sym (·ᵐ-zero (usage σ))) ⊢lit-int
  sub-⊢ σ ⊢lit-float = cast (sym (·ᵐ-zero (usage σ))) ⊢lit-float
  sub-⊢ σ (⊢prim p d) = ⊢prim p (sub-⊢ σ d)
  sub-⊢ σ (⊢sigop mem) = cast (sym (·ᵐ-zero (usage σ))) (⊢sigop mem)
  sub-⊢ σ (⊢ref d τ r) = cast (sym (·ᵐ-zero (usage σ))) (⊢ref d τ r)
  sub-⊢ σ (⊢sub-use p d) = ⊢sub-use (·ᵐ-mono (usage σ) p) (sub-⊢ σ d)
  sub-⊢ σ (⊢sub-eff g d) = ⊢sub-eff g (sub-⊢ σ d)

  -- The first variable replaced by a pure term.
  single : ∀ {n} {Γ : Ctx m n} {A Ψᵤ u} → Δ ⊩ Γ ⊢[ Ψᵤ ] u ∷ A ! pure → TSub Γ (Γ ▸ A)
  term  (single {u = u} du) zero    = u
  term  (single du) (suc i) = var i
  usage (single {Ψᵤ = Ψᵤ} du) zero = Ψᵤ
  usage (single du) (suc i) = singleUse i One
  typed (single du) zero    = du
  typed (single du) (suc i) = ⊢var i

  ·ᵐ-id : ∀ {n} (Ψ : Usage n) → Ψ ·ᵐ (λ i → singleUse i One) ≡ Ψ
  ·ᵐ-id []      = refl
  ·ᵐ-id (q ∷ Ψ) =
    trans (cong (q *ᵘ (One ∷ zeroUsage) +ᵘ_) (trans (·ᵐ-wk Ψ (λ i → singleUse i One)) (cong (Zero ∷_) (·ᵐ-id Ψ))))
          (cong₂ _∷_ (trans (+q-identityʳ (q *q One)) (*q-identityʳ q))
                     (trans (cong (_+ᵘ Ψ) (*ᵘ-zero q)) (+ᵘ-identityˡ Ψ)))

  -- Substitution only looks at the terms it substitutes.
  exts-cong : ∀ {n n′} {σ σ′ : Fin n → Tm S m n′} → (∀ i → σ i ≡ σ′ i) → ∀ i → exts σ i ≡ exts σ′ i
  exts-cong h zero    = refl
  exts-cong h (suc i) = cong wk (h i)

  subₜ-cong : ∀ {n n′} {σ σ′ : Fin n → Tm S m n′} → (∀ i → σ i ≡ σ′ i) → ∀ t → subₜ σ t ≡ subₜ σ′ t
  subₜ-cong h (var i)            = h i
  subₜ-cong h (lam A q π t)      = cong (lam A q π) (subₜ-cong (exts-cong h) t)
  subₜ-cong h (app f x)          = cong₂ app (subₜ-cong h f) (subₜ-cong h x)
  subₜ-cong h (let′ q e b)       = cong₂ (let′ q) (subₜ-cong h e) (subₜ-cong (exts-cong h) b)
  subₜ-cong h unit               = refl
  subₜ-cong h (pair a b)         = cong₂ pair (subₜ-cong h a) (subₜ-cong h b)
  subₜ-cong h (fst p)            = cong fst (subₜ-cong h p)
  subₜ-cong h (snd p)            = cong snd (subₜ-cong h p)
  subₜ-cong h (inl B a)          = cong (inl B) (subₜ-cong h a)
  subₜ-cong h (inr A b)          = cong (inr A) (subₜ-cong h b)
  subₜ-cong h (case qℓ qr e l r) =
    cong₂ (λ x y → x y) (cong₂ (case qℓ qr) (subₜ-cong h e) (subₜ-cong (exts-cong h) l)) (subₜ-cong (exts-cong h) r)
  subₜ-cong h (absurd A e)       = cong (absurd A) (subₜ-cong h e)
  subₜ-cong h (roll F t)         = cong (roll F) (subₜ-cong h t)
  subₜ-cong h (fold F a t)       = cong₂ (fold F) (subₜ-cong h a) (subₜ-cong h t)
  subₜ-cong h (unfold F c a)     = cong₂ (unfold F) (subₜ-cong h c) (subₜ-cong h a)
  subₜ-cong h (out t)            = cong out (subₜ-cong h t)
  subₜ-cong h (iter f a)         = cong₂ iter (subₜ-cong h f) (subₜ-cong h a)
  subₜ-cong h (coerce A B t)     = cong (coerce A B) (subₜ-cong h t)
  subₜ-cong h (lit l)            = refl
  subₜ-cong h (prim p t)         = cong (prim p) (subₜ-cong h t)
  subₜ-cong h (sigop c t)        = refl
  subₜ-cong h (ref d τ)          = refl

  -- The usage and the term `subst-⊢` reads the substitution's result at.
  single-usage : ∀ {n} {Γ : Ctx m n} {A Ψᵤ u} (du : Δ ⊩ Γ ⊢[ Ψᵤ ] u ∷ A ! pure) (q : Quantity) (Ψₜ : Usage n)
               → (q ∷ Ψₜ) ·ᵐ usage (single du) ≡ Ψₜ +ᵘ q *ᵘ Ψᵤ
  single-usage {Ψᵤ = Ψᵤ} du q Ψₜ = trans (+ᵘ-comm (q *ᵘ Ψᵤ) (Ψₜ ·ᵐ _)) (cong (_+ᵘ q *ᵘ Ψᵤ) (·ᵐ-id Ψₜ))

  single-term : ∀ {n} {Γ : Ctx m n} {A Ψᵤ u} (du : Δ ⊩ Γ ⊢[ Ψᵤ ] u ∷ A ! pure) (t : Tm S m (suc n))
              → subₜ (term (single du)) t ≡ t [ u ]
  single-term du t = subₜ-cong (λ { zero → refl ; (suc i) → refl }) t

  -- The typing of `t [ u ]` the term model states: the substitution, at the
  -- term `_[_]` builds.
  subst-⊢ : ∀ {n} {Γ : Ctx m n} {Ψₜ Ψᵤ q π A B t u}
          → Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψₜ ] t ∷ B ! π
          → Δ ⊩ Γ ⊢[ Ψᵤ ] u ∷ A ! pure
          → Δ ⊩ Γ ⊢[ Ψₜ +ᵘ q *ᵘ Ψᵤ ] t [ u ] ∷ B ! π
  subst-⊢ {Ψₜ = Ψₜ} {Ψᵤ} {q} {t = t} dt du =
    subst (λ x → Δ ⊩ _ ⊢[ Ψₜ +ᵘ q *ᵘ Ψᵤ ] x ∷ _ ! _) (single-term du t)
      (cast (single-usage du q Ψₜ) (sub-⊢ (single du) dt))
