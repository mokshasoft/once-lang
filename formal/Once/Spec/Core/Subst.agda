-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Subst — plan 0.102 phase B (D276): COMPOSITION IS DEFINED.
--
-- The typing substitution lemma, simultaneous: a substitution `σ` of PURE
-- terms (values, D250), row `i` typed at `Φ i`, sends a term typed at `Ψ` to
-- one typed at `Ψ ⋆ Φ` (`Once.Surface.GradeMatrix`). Each rule consumes one
-- law of the linear map `_⋆ Φ`: a variable selects its row, `app`/`let`/
-- `pair`/`case`/`fold`/`unfold` use `⋆-+` (and `⋆-*` for a scaled argument),
-- binders use `⋆-ext`, closed terms `⋆-zero`, and `⊢sub-use` — the reason the
-- lemma is exact — uses `⋆-mono`.
--
-- Single substitution (`subst-⊢`, the field of `TermModel`) is the instance
-- `single u` with the identity matrix on the remaining variables.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Contract using (ISig)

module Once.Spec.Core.Subst {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Once.Type using (Type; Quantity; Zero; One; Many; Purity; pure)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; _,_; lookup; Usage; []; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_)
open import Once.Surface.Properties using (+ᵘ-comm)
open import Once.Surface.GradeMatrix using (Grades; _⋆_; ⋆-zero; ⋆-+; ⋆-*; ⋆-single; ⋆-mono; extΦ; ⋆-ext; ⋆-id)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
open import Once.Spec.Core.DerivedTyping S using (wk-⊢′)

------------------------------------------------------------------------
-- Typed substitutions
------------------------------------------------------------------------

-- `σ` sends `Γ` to `Δ`, row `i` used at `Φ i`; its terms are values.
-- (A record, so that its indices are inferable from a row bundle.)
record SubTy {n m} (Δ : Ctx m) (σ : Sub n m) (Γ : Ctx n) (Φ : Grades n m) : Set where
  constructor rows
  field row : ∀ i → Δ ⊢[ Φ i ] σ i ∷ lookup Γ i ! pure
open SubTy

-- The rows after the first.
tailᴿ : ∀ {n m} {Δ : Ctx m} {σ : Sub (suc n) m} {Γ : Ctx n} {A : Type} {r : Quantity} {Φ : Grades (suc n) m}
      → SubTy Δ σ (Γ , A ^ r) Φ → SubTy Δ (λ i → σ (suc i)) Γ (λ i → Φ (suc i))
tailᴿ h = rows (λ i → row h (suc i))

-- A usage transport (its meaning is a transport of the environment).
retype : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {t A π} → Ψ ≡ Ψ′ → Γ ⊢[ Ψ ] t ∷ A ! π → Γ ⊢[ Ψ′ ] t ∷ A ! π
retype refl d = d

-- Under a binder: the new variable is itself, the old rows are weakened.
ext-ty : ∀ {n m} {Δ : Ctx m} {σ : Sub n m} {Γ : Ctx n} {Φ : Grades n m} (A : Type)
       → SubTy Δ σ Γ Φ → SubTy (Δ , A) (extS σ) (Γ , A) (extΦ Φ)
ext-ty A h = rows (ext-row A h)
  where
    ext-row : ∀ {n m} {Δ : Ctx m} {σ : Sub n m} {Γ : Ctx n} {Φ : Grades n m} (A : Type)
            → SubTy Δ σ Γ Φ → ∀ i → (Δ , A) ⊢[ extΦ Φ i ] extS σ i ∷ lookup (Γ , A) i ! pure
    ext-row A h zero    = ⊢var zero
    ext-row A h (suc i) = wk-⊢′ A (row h i)

------------------------------------------------------------------------
-- THE SUBSTITUTION LEMMA
------------------------------------------------------------------------

sub-⊢ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ : Usage n} {t A π} {σ : Sub n m} {Φ : Grades n m}
      → Γ ⊢[ Ψ ] t ∷ A ! π → SubTy Δ σ Γ Φ → Δ ⊢[ Ψ ⋆ Φ ] sub σ t ∷ A ! π
sub-⊢ {Φ = Φ} (⊢var i) h = retype (sym (⋆-single i Φ)) (row h i)
sub-⊢ {Φ = Φ} (⊢lam {Ψ = Ψ} {q' = q'} {A = A} le d) h =
  ⊢lam le (retype (⋆-ext q' Ψ Φ) (sub-⊢ d (ext-ty A h)))
sub-⊢ {Φ = Φ} (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = q} df dx) h =
  retype (sym (trans (⋆-+ Ψ₁ (q *ᵘ Ψ₂) Φ) (cong ((Ψ₁ ⋆ Φ) +ᵘ_) (⋆-* q Ψ₂ Φ))))
         (⊢app (sub-⊢ df h) (sub-⊢ dx h))
sub-⊢ {Φ = Φ} (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = q} {A = A} de db) h =
  retype (sym (trans (⋆-+ Ψ₂ (q *ᵘ Ψ₁) Φ) (cong ((Ψ₂ ⋆ Φ) +ᵘ_) (⋆-* q Ψ₁ Φ))))
         (⊢let (sub-⊢ de h) (retype (⋆-ext q Ψ₂ Φ) (sub-⊢ db (ext-ty A h))))
sub-⊢ {Φ = Φ} ⊢unit h = retype (sym (⋆-zero Φ)) ⊢unit
sub-⊢ {Φ = Φ} (⊢pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} da db) h =
  retype (sym (⋆-+ Ψ₁ Ψ₂ Φ)) (⊢pair (sub-⊢ da h) (sub-⊢ db h))
sub-⊢ (⊢fst d) h = ⊢fst (sub-⊢ d h)
sub-⊢ (⊢snd d) h = ⊢snd (sub-⊢ d h)
sub-⊢ (⊢inl d) h = ⊢inl (sub-⊢ d h)
sub-⊢ (⊢inr d) h = ⊢inr (sub-⊢ d h)
sub-⊢ {Φ = Φ} (⊢case {Ψs = Ψs} {Ψ = Ψ} {qℓ = qℓ} {qr = qr} {A = A} {B = B} ds dl dr) h =
  retype (sym (⋆-+ Ψs Ψ Φ))
         (⊢case (sub-⊢ ds h) (retype (⋆-ext qℓ Ψ Φ) (sub-⊢ dl (ext-ty A h)))
                             (retype (⋆-ext qr Ψ Φ) (sub-⊢ dr (ext-ty B h))))
sub-⊢ (⊢absurd d) h = ⊢absurd (sub-⊢ d h)
sub-⊢ (⊢roll wf d) h = ⊢roll wf (sub-⊢ d h)
sub-⊢ {Φ = Φ} (⊢fold {Ψa = Ψa} {Ψt = Ψt} wf da dt) h =
  retype (sym (⋆-+ Ψa Ψt Φ)) (⊢fold wf (sub-⊢ da h) (sub-⊢ dt h))
sub-⊢ {Φ = Φ} (⊢unfold {Ψc = Ψc} {Ψs = Ψs} wf dc ds) h =
  retype (sym (⋆-+ Ψc Ψs Φ)) (⊢unfold wf (sub-⊢ dc h) (sub-⊢ ds h))
sub-⊢ (⊢out wf d) h = ⊢out wf (sub-⊢ d h)
sub-⊢ (⊢coerce p d) h = ⊢coerce p (sub-⊢ d h)
sub-⊢ {Φ = Φ} ⊢lit-int h = retype (sym (⋆-zero Φ)) ⊢lit-int
sub-⊢ {Φ = Φ} ⊢lit-float h = retype (sym (⋆-zero Φ)) ⊢lit-float
sub-⊢ (⊢prim p d) h = ⊢prim p (sub-⊢ d h)
sub-⊢ {Φ = Φ} (⊢sigop c k hf rf m) h = retype (sym (⋆-zero Φ)) (⊢sigop c k hf rf m)
sub-⊢ {Φ = Φ} (⊢ref d τ r) h = retype (sym (⋆-zero Φ)) (⊢ref d τ r)
sub-⊢ (⊢sub-eff g d) h = ⊢sub-eff g (sub-⊢ d h)
sub-⊢ {Φ = Φ} (⊢sub-use p d) h = ⊢sub-use (⋆-mono Φ p) (sub-⊢ d h)

------------------------------------------------------------------------
-- Single substitution: `t [ u ]`
------------------------------------------------------------------------

-- The matrix of `single u`: row 0 is `u`'s usage, the rest is the identity.
singleΦ : ∀ {n} → Usage n → Grades (suc n) n
singleΦ Ψᵤ zero    = Ψᵤ
singleΦ Ψᵤ (suc i) = singleUse i One

single-ty : ∀ {n} {Γ : Ctx n} {Ψᵤ : Usage n} {A u} → Γ ⊢[ Ψᵤ ] u ∷ A ! pure → SubTy Γ (single u) (Γ , A) (singleΦ Ψᵤ)
single-ty {Γ = Γ} {Ψᵤ = Ψᵤ} {A = A} {u = u} du = rows r
  where
    r : ∀ i → Γ ⊢[ singleΦ Ψᵤ i ] single u i ∷ lookup (Γ , A) i ! pure
    r zero    = du
    r (suc i) = ⊢var i

single-usage : ∀ {n} (q : Quantity) (Ψₜ Ψᵤ : Usage n) → (q ∷ Ψₜ) ⋆ singleΦ Ψᵤ ≡ Ψₜ +ᵘ q *ᵘ Ψᵤ
single-usage q Ψₜ Ψᵤ = trans (cong ((q *ᵘ Ψᵤ) +ᵘ_) (⋆-id Ψₜ)) (+ᵘ-comm (q *ᵘ Ψᵤ) Ψₜ)

subst-⊢ : ∀ {n} {Γ : Ctx n} {Ψₜ Ψᵤ : Usage n} {q : Quantity} {π : Purity} {A B : Type}
            {t : Tm (suc n)} {u : Tm n}
        → (Γ , A) ⊢[ q ∷ Ψₜ ] t ∷ B ! π
        → Γ ⊢[ Ψᵤ ] u ∷ A ! pure
        → Γ ⊢[ Ψₜ +ᵘ q *ᵘ Ψᵤ ] t [ u ] ∷ B ! π
subst-⊢ {Ψₜ = Ψₜ} {Ψᵤ} {q} dt du = retype (single-usage q Ψₜ Ψᵤ) (sub-⊢ dt (single-ty du))
