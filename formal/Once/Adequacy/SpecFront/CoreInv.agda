-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.CoreInv — reading a Spec core typing back (plan
-- 0.121 §3.6, F5).
--
-- The Spec's surface rules leave linearity to the core typing of the term
-- they name. To check a source with the compiler's rules, which count usage
-- as they go, the usage a core typing gives each part of the term is read
-- back: a typing of a former is its rule's typing under a stack of
-- subsumptions, so each part is typed at a usage the whole one bounds
-- (`inv-*`). A term moved under a binder by weakening is typed without it
-- (`strengthen`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
import Once.Spec.Core.Syntax as SC
import Once.Spec.Type as ST

module Once.Adequacy.SpecFront.CoreInv (Σ : Signature) {s : ℕ} (S : SC.Defs s) {m : ℕ} {Δ : ST.KCtx m} where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; mk-kind; _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω; _+q_; _*q_)
open import Once.Spec.Type using (Ty; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F)
open import Once.Spec.Context
  using (Ctx; ∅; _▸_; lookup; Usage; []; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊑∷_)
open import Once.Spec.Core.Syntax using (Tm; var; lam; app; let′; unit; pair; fst; snd; inl; inr; case; absurd; roll; fold;
  unfold; out; iter; coerce; lit; prim; sigop; ref; ren; ext; wk)
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-refl; ⊑ᵘ-+; ⊑ᵘ-*ʳ)
open import Once.Metatheory.TermModel.Subst Σ S using (Thin; done; keep; skip; ⟦_⟧θ; idθ; idθ-id; CThin; cdone; ckeep; cskip; cid; cthin-lookup)

------------------------------------------------------------------------
-- Usage, ordered
------------------------------------------------------------------------

≤q-trans : ∀ {p q r} → p ≤q q → q ≤q r → p ≤q r
≤q-trans 0≤q _   = 0≤q
≤q-trans 1≤1 1≤1 = 1≤1
≤q-trans 1≤1 1≤ω = 1≤ω
≤q-trans 1≤ω ω≤ω = 1≤ω
≤q-trans ω≤ω ω≤ω = ω≤ω

⊑ᵘ-trans : ∀ {n} {Ψ Ψ′ Ψ″ : Usage n} → Ψ ⊑ᵘ Ψ′ → Ψ′ ⊑ᵘ Ψ″ → Ψ ⊑ᵘ Ψ″
⊑ᵘ-trans []        []        = []
⊑ᵘ-trans (p ⊑∷ ps) (q ⊑∷ qs) = ≤q-trans p q ⊑∷ ⊑ᵘ-trans ps qs

------------------------------------------------------------------------
-- A usage restricted along a thinning: the variables it keeps
------------------------------------------------------------------------

_θ⁻_ : ∀ {n n′} → Thin n n′ → Usage n′ → Usage n
done   θ⁻ []      = []
keep θ θ⁻ (q ∷ Ψ) = q ∷ (θ θ⁻ Ψ)
skip θ θ⁻ (q ∷ Ψ) = θ θ⁻ Ψ

infixr 75 _θ⁻_

θ⁻-zero : ∀ {n n′} (θ : Thin n n′) → θ θ⁻ zeroUsage ≡ zeroUsage
θ⁻-zero done     = refl
θ⁻-zero (keep θ) = cong (Zero ∷_) (θ⁻-zero θ)
θ⁻-zero (skip θ) = θ⁻-zero θ

θ⁻-+ : ∀ {n n′} (θ : Thin n n′) (Ψ Ψ′ : Usage n′) → θ θ⁻ (Ψ +ᵘ Ψ′) ≡ θ θ⁻ Ψ +ᵘ θ θ⁻ Ψ′
θ⁻-+ done     []      []        = refl
θ⁻-+ (keep θ) (p ∷ Ψ) (q ∷ Ψ′) = cong ((p +q q) ∷_) (θ⁻-+ θ Ψ Ψ′)
θ⁻-+ (skip θ) (p ∷ Ψ) (q ∷ Ψ′) = θ⁻-+ θ Ψ Ψ′

θ⁻-* : ∀ {n n′} (θ : Thin n n′) q (Ψ : Usage n′) → θ θ⁻ (q *ᵘ Ψ) ≡ q *ᵘ θ θ⁻ Ψ
θ⁻-* done     q []      = refl
θ⁻-* (keep θ) q (p ∷ Ψ) = cong ((q *q p) ∷_) (θ⁻-* θ q Ψ)
θ⁻-* (skip θ) q (p ∷ Ψ) = θ⁻-* θ q Ψ

θ⁻-single : ∀ {n n′} (θ : Thin n n′) (i : Fin n) → θ θ⁻ singleUse (⟦ θ ⟧θ i) One ≡ singleUse i One
θ⁻-single (keep θ) zero    = cong (One ∷_) (θ⁻-zero θ)
θ⁻-single (keep θ) (suc i) = cong (Zero ∷_) (θ⁻-single θ i)
θ⁻-single (skip θ) i       = θ⁻-single θ i

θ⁻-mono : ∀ {n n′} (θ : Thin n n′) {Ψ Ψ′ : Usage n′} → Ψ ⊑ᵘ Ψ′ → θ θ⁻ Ψ ⊑ᵘ θ θ⁻ Ψ′
θ⁻-mono done     []        = []
θ⁻-mono (keep θ) (p ⊑∷ ps) = p ⊑∷ θ⁻-mono θ ps
θ⁻-mono (skip θ) (p ⊑∷ ps) = θ⁻-mono θ ps

------------------------------------------------------------------------
-- Strengthening: a term moved along a thinning is typed without the
-- variables the thinning inserts
------------------------------------------------------------------------

private
  use≡ : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ t A π} → Ψ ≡ Ψ′ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ A ! π
  use≡ refl d = d

  ty≡ : ∀ {n} {Γ : Ctx m n} {Ψ t A A′ π} → A ≡ A′ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A′ ! π
  ty≡ refl d = d

  ext-h : ∀ {n n′} (θ : Thin n n′) (ρ : Fin n → Fin n′) → (∀ i → ⟦ θ ⟧θ i ≡ ρ i) → ∀ i → ⟦ keep θ ⟧θ i ≡ ext {S = S} {m = m} ρ i
  ext-h θ ρ h zero    = refl
  ext-h θ ρ h (suc i) = cong suc (h i)

  single-at : ∀ {n n′} (θ : Thin n n′) (ρ : Fin n → Fin n′) → (∀ i → ⟦ θ ⟧θ i ≡ ρ i) → ∀ i
            → θ θ⁻ singleUse (ρ i) One ≡ singleUse i One
  single-at θ ρ h i = subst (λ j → θ θ⁻ singleUse j One ≡ singleUse i One) (h i) (θ⁻-single θ i)

strengthen : ∀ {n n′} (θ : Thin n n′) {Γ : Ctx m n} {Γ′ : Ctx m n′} → CThin θ Γ Γ′
           → (ρ : Fin n → Fin n′) → (∀ i → ⟦ θ ⟧θ i ≡ ρ i)
           → ∀ (t : Tm S m n) {Ψ A π} → Δ ⊩ Γ′ ⊢[ Ψ ] ren ρ t ∷ A ! π → Δ ⊩ Γ ⊢[ θ θ⁻ Ψ ] t ∷ A ! π
strengthen θ {Γ′ = Γ′} c ρ h (var i) (⊢var _) =
  use≡ (sym (single-at θ ρ h i)) (ty≡ (sym (trans (cong (lookup Γ′) (sym (h i))) (cthin-lookup c i))) (⊢var i))
strengthen θ c ρ h (lam A q π t) (⊢lam le d) = ⊢lam le (strengthen (keep θ) (ckeep c) (ext {S = S} {m = m} ρ) (ext-h θ ρ h) t d)
strengthen θ c ρ h (app f x) (⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q} df dx) =
  use≡ (sym (trans (θ⁻-+ θ Ψ₁ (q *ᵘ Ψ₂)) (cong (θ θ⁻ Ψ₁ +ᵘ_) (θ⁻-* θ q Ψ₂))))
       (⊢app (strengthen θ c ρ h f df) (strengthen θ c ρ h x dx))
strengthen θ c ρ h (let′ q e b) (⊢let {Ψ₁ = Ψ₁} {Ψ₂} de db) =
  use≡ (sym (trans (θ⁻-+ θ Ψ₂ (q *ᵘ Ψ₁)) (cong (θ θ⁻ Ψ₂ +ᵘ_) (θ⁻-* θ q Ψ₁))))
       (⊢let (strengthen θ c ρ h e de) (strengthen (keep θ) (ckeep c) (ext {S = S} {m = m} ρ) (ext-h θ ρ h) b db))
strengthen θ c ρ h unit ⊢unit = use≡ (sym (θ⁻-zero θ)) ⊢unit
strengthen θ c ρ h (pair a b) (⊢pair {Ψ₁ = Ψ₁} {Ψ₂} da db) =
  use≡ (sym (θ⁻-+ θ Ψ₁ Ψ₂)) (⊢pair (strengthen θ c ρ h a da) (strengthen θ c ρ h b db))
strengthen θ c ρ h (fst p) (⊢fst d) = ⊢fst (strengthen θ c ρ h p d)
strengthen θ c ρ h (snd p) (⊢snd d) = ⊢snd (strengthen θ c ρ h p d)
strengthen θ c ρ h (inl B a) (⊢inl d) = ⊢inl (strengthen θ c ρ h a d)
strengthen θ c ρ h (inr A b) (⊢inr d) = ⊢inr (strengthen θ c ρ h b d)
strengthen θ c ρ h (case qℓ qr e l r) (⊢case {Ψs = Ψs} {Ψ} ds dl dr) =
  use≡ (sym (θ⁻-+ θ Ψs Ψ))
       (⊢case (strengthen θ c ρ h e ds) (strengthen (keep θ) (ckeep c) (ext {S = S} {m = m} ρ) (ext-h θ ρ h) l dl)
              (strengthen (keep θ) (ckeep c) (ext {S = S} {m = m} ρ) (ext-h θ ρ h) r dr))
strengthen θ c ρ h (absurd A e) (⊢absurd d) = ⊢absurd (strengthen θ c ρ h e d)
strengthen θ c ρ h (roll F t) (⊢roll wf d) = ⊢roll wf (strengthen θ c ρ h t d)
strengthen θ c ρ h (fold F a t) (⊢fold {Ψa = Ψa} {Ψt} wf da dt) =
  use≡ (sym (trans (θ⁻-+ θ (Many *ᵘ Ψa) Ψt) (cong (_+ᵘ θ θ⁻ Ψt) (θ⁻-* θ Many Ψa))))
       (⊢fold wf (strengthen θ c ρ h a da) (strengthen θ c ρ h t dt))
strengthen θ c ρ h (unfold F k a) (⊢unfold {Ψc = Ψc} {Ψs} wf dk da) =
  use≡ (sym (trans (θ⁻-+ θ (Many *ᵘ Ψc) Ψs) (cong (_+ᵘ θ θ⁻ Ψs) (θ⁻-* θ Many Ψc))))
       (⊢unfold wf (strengthen θ c ρ h k dk) (strengthen θ c ρ h a da))
strengthen θ c ρ h (out t) (⊢out wf d) = ⊢out wf (strengthen θ c ρ h t d)
strengthen θ c ρ h (iter f a) (⊢iter {Ψf = Ψf} {Ψs} df da) =
  use≡ (sym (trans (θ⁻-+ θ (Many *ᵘ Ψf) Ψs) (cong (_+ᵘ θ θ⁻ Ψs) (θ⁻-* θ Many Ψf))))
       (⊢iter (strengthen θ c ρ h f df) (strengthen θ c ρ h a da))
strengthen θ c ρ h (coerce A B t) (⊢coerce p d) = ⊢coerce p (strengthen θ c ρ h t d)
strengthen θ c ρ h (lit _) ⊢lit-int = use≡ (sym (θ⁻-zero θ)) ⊢lit-int
strengthen θ c ρ h (lit _) ⊢lit-float = use≡ (sym (θ⁻-zero θ)) ⊢lit-float
strengthen θ c ρ h (prim p t) (⊢prim p d) = ⊢prim p (strengthen θ c ρ h t d)
strengthen θ c ρ h (sigop _ _) (⊢sigop mem) = use≡ (sym (θ⁻-zero θ)) (⊢sigop mem)
strengthen θ c ρ h (ref d τ) (⊢ref d τ r) = use≡ (sym (θ⁻-zero θ)) (⊢ref d τ r)
-- (a subsumption, over any former)
{-# CATCHALL #-}
strengthen θ c ρ h t (⊢sub-use p d) = ⊢sub-use (θ⁻-mono θ p) (strengthen θ c ρ h t d)
{-# CATCHALL #-}
strengthen θ c ρ h t (⊢sub-eff g d) = ⊢sub-eff g (strengthen θ c ρ h t d)

-- The one-variable case.
strengthen-wk : ∀ {n} {Γ : Ctx m n} {X q Ψ t A π} → Δ ⊩ (Γ ▸ X) ⊢[ q ∷ Ψ ] wk t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π
strengthen-wk {n} {Γ} {Ψ = Ψ} {t = t} d =
  use≡ (θid Ψ) (strengthen (skip (idθ n)) (cskip (cid Γ)) suc (λ i → cong suc (idθ-id i)) t d)
  where
    θid : ∀ {k} (Φ : Usage k) → idθ k θ⁻ Φ ≡ Φ
    θid []      = refl
    θid (q ∷ Φ) = cong (q ∷_) (θid Φ)
