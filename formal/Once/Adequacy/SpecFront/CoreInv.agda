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

------------------------------------------------------------------------
-- Inversion: a former's parts, typed at usages the whole one bounds
-- (grades are not needed and are left existential)
------------------------------------------------------------------------

module _ {n : ℕ} {Γ : Ctx m n} where

  inv-var : ∀ {Φ i X π} → Δ ⊩ Γ ⊢[ Φ ] var i ∷ X ! π → (X ≡ lookup Γ i) × (singleUse i One ⊑ᵘ Φ)
  inv-var (⊢var i)       = refl , ⊑ᵘ-refl _
  inv-var (⊢sub-use p d) = let (e , u) = inv-var d in e , ⊑ᵘ-trans u p
  inv-var (⊢sub-eff g d) = inv-var d

  record ILam (Φ : Usage n) (A : Ty m) (q : Quantity) (π : Purity) (t : Tm S m (suc n)) (X : Ty m) : Set where
    field
      {B}  : Ty m
      ty   : X ≡ A ⇒[ mk-kind q π ] B
      {q′} : Quantity
      {Ψ}  : Usage n
      le   : q′ ≤q q
      body : Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ ] t ∷ B ! π
      use  : Ψ ⊑ᵘ Φ

  inv-lam : ∀ {Φ A q π t X π₀} → Δ ⊩ Γ ⊢[ Φ ] lam A q π t ∷ X ! π₀ → ILam Φ A q π t X
  inv-lam (⊢lam le d)    = record { ty = refl ; le = le ; body = d ; use = ⊑ᵘ-refl _ }
  inv-lam (⊢sub-use p d) = let r = inv-lam d in
    record { ty = ILam.ty r ; le = ILam.le r ; body = ILam.body r ; use = ⊑ᵘ-trans (ILam.use r) p }
  inv-lam (⊢sub-eff g d) = inv-lam d

  record IApp (Φ : Usage n) (f x : Tm S m n) (B : Ty m) : Set where
    field
      {A}        : Ty m
      {q}        : Quantity
      {πf π₁ π₂} : Purity
      {Φ₁ Φ₂}    : Usage n
      df         : Δ ⊩ Γ ⊢[ Φ₁ ] f ∷ A ⇒[ mk-kind q πf ] B ! π₁
      dx         : Δ ⊩ Γ ⊢[ Φ₂ ] x ∷ A ! π₂
      use        : Φ₁ +ᵘ q *ᵘ Φ₂ ⊑ᵘ Φ

  inv-app : ∀ {Φ f x B π} → Δ ⊩ Γ ⊢[ Φ ] app f x ∷ B ! π → IApp Φ f x B
  inv-app (⊢app df dx)   = record { df = df ; dx = dx ; use = ⊑ᵘ-refl _ }
  inv-app (⊢sub-use p d) = let r = inv-app d in
    record { df = IApp.df r ; dx = IApp.dx r ; use = ⊑ᵘ-trans (IApp.use r) p }
  inv-app (⊢sub-eff g d) = inv-app d

  record ILet (Φ : Usage n) (q : Quantity) (e : Tm S m n) (b : Tm S m (suc n)) (B : Ty m) : Set where
    field
      {A}     : Ty m
      {π₁ π₂} : Purity
      {Φ₁ Φ₂} : Usage n
      de      : Δ ⊩ Γ ⊢[ Φ₁ ] e ∷ A ! π₁
      db      : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Φ₂ ] b ∷ B ! π₂
      use     : Φ₂ +ᵘ q *ᵘ Φ₁ ⊑ᵘ Φ

  inv-let : ∀ {Φ q e b B π} → Δ ⊩ Γ ⊢[ Φ ] let′ q e b ∷ B ! π → ILet Φ q e b B
  inv-let (⊢let de db)   = record { de = de ; db = db ; use = ⊑ᵘ-refl _ }
  inv-let (⊢sub-use p d) = let r = inv-let d in
    record { de = ILet.de r ; db = ILet.db r ; use = ⊑ᵘ-trans (ILet.use r) p }
  inv-let (⊢sub-eff g d) = inv-let d

  record IPair (Φ : Usage n) (a b : Tm S m n) (X : Ty m) : Set where
    field
      {A B}   : Ty m
      {π₁ π₂} : Purity
      {Φ₁ Φ₂} : Usage n
      ty      : X ≡ A * B
      da      : Δ ⊩ Γ ⊢[ Φ₁ ] a ∷ A ! π₁
      db      : Δ ⊩ Γ ⊢[ Φ₂ ] b ∷ B ! π₂
      use     : Φ₁ +ᵘ Φ₂ ⊑ᵘ Φ

  inv-pair : ∀ {Φ a b X π} → Δ ⊩ Γ ⊢[ Φ ] pair a b ∷ X ! π → IPair Φ a b X
  inv-pair (⊢pair da db)  = record { ty = refl ; da = da ; db = db ; use = ⊑ᵘ-refl _ }
  inv-pair (⊢sub-use p d) = let r = inv-pair d in
    record { ty = IPair.ty r ; da = IPair.da r ; db = IPair.db r ; use = ⊑ᵘ-trans (IPair.use r) p }
  inv-pair (⊢sub-eff g d) = inv-pair d

  record ICase (Φ : Usage n) (qℓ qr : Quantity) (e : Tm S m n) (l r : Tm S m (suc n)) (C : Ty m) : Set where
    field
      {A B}   : Ty m
      {π₁ π₂} : Purity
      {Φs Ψ}  : Usage n
      ds      : Δ ⊩ Γ ⊢[ Φs ] e ∷ A + B ! π₁
      dl      : Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψ ] l ∷ C ! π₂
      dr      : Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψ ] r ∷ C ! π₂
      use     : Φs +ᵘ Ψ ⊑ᵘ Φ

  inv-case : ∀ {Φ qℓ qr e l r C π} → Δ ⊩ Γ ⊢[ Φ ] case qℓ qr e l r ∷ C ! π → ICase Φ qℓ qr e l r C
  inv-case (⊢case ds dl dr) = record { ds = ds ; dl = dl ; dr = dr ; use = ⊑ᵘ-refl _ }
  inv-case (⊢sub-use p d)   = let r = inv-case d in
    record { ds = ICase.ds r ; dl = ICase.dl r ; dr = ICase.dr r ; use = ⊑ᵘ-trans (ICase.use r) p }
  inv-case (⊢sub-eff g d)   = inv-case d

  record ICoerce (Φ : Usage n) (A B : Ty m) (t : Tm S m n) (X : Ty m) : Set where
    field
      ty  : X ≡ B
      {π₀} : Purity
      {Φ₀} : Usage n
      dt  : Δ ⊩ Γ ⊢[ Φ₀ ] t ∷ A ! π₀
      use : Φ₀ ⊑ᵘ Φ

  inv-coerce : ∀ {Φ A B t X π} → Δ ⊩ Γ ⊢[ Φ ] coerce A B t ∷ X ! π → ICoerce Φ A B t X
  inv-coerce (⊢coerce p d)  = record { ty = refl ; dt = d ; use = ⊑ᵘ-refl _ }
  inv-coerce (⊢sub-use p d) = let r = inv-coerce d in
    record { ty = ICoerce.ty r ; dt = ICoerce.dt r ; use = ⊑ᵘ-trans (ICoerce.use r) p }
  inv-coerce (⊢sub-eff g d) = inv-coerce d

  record IPrim (Φ : Usage n) (p : Once.Spec.Core.Syntax.Prim) (t : Tm S m n) (X : Ty m) : Set where
    field
      ty  : X ≡ Once.Spec.Core.Syntax.primCod p
      {π₀} : Purity
      {Φ₀} : Usage n
      dt  : Δ ⊩ Γ ⊢[ Φ₀ ] t ∷ Once.Spec.Core.Syntax.primDom p ! π₀
      use : Φ₀ ⊑ᵘ Φ

  inv-prim : ∀ {Φ p t X π} → Δ ⊩ Γ ⊢[ Φ ] prim p t ∷ X ! π → IPrim Φ p t X
  inv-prim (⊢prim p d)    = record { ty = refl ; dt = d ; use = ⊑ᵘ-refl _ }
  inv-prim (⊢sub-use q d) = let r = inv-prim d in
    record { ty = IPrim.ty r ; dt = IPrim.dt r ; use = ⊑ᵘ-trans (IPrim.use r) q }
  inv-prim (⊢sub-eff g d) = inv-prim d

  -- The remaining formers: their parts and types (usage where a generator's
  -- body needs it).
  inv-fst : ∀ {Φ p X π} → Δ ⊩ Γ ⊢[ Φ ] fst p ∷ X ! π → Σ[ Y ∈ Ty m ] Σ[ π₀ ∈ Purity ] Σ[ Φ₀ ∈ Usage n ] (Δ ⊩ Γ ⊢[ Φ₀ ] p ∷ X * Y ! π₀) × (Φ₀ ⊑ᵘ Φ)
  inv-fst (⊢fst d)       = _ , _ , _ , d , ⊑ᵘ-refl _
  inv-fst (⊢sub-use q d) = let (Y , π₀ , Φ₀ , d₀ , u) = inv-fst d in Y , π₀ , Φ₀ , d₀ , ⊑ᵘ-trans u q
  inv-fst (⊢sub-eff g d) = inv-fst d

  inv-snd : ∀ {Φ p X π} → Δ ⊩ Γ ⊢[ Φ ] snd p ∷ X ! π → Σ[ Y ∈ Ty m ] Σ[ π₀ ∈ Purity ] Σ[ Φ₀ ∈ Usage n ] (Δ ⊩ Γ ⊢[ Φ₀ ] p ∷ Y * X ! π₀) × (Φ₀ ⊑ᵘ Φ)
  inv-snd (⊢snd d)       = _ , _ , _ , d , ⊑ᵘ-refl _
  inv-snd (⊢sub-use q d) = let (Y , π₀ , Φ₀ , d₀ , u) = inv-snd d in Y , π₀ , Φ₀ , d₀ , ⊑ᵘ-trans u q
  inv-snd (⊢sub-eff g d) = inv-snd d

  inv-inl : ∀ {Φ B a X π} → Δ ⊩ Γ ⊢[ Φ ] inl B a ∷ X ! π → Σ[ A ∈ Ty m ] (X ≡ A + B) × Σ[ π₀ ∈ Purity ] Σ[ Φ₀ ∈ Usage n ] (Δ ⊩ Γ ⊢[ Φ₀ ] a ∷ A ! π₀)
  inv-inl (⊢inl d)       = _ , refl , _ , _ , d
  inv-inl (⊢sub-use q d) = inv-inl d
  inv-inl (⊢sub-eff g d) = inv-inl d

  inv-inr : ∀ {Φ A b X π} → Δ ⊩ Γ ⊢[ Φ ] inr A b ∷ X ! π → Σ[ B ∈ Ty m ] (X ≡ A + B) × Σ[ π₀ ∈ Purity ] Σ[ Φ₀ ∈ Usage n ] (Δ ⊩ Γ ⊢[ Φ₀ ] b ∷ B ! π₀)
  inv-inr (⊢inr d)       = _ , refl , _ , _ , d
  inv-inr (⊢sub-use q d) = inv-inr d
  inv-inr (⊢sub-eff g d) = inv-inr d

  inv-absurd : ∀ {Φ A e X π} → Δ ⊩ Γ ⊢[ Φ ] absurd A e ∷ X ! π → X ≡ A
  inv-absurd (⊢absurd d)    = refl
  inv-absurd (⊢sub-use q d) = inv-absurd d
  inv-absurd (⊢sub-eff g d) = inv-absurd d

  inv-roll : ∀ {Φ F t X π} → Δ ⊩ Γ ⊢[ Φ ] roll F t ∷ X ! π → X ≡ μ F
  inv-roll (⊢roll wf d)   = refl
  inv-roll (⊢sub-use q d) = inv-roll d
  inv-roll (⊢sub-eff g d) = inv-roll d

  inv-fold : ∀ {Φ F a t X π} → Δ ⊩ Γ ⊢[ Φ ] fold F a t ∷ X ! π
           → Σ[ π₀ ∈ Purity ] Σ[ π₁ ∈ Purity ] Σ[ Φ₀ ∈ Usage n ] (Δ ⊩ Γ ⊢[ Φ₀ ] a ∷ ⟦ F ⟧F X ⇒[ mk-kind Many π₀ ] X ! π₁)
  inv-fold (⊢fold wf da dt) = _ , _ , _ , da
  inv-fold (⊢sub-use q d)   = inv-fold d
  inv-fold (⊢sub-eff g d)   = inv-fold d

  inv-unfold : ∀ {Φ F k a X π} → Δ ⊩ Γ ⊢[ Φ ] unfold F k a ∷ X ! π
             → Σ[ f ∈ Once.Spec.Grade.Finite ] Σ[ A ∈ Ty m ] (X ≡ ν F f)
               × Σ[ π₁ ∈ Purity ] Σ[ Φk ∈ Usage n ] Σ[ Φa ∈ Usage n ]
                   (Δ ⊩ Γ ⊢[ Φk ] k ∷ A ⇒[ mk-kind Many (Once.Spec.Grade.fin f) ] ⟦ F ⟧F A ! π₁) × (Many *ᵘ Φk +ᵘ Φa ⊑ᵘ Φ)
  inv-unfold (⊢unfold wf dk da) = _ , _ , refl , _ , _ , _ , dk , ⊑ᵘ-refl _
  inv-unfold (⊢sub-use q d)     = let (f , A , e , π₁ , Φk , Φa , dk , u) = inv-unfold d in f , A , e , π₁ , Φk , Φa , dk , ⊑ᵘ-trans u q
  inv-unfold (⊢sub-eff g d)     = inv-unfold d

  inv-out : ∀ {Φ t X π} → Δ ⊩ Γ ⊢[ Φ ] out t ∷ X ! π
          → Σ[ F ∈ Once.Spec.Type.Fun m ] Σ[ f ∈ Once.Spec.Grade.Finite ] (X ≡ ⟦ F ⟧F (ν F f))
            × Σ[ π₀ ∈ Purity ] Σ[ Φ₀ ∈ Usage n ] (Δ ⊩ Γ ⊢[ Φ₀ ] t ∷ ν F f ! π₀)
  inv-out (⊢out wf d)    = _ , _ , refl , _ , _ , d
  inv-out (⊢sub-use q d) = inv-out d
  inv-out (⊢sub-eff g d) = inv-out d

  inv-iter : ∀ {Φ f a X π} → Δ ⊩ Γ ⊢[ Φ ] iter f a ∷ X ! π
           → Σ[ A ∈ Ty m ] Σ[ π₁ ∈ Purity ] Σ[ Φf ∈ Usage n ] (Δ ⊩ Γ ⊢[ Φf ] f ∷ A ⇒[ mk-kind Many Once.Spec.Grade.act ] (X + A) ! π₁)
  inv-iter (⊢iter df da)  = _ , _ , _ , df
  inv-iter (⊢sub-use q d) = inv-iter d
  inv-iter (⊢sub-eff g d) = inv-iter d

  inv-unit : ∀ {Φ X π} → Δ ⊩ Γ ⊢[ Φ ] unit ∷ X ! π → X ≡ Unit
  inv-unit ⊢unit          = refl
  inv-unit (⊢sub-use q d) = inv-unit d
  inv-unit (⊢sub-eff g d) = inv-unit d

  inv-lit-int : ∀ {Φ i X π} → Δ ⊩ Γ ⊢[ Φ ] lit (Once.Spec.Core.Syntax.lit-int i) ∷ X ! π → X ≡ Once.Spec.Type.Int
  inv-lit-int ⊢lit-int       = refl
  inv-lit-int (⊢sub-use q d) = inv-lit-int d
  inv-lit-int (⊢sub-eff g d) = inv-lit-int d

  inv-lit-float : ∀ {Φ f X π} → Δ ⊩ Γ ⊢[ Φ ] lit (Once.Spec.Core.Syntax.lit-float f) ∷ X ! π → X ≡ Once.Spec.Type.Float
  inv-lit-float ⊢lit-float     = refl
  inv-lit-float (⊢sub-use q d) = inv-lit-float d
  inv-lit-float (⊢sub-eff g d) = inv-lit-float d

  inv-sigop : ∀ {Φ c t X π} → Δ ⊩ Γ ⊢[ Φ ] sigop c t ∷ X ! π → X ≡ Once.Spec.Signature.⌜_⌝ᵈ t
  inv-sigop (⊢sigop mem)   = refl
  inv-sigop (⊢sub-use q d) = inv-sigop d
  inv-sigop (⊢sub-eff g d) = inv-sigop d

  inv-ref : ∀ {Φ d τ X π} → Δ ⊩ Γ ⊢[ Φ ] ref d τ ∷ X ! π → X ≡ Once.Spec.Core.Syntax.Schema.type (S Once.Spec.Core.Syntax.!! d) Once.Spec.Type.⟨ τ ⟩
  inv-ref (⊢ref d τ r)   = refl
  inv-ref (⊢sub-use q e) = inv-ref e
  inv-ref (⊢sub-eff g e) = inv-ref e
