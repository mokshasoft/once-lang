-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Rename — plan 0.102 phase B (for plan 0.103 phase 6): the
-- core judgment is stable under RENAMING along an order-preserving embedding
-- of contexts, with the usage thinned (the new positions are unused). The
-- combinators' `let`-bound arms are weakened into their bodies, which is where
-- the surface → core translation needs it.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

module Once.Spec.Core.Rename {s : ℕ} (S : Sig s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Once.Type using (Type; Quantity; Zero; One; Many)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; lookup; Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊔ᵘ_)
open import Once.Surface.Thinning using (_⊆_; done; skip; keep; thin-var; thin-var-lookup; thin-usage;
  thin-usage-+ᵘ; thin-usage-*ᵘ; thin-usage-⊔ᵘ; thin-usage-zeroUsage; thin-usage-singleUse; ⊆-wk)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S

-- Renaming is extensional in the renaming.
ren-cong : ∀ {n m} {ρ ρ′ : Ren n m} → (∀ i → ρ i ≡ ρ′ i) → ∀ t → ren ρ t ≡ ren ρ′ t
ren-cong h (var i)        = cong var (h i)
ren-cong h (lam t)        = cong lam (ren-cong (extR-cong h) t)
  where
    extR-cong : ∀ {n m} {ρ ρ′ : Ren n m} → (∀ i → ρ i ≡ ρ′ i) → ∀ i → extR ρ i ≡ extR ρ′ i
    extR-cong h zero    = refl
    extR-cong h (suc i) = cong suc (h i)
ren-cong h (app t u)      = cong₂ app (ren-cong h t) (ren-cong h u)
ren-cong {ρ = ρ} {ρ′} h (let′ t u) = cong₂ let′ (ren-cong h t) (ren-cong (ext h) u)
  where
    ext : (∀ i → ρ i ≡ ρ′ i) → ∀ i → extR ρ i ≡ extR ρ′ i
    ext h zero    = refl
    ext h (suc i) = cong suc (h i)
ren-cong h unit           = refl
ren-cong h (pair t u)     = cong₂ pair (ren-cong h t) (ren-cong h u)
ren-cong h (fst t)        = cong fst (ren-cong h t)
ren-cong h (snd t)        = cong snd (ren-cong h t)
ren-cong h (inl t)        = cong inl (ren-cong h t)
ren-cong h (inr t)        = cong inr (ren-cong h t)
ren-cong {ρ = ρ} {ρ′} h (case s l r) = cong₂ (λ a b → a b) (cong₂ case (ren-cong h s) (ren-cong (ext h) l)) (ren-cong (ext h) r)
  where
    ext : (∀ i → ρ i ≡ ρ′ i) → ∀ i → extR ρ i ≡ extR ρ′ i
    ext h zero    = refl
    ext h (suc i) = cong suc (h i)
ren-cong h (absurd t)     = cong absurd (ren-cong h t)
ren-cong h (roll t)       = cong roll (ren-cong h t)
ren-cong h (fold a t)     = cong₂ fold (ren-cong h a) (ren-cong h t)
ren-cong h (unfold c t)   = cong₂ unfold (ren-cong h c) (ren-cong h t)
ren-cong h (out t)        = cong out (ren-cong h t)
ren-cong h (coerce A B t) = cong (coerce A B) (ren-cong h t)
ren-cong h (lit l)        = refl
ren-cong h (prim p t)     = cong (prim p) (ren-cong h t)
ren-cong h (sigop c A)    = refl
ren-cong h (ref d τ)      = refl

-- Under a binder, the kept embedding renames as `extR`.
keep-extR : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {A : Type} {q : Quantity} (θ : Γ ⊆ Δ)
  → ∀ i → thin-var (keep {A = A} {q = q} θ) i ≡ extR (thin-var θ) i
keep-extR θ zero    = refl
keep-extR θ (suc i) = refl

-- THE RENAMING LEMMA.
ren-⊢ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ : Usage n} {t A π} (θ : Γ ⊆ Δ)
  → Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊢[ thin-usage θ Ψ ] ren (thin-var θ) t ∷ A ! π
ren-⊢ {Δ = Δ} θ (⊢var {Γ = Γ} i) =
  subst (λ U → Δ ⊢[ U ] var (thin-var θ i) ∷ lookup Γ i ! _) (sym (thin-usage-singleUse θ i One))
    (subst (λ X → Δ ⊢[ singleUse (thin-var θ i) One ] var (thin-var θ i) ∷ X ! _) (sym (thin-var-lookup θ i))
      (⊢var (thin-var θ i)))
ren-⊢ {Δ = Δ} {Ψ = Ψ} {π = π} θ (⊢lam {q = q} {A = A} {B = B} {t = t} le d) =
  ⊢lam le (subst (λ u → (Δ , A ^ Many) ⊢[ _ ] u ∷ B ! _) (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d))
ren-⊢ {Δ = Δ} θ (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = q} {B = B} {f = f} {x = x} df dx) =
  subst (λ U → Δ ⊢[ U ] app (ren (thin-var θ) f) (ren (thin-var θ) x) ∷ B ! _)
    (sym (trans (thin-usage-+ᵘ θ Ψ₁ (q *ᵘ Ψ₂)) (cong (thin-usage θ Ψ₁ +ᵘ_) (thin-usage-*ᵘ θ q Ψ₂))))
    (⊢app (ren-⊢ θ df) (ren-⊢ θ dx))
ren-⊢ {Δ = Δ} θ (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = q} {A = A} {B = B} {e = e} {b = b} de db) =
  subst (λ U → Δ ⊢[ U ] let′ (ren (thin-var θ) e) (ren (extR (thin-var θ)) b) ∷ B ! _)
    (sym (trans (thin-usage-+ᵘ θ Ψ₂ (q *ᵘ Ψ₁)) (cong (thin-usage θ Ψ₂ +ᵘ_) (thin-usage-*ᵘ θ q Ψ₁))))
    (⊢let (ren-⊢ θ de) (subst (λ u → (Δ , A ^ Many) ⊢[ _ ] u ∷ B ! _) (ren-cong (keep-extR θ) b) (ren-⊢ (keep θ) db)))
ren-⊢ {Δ = Δ} θ ⊢unit = subst (λ U → Δ ⊢[ U ] unit ∷ _ ! _) (sym (thin-usage-zeroUsage θ)) ⊢unit
ren-⊢ {Δ = Δ} θ (⊢pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {a = a} {b = b} da db) =
  subst (λ U → Δ ⊢[ U ] pair (ren (thin-var θ) a) (ren (thin-var θ) b) ∷ _ ! _)
    (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (⊢pair (ren-⊢ θ da) (ren-⊢ θ db))
ren-⊢ θ (⊢fst d) = ⊢fst (ren-⊢ θ d)
ren-⊢ θ (⊢snd d) = ⊢snd (ren-⊢ θ d)
ren-⊢ θ (⊢inl d) = ⊢inl (ren-⊢ θ d)
ren-⊢ θ (⊢inr d) = ⊢inr (ren-⊢ θ d)
ren-⊢ {Δ = Δ} θ (⊢case {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {A = A} {B = B} {C = C} {s = sc} {l = l} {r = r} ds dl dr) =
  subst (λ U → Δ ⊢[ U ] case (ren (thin-var θ) sc) (ren (extR (thin-var θ)) l) (ren (extR (thin-var θ)) r) ∷ C ! _)
    (sym (trans (thin-usage-+ᵘ θ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) (cong (thin-usage θ Ψs +ᵘ_) (thin-usage-⊔ᵘ θ Ψₗ Ψᵣ))))
    (⊢case (ren-⊢ θ ds)
       (subst (λ u → (Δ , A ^ Many) ⊢[ _ ] u ∷ C ! _) (ren-cong (keep-extR θ) l) (ren-⊢ (keep θ) dl))
       (subst (λ u → (Δ , B ^ Many) ⊢[ _ ] u ∷ C ! _) (ren-cong (keep-extR θ) r) (ren-⊢ (keep θ) dr)))
ren-⊢ θ (⊢absurd d) = ⊢absurd (ren-⊢ θ d)
ren-⊢ θ (⊢roll wf d) = ⊢roll wf (ren-⊢ θ d)
ren-⊢ {Δ = Δ} θ (⊢fold {Ψa = Ψa} {Ψt = Ψt} {alg = alg} {t = t} wf da dt) =
  subst (λ U → Δ ⊢[ U ] fold (ren (thin-var θ) alg) (ren (thin-var θ) t) ∷ _ ! _)
    (sym (thin-usage-+ᵘ θ Ψa Ψt)) (⊢fold wf (ren-⊢ θ da) (ren-⊢ θ dt))
ren-⊢ {Δ = Δ} θ (⊢unfold {Ψc = Ψc} {Ψs = Ψs} {c = c} {s = sd} wf dc ds) =
  subst (λ U → Δ ⊢[ U ] unfold (ren (thin-var θ) c) (ren (thin-var θ) sd) ∷ _ ! _)
    (sym (thin-usage-+ᵘ θ Ψc Ψs)) (⊢unfold wf (ren-⊢ θ dc) (ren-⊢ θ ds))
ren-⊢ θ (⊢out wf d) = ⊢out wf (ren-⊢ θ d)
ren-⊢ θ (⊢coerce p d) = ⊢coerce p (ren-⊢ θ d)
ren-⊢ {Δ = Δ} θ ⊢lit-int   = subst (λ U → Δ ⊢[ U ] _ ∷ _ ! _) (sym (thin-usage-zeroUsage θ)) ⊢lit-int
ren-⊢ {Δ = Δ} θ ⊢lit-float = subst (λ U → Δ ⊢[ U ] _ ∷ _ ! _) (sym (thin-usage-zeroUsage θ)) ⊢lit-float
ren-⊢ {Δ = Δ} θ ⊢lit-str   = subst (λ U → Δ ⊢[ U ] _ ∷ _ ! _) (sym (thin-usage-zeroUsage θ)) ⊢lit-str
ren-⊢ θ (⊢prim p d) = ⊢prim p (ren-⊢ θ d)
ren-⊢ {Δ = Δ} θ (⊢sigop c k h) = subst (λ U → Δ ⊢[ U ] _ ∷ _ ! _) (sym (thin-usage-zeroUsage θ)) (⊢sigop c k h)
ren-⊢ θ (⊢sub-eff g d) = ⊢sub-eff g (ren-⊢ θ d)
ren-⊢ {Δ = Δ} θ (⊢ref d τ r) = subst (λ U → Δ ⊢[ U ] _ ∷ _ ! _) (sym (thin-usage-zeroUsage θ)) (⊢ref d τ r)

-- The identity embedding renames as the identity.
thin-var-refl : ∀ {n} {Γ : Ctx n} (i : Fin n) → thin-var (Once.Surface.Thinning.⊆-refl {Γ = Γ}) i ≡ i
thin-var-refl {Γ = Γ , _ ^ _} zero    = refl
thin-var-refl {Γ = Γ , _ ^ _} (suc i) = cong suc (thin-var-refl {Γ = Γ} i)

-- Weakening by one variable (unused).
wk-⊢ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {t A π} (B : Type)
  → Γ ⊢[ Ψ ] t ∷ A ! π → (Γ , B ^ Many) ⊢[ Zero ∷ thin-usage (Once.Surface.Thinning.⊆-refl {Γ = Γ}) Ψ ] wk t ∷ A ! π
wk-⊢ {Γ = Γ} {t = t} B d =
  subst (λ u → _ ⊢[ _ ] u ∷ _ ! _) (ren-cong (λ i → cong suc (thin-var-refl {Γ = Γ} i)) t)
    (ren-⊢ (⊆-wk {Γ = Γ} {A = B} {q = Many}) d)

-- The empty context embeds everywhere.
∅⊆ : ∀ {n} {Γ : Ctx n} → ∅ ⊆ Γ
∅⊆ {Γ = ∅}         = done
∅⊆ {Γ = Γ , _ ^ _} = skip (∅⊆ {Γ = Γ})

-- A CLOSED term, embedded in any context (a cata algebra, D131).
close : ∀ {n} → Tm 0 → Tm n
close = ren (λ ())

⊢close : ∀ {n} {Γ : Ctx n} {t A π} → ∅ ⊢[ zeroUsage ] t ∷ A ! π → Γ ⊢[ zeroUsage ] close t ∷ A ! π
⊢close {Γ = Γ} {t = t} {A} {π} d =
  subst (λ u → Γ ⊢[ zeroUsage ] u ∷ _ ! _) (ren-cong {ρ = thin-var (∅⊆ {Γ = Γ})} {ρ′ = λ ()} (λ ()) t)
    (subst (λ U → Γ ⊢[ U ] ren (thin-var (∅⊆ {Γ = Γ})) t ∷ A ! π) (thin-usage-zeroUsage (∅⊆ {Γ = Γ})) (ren-⊢ (∅⊆ {Γ = Γ}) d))
