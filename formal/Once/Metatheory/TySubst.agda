-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.TySubst — the proof of THE TYPE-SUBSTITUTION LEMMA (D303),
-- stated as `ty-subst-⊢` in `Once.Spec.Core.TermModel`:
--
--     Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π   ⟹   Δ′ ⊩ Γ⟨σ⟩ ⊢[ Ψ ] t⟨σ⟩ₜ ∷ A⟨σ⟩ ! π
--
-- for every kind-respecting `σ`. It is what makes "typed once, instances for
-- free" (D243) a valid argument: a polymorphic definition's one parametric
-- typing yields a typing at every instance, open or ground
-- (`PolyTyping.instantiate` is the ground-target counterpart the compiler
-- proof uses). Postulate-free; by induction on the derivation.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Contract using (ISig)

module Once.Metatheory.TySubst {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)

import Once.Spec.Type as T
import Once.Type as T
open import Once.Spec.Type.Grade using (Purity; pure; mk-kind; Many; One; _·p_)
open import Once.Spec.Context using (Usage; zeroUsage; singleUse)
open import Once.Spec.Core.PolyTy
open Schema using (type)
open import Once.Spec.Core.PolyTyping S
import Once.Spec.Core.Syntax S as G
open G using (primDom; primCod)
open import Once.Spec.Core.TySubst S

------------------------------------------------------------------------
-- Kinds, functors and subtyping are stable under a kind-respecting σ
------------------------------------------------------------------------

-- Ground types are fixed by substitution.
mutual
  ⌈⌉-⟨⟩ : ∀ {m k} (A : T.Type) (σ : Sub m k) → ⌈ A ⌉ ⟨ σ ⟩ ≡ ⌈ A ⌉
  ⌈⌉-⟨⟩ T.Unit σ = refl
  ⌈⌉-⟨⟩ T.Void σ = refl
  ⌈⌉-⟨⟩ T.Int σ = refl
  ⌈⌉-⟨⟩ T.Float σ = refl
  ⌈⌉-⟨⟩ (T.rigid k i) σ = refl
  ⌈⌉-⟨⟩ (A T.* B) σ = cong₂ _*_ (⌈⌉-⟨⟩ A σ) (⌈⌉-⟨⟩ B σ)
  ⌈⌉-⟨⟩ (A T.+ B) σ = cong₂ _+_ (⌈⌉-⟨⟩ A σ) (⌈⌉-⟨⟩ B σ)
  ⌈⌉-⟨⟩ (A T.⇒[ k ] B) σ = cong₂ (λ a b → a ⇒[ k ] b) (⌈⌉-⟨⟩ A σ) (⌈⌉-⟨⟩ B σ)
  ⌈⌉-⟨⟩ (T.μ-type F) σ = cong μ-type (⌈⌉F-⟨⟩ F σ)
  ⌈⌉-⟨⟩ (T.ν-type F π) σ = cong (λ G → ν-type G π) (⌈⌉F-⟨⟩ F σ)

  ⌈⌉F-⟨⟩ : ∀ {m k} (F : T.Functor) (σ : Sub m k) → ⌈ F ⌉F ⟨ σ ⟩F ≡ ⌈ F ⌉F
  ⌈⌉F-⟨⟩ (T.K A) σ = cong K (⌈⌉-⟨⟩ A σ)
  ⌈⌉F-⟨⟩ T.Id σ = refl
  ⌈⌉F-⟨⟩ (F T.⊕ G) σ = cong₂ _⊕_ (⌈⌉F-⟨⟩ F σ) (⌈⌉F-⟨⟩ G σ)
  ⌈⌉F-⟨⟩ (F T.⊗ G) σ = cong₂ _⊗_ (⌈⌉F-⟨⟩ F σ) (⌈⌉F-⟨⟩ G σ)

base-⟨⟩ : ∀ {m k} {Δ : KCtx m} {Δ′ : KCtx k} {σ : Sub m k} {A} → KSub Δ Δ′ σ → Base Δ A → Base Δ′ (A ⟨ σ ⟩)
base-⟨⟩ r (b-var {i} e) = r i e
base-⟨⟩ r b-Unit   = b-Unit
base-⟨⟩ r b-Void   = b-Void
base-⟨⟩ r b-Int    = b-Int
base-⟨⟩ r b-Float  = b-Float
base-⟨⟩ r b-rigid  = b-rigid
base-⟨⟩ r (b-Prod a b) = b-Prod (base-⟨⟩ r a) (base-⟨⟩ r b)
base-⟨⟩ r (b-Sum a b)  = b-Sum (base-⟨⟩ r a) (base-⟨⟩ r b)

wf-⟨⟩ : ∀ {m k} {Δ : KCtx m} {Δ′ : KCtx k} {σ : Sub m k} {F} → KSub Δ Δ′ σ → WFFun Δ F → WFFun Δ′ (F ⟨ σ ⟩F)
wf-⟨⟩ r (wf-K b)      = wf-K (base-⟨⟩ r b)
wf-⟨⟩ r wf-Id         = wf-Id
wf-⟨⟩ r (wf-Sum f g)  = wf-Sum (wf-⟨⟩ r f) (wf-⟨⟩ r g)
wf-⟨⟩ r (wf-Prod f g) = wf-Prod (wf-⟨⟩ r f) (wf-⟨⟩ r g)

<:ₚ-⟨⟩ : ∀ {m k} {A B : Ty m} (σ : Sub m k) → A <:ₚ B → A ⟨ σ ⟩ <:ₚ B ⟨ σ ⟩
<:ₚ-⟨⟩ {A = var i} σ sub-var = <:ₚ-refl (σ i)
<:ₚ-⟨⟩ σ sub-void   = sub-void
<:ₚ-⟨⟩ σ sub-unit   = sub-unit
<:ₚ-⟨⟩ σ sub-int    = sub-int
<:ₚ-⟨⟩ σ sub-float  = sub-float
<:ₚ-⟨⟩ σ sub-rigid  = sub-rigid
<:ₚ-⟨⟩ σ (sub-arr a b g) = sub-arr (<:ₚ-⟨⟩ σ a) (<:ₚ-⟨⟩ σ b) g
<:ₚ-⟨⟩ σ (sub-prod a b)  = sub-prod (<:ₚ-⟨⟩ σ a) (<:ₚ-⟨⟩ σ b)
<:ₚ-⟨⟩ σ (sub-sum a b)   = sub-sum (<:ₚ-⟨⟩ σ a) (<:ₚ-⟨⟩ σ b)
<:ₚ-⟨⟩ σ sub-μ           = sub-μ
<:ₚ-⟨⟩ σ (sub-ν g)       = sub-ν g

-- Substitution commutes with functor application.
⟦⟧F-⟨⟩ : ∀ {m k} (F : Fun m) (X : Ty m) (σ : Sub m k) → (⟦ F ⟧F X) ⟨ σ ⟩ ≡ ⟦ F ⟨ σ ⟩F ⟧F (X ⟨ σ ⟩)
⟦⟧F-⟨⟩ (K A)   X σ = refl
⟦⟧F-⟨⟩ Id      X σ = refl
⟦⟧F-⟨⟩ (F ⊕ G) X σ = cong₂ _+_ (⟦⟧F-⟨⟩ F X σ) (⟦⟧F-⟨⟩ G X σ)
⟦⟧F-⟨⟩ (F ⊗ G) X σ = cong₂ _*_ (⟦⟧F-⟨⟩ F X σ) (⟦⟧F-⟨⟩ G X σ)

lookup-⟨⟩ : ∀ {m k n} (Γ : PCtx m n) (σ : Sub m k) (i : Fin n) → lookupP (Γ ⟨ σ ⟩ᶜ) i ≡ lookupP Γ i ⟨ σ ⟩
lookup-⟨⟩ (Γ , A ^ q) σ zero    = refl
lookup-⟨⟩ (Γ , A ^ q) σ (suc i) = lookup-⟨⟩ Γ σ i

------------------------------------------------------------------------
-- THE TYPE-SUBSTITUTION LEMMA
------------------------------------------------------------------------

tsubst : ∀ {m k} {Δ : KCtx m} {Δ′ : KCtx k} {n} {Γ : PCtx m n} {Ψ : Usage n} {t : PTm m n} {A : Ty m} {π : Purity}
  (σ : Sub m k) → KSub Δ Δ′ σ
  → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π
  → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] t ⟨ σ ⟩ₜ ∷ A ⟨ σ ⟩ ! π
tsubst {Δ′ = Δ′} {Γ = Γ} σ r (⊢var i) =
  subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ singleUse i One ] var i ∷ X ! pure) (lookup-⟨⟩ Γ σ i) (⊢var i)
tsubst σ r (⊢lam le d) = ⊢lam le (tsubst σ r d)
tsubst σ r (⊢app f x) = ⊢app (tsubst σ r f) (tsubst σ r x)
tsubst σ r (⊢let e b) = ⊢let (tsubst σ r e) (tsubst σ r b)
tsubst σ r ⊢unit = ⊢unit
tsubst σ r (⊢pair a b) = ⊢pair (tsubst σ r a) (tsubst σ r b)
tsubst σ r (⊢fst p) = ⊢fst (tsubst σ r p)
tsubst σ r (⊢snd p) = ⊢snd (tsubst σ r p)
tsubst σ r (⊢inl a) = ⊢inl (tsubst σ r a)
tsubst σ r (⊢inr b) = ⊢inr (tsubst σ r b)
tsubst σ r (⊢case s l x) = ⊢case (tsubst σ r s) (tsubst σ r l) (tsubst σ r x)
tsubst σ r (⊢absurd e) = ⊢absurd (tsubst σ r e)
tsubst {Δ′ = Δ′} {Γ = Γ} {Ψ = Ψ} {π = π} σ r (⊢roll {F = F} {t = t} wf d) =
  ⊢roll (wf-⟨⟩ r wf)
    (subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] t ⟨ σ ⟩ₜ ∷ X ! π) (⟦⟧F-⟨⟩ F (μ-type F) σ) (tsubst σ r d))
tsubst {Δ′ = Δ′} {Γ = Γ} σ r (⊢fold {Ψa = Ψa} {π = π} {π₁ = π₁} {F = F} {A = A} {alg = alg} wf a t) =
  ⊢fold (wf-⟨⟩ r wf)
    (subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψa ] alg ⟨ σ ⟩ₜ ∷ X ⇒[ mk-kind Many π ] A ⟨ σ ⟩ ! π₁) (⟦⟧F-⟨⟩ F A σ)
           (tsubst σ r a))
    (tsubst σ r t)
tsubst {Δ′ = Δ′} {Γ = Γ} σ r (⊢unfold {Ψc = Ψc} {π = π} {π₁ = π₁} {F = F} {A = A} {c = c} wf k x) =
  ⊢unfold (wf-⟨⟩ r wf)
    (subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψc ] c ⟨ σ ⟩ₜ ∷ A ⟨ σ ⟩ ⇒[ mk-kind Many π ] X ! π₁) (⟦⟧F-⟨⟩ F A σ)
           (tsubst σ r k))
    (tsubst σ r x)
tsubst {Δ′ = Δ′} {Γ = Γ} {Ψ = Ψ} σ r (⊢out {π = π} {π₁ = π₁} {F = F} {t = t} wf d) =
  subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] out (t ⟨ σ ⟩ₜ) ∷ X ! π₁ ·p π) (sym (⟦⟧F-⟨⟩ F (ν-type F π) σ))
    (⊢out (wf-⟨⟩ r wf) (tsubst σ r d))
tsubst σ r (⊢coerce p d) = ⊢coerce (<:ₚ-⟨⟩ σ p) (tsubst σ r d)
tsubst σ r ⊢lit-int = ⊢lit-int
tsubst σ r ⊢lit-float = ⊢lit-float
tsubst {Δ′ = Δ′} {Γ = Γ} {Ψ = Ψ} {π = π} σ r (⊢prim {t = t} p d) =
  subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] prim p (t ⟨ σ ⟩ₜ) ∷ X ! π) (sym (⌈⌉-⟨⟩ (primCod p) σ))
    (⊢prim p (subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] t ⟨ σ ⟩ₜ ∷ X ! π) (⌈⌉-⟨⟩ (primDom p) σ) (tsubst σ r d)))
tsubst {Δ′ = Δ′} {Γ = Γ} σ r (⊢sigop {A = A} c k h g m) =
  subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ zeroUsage ] sigop c A ∷ X ! pure) (sym (⌈⌉-⟨⟩ A σ)) (⊢sigop c k h g m)
tsubst σ r (⊢sub-eff g d) = ⊢sub-eff g (tsubst σ r d)
tsubst σ r (⊢sub-use p d) = ⊢sub-use p (tsubst σ r d)
tsubst {Δ′ = Δ′} {Γ = Γ} σ r (⊢ref d τ k) =
  subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ zeroUsage ] ref d (λ i → τ i ⟨ σ ⟩) ∷ X ! pure)
        (sym (⟨⟩-∘ (type (S !! d)) τ σ))
        (⊢ref d (λ i → τ i ⟨ σ ⟩) (λ i e → base-⟨⟩ r (k i e)))
