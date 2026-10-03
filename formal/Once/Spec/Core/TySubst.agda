-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.TySubst — plan 0.103 phase 5: THE TYPE-SUBSTITUTION LEMMA.
--
--     Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π   ⟹   Δ′ ⊩ Γ⟨σ⟩ ⊢[ Ψ ] t⟨σ⟩ ∷ A⟨σ⟩ ! π
--
-- for every substitution `σ` of open types that RESPECTS the kinds (a base
-- variable becomes a type that is base under `Δ′`). A METATHEOREM about the
-- core judgment, not a rule of it — postulate-free. It is what makes "typed
-- once, instances for free" a valid argument: a polymorphic definition's one
-- parametric typing yields a typing at every instance, open or ground
-- (`PolyTyping.instantiate` is its ground-target counterpart).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
import Once.Type
open import Once.Spec.Core.PolyTy using (Sig)

open import Once.Spec.Contract using (ISig)
module Once.Spec.Core.TySubst {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

import Once.Type as T
open T using (Purity; pure; mk-kind; Many; One)
open import Once.Type.Sub using (⊑π-refl)
open import Once.Surface.Context using (Usage; zeroUsage; singleUse)
open import Once.Spec.Core.PolyTy
open import Once.Spec.Core.PolyTyping S
import Once.Spec.Core.Syntax S as G
open G using (primDom; primCod)

------------------------------------------------------------------------
-- Substitution respecting kinds
------------------------------------------------------------------------

KSub : ∀ {m k} → KCtx m → KCtx k → Sub m k → Set
KSub Δ Δ′ σ = ∀ i → Δ i ≡ Once.Type.k-base → Base Δ′ (σ i)

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

-- Subtyping over open types is reflexive, hence stable under substitution.
<:ₚ-refl : ∀ {m} (A : Ty m) → A <:ₚ A
<:ₚ-refl (var i) = sub-var
<:ₚ-refl Unit = sub-unit
<:ₚ-refl Void = sub-void
<:ₚ-refl Int = sub-int
<:ₚ-refl Float = sub-float
<:ₚ-refl (rigid k i) = sub-rigid
<:ₚ-refl (A * B) = sub-prod (<:ₚ-refl A) (<:ₚ-refl B)
<:ₚ-refl (A + B) = sub-sum (<:ₚ-refl A) (<:ₚ-refl B)
<:ₚ-refl (A ⇒[ mk-kind q π ] B) = sub-arr (<:ₚ-refl A) (<:ₚ-refl B) (⊑π-refl π)
<:ₚ-refl (μ-type F) = sub-μ
<:ₚ-refl (ν-type F π) = sub-ν (⊑π-refl π)

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

------------------------------------------------------------------------
-- Substitution on contexts and terms
------------------------------------------------------------------------

_⟨_⟩ᶜ : ∀ {m k n} → PCtx m n → Sub m k → PCtx k n
∅           ⟨ σ ⟩ᶜ = ∅
(Γ , A ^ q) ⟨ σ ⟩ᶜ = (Γ ⟨ σ ⟩ᶜ) , (A ⟨ σ ⟩) ^ q

lookup-⟨⟩ : ∀ {m k n} (Γ : PCtx m n) (σ : Sub m k) (i : Fin n) → lookupP (Γ ⟨ σ ⟩ᶜ) i ≡ lookupP Γ i ⟨ σ ⟩
lookup-⟨⟩ (Γ , A ^ q) σ zero    = refl
lookup-⟨⟩ (Γ , A ^ q) σ (suc i) = lookup-⟨⟩ Γ σ i

_⟨_⟩ₜ : ∀ {m k n} → PTm m n → Sub m k → PTm k n
var i        ⟨ σ ⟩ₜ = var i
lam t        ⟨ σ ⟩ₜ = lam (t ⟨ σ ⟩ₜ)
app t u      ⟨ σ ⟩ₜ = app (t ⟨ σ ⟩ₜ) (u ⟨ σ ⟩ₜ)
let′ t u     ⟨ σ ⟩ₜ = let′ (t ⟨ σ ⟩ₜ) (u ⟨ σ ⟩ₜ)
unit         ⟨ σ ⟩ₜ = unit
pair t u     ⟨ σ ⟩ₜ = pair (t ⟨ σ ⟩ₜ) (u ⟨ σ ⟩ₜ)
fst t        ⟨ σ ⟩ₜ = fst (t ⟨ σ ⟩ₜ)
snd t        ⟨ σ ⟩ₜ = snd (t ⟨ σ ⟩ₜ)
inl t        ⟨ σ ⟩ₜ = inl (t ⟨ σ ⟩ₜ)
inr t        ⟨ σ ⟩ₜ = inr (t ⟨ σ ⟩ₜ)
case s l r   ⟨ σ ⟩ₜ = case (s ⟨ σ ⟩ₜ) (l ⟨ σ ⟩ₜ) (r ⟨ σ ⟩ₜ)
absurd t     ⟨ σ ⟩ₜ = absurd (t ⟨ σ ⟩ₜ)
roll t       ⟨ σ ⟩ₜ = roll (t ⟨ σ ⟩ₜ)
fold a t     ⟨ σ ⟩ₜ = fold (a ⟨ σ ⟩ₜ) (t ⟨ σ ⟩ₜ)
unfold c t   ⟨ σ ⟩ₜ = unfold (c ⟨ σ ⟩ₜ) (t ⟨ σ ⟩ₜ)
out t        ⟨ σ ⟩ₜ = out (t ⟨ σ ⟩ₜ)
coerce A B t ⟨ σ ⟩ₜ = coerce (A ⟨ σ ⟩) (B ⟨ σ ⟩) (t ⟨ σ ⟩ₜ)
lit l        ⟨ σ ⟩ₜ = lit l
prim p t     ⟨ σ ⟩ₜ = prim p (t ⟨ σ ⟩ₜ)
sigop c A    ⟨ σ ⟩ₜ = sigop c A
ref d τ      ⟨ σ ⟩ₜ = ref d (λ i → τ i ⟨ σ ⟩)

infixl 60 _⟨_⟩ᶜ _⟨_⟩ₜ

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
tsubst {Δ′ = Δ′} {Γ = Γ} {π = π} σ r (⊢fold {Ψa = Ψa} {F = F} {A = A} {alg = alg} wf a t) =
  ⊢fold (wf-⟨⟩ r wf)
    (subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψa ] alg ⟨ σ ⟩ₜ ∷ X ⇒[ mk-kind Many π ] A ⟨ σ ⟩ ! π) (⟦⟧F-⟨⟩ F A σ)
           (tsubst σ r a))
    (tsubst σ r t)
tsubst {Δ′ = Δ′} {Γ = Γ} σ r (⊢unfold {Ψc = Ψc} {π = π} {π′ = π′} {F = F} {A = A} {c = c} wf k x) =
  ⊢unfold (wf-⟨⟩ r wf)
    (subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψc ] c ⟨ σ ⟩ₜ ∷ A ⟨ σ ⟩ ⇒[ mk-kind Many π ] X ! π′) (⟦⟧F-⟨⟩ F A σ)
           (tsubst σ r k))
    (tsubst σ r x)
tsubst {Δ′ = Δ′} {Γ = Γ} {Ψ = Ψ} σ r (⊢out {π = π} {F = F} {t = t} wf d) =
  subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] out (t ⟨ σ ⟩ₜ) ∷ X ! π) (sym (⟦⟧F-⟨⟩ F (ν-type F π) σ))
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
tsubst {Δ′ = Δ′} {Γ = Γ} σ r (⊢ref d τ k) =
  subst (λ X → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ zeroUsage ] ref d (λ i → τ i ⟨ σ ⟩) ∷ X ! pure)
        (sym (⟨⟩-∘ (type (S !! d)) τ σ))
        (⊢ref d (λ i → τ i ⟨ σ ⟩) (λ i e → base-⟨⟩ r (k i e)))
