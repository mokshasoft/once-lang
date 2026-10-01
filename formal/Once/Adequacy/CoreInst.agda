-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreInst — plan 0.104 E.2 (i): the core's rigid
-- substitution on derivations, and that instantiating an abstraction IS it.
--
-- `ρ̂ᶜ` maps a ground derivation whose types mention rigids to the derivation
-- at the substituted types, rule by rule (`ρ̂ = absTy Δ _ ⟪ τ ⟫`, the surface's
-- `RigidSubst.ρ̂`). Its term is `absTm Δ t ⟪ τ ⟫ₜ` definitionally, the term
-- `instantiate ∘ abs-⊢` produces. The round trip of CoreAbsSem (arity 0) is the
-- instance at `τ` of the empty context.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig; KCtx; GSub; Respects)

module Once.Adequacy.CoreInst {s : ℕ} (S : Sig s) {m : ℕ} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ) where

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import Once.Type as T
open T using (Type; mk-kind; Many; pure; μ-type; ν-type; ⟦_⟧T)
import Once.Surface.Context as C
open import Once.Spec.Core.PolyTy using (_⟪_⟫; _!!_; type; ⟨⟩-⟪⟫; ⌈⌉-⟪⟫)
open import Once.Spec.Core.AbsTy using (absTy; abs-⟪⟫)
import Once.Spec.Core.Syntax S as G
import Once.Spec.Core.Typing S as GT
open GT using (_⊢[_]_∷_!_)
import Once.Spec.Core.PolyTyping S as PT
open PT using (_⟪_⟫ᶜ; _⟪_⟫ₜ)
open import Once.Spec.Core.Abstract S using (SigGround; absCtx; absTm; abs-⊢; primDom-abs; primCod-abs)
import Once.TypeCheck.RigidSubst Δ τ r as RS
open RS using (ρ̂; ρ̂F; ρ̂S; ρ̂-⟦⟧; ρ̂-wf; ρ̂-<:; ρ̂-rf; ρ̂-base; lookup-ρ̂)
open import Once.Adequacy.CoreAbsSem S using (tr)

ρ̂ₜ : ∀ {n} → G.Tm n → G.Tm n
ρ̂ₜ t = absTm Δ t ⟪ τ ⟫ₜ

-- The primitives' types are ground.
ρ̂-dom : ∀ p → ρ̂ (G.primDom p) ≡ G.primDom p
ρ̂-dom p = trans (cong (_⟪ τ ⟫) (primDom-abs Δ p)) (⌈⌉-⟪⟫ (G.primDom p) τ)

ρ̂-cod : ∀ p → ρ̂ (G.primCod p) ≡ G.primCod p
ρ̂-cod p = trans (cong (_⟪ τ ⟫) (primCod-abs Δ p)) (⌈⌉-⟪⟫ (G.primCod p) τ)

module _ (sg : SigGround) where

  -- A definition's instance, substituted, is the substituted instance.
  ρ̂-ref : ∀ d (τ′ : GSub (Once.Spec.Core.PolyTy.arity (S !! d)))
        → ρ̂ (type (S !! d) ⟪ τ′ ⟫) ≡ type (S !! d) ⟪ (λ i → ρ̂ (τ′ i)) ⟫
  ρ̂-ref d τ′ = trans (cong (_⟪ τ ⟫) (abs-⟪⟫ Δ τ′ (sg d))) (⟨⟩-⟪⟫ (type (S !! d)) (λ i → absTy Δ (τ′ i)) τ)

  ρ̂ᶜ : ∀ {n} {Γ : C.Ctx n} {Ψ t A π} → Γ ⊢[ Ψ ] t ∷ A ! π → ρ̂S Γ ⊢[ Ψ ] ρ̂ₜ t ∷ ρ̂ A ! π
  ρ̂ᶜ {Γ = Γ} (GT.⊢var i) = subst (λ X → ρ̂S Γ ⊢[ _ ] G.var i ∷ X ! pure) (lookup-ρ̂ Γ i) (GT.⊢var i)
  ρ̂ᶜ (GT.⊢lam le d)    = GT.⊢lam le (ρ̂ᶜ d)
  ρ̂ᶜ (GT.⊢app f x)     = GT.⊢app (ρ̂ᶜ f) (ρ̂ᶜ x)
  ρ̂ᶜ (GT.⊢let e b)     = GT.⊢let (ρ̂ᶜ e) (ρ̂ᶜ b)
  ρ̂ᶜ GT.⊢unit          = GT.⊢unit
  ρ̂ᶜ (GT.⊢pair a b)    = GT.⊢pair (ρ̂ᶜ a) (ρ̂ᶜ b)
  ρ̂ᶜ (GT.⊢fst p)       = GT.⊢fst (ρ̂ᶜ p)
  ρ̂ᶜ (GT.⊢snd p)       = GT.⊢snd (ρ̂ᶜ p)
  ρ̂ᶜ (GT.⊢inl a)       = GT.⊢inl (ρ̂ᶜ a)
  ρ̂ᶜ (GT.⊢inr b)       = GT.⊢inr (ρ̂ᶜ b)
  ρ̂ᶜ (GT.⊢case s l x)  = GT.⊢case (ρ̂ᶜ s) (ρ̂ᶜ l) (ρ̂ᶜ x)
  ρ̂ᶜ (GT.⊢absurd e)    = GT.⊢absurd (ρ̂ᶜ e)
  ρ̂ᶜ {Γ = Γ} {Ψ = Ψ} {π = π} (GT.⊢roll {F = F} {t = t} wf d) =
    GT.⊢roll (ρ̂-wf wf) (subst (λ X → ρ̂S Γ ⊢[ Ψ ] ρ̂ₜ t ∷ X ! π) (ρ̂-⟦⟧ F (μ-type F)) (ρ̂ᶜ d))
  ρ̂ᶜ {Γ = Γ} {π = π} (GT.⊢fold {Ψa = Ψa} {F = F} {A = A} {alg = alg} wf a t) =
    GT.⊢fold (ρ̂-wf wf)
      (subst (λ X → ρ̂S Γ ⊢[ Ψa ] ρ̂ₜ alg ∷ X T.⇒[ mk-kind Many π ] ρ̂ A ! π) (ρ̂-⟦⟧ F A) (ρ̂ᶜ a))
      (ρ̂ᶜ t)
  ρ̂ᶜ {Γ = Γ} (GT.⊢unfold {Ψc = Ψc} {π = π} {π′ = π′} {F = F} {A = A} {c = c} wf k x) =
    GT.⊢unfold (ρ̂-wf wf)
      (subst (λ X → ρ̂S Γ ⊢[ Ψc ] ρ̂ₜ c ∷ ρ̂ A T.⇒[ mk-kind Many π ] X ! π′) (ρ̂-⟦⟧ F A) (ρ̂ᶜ k))
      (ρ̂ᶜ x)
  ρ̂ᶜ {Γ = Γ} {Ψ = Ψ} (GT.⊢out {π = π} {F = F} {t = t} wf d) =
    subst (λ X → ρ̂S Γ ⊢[ Ψ ] G.out (ρ̂ₜ t) ∷ X ! π) (sym (ρ̂-⟦⟧ F (ν-type F π))) (GT.⊢out (ρ̂-wf wf) (ρ̂ᶜ d))
  ρ̂ᶜ (GT.⊢coerce p d)  = GT.⊢coerce (ρ̂-<: p) (ρ̂ᶜ d)
  ρ̂ᶜ GT.⊢lit-int       = GT.⊢lit-int
  ρ̂ᶜ GT.⊢lit-float     = GT.⊢lit-float
  ρ̂ᶜ GT.⊢lit-str       = GT.⊢lit-str
  ρ̂ᶜ {Γ = Γ} {Ψ = Ψ} {π = π} (GT.⊢prim {t = t} p d) =
    subst (λ X → ρ̂S Γ ⊢[ Ψ ] G.prim p (ρ̂ₜ t) ∷ X ! π) (sym (ρ̂-cod p))
      (GT.⊢prim p (subst (λ X → ρ̂S Γ ⊢[ Ψ ] ρ̂ₜ t ∷ X ! π) (ρ̂-dom p) (ρ̂ᶜ d)))
  ρ̂ᶜ {Γ = Γ} (GT.⊢sigop {A = A} c k h g) =
    subst (λ X → ρ̂S Γ ⊢[ C.zeroUsage ] G.sigop c A ∷ X ! pure) (sym (ρ̂-rf g)) (GT.⊢sigop c k h g)
  ρ̂ᶜ (GT.⊢sub-eff g d) = GT.⊢sub-eff g (ρ̂ᶜ d)
  ρ̂ᶜ {Γ = Γ} (GT.⊢ref d τ′ k) =
    subst (λ X → ρ̂S Γ ⊢[ C.zeroUsage ] G.ref d (λ i → ρ̂ (τ′ i)) ∷ X ! pure) (sym (ρ̂-ref d τ′))
      (GT.⊢ref d (λ i → ρ̂ (τ′ i)) (λ i e → ρ̂-base (k i e)))

  -- The context of the instantiated abstraction is the substituted context.
  ρ̂S-abs : ∀ {n} (Γ : C.Ctx n) → absCtx Δ Γ ⟪ τ ⟫ᶜ ≡ ρ̂S Γ
  ρ̂S-abs C.∅           = refl
  ρ̂S-abs (Γ C., A ^ q) = cong (λ G → G C., ρ̂ A ^ q) (ρ̂S-abs Γ)

  -- RESIDUAL (plan 0.104 E.2 (i), deferred proof, discharged next): the
  -- instantiated abstraction is the substitution (CoreAbsSem's round trip,
  -- at any instance).
  postulate
    inst-abs : ∀ {n} {Γ : C.Ctx n} {Ψ t A π} (D : Γ ⊢[ Ψ ] t ∷ A ! π)
             → tr (ρ̂S-abs Γ) refl refl (PT.instantiate τ r (abs-⊢ Δ sg D)) ≡ ρ̂ᶜ D
