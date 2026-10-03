-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Abstract — D243 (plan 0.103 phase 6c/6d): ABSTRACTION.
--
-- A polymorphic definition's body is typed ONCE, at its schema with rigid
-- parameters, and elaborates (6b) to a ground core derivation whose types may
-- mention those rigid constants. Abstraction turns it into the definition's
-- `∀` entry over its kinds `Δ`: `rigid k i ↦ var i`.
--
-- `absTy Δ` abstracts `rigid k i` exactly when `i` is one of `Δ`'s variables
-- AND `k` is its kind; any other rigid stays a constant. So abstraction is
-- TOTAL — it needs no invariant about which rigids a derivation mentions — and
-- a base-kinded rigid stays base whichever way it goes. `abs-⊢` holds for every
-- ground derivation, given one fact about the signature: its entries' types
-- mention no rigid constant (they were abstracted themselves).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

open import Once.Spec.Contract using (ISig)
module Once.Spec.Core.Abstract {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (zero; suc; _<?_)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

import Once.Type as T
open T using (TKind; k-base; k-any; Purity; mk-kind; Many)
open import Once.Type.DecEq using (_≟tk_)
open import Once.Type.Sub using (_<:_; sub-void; sub-unit; sub-int; sub-float; sub-rigid;
  sub-arr; sub-prod; sub-sum; sub-μ; sub-ν)
open import Once.Type.Rigid using (RigidFree; RigidFreeF; rf-Unit; rf-Void; rf-Int; rf-Float;
  rf-*; rf-+; rf-⇒; rf-μ; rf-ν; rf-K; rf-Id; rf-⊕; rf-⊗)
open import Once.Functor.Translate using (IsBaseType; WellFormedF; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; base-rigid)
import Once.Functor.Translate as Tr
open import Once.Surface.Context as C using (Ctx; Usage)
open import Once.Spec.Core.PolyTy
import Once.Spec.Core.Syntax S as G
import Once.Spec.Core.Typing S as GT
open import Once.Spec.Core.PolyTyping S
open import Once.Spec.Core.TySubst S using (<:ₚ-refl)
open import Once.Spec.Core.AbsTy

------------------------------------------------------------------------
-- Subtyping survives abstraction
------------------------------------------------------------------------

abs-<: : ∀ {m} (Δ : KCtx m) {A B : T.Type} → A <: B → absTy Δ A <:ₚ absTy Δ B
abs-<: Δ sub-void   = sub-void
abs-<: Δ sub-unit   = sub-unit
abs-<: Δ sub-int    = sub-int
abs-<: Δ sub-float  = sub-float
abs-<: Δ (sub-rigid {k} {i}) = <:ₚ-refl (absRigid Δ k i)
abs-<: Δ (sub-arr a b g) = sub-arr (abs-<: Δ a) (abs-<: Δ b) g
abs-<: Δ (sub-prod a b)  = sub-prod (abs-<: Δ a) (abs-<: Δ b)
abs-<: Δ (sub-sum a b)   = sub-sum (abs-<: Δ a) (abs-<: Δ b)
abs-<: Δ sub-μ           = sub-μ
abs-<: Δ (sub-ν g)       = sub-ν g

------------------------------------------------------------------------
-- A signature whose entry types mention no rigid constant
------------------------------------------------------------------------

SigGround : Set
SigGround = ∀ (d : Fin s) → ConstFree (type (S !! d))

------------------------------------------------------------------------
-- Abstracting contexts and terms
------------------------------------------------------------------------

absCtx : ∀ {m n} (Δ : KCtx m) → Ctx n → PCtx m n
absCtx Δ C.∅             = ∅
absCtx Δ (Γ C., A ^ q)   = absCtx Δ Γ , absTy Δ A ^ q

absCtx-lookup : ∀ {m n} (Δ : KCtx m) (Γ : Ctx n) (i : Fin n) → lookupP (absCtx Δ Γ) i ≡ absTy Δ (C.lookup Γ i)
absCtx-lookup Δ (Γ C., A ^ q) zero    = refl
absCtx-lookup Δ (Γ C., A ^ q) (suc i) = absCtx-lookup Δ Γ i

absTm : ∀ {m n} (Δ : KCtx m) → G.Tm n → PTm m n
absTm Δ (G.var i)        = var i
absTm Δ (G.lam t)        = lam (absTm Δ t)
absTm Δ (G.app t u)      = app (absTm Δ t) (absTm Δ u)
absTm Δ (G.let′ t u)     = let′ (absTm Δ t) (absTm Δ u)
absTm Δ G.unit           = unit
absTm Δ (G.pair t u)     = pair (absTm Δ t) (absTm Δ u)
absTm Δ (G.fst t)        = fst (absTm Δ t)
absTm Δ (G.snd t)        = snd (absTm Δ t)
absTm Δ (G.inl t)        = inl (absTm Δ t)
absTm Δ (G.inr t)        = inr (absTm Δ t)
absTm Δ (G.case s l r)   = case (absTm Δ s) (absTm Δ l) (absTm Δ r)
absTm Δ (G.absurd t)     = absurd (absTm Δ t)
absTm Δ (G.roll t)       = roll (absTm Δ t)
absTm Δ (G.fold a t)     = fold (absTm Δ a) (absTm Δ t)
absTm Δ (G.unfold c t)   = unfold (absTm Δ c) (absTm Δ t)
absTm Δ (G.out t)        = out (absTm Δ t)
absTm Δ (G.coerce A B t) = coerce (absTy Δ A) (absTy Δ B) (absTm Δ t)
absTm Δ (G.lit l)        = lit l
absTm Δ (G.prim p t)     = prim p (absTm Δ t)
absTm Δ (G.sigop c A)    = sigop c A
absTm Δ (G.ref d τ)      = ref d (λ i → absTy Δ (τ i))

------------------------------------------------------------------------
-- The primitives' types are ground
------------------------------------------------------------------------

primDom-abs : ∀ {m} (Δ : KCtx m) (p : G.Prim) → absTy Δ (G.primDom p) ≡ ⌈ G.primDom p ⌉
primDom-abs Δ G.p-add  = refl
primDom-abs Δ G.p-sub  = refl
primDom-abs Δ G.p-mul  = refl
primDom-abs Δ G.p-div  = refl
primDom-abs Δ G.p-mod  = refl
primDom-abs Δ G.p-neg  = refl
primDom-abs Δ G.p-lt   = refl
primDom-abs Δ G.p-le   = refl
primDom-abs Δ G.p-gt   = refl
primDom-abs Δ G.p-ge   = refl
primDom-abs Δ G.p-eq   = refl
primDom-abs Δ G.p-ne   = refl
primDom-abs Δ G.p-fadd = refl
primDom-abs Δ G.p-fsub = refl
primDom-abs Δ G.p-fmul = refl
primDom-abs Δ G.p-fdiv = refl
primDom-abs Δ G.p-i2f  = refl

primCod-abs : ∀ {m} (Δ : KCtx m) (p : G.Prim) → absTy Δ (G.primCod p) ≡ ⌈ G.primCod p ⌉
primCod-abs Δ G.p-add  = refl
primCod-abs Δ G.p-sub  = refl
primCod-abs Δ G.p-mul  = refl
primCod-abs Δ G.p-div  = refl
primCod-abs Δ G.p-mod  = refl
primCod-abs Δ G.p-neg  = refl
primCod-abs Δ G.p-lt   = refl
primCod-abs Δ G.p-le   = refl
primCod-abs Δ G.p-gt   = refl
primCod-abs Δ G.p-ge   = refl
primCod-abs Δ G.p-eq   = refl
primCod-abs Δ G.p-ne   = refl
primCod-abs Δ G.p-fadd = refl
primCod-abs Δ G.p-fsub = refl
primCod-abs Δ G.p-fmul = refl
primCod-abs Δ G.p-fdiv = refl
primCod-abs Δ G.p-i2f  = refl

------------------------------------------------------------------------
-- THE ABSTRACTION THEOREM: every ground derivation abstracts
------------------------------------------------------------------------

abs-⊢ : ∀ {m} (Δ : KCtx m) → SigGround → ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {t A π}
      → Γ GT.⊢[ Ψ ] t ∷ A ! π
      → Δ ⊩ absCtx Δ Γ ⊢[ Ψ ] absTm Δ t ∷ absTy Δ A ! π
abs-⊢ Δ sg {Γ = Γ} (GT.⊢var i) =
  subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ _ ] var i ∷ X ! _) (absCtx-lookup Δ Γ i) (⊢var i)
abs-⊢ Δ sg (GT.⊢lam le d) = ⊢lam le (abs-⊢ Δ sg d)
abs-⊢ Δ sg (GT.⊢app f x) = ⊢app (abs-⊢ Δ sg f) (abs-⊢ Δ sg x)
abs-⊢ Δ sg (GT.⊢let e b) = ⊢let (abs-⊢ Δ sg e) (abs-⊢ Δ sg b)
abs-⊢ Δ sg GT.⊢unit = ⊢unit
abs-⊢ Δ sg (GT.⊢pair a b) = ⊢pair (abs-⊢ Δ sg a) (abs-⊢ Δ sg b)
abs-⊢ Δ sg (GT.⊢fst p) = ⊢fst (abs-⊢ Δ sg p)
abs-⊢ Δ sg (GT.⊢snd p) = ⊢snd (abs-⊢ Δ sg p)
abs-⊢ Δ sg (GT.⊢inl a) = ⊢inl (abs-⊢ Δ sg a)
abs-⊢ Δ sg (GT.⊢inr b) = ⊢inr (abs-⊢ Δ sg b)
abs-⊢ Δ sg (GT.⊢case s l r) = ⊢case (abs-⊢ Δ sg s) (abs-⊢ Δ sg l) (abs-⊢ Δ sg r)
abs-⊢ Δ sg (GT.⊢absurd e) = ⊢absurd (abs-⊢ Δ sg e)
abs-⊢ Δ sg {Γ = Γ} {Ψ = Ψ} {π = π} (GT.⊢roll {F = F} {t = t} wf d) =
  ⊢roll (abs-wf Δ wf)
    (subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψ ] absTm Δ t ∷ X ! π) (absTy-⟦⟧ Δ F (T.μ-type F)) (abs-⊢ Δ sg d))
abs-⊢ Δ sg {Γ = Γ} {π = π} (GT.⊢fold {Ψa = Ψa} {F = F} {A = A} {alg = alg} wf a t) =
  ⊢fold (abs-wf Δ wf)
    (subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψa ] absTm Δ alg ∷ X ⇒[ mk-kind Many π ] absTy Δ A ! π)
           (absTy-⟦⟧ Δ F A) (abs-⊢ Δ sg a))
    (abs-⊢ Δ sg t)
abs-⊢ Δ sg {Γ = Γ} (GT.⊢unfold {Ψc = Ψc} {π = π} {π′ = π′} {F = F} {A = A} {c = c} wf k x) =
  ⊢unfold (abs-wf Δ wf)
    (subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψc ] absTm Δ c ∷ absTy Δ A ⇒[ mk-kind Many π ] X ! π′)
           (absTy-⟦⟧ Δ F A) (abs-⊢ Δ sg k))
    (abs-⊢ Δ sg x)
abs-⊢ Δ sg {Γ = Γ} {Ψ = Ψ} (GT.⊢out {π = π} {F = F} {t = t} wf d) =
  subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψ ] out (absTm Δ t) ∷ X ! π) (sym (absTy-⟦⟧ Δ F (T.ν-type F π)))
    (⊢out (abs-wf Δ wf) (abs-⊢ Δ sg d))
abs-⊢ Δ sg (GT.⊢coerce p d) = ⊢coerce (abs-<: Δ p) (abs-⊢ Δ sg d)
abs-⊢ Δ sg GT.⊢lit-int   = ⊢lit-int
abs-⊢ Δ sg GT.⊢lit-float = ⊢lit-float
abs-⊢ Δ sg {Γ = Γ} {Ψ = Ψ} {π = π} (GT.⊢prim {t = t} p d) =
  subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψ ] prim p (absTm Δ t) ∷ X ! π) (sym (primCod-abs Δ p))
    (⊢prim p (subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ Ψ ] absTm Δ t ∷ X ! π) (primDom-abs Δ p) (abs-⊢ Δ sg d)))
abs-⊢ Δ sg {Γ = Γ} (GT.⊢sigop {A = A} c k h g m) =
  subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ C.zeroUsage ] sigop c A ∷ X ! T.pure) (sym (absTy-ground Δ g)) (⊢sigop c k h g m)
abs-⊢ Δ sg (GT.⊢sub-eff g d) = ⊢sub-eff g (abs-⊢ Δ sg d)
abs-⊢ Δ sg {Γ = Γ} (GT.⊢ref d τ r) =
  subst (λ X → Δ ⊩ absCtx Δ Γ ⊢[ C.zeroUsage ] ref d (λ i → absTy Δ (τ i)) ∷ X ! T.pure)
        (sym (abs-⟪⟫ Δ τ (sg d)))
        (⊢ref d (λ i → absTy Δ (τ i)) (λ i e → abs-base Δ (r i e)))
