-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.AbsTy — D243: abstracting TYPES (`rigid k i ↦ var i`),
-- independent of any signature. See `Once.Spec.Core.Abstract`.
------------------------------------------------------------------------

module Once.Spec.Core.AbsTy where

open import Data.Nat using (ℕ; zero; suc; _<?_)
import Data.Nat
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

import Once.Type as T
open T using (TKind; k-base; k-any; Purity; mk-kind; Many)
open import Once.Type.DecEq using (_≟tk_)
open import Once.Type.Rigid using (RigidFree; RigidFreeF; rf-Unit; rf-Void; rf-Int; rf-Float;
  rf-*; rf-+; rf-⇒; rf-μ; rf-ν; rf-K; rf-Id; rf-⊕; rf-⊗)
open import Once.Functor.Translate using (IsBaseType; WellFormedF; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; base-rigid)
import Once.Functor.Translate as Tr
open import Once.Spec.Core.PolyTy

------------------------------------------------------------------------
-- Abstracting types
------------------------------------------------------------------------

-- `rigid k i` becomes `var i` when `i` is a variable of `Δ` of kind `k`.
ar-kind : ∀ {m} (Δ : KCtx m) (k : TKind) (i : ℕ) (j : Fin m) → Dec (Δ j ≡ k) → Ty m
ar-kind Δ k i j (yes _) = var j
ar-kind Δ k i j (no _)  = rigid k i

ar-bound : ∀ {m} (Δ : KCtx m) (k : TKind) (i : ℕ) → Dec (i Data.Nat.< m) → Ty m
ar-bound Δ k i (yes p) = ar-kind Δ k i (fromℕ< p) (Δ (fromℕ< p) ≟tk k)
ar-bound Δ k i (no _)  = rigid k i

absRigid : ∀ {m} (Δ : KCtx m) (k : TKind) (i : ℕ) → Ty m
absRigid {m} Δ k i = ar-bound Δ k i (i <? m)

mutual
  absTy : ∀ {m} (Δ : KCtx m) → T.Type → Ty m
  absTy Δ T.Unit          = Unit
  absTy Δ T.Void          = Void
  absTy Δ T.Int           = Int
  absTy Δ T.Float         = Float
  absTy Δ (A T.* B)       = absTy Δ A * absTy Δ B
  absTy Δ (A T.+ B)       = absTy Δ A + absTy Δ B
  absTy Δ (A T.⇒[ k ] B)  = absTy Δ A ⇒[ k ] absTy Δ B
  absTy Δ (T.μ-type F)    = μ-type (absF Δ F)
  absTy Δ (T.ν-type F π)  = ν-type (absF Δ F) π
  absTy Δ (T.rigid k i)   = absRigid Δ k i

  absF : ∀ {m} (Δ : KCtx m) → T.Functor → Fun m
  absF Δ (T.K A)   = K (absTy Δ A)
  absF Δ T.Id      = Id
  absF Δ (F T.⊕ G) = absF Δ F ⊕ absF Δ G
  absF Δ (F T.⊗ G) = absF Δ F ⊗ absF Δ G

-- Functor application commutes with abstraction.
absTy-⟦⟧ : ∀ {m} (Δ : KCtx m) (F : T.Functor) (A : T.Type) → absTy Δ (T.⟦ F ⟧T A) ≡ ⟦ absF Δ F ⟧F (absTy Δ A)
absTy-⟦⟧ Δ (T.K B)   A = refl
absTy-⟦⟧ Δ T.Id      A = refl
absTy-⟦⟧ Δ (F T.⊕ G) A = cong₂ _+_ (absTy-⟦⟧ Δ F A) (absTy-⟦⟧ Δ G A)
absTy-⟦⟧ Δ (F T.⊗ G) A = cong₂ _*_ (absTy-⟦⟧ Δ F A) (absTy-⟦⟧ Δ G A)

-- A ground type abstracts to its embedding.
mutual
  absTy-ground : ∀ {m} (Δ : KCtx m) {A : T.Type} → RigidFree A → absTy Δ A ≡ ⌈ A ⌉
  absTy-ground Δ rf-Unit   = refl
  absTy-ground Δ rf-Void   = refl
  absTy-ground Δ rf-Int    = refl
  absTy-ground Δ rf-Float  = refl
  absTy-ground Δ (rf-* a b) = cong₂ _*_ (absTy-ground Δ a) (absTy-ground Δ b)
  absTy-ground Δ (rf-+ a b) = cong₂ _+_ (absTy-ground Δ a) (absTy-ground Δ b)
  absTy-ground Δ (rf-⇒ {k = k} a b) = cong₂ (λ x y → x ⇒[ k ] y) (absTy-ground Δ a) (absTy-ground Δ b)
  absTy-ground Δ (rf-μ f) = cong μ-type (absF-ground Δ f)
  absTy-ground Δ (rf-ν {π = π} f) = cong (λ G → ν-type G π) (absF-ground Δ f)

  absF-ground : ∀ {m} (Δ : KCtx m) {F : T.Functor} → RigidFreeF F → absF Δ F ≡ ⌈ F ⌉F
  absF-ground Δ (rf-K a) = cong K (absTy-ground Δ a)
  absF-ground Δ rf-Id = refl
  absF-ground Δ (rf-⊕ f g) = cong₂ _⊕_ (absF-ground Δ f) (absF-ground Δ g)
  absF-ground Δ (rf-⊗ f g) = cong₂ _⊗_ (absF-ground Δ f) (absF-ground Δ g)

------------------------------------------------------------------------
-- Kinds survive abstraction
------------------------------------------------------------------------

private
  base-ar-kind : ∀ {m} (Δ : KCtx m) (i : ℕ) (j : Fin m) (d : Dec (Δ j ≡ k-base))
    → Base Δ (ar-kind Δ k-base i j d)
  base-ar-kind Δ i j (yes e) = b-var e
  base-ar-kind Δ i j (no _)  = b-rigid

  base-ar-bound : ∀ {m} (Δ : KCtx m) (i : ℕ) (d : Dec (i Data.Nat.< m)) → Base Δ (ar-bound Δ k-base i d)
  base-ar-bound Δ i (yes p) = base-ar-kind Δ i (fromℕ< p) (Δ (fromℕ< p) ≟tk k-base)
  base-ar-bound Δ i (no _)  = b-rigid

abs-base : ∀ {m} (Δ : KCtx m) {A : T.Type} → IsBaseType A → Base Δ (absTy Δ A)
abs-base Δ base-Unit   = b-Unit
abs-base Δ base-Void   = b-Void
abs-base Δ base-Int    = b-Int
abs-base Δ base-Float  = b-Float
abs-base Δ (base-Prod a b) = b-Prod (abs-base Δ a) (abs-base Δ b)
abs-base Δ (base-Sum a b)  = b-Sum (abs-base Δ a) (abs-base Δ b)
abs-base {m} Δ (base-rigid {i}) = base-ar-bound Δ i (i <? m)

abs-wf : ∀ {m} (Δ : KCtx m) {F : T.Functor} → WellFormedF F → WFFun Δ (absF Δ F)
abs-wf Δ (Tr.wf-K b)      = wf-K (abs-base Δ b)
abs-wf Δ Tr.wf-Id         = wf-Id
abs-wf Δ (Tr.wf-Sum f g)  = wf-Sum (abs-wf Δ f) (abs-wf Δ g)
abs-wf Δ (Tr.wf-Prod f g) = wf-Prod (abs-wf Δ f) (abs-wf Δ g)

mutual
  data ConstFree {m} : Ty m → Set where
    cf-var    : ∀ {i} → ConstFree (var i)
    cf-Unit   : ConstFree Unit
    cf-Void   : ConstFree Void
    cf-Int    : ConstFree Int
    cf-Float  : ConstFree Float
    cf-*      : ∀ {A B} → ConstFree A → ConstFree B → ConstFree (A * B)
    cf-+      : ∀ {A B} → ConstFree A → ConstFree B → ConstFree (A + B)
    cf-⇒      : ∀ {A B k} → ConstFree A → ConstFree B → ConstFree (A ⇒[ k ] B)
    cf-μ      : ∀ {F} → ConstFreeF F → ConstFree (μ-type F)
    cf-ν      : ∀ {F π} → ConstFreeF F → ConstFree (ν-type F π)

  data ConstFreeF {m} : Fun m → Set where
    cf-K  : ∀ {A} → ConstFree A → ConstFreeF (K A)
    cf-Id : ConstFreeF Id
    cf-⊕  : ∀ {F G} → ConstFreeF F → ConstFreeF G → ConstFreeF (F ⊕ G)
    cf-⊗  : ∀ {F G} → ConstFreeF F → ConstFreeF G → ConstFreeF (F ⊗ G)

-- Instantiating a constant-free type, then abstracting, is substituting the
-- abstracted instance.
mutual
  abs-⟪⟫ : ∀ {m k} (Δ : KCtx m) {A : Ty k} (τ : GSub k) → ConstFree A
         → absTy Δ (A ⟪ τ ⟫) ≡ A ⟨ (λ i → absTy Δ (τ i)) ⟩
  abs-⟪⟫ Δ τ cf-var    = refl
  abs-⟪⟫ Δ τ cf-Unit   = refl
  abs-⟪⟫ Δ τ cf-Void   = refl
  abs-⟪⟫ Δ τ cf-Int    = refl
  abs-⟪⟫ Δ τ cf-Float  = refl
  abs-⟪⟫ Δ τ (cf-* a b) = cong₂ _*_ (abs-⟪⟫ Δ τ a) (abs-⟪⟫ Δ τ b)
  abs-⟪⟫ Δ τ (cf-+ a b) = cong₂ _+_ (abs-⟪⟫ Δ τ a) (abs-⟪⟫ Δ τ b)
  abs-⟪⟫ Δ τ (cf-⇒ {k = k} a b) = cong₂ (λ x y → x ⇒[ k ] y) (abs-⟪⟫ Δ τ a) (abs-⟪⟫ Δ τ b)
  abs-⟪⟫ Δ τ (cf-μ f) = cong μ-type (absF-⟪⟫ Δ τ f)
  abs-⟪⟫ Δ τ (cf-ν {π = π} f) = cong (λ G → ν-type G π) (absF-⟪⟫ Δ τ f)

  absF-⟪⟫ : ∀ {m k} (Δ : KCtx m) {F : Fun k} (τ : GSub k) → ConstFreeF F
          → absF Δ (F ⟪ τ ⟫F) ≡ F ⟨ (λ i → absTy Δ (τ i)) ⟩F
  absF-⟪⟫ Δ τ (cf-K a) = cong K (abs-⟪⟫ Δ τ a)
  absF-⟪⟫ Δ τ cf-Id = refl
  absF-⟪⟫ Δ τ (cf-⊕ f g) = cong₂ _⊕_ (absF-⟪⟫ Δ τ f) (absF-⟪⟫ Δ τ g)
  absF-⟪⟫ Δ τ (cf-⊗ f g) = cong₂ _⊗_ (absF-⟪⟫ Δ τ f) (absF-⟪⟫ Δ τ g)

