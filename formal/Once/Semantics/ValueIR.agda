-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Semantics.ValueIR
--
-- The IR-object value domain (Plan 0.52 M2). IR objects are the ungraded
-- `Once.IRTy`; this reuses the surface value domain `Once.Semantics.Value.⟦_⟧`
-- via the canonical section `⌈_⌉ : IRTy → Type`:
--
--   ⟦ A ⟧ᴵ  :=  ⟦ ⌈ A ⌉ ⟧
--
-- The coherence `⟦ ⌊ T ⌋ ⟧ᴵ ≡ ⟦ T ⟧` (`coh`) is the load-bearing bridge for
-- the S2 re-thread: everywhere a proof used `⟦ T ⟧` on an IR object it now uses
-- `⟦ ⌊ T ⌋ ⟧ᴵ`, and `coh` rewrites between them, so no correctness proof
-- genuinely changes — it TRANSPORTS across the grade erasure. Sound because
-- the value domain is grade-blind (the arrow ignores its kind; `⟦_⟧-base`
-- sends every arrow / fixpoint to `⊤`).
------------------------------------------------------------------------

-- Plan 0.72 (D112): `FloatRep` joins `IntRep`, as in `Semantics.Value`.
module Once.Semantics.ValueIR (IntRep : Set) (FloatRep : Set) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)

open import Once.Type
open import Once.IRTy using (IRTy; IRFunctor; ⌈_⌉; ⌈_⌉F; ⌊_⌋; eraseF)
open import Once.Functor.Translate using (⟦_,_⟧-base; translateF)
open import Once.Semantics.Functor using (SK; _S⊕_; _S⊗_; μS; νS)
open import Once.Semantics.Value IntRep FloatRep using (⟦_⟧; ⟦_⟧F; ⟦μ⟧; ⟦ν⟧)

------------------------------------------------------------------------
-- The IR-object value domain: the surface domain at the canonical rep.

⟦_⟧ᴵ : IRTy → Set
⟦ A ⟧ᴵ = ⟦ ⌈ A ⌉ ⟧

-- The IR functor's Set-interpretation, likewise via the section.
⟦_⟧Fᴵ : IRFunctor → Set → Set
⟦ F ⟧Fᴵ X = ⟦ ⌈ F ⌉F ⟧F X

------------------------------------------------------------------------
-- Coherence: erasing a surface type and re-denoting is the identity.

-- Grade-blindness of the base carrier: `⟦_⟧-base` sends arrows and μ/ν to
-- `⊤`, so re-grading (`⌈ ⌊ · ⌋ ⌉`) leaves it unchanged.
base-coh : ∀ (A : Type) → ⟦ IntRep , FloatRep ⟧-base ⌈ ⌊ A ⌋ ⌉ ≡ ⟦ IntRep , FloatRep ⟧-base A
base-coh Unit          = refl
base-coh Void          = refl
base-coh (A * B)       = cong₂ _×_ (base-coh A) (base-coh B)
base-coh (A + B)       = cong₂ _⊎_ (base-coh A) (base-coh B)
base-coh (A ⇒[ k ] B)  = refl
base-coh (μ-type F)    = refl
base-coh (ν-type F)    = refl
base-coh Int           = refl
base-coh Float         = refl
base-coh Str           = refl
base-coh Buffer        = refl

-- The translated SFunctor is unchanged by re-grading (its only Type-payloads
-- are the `K`-constants, handled by `base-coh`).
tF-coh : ∀ (F : Functor) → translateF IntRep FloatRep ⌈ eraseF F ⌉F ≡ translateF IntRep FloatRep F
tF-coh (K A)   = cong SK (base-coh A)
tF-coh Id      = refl
tF-coh (F ⊕ G) = cong₂ _S⊕_ (tF-coh F) (tF-coh G)
tF-coh (F ⊗ G) = cong₂ _S⊗_ (tF-coh F) (tF-coh G)

-- The bridge: `⟦ ⌊ T ⌋ ⟧ᴵ ≡ ⟦ T ⟧`.
coh : ∀ (T : Type) → ⟦ ⌊ T ⌋ ⟧ᴵ ≡ ⟦ T ⟧
coh Unit          = refl
coh Void          = refl
coh (A * B)       = cong₂ _×_ (coh A) (coh B)
coh (A + B)       = cong₂ _⊎_ (coh A) (coh B)
coh (A ⇒[ k ] B)  = cong₂ (λ x y → x → y) (coh A) (coh B)
coh (μ-type F)    = cong μS (tF-coh F)
coh (ν-type F)    = cong νS (tF-coh F)
coh Int           = refl
coh Float         = refl
coh Str           = refl
coh Buffer        = refl
