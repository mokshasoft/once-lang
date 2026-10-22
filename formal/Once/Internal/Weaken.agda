-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Weaken — a ground type read over type variables means what
-- it means as a ground type.
--
-- A polymorphic body is typed over its parameters (`Ty m`); what it refers to
-- outside itself — an external operation, a monomorphic definition, an
-- annotation — has a ground type `T`, read there as `wk₀ T`. The meanings
-- agree: `⟦ wk₀ T ⟧ ≡ ⟦ T ⟧` in each domain, so a reference's meaning at its
-- ground type is transported to the body's.
------------------------------------------------------------------------

module Once.Internal.Weaken where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Once.Spec.Grade using (mk-kind; Zero; One; Many; pureᶠ; actᶠ)
open import Once.Spec.Type
  using (Ty; Fun; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
open import Once.Internal.Type using (wk₀; wk₀F)
open import Once.Internal.FunctorMeaning using (⟦_,_⟧-base; translateF; μ-sem; ν-sem)
open import Once.Internal.Polynomial using (SK; _S⊕_; _S⊗_; μS; νS)

------------------------------------------------------------------------
-- Base values and functor codes
------------------------------------------------------------------------

base-wk₀ : ∀ {m} (I F : Set) (A : Type) → ⟦ I , F ⟧-base (wk₀ {m} A) ≡ ⟦ I , F ⟧-base A
base-wk₀ I F Unit         = refl
base-wk₀ I F Void         = refl
base-wk₀ I F Int          = refl
base-wk₀ I F Float        = refl
base-wk₀ I F (A * B)      = cong₂ _×_ (base-wk₀ I F A) (base-wk₀ I F B)
base-wk₀ I F (A + B)      = cong₂ _⊎_ (base-wk₀ I F A) (base-wk₀ I F B)
base-wk₀ I F (A ⇒[ _ ] B) = refl
base-wk₀ I F (μ _)        = refl
base-wk₀ I F (ν _ _)      = refl

translateF-wk₀ : ∀ {m} (I F : Set) (G : Fun 0) → translateF I F (wk₀F {m} G) ≡ translateF I F G
translateF-wk₀ I F (K A)   = cong SK (base-wk₀ I F A)
translateF-wk₀ I F Id      = refl
translateF-wk₀ I F (G ⊕ H) = cong₂ _S⊕_ (translateF-wk₀ I F G) (translateF-wk₀ I F H)
translateF-wk₀ I F (G ⊗ H) = cong₂ _S⊗_ (translateF-wk₀ I F G) (translateF-wk₀ I F H)

μ-sem-wk₀ : ∀ {m} (I F : Set) (G : Fun 0) → μ-sem I F (wk₀F {m} G) ≡ μ-sem I F G
μ-sem-wk₀ I F G = cong μS (translateF-wk₀ I F G)

ν-sem-wk₀ : ∀ {m} (I F : Set) (G : Fun 0) → ν-sem I F (wk₀F {m} G) ≡ ν-sem I F G
ν-sem-wk₀ I F G = cong νS (translateF-wk₀ I F G)

------------------------------------------------------------------------
-- The machine's value domain
------------------------------------------------------------------------

open import Once.Internal.Res using (Res)

module ValueWk₀ (I F : Set) where
  open import Once.Internal.Value I F using (⟦_⟧)

  ⟦wk₀⟧ : ∀ {m} (A : Type) → ⟦ wk₀ {m} A ⟧ ≡ ⟦ A ⟧
  ⟦wk₀⟧ Unit                       = refl
  ⟦wk₀⟧ Void                       = refl
  ⟦wk₀⟧ Int                        = refl
  ⟦wk₀⟧ Float                      = refl
  ⟦wk₀⟧ (A * B)                    = cong₂ _×_ (⟦wk₀⟧ A) (⟦wk₀⟧ B)
  ⟦wk₀⟧ (A + B)                    = cong₂ _⊎_ (⟦wk₀⟧ A) (⟦wk₀⟧ B)
  ⟦wk₀⟧ (A ⇒[ mk-kind Zero π ] B)  = cong (λ Y → ⟦ Unit {0} ⟧ → Res Y) (⟦wk₀⟧ B)
  ⟦wk₀⟧ (A ⇒[ mk-kind One π ] B)   = cong₂ (λ X Y → X → Res Y) (⟦wk₀⟧ A) (⟦wk₀⟧ B)
  ⟦wk₀⟧ (A ⇒[ mk-kind Many π ] B)  = cong₂ (λ X Y → X → Res Y) (⟦wk₀⟧ A) (⟦wk₀⟧ B)
  ⟦wk₀⟧ (μ G)                      = μ-sem-wk₀ I F G
  ⟦wk₀⟧ (ν G _)                    = ν-sem-wk₀ I F G

------------------------------------------------------------------------
-- The graded values (the source's meaning)
------------------------------------------------------------------------

open import Once.Spec.Word using (Carrier)
open import Once.Internal.Graded using (⟦_⟧ᵛ; M)
open import Once.Internal.Stream using (νᵈ)
open import Once.Internal.Graded using (νᵖ)
open ValueWk₀ Carrier Carrier

⟦wk₀⟧ᵛ : ∀ {m} (A : Type) → ⟦ wk₀ {m} A ⟧ᵛ ≡ ⟦ A ⟧ᵛ
⟦wk₀⟧ᵛ Unit                       = refl
⟦wk₀⟧ᵛ Void                       = refl
⟦wk₀⟧ᵛ Int                        = refl
⟦wk₀⟧ᵛ Float                      = refl
⟦wk₀⟧ᵛ (A * B)                    = cong₂ _×_ (⟦wk₀⟧ᵛ A) (⟦wk₀⟧ᵛ B)
⟦wk₀⟧ᵛ (A + B)                    = cong₂ _⊎_ (⟦wk₀⟧ᵛ A) (⟦wk₀⟧ᵛ B)
⟦wk₀⟧ᵛ (A ⇒[ mk-kind Zero π ] B)  = cong (λ Y → _ → M π Y) (⟦wk₀⟧ᵛ B)
⟦wk₀⟧ᵛ (A ⇒[ mk-kind One π ] B)   = cong₂ (λ X Y → X → M π Y) (⟦wk₀⟧ᵛ A) (⟦wk₀⟧ᵛ B)
⟦wk₀⟧ᵛ (A ⇒[ mk-kind Many π ] B)  = cong₂ (λ X Y → X → M π Y) (⟦wk₀⟧ᵛ A) (⟦wk₀⟧ᵛ B)
⟦wk₀⟧ᵛ (μ G)                      = ⟦wk₀⟧ (μ G)
⟦wk₀⟧ᵛ (ν G pureᶠ)                = cong νᵖ (translateF-wk₀ Carrier Carrier G)
⟦wk₀⟧ᵛ (ν G actᶠ)                 = cong νᵈ (translateF-wk₀ Carrier Carrier G)

------------------------------------------------------------------------
-- The denotational value domain
------------------------------------------------------------------------

open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Internal.Iterative using (T∞)
open import Once.Internal.StreamInf using (νᴵ)
open import Data.Unit using (⊤)

⟦wk₀⟧ᴰ : ∀ {m} (A : Type) → ⟦ wk₀ {m} A ⟧ᴰ ≡ ⟦ A ⟧ᴰ
⟦wk₀⟧ᴰ Unit                       = refl
⟦wk₀⟧ᴰ Void                       = refl
⟦wk₀⟧ᴰ Int                        = refl
⟦wk₀⟧ᴰ Float                      = refl
⟦wk₀⟧ᴰ (A * B)                    = cong₂ _×_ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)
⟦wk₀⟧ᴰ (A + B)                    = cong₂ _⊎_ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)
⟦wk₀⟧ᴰ (A ⇒[ mk-kind Zero π ] B)  = cong (λ Y → ⊤ → T∞ Y) (⟦wk₀⟧ᴰ B)
⟦wk₀⟧ᴰ (A ⇒[ mk-kind One π ] B)   = cong₂ (λ X Y → X → T∞ Y) (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)
⟦wk₀⟧ᴰ (A ⇒[ mk-kind Many π ] B)  = cong₂ (λ X Y → X → T∞ Y) (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)
⟦wk₀⟧ᴰ (μ G)                      = ⟦wk₀⟧ (μ G)
⟦wk₀⟧ᴰ (ν G _)                    = cong νᴵ (translateF-wk₀ Carrier Carrier G)
