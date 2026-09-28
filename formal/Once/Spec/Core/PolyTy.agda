-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.PolyTy — plan 0.103 phase 3: TYPE VARIABLES IN THE CORE.
--
-- SPEC. The core's types over `m` type variables (de Bruijn, `Fin m`), the
-- non-dependent fragment of OCP-0009's `Π (A : U)`:
--
--   * a variable has a KIND — the universe it ranges over. `base` ranges over
--     the base types (the first-order, FFI-representable ones); `any` over all
--     monotypes. The kinds are forced by the type language, not chosen: a
--     functor's `K` positions hold BASE types (`WellFormedF`), so a variable
--     used there (`List a = μ (K Unit ⊕ (K a ⊗ Id))`) must range over base
--     types, or its instances would not be well-formed;
--   * SUBSTITUTION `A ⟨ σ ⟩` of types for variables, and GROUND INSTANTIATION
--     `A ⟪ σ ⟫` into the ground `Type` — a polymorphic type means the family of
--     its ground instances (plan 0.103 phase 4);
--   * the ground types embed (`⌈_⌉`), so the ground core is the `m = 0` case.
------------------------------------------------------------------------

module Once.Spec.Core.PolyTy where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

import Once.Type as T
open T using (Purity; pure; eff; ArrowKind; mk-kind; Quantity)
open import Once.Functor.Translate using (IsBaseType; WellFormedF; base-Unit; base-Void; base-Int;
  base-Float; base-Str; base-Buffer; base-Prod; base-Sum; wf-K; wf-Id; wf-Sum; wf-Prod)

------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------

data Kind : Set where
  base any : Kind

-- A kinding context: the kind of each type variable.
KCtx : ℕ → Set
KCtx m = Fin m → Kind

------------------------------------------------------------------------
-- Types over `m` type variables
------------------------------------------------------------------------

infixr 7 _*_
infixr 6 _+_
infixr 5 _⇒[_]_
infixr 6 _⊕_
infixr 7 _⊗_
infixl 60 _⟨_⟩ _⟨_⟩F _⟪_⟫ _⟪_⟫F

mutual
  data Ty (m : ℕ) : Set where
    var : Fin m → Ty m
    Unit Void Int Float Str Buffer : Ty m
    _*_ _+_ : Ty m → Ty m → Ty m
    _⇒[_]_  : Ty m → ArrowKind → Ty m → Ty m
    μ-type  : Fun m → Ty m
    ν-type  : Fun m → Purity → Ty m

  data Fun (m : ℕ) : Set where
    K       : Ty m → Fun m
    Id      : Fun m
    _⊕_ _⊗_ : Fun m → Fun m → Fun m

-- Functor application, as the ground `⟦_⟧T`.
⟦_⟧F : ∀ {m} → Fun m → Ty m → Ty m
⟦ K A ⟧F X   = A
⟦ Id ⟧F X    = X
⟦ F ⊕ G ⟧F X = ⟦ F ⟧F X + ⟦ G ⟧F X
⟦ F ⊗ G ⟧F X = ⟦ F ⟧F X * ⟦ G ⟧F X

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

Sub : ℕ → ℕ → Set
Sub m k = Fin m → Ty k

mutual
  _⟨_⟩ : ∀ {m k} → Ty m → Sub m k → Ty k
  var i       ⟨ σ ⟩ = σ i
  Unit        ⟨ σ ⟩ = Unit
  Void        ⟨ σ ⟩ = Void
  Int         ⟨ σ ⟩ = Int
  Float       ⟨ σ ⟩ = Float
  Str         ⟨ σ ⟩ = Str
  Buffer      ⟨ σ ⟩ = Buffer
  (A * B)     ⟨ σ ⟩ = A ⟨ σ ⟩ * B ⟨ σ ⟩
  (A + B)     ⟨ σ ⟩ = A ⟨ σ ⟩ + B ⟨ σ ⟩
  (A ⇒[ k ] B) ⟨ σ ⟩ = A ⟨ σ ⟩ ⇒[ k ] B ⟨ σ ⟩
  μ-type F    ⟨ σ ⟩ = μ-type (F ⟨ σ ⟩F)
  ν-type F π  ⟨ σ ⟩ = ν-type (F ⟨ σ ⟩F) π

  _⟨_⟩F : ∀ {m k} → Fun m → Sub m k → Fun k
  K A     ⟨ σ ⟩F = K (A ⟨ σ ⟩)
  Id      ⟨ σ ⟩F = Id
  (F ⊕ G) ⟨ σ ⟩F = F ⟨ σ ⟩F ⊕ G ⟨ σ ⟩F
  (F ⊗ G) ⟨ σ ⟩F = F ⟨ σ ⟩F ⊗ G ⟨ σ ⟩F

-- Substitution commutes with functor application.
⟦⟧F-⟨⟩ : ∀ {m k} (F : Fun m) (X : Ty m) (σ : Sub m k) → (⟦ F ⟧F X) ⟨ σ ⟩ ≡ ⟦ F ⟨ σ ⟩F ⟧F (X ⟨ σ ⟩)
⟦⟧F-⟨⟩ (K A)   X σ = refl
⟦⟧F-⟨⟩ Id      X σ = refl
⟦⟧F-⟨⟩ (F ⊕ G) X σ = cong₂ _+_ (⟦⟧F-⟨⟩ F X σ) (⟦⟧F-⟨⟩ G X σ)
⟦⟧F-⟨⟩ (F ⊗ G) X σ = cong₂ _*_ (⟦⟧F-⟨⟩ F X σ) (⟦⟧F-⟨⟩ G X σ)

-- Substitutions compose.
mutual
  ⟨⟩-∘ : ∀ {m k l} (A : Ty m) (σ : Sub m k) (τ : Sub k l) → (A ⟨ σ ⟩) ⟨ τ ⟩ ≡ A ⟨ (λ i → σ i ⟨ τ ⟩) ⟩
  ⟨⟩-∘ (var i) σ τ = refl
  ⟨⟩-∘ Unit σ τ = refl
  ⟨⟩-∘ Void σ τ = refl
  ⟨⟩-∘ Int σ τ = refl
  ⟨⟩-∘ Float σ τ = refl
  ⟨⟩-∘ Str σ τ = refl
  ⟨⟩-∘ Buffer σ τ = refl
  ⟨⟩-∘ (A * B) σ τ = cong₂ _*_ (⟨⟩-∘ A σ τ) (⟨⟩-∘ B σ τ)
  ⟨⟩-∘ (A + B) σ τ = cong₂ _+_ (⟨⟩-∘ A σ τ) (⟨⟩-∘ B σ τ)
  ⟨⟩-∘ (A ⇒[ k ] B) σ τ = cong₂ (λ a b → a ⇒[ k ] b) (⟨⟩-∘ A σ τ) (⟨⟩-∘ B σ τ)
  ⟨⟩-∘ (μ-type F) σ τ = cong μ-type (⟨⟩F-∘ F σ τ)
  ⟨⟩-∘ (ν-type F π) σ τ = cong (λ G → ν-type G π) (⟨⟩F-∘ F σ τ)

  ⟨⟩F-∘ : ∀ {m k l} (F : Fun m) (σ : Sub m k) (τ : Sub k l) → (F ⟨ σ ⟩F) ⟨ τ ⟩F ≡ F ⟨ (λ i → σ i ⟨ τ ⟩) ⟩F
  ⟨⟩F-∘ (K A) σ τ = cong K (⟨⟩-∘ A σ τ)
  ⟨⟩F-∘ Id σ τ = refl
  ⟨⟩F-∘ (F ⊕ G) σ τ = cong₂ _⊕_ (⟨⟩F-∘ F σ τ) (⟨⟩F-∘ G σ τ)
  ⟨⟩F-∘ (F ⊗ G) σ τ = cong₂ _⊗_ (⟨⟩F-∘ F σ τ) (⟨⟩F-∘ G σ τ)

------------------------------------------------------------------------
-- The ground types, and ground instantiation
------------------------------------------------------------------------

mutual
  ⌈_⌉ : ∀ {m} → T.Type → Ty m
  ⌈ T.Unit ⌉        = Unit
  ⌈ T.Void ⌉        = Void
  ⌈ T.Int ⌉         = Int
  ⌈ T.Float ⌉       = Float
  ⌈ T.Str ⌉         = Str
  ⌈ T.Buffer ⌉      = Buffer
  ⌈ A T.* B ⌉       = ⌈ A ⌉ * ⌈ B ⌉
  ⌈ A T.+ B ⌉       = ⌈ A ⌉ + ⌈ B ⌉
  ⌈ A T.⇒[ k ] B ⌉  = ⌈ A ⌉ ⇒[ k ] ⌈ B ⌉
  ⌈ T.μ-type F ⌉    = μ-type ⌈ F ⌉F
  ⌈ T.ν-type F π ⌉  = ν-type ⌈ F ⌉F π

  ⌈_⌉F : ∀ {m} → T.Functor → Fun m
  ⌈ T.K A ⌉F   = K ⌈ A ⌉
  ⌈ T.Id ⌉F    = Id
  ⌈ F T.⊕ G ⌉F = ⌈ F ⌉F ⊕ ⌈ G ⌉F
  ⌈ F T.⊗ G ⌉F = ⌈ F ⌉F ⊗ ⌈ G ⌉F

-- A ground instantiation of the variables.
GSub : ℕ → Set
GSub m = Fin m → T.Type

mutual
  _⟪_⟫ : ∀ {m} → Ty m → GSub m → T.Type
  var i        ⟪ σ ⟫ = σ i
  Unit         ⟪ σ ⟫ = T.Unit
  Void         ⟪ σ ⟫ = T.Void
  Int          ⟪ σ ⟫ = T.Int
  Float        ⟪ σ ⟫ = T.Float
  Str          ⟪ σ ⟫ = T.Str
  Buffer       ⟪ σ ⟫ = T.Buffer
  (A * B)      ⟪ σ ⟫ = A ⟪ σ ⟫ T.* B ⟪ σ ⟫
  (A + B)      ⟪ σ ⟫ = A ⟪ σ ⟫ T.+ B ⟪ σ ⟫
  (A ⇒[ k ] B) ⟪ σ ⟫ = A ⟪ σ ⟫ T.⇒[ k ] B ⟪ σ ⟫
  μ-type F     ⟪ σ ⟫ = T.μ-type (F ⟪ σ ⟫F)
  ν-type F π   ⟪ σ ⟫ = T.ν-type (F ⟪ σ ⟫F) π

  _⟪_⟫F : ∀ {m} → Fun m → GSub m → T.Functor
  K A     ⟪ σ ⟫F = T.K (A ⟪ σ ⟫)
  Id      ⟪ σ ⟫F = T.Id
  (F ⊕ G) ⟪ σ ⟫F = F ⟪ σ ⟫F T.⊕ G ⟪ σ ⟫F
  (F ⊗ G) ⟪ σ ⟫F = F ⟪ σ ⟫F T.⊗ G ⟪ σ ⟫F

-- Ground instantiation commutes with functor application.
⟦⟧F-⟪⟫ : ∀ {m} (F : Fun m) (X : Ty m) (σ : GSub m) → (⟦ F ⟧F X) ⟪ σ ⟫ ≡ T.⟦ F ⟪ σ ⟫F ⟧T (X ⟪ σ ⟫)
⟦⟧F-⟪⟫ (K A)   X σ = refl
⟦⟧F-⟪⟫ Id      X σ = refl
⟦⟧F-⟪⟫ (F ⊕ G) X σ = cong₂ T._+_ (⟦⟧F-⟪⟫ F X σ) (⟦⟧F-⟪⟫ G X σ)
⟦⟧F-⟪⟫ (F ⊗ G) X σ = cong₂ T._*_ (⟦⟧F-⟪⟫ F X σ) (⟦⟧F-⟪⟫ G X σ)

-- A ground type instantiates to itself.
mutual
  ⌈⌉-⟪⟫ : ∀ {m} (A : T.Type) (σ : GSub m) → ⌈ A ⌉ ⟪ σ ⟫ ≡ A
  ⌈⌉-⟪⟫ T.Unit σ = refl
  ⌈⌉-⟪⟫ T.Void σ = refl
  ⌈⌉-⟪⟫ T.Int σ = refl
  ⌈⌉-⟪⟫ T.Float σ = refl
  ⌈⌉-⟪⟫ T.Str σ = refl
  ⌈⌉-⟪⟫ T.Buffer σ = refl
  ⌈⌉-⟪⟫ (A T.* B) σ = cong₂ T._*_ (⌈⌉-⟪⟫ A σ) (⌈⌉-⟪⟫ B σ)
  ⌈⌉-⟪⟫ (A T.+ B) σ = cong₂ T._+_ (⌈⌉-⟪⟫ A σ) (⌈⌉-⟪⟫ B σ)
  ⌈⌉-⟪⟫ (A T.⇒[ k ] B) σ = cong₂ (λ a b → a T.⇒[ k ] b) (⌈⌉-⟪⟫ A σ) (⌈⌉-⟪⟫ B σ)
  ⌈⌉-⟪⟫ (T.μ-type F) σ = cong T.μ-type (⌈⌉F-⟪⟫ F σ)
  ⌈⌉-⟪⟫ (T.ν-type F π) σ = cong (λ G → T.ν-type G π) (⌈⌉F-⟪⟫ F σ)

  ⌈⌉F-⟪⟫ : ∀ {m} (F : T.Functor) (σ : GSub m) → ⌈ F ⌉F ⟪ σ ⟫F ≡ F
  ⌈⌉F-⟪⟫ (T.K A) σ = cong T.K (⌈⌉-⟪⟫ A σ)
  ⌈⌉F-⟪⟫ T.Id σ = refl
  ⌈⌉F-⟪⟫ (F T.⊕ G) σ = cong₂ T._⊕_ (⌈⌉F-⟪⟫ F σ) (⌈⌉F-⟪⟫ G σ)
  ⌈⌉F-⟪⟫ (F T.⊗ G) σ = cong₂ T._⊗_ (⌈⌉F-⟪⟫ F σ) (⌈⌉F-⟪⟫ G σ)

-- Instantiating after substituting is instantiating the composite.
mutual
  ⟨⟩-⟪⟫ : ∀ {m k} (A : Ty m) (σ : Sub m k) (ρ : GSub k) → (A ⟨ σ ⟩) ⟪ ρ ⟫ ≡ A ⟪ (λ i → σ i ⟪ ρ ⟫) ⟫
  ⟨⟩-⟪⟫ (var i) σ ρ = refl
  ⟨⟩-⟪⟫ Unit σ ρ = refl
  ⟨⟩-⟪⟫ Void σ ρ = refl
  ⟨⟩-⟪⟫ Int σ ρ = refl
  ⟨⟩-⟪⟫ Float σ ρ = refl
  ⟨⟩-⟪⟫ Str σ ρ = refl
  ⟨⟩-⟪⟫ Buffer σ ρ = refl
  ⟨⟩-⟪⟫ (A * B) σ ρ = cong₂ T._*_ (⟨⟩-⟪⟫ A σ ρ) (⟨⟩-⟪⟫ B σ ρ)
  ⟨⟩-⟪⟫ (A + B) σ ρ = cong₂ T._+_ (⟨⟩-⟪⟫ A σ ρ) (⟨⟩-⟪⟫ B σ ρ)
  ⟨⟩-⟪⟫ (A ⇒[ k ] B) σ ρ = cong₂ (λ a b → a T.⇒[ k ] b) (⟨⟩-⟪⟫ A σ ρ) (⟨⟩-⟪⟫ B σ ρ)
  ⟨⟩-⟪⟫ (μ-type F) σ ρ = cong T.μ-type (⟨⟩F-⟪⟫ F σ ρ)
  ⟨⟩-⟪⟫ (ν-type F π) σ ρ = cong (λ G → T.ν-type G π) (⟨⟩F-⟪⟫ F σ ρ)

  ⟨⟩F-⟪⟫ : ∀ {m k} (F : Fun m) (σ : Sub m k) (ρ : GSub k) → (F ⟨ σ ⟩F) ⟪ ρ ⟫F ≡ F ⟪ (λ i → σ i ⟪ ρ ⟫) ⟫F
  ⟨⟩F-⟪⟫ (K A) σ ρ = cong T.K (⟨⟩-⟪⟫ A σ ρ)
  ⟨⟩F-⟪⟫ Id σ ρ = refl
  ⟨⟩F-⟪⟫ (F ⊕ G) σ ρ = cong₂ T._⊕_ (⟨⟩F-⟪⟫ F σ ρ) (⟨⟩F-⟪⟫ G σ ρ)
  ⟨⟩F-⟪⟫ (F ⊗ G) σ ρ = cong₂ T._⊗_ (⟨⟩F-⟪⟫ F σ ρ) (⟨⟩F-⟪⟫ G σ ρ)

------------------------------------------------------------------------
-- Kinding: base types, and well-formed functors, under a kinding context
------------------------------------------------------------------------

data Base {m} (Δ : KCtx m) : Ty m → Set where
  b-var    : ∀ {i} → Δ i ≡ base → Base Δ (var i)
  b-Unit   : Base Δ Unit
  b-Void   : Base Δ Void
  b-Int    : Base Δ Int
  b-Float  : Base Δ Float
  b-Str    : Base Δ Str
  b-Buffer : Base Δ Buffer
  b-Prod   : ∀ {A B} → Base Δ A → Base Δ B → Base Δ (A * B)
  b-Sum    : ∀ {A B} → Base Δ A → Base Δ B → Base Δ (A + B)

data WFFun {m} (Δ : KCtx m) : Fun m → Set where
  wf-K   : ∀ {A} → Base Δ A → WFFun Δ (K A)
  wf-Id  : WFFun Δ Id
  wf-Sum : ∀ {F G} → WFFun Δ F → WFFun Δ G → WFFun Δ (F ⊕ G)
  wf-Prod : ∀ {F G} → WFFun Δ F → WFFun Δ G → WFFun Δ (F ⊗ G)

-- A ground instantiation RESPECTS the kinds: base variables become base types.
Respects : ∀ {m} → KCtx m → GSub m → Set
Respects Δ σ = ∀ i → Δ i ≡ base → IsBaseType (σ i)

base-⟪⟫ : ∀ {m} {Δ : KCtx m} {σ : GSub m} {A} → Respects Δ σ → Base Δ A → IsBaseType (A ⟪ σ ⟫)
base-⟪⟫ r (b-var {i} e) = r i e
base-⟪⟫ r b-Unit   = base-Unit
base-⟪⟫ r b-Void   = base-Void
base-⟪⟫ r b-Int    = base-Int
base-⟪⟫ r b-Float  = base-Float
base-⟪⟫ r b-Str    = base-Str
base-⟪⟫ r b-Buffer = base-Buffer
base-⟪⟫ r (b-Prod a b) = base-Prod (base-⟪⟫ r a) (base-⟪⟫ r b)
base-⟪⟫ r (b-Sum a b)  = base-Sum (base-⟪⟫ r a) (base-⟪⟫ r b)

wf-⟪⟫ : ∀ {m} {Δ : KCtx m} {σ : GSub m} {F} → Respects Δ σ → WFFun Δ F → WellFormedF (F ⟪ σ ⟫F)
wf-⟪⟫ r (wf-K b)      = WellFormedF.wf-K (base-⟪⟫ r b)
wf-⟪⟫ r wf-Id         = WellFormedF.wf-Id
wf-⟪⟫ r (wf-Sum f g)  = WellFormedF.wf-Sum (wf-⟪⟫ r f) (wf-⟪⟫ r g)
wf-⟪⟫ r (wf-Prod f g) = WellFormedF.wf-Prod (wf-⟪⟫ r f) (wf-⟪⟫ r g)
