{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Generators — the generators, as a table.
--
-- The generators are the structure of a bicartesian closed category with an
-- initial algebra and a final coalgebra for each functor, graded by effect:
--
--   category            id, compose
--   products            fst, snd, terminal       pair
--   coproducts          inl, inr, initial        case
--   exponentials        apply                    curry
--   initial algebras    In                       cata
--   final coalgebras    Out                      ana
--
-- In each group the first column are STRUCTURE MAPS, the second the MEDIATING
-- morphism of the universal property, built from its arms (a COMBINATOR).
-- `unit` and `toFloat` are constants. Each generator means its definition in
-- the core (`Spec.Core.Derived`).
--
-- The table says, once per generator, what the typing rules need
-- (`Spec.Surface.Typing`):
--
--   * `kind`: a constant, a structure map, or a combinator with its number of
--     arms. A structure map says which side of its arrow fixes its instance:
--     a map OUT OF a universal object is fixed by its domain (`fst`, `apply`,
--     `Out`), a map INTO one by its codomain (`inl`, `In`). `terminal` is
--     fixed by its domain; `id` by either side (they are the same object);
--     `initial` by either side (its domain is `Void`, and its least codomain
--     too).
--   * `Constant`: a constant's type and core term.
--   * `Morphism`: a structure map's instances, each with its core term, at
--     every grade (a map of the base category is a map at each grade).
--
-- Each row of `Constant` and `Morphism` carries its kind, so a row in the
-- wrong relation does not type.
--   * `Final`: the final coalgebras `ana` maps into.
--
-- The combinators' rules are their universal properties, one per mode, in
-- `Spec.Surface.Typing`.
------------------------------------------------------------------------

module Once.Spec.Surface.Generators where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Purity; Finite; fin; pure; act; eff; mk-kind; Many; _⊑π_)
open import Once.Spec.Type
  using (Ty; Fun; KCtx; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F; WFFun)
open import Once.Spec.Core.Syntax using (Defs; Tm; unit)
open import Once.Spec.Core.Derived

------------------------------------------------------------------------
-- The generators and the words that name them
------------------------------------------------------------------------

data Gen : Set where
  id compose                      : Gen
  fst snd terminal pair           : Gen
  inl inr initial case            : Gen
  apply curry                     : Gen
  In cata                         : Gen
  Out ana                         : Gen
  unit toFloat                    : Gen

word : Gen → String
word id       = "id"
word compose  = "compose"
word fst      = "fst"
word snd      = "snd"
word terminal = "terminal"
word pair     = "pair"
word inl      = "inl"
word inr      = "inr"
word initial  = "initial"
word case     = "case"
word apply    = "apply"
word curry    = "curry"
word In       = "In"
word cata     = "cata"
word Out      = "Out"
word ana      = "ana"
word unit     = "unit"
word toFloat  = "toFloat"

-- A word that names a generator: reserved (`Spec.Surface.Resolution`).
GenWord : String → Set
GenWord x = Σ[ g ∈ Gen ] word g ≡ x

------------------------------------------------------------------------
-- What kind of generator each is
------------------------------------------------------------------------

-- Which side of a structure map's arrow fixes its instance.
data Fixes : Set where
  domain codomain both : Fixes

data GenKind : Set where
  constant   : GenKind
  map        : Fixes → GenKind
  combinator : ℕ → GenKind          -- with its number of arms

kind : Gen → GenKind
kind id       = map both
kind compose  = combinator 2
kind fst      = map domain
kind snd      = map domain
kind terminal = map domain
kind pair     = combinator 2
kind inl      = map codomain
kind inr      = map codomain
kind initial  = map both
kind case     = combinator 2
kind apply    = map domain
kind curry    = combinator 1
kind In       = map codomain
kind cata     = combinator 1
kind Out      = map domain
kind ana      = combinator 1
kind unit     = constant
kind toFloat  = constant

data IsConstant : GenKind → Set where
  is-constant : IsConstant constant

data IsMap : GenKind → Set where
  is-map : ∀ {φ} → IsMap (map φ)

-- The domain fixes the instance: the map has a domain-given rule.
data FromDomain : GenKind → Set where
  fd-domain : FromDomain (map domain)
  fd-both   : FromDomain (map both)

-- The codomain fixes the instance: the map applied to an argument is checked.
data FromCodomain : GenKind → Set where
  fc-codomain : FromCodomain (map codomain)
  fc-both     : FromCodomain (map both)

data IsCombinator (k : ℕ) : GenKind → Set where
  is-combinator : IsCombinator k (combinator k)

------------------------------------------------------------------------
-- The constants, the structure maps and the final coalgebras, typed
------------------------------------------------------------------------

module _ {s} {S : Defs s} {m : ℕ} (Δ : KCtx m) where

  private
    _⇒⟨_⟩_ : Ty m → Purity → Ty m → Ty m
    A ⇒⟨ π ⟩ B = A ⇒[ mk-kind Many π ] B
    infixr 30 _⇒⟨_⟩_

  data Constant {n} : (g : Gen) → IsConstant (kind g) → Ty m → Tm S m n → Set where
    k-unit    : Constant unit is-constant Unit unit
    -- `Int` → `Float`, correctly rounded (IEEE's `convertFromInt`; D408).
    k-toFloat : Constant toFloat is-constant (Int ⇒⟨ pure ⟩ Float) toFloatᶜ

  -- `Morphism g A π B t`: the structure map `g` at `A ⇒⟨ π ⟩ B`, meaning `t`.
  -- `apply` and `Out` act on an arrow and a stream: what running them gives
  -- is `𝕋` of their grade, whatever the grade `π` of the map itself.
  data Morphism {n} : (g : Gen) → IsMap (kind g) → Ty m → Purity → Ty m → Tm S m n → Set where
    m-id       : ∀ {T π}   → Morphism id is-map T π T (idᶜ T π)
    m-fst      : ∀ {A B π} → Morphism fst is-map (A * B) π A (fstᶜ A B π)
    m-snd      : ∀ {A B π} → Morphism snd is-map (A * B) π B (sndᶜ A B π)
    m-terminal : ∀ {A π}   → Morphism terminal is-map A π Unit (terminalᶜ A π)
    m-inl      : ∀ {A B π} → Morphism inl is-map A π (A + B) (inlᶜ A B π)
    m-inr      : ∀ {A B π} → Morphism inr is-map B π (A + B) (inrᶜ A B π)
    m-initial  : ∀ {A π}   → Morphism initial is-map Void π A (initialᶜ A π)
    m-apply    : ∀ {A B ρ π} → Morphism apply is-map ((A ⇒⟨ ρ ⟩ B) * A) π (𝕋 ρ B) (applyᵀ ρ A B π)
    m-In       : ∀ {F π} → WFFun Δ F → Morphism In is-map (⟦ F ⟧F (μ F)) π (μ F) (inᶜ F π)
    m-Out      : ∀ {F f π} → WFFun Δ F
               → Morphism Out is-map (ν F f) π (𝕋 (fin f) (⟦ F ⟧F (ν F f))) (outᵀ f F π)

  -- `Final A π₀ X G ρ k`: an arrow `A ⇒⟨ π₀ ⟩ X` into the final coalgebra `X`
  -- of `G` at grade `ρ`; `k` builds it from a coalgebra `A ⇒⟨ ρ ⟩ G A` (D317).
  -- Into a stream `ν F f`, built by an arrow that runs nothing more; and into
  -- `T∞ B`, the final coalgebra of `T act (B + −)`, which `Eff` presents as
  -- the grade `eff`.
  data Final {n} (A : Ty m) : Purity → Ty m → (Ty m → Ty m) → Purity → (Tm S m n → Tm S m n) → Set where
    final-ν  : ∀ {π₀ F f} → π₀ ⊑π act → WFFun Δ F
             → Final A π₀ (ν F f) (λ X → ⟦ F ⟧F X) (fin f) (anaᶜ F A π₀)
    final-T∞ : ∀ {B} → Final A eff B (λ X → B + X) act (anaEffᶜ A)
