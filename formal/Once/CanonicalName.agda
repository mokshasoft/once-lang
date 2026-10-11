-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CanonicalName — deciding and comparing canonical names.
--
-- The names are the Spec's (`Once.Spec.Name`). This module holds what the
-- implementation needs beyond them: decidable equality, the reserved-word
-- decider, the generator namespace as a string, and the disjointness facts
-- the resolver and elaborator use.
------------------------------------------------------------------------

module Once.CanonicalName where

open import Once.Spec.Name
  using (CanonicalName; canonical; bare; gen; own; generatorNS; genWords; GenWord; genNames; NotGenerator)

open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Data.String using (String) renaming (_≟_ to _≟ˢ_; _++_ to _++ˢ_)
open import Relation.Binary using (DecidableEquality)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; any?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (yes; no; Dec; ¬_)
open import Data.Product using (∃-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≢_)

-- D136: THE GENERATOR NAMESPACE. The twelve categorical generators are
-- identified by a canonical name the COMPILER owns, not by a reserved bare
-- string — so a user's `fst` (`User.Module.fst`) and the generator
-- (`Generators.fst`) are different names and cannot collide. D001 reserved the
-- bare names instead; that was never enforced at the parser and produced a
-- collision in which the builtin silently won.
--
-- Here rather than in `Classify` because BOTH sides need it: the resolver
-- (`Once.Parser.Module.Resolve`, which emits it) and the elaborator
-- (`Once.TypeCheck.*`, which dispatches on it) — and this module is already
-- below both.
-- A user path can never BE a generator name: `bare x = canonical [x]` has one
-- component and `gen g` has two, so the two families are disjoint by length —
-- which is the property that replaces every "this name is not a builtin" side
-- condition once the migration lands.
gen≢bare : ∀ (g x : String) → gen g ≢ bare x
gen≢bare g x ()

gen-inj : ∀ {g h : String} → gen g ≡ gen h → g ≡ h
gen-inj refl = refl

-- | Its decider. `Resolve.isBuiltinName` is the BOOLEAN form the resolver
-- computes with; this is the form that discharges the rule's premise.
genWord? : (x : String) → Dec (GenWord x)
genWord? x = any? (λ g → x ≟ˢ g) genWords

-- | Drive the decider to its `no` branch from the PROPERTY. The elaborator
-- de-withes `genWord? x`, so completeness has to name the reduced form.
genWord?-no : ∀ (x : String) → ¬ GenWord x → ∃[ ¬p ] (genWord? x ≡ no ¬p)
genWord?-no x ¬gw with genWord? x
... | yes gw = ⊥-elim (¬gw gw)
... | no ¬p  = ¬p , refl

-- A bare name is never a generator — the disjointness `gen≢bare` gives, packed
-- into the shape the rules want.
bare-NotGenerator : ∀ (x : String) → NotGenerator (bare x)
bare-NotGenerator x =
    (λ eq → gen≢bare "id" x (sym eq))
  ∷ (λ eq → gen≢bare "fst" x (sym eq))
  ∷ (λ eq → gen≢bare "snd" x (sym eq))
  ∷ (λ eq → gen≢bare "terminal" x (sym eq))
  ∷ (λ eq → gen≢bare "initial" x (sym eq))
  ∷ (λ eq → gen≢bare "inl" x (sym eq))
  ∷ (λ eq → gen≢bare "inr" x (sym eq))
  ∷ (λ eq → gen≢bare "unit" x (sym eq))
  ∷ []

-- Decidable equality — the trace's `ev-name` comparison needs it.
_≟ᶜ_ : DecidableEquality CanonicalName
canonical ps ≟ᶜ canonical qs with ≡-dec _≟ˢ_ ps qs
... | yes p = yes (cong canonical p)
... | no ¬p = no λ where refl → ¬p refl
