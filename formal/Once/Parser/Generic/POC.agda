-- SPDX-License-Identifier: AGPL-3.0-or-later
-- POC: parameterize the type-grammar parser+relation over a "type algebra"
-- (AST builders) + an extra-atom hook, instantiated for Type and PolyType.
-- Validates the mechanism before the full generic build (Plan 0.7 Phase 2).

module Once.Parser.Generic.POC where

open import Data.List using (List; []; _∷_; length)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (_<_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; PolyType; PUnit; PTVar)
open import Once.Parser.Token
open import Once.Parser.PolyType using (isLowerWord)

------------------------------------------------------------------------
-- Algebra (minimal: `unit` builder + the extra-atom hook). The full
-- version adds all builders (void/int/.../prod/sum/arrow/eff/io/mu/functor).
------------------------------------------------------------------------

record TyAlg : Set₁ where
  field
    R      : Set
    unit   : R
    Extra  : List Token → R → List Token → Set
    extraP : (toks : List Token) → Maybe (Σ[ a ∈ R ] Σ[ rest ∈ List Token ] Extra toks a rest)

------------------------------------------------------------------------
-- Generic atom relation + parser, parameterised over the algebra.
------------------------------------------------------------------------

module Gen (alg : TyAlg) where
  open TyAlg alg

  data ParsesAtomG : List Token → R → List Token → Set where
    pa-unit  : ∀ rest → ParsesAtomG (TWord "Unit" ∷ rest) unit rest
    pa-extra : ∀ {toks a rest} → Extra toks a rest → ParsesAtomG toks a rest

  ParseAtomGD : List Token → Set
  ParseAtomGD toks = Maybe (Σ[ a ∈ R ] Σ[ rest ∈ List Token ] ParsesAtomG toks a rest)

  parseAtomG : (toks : List Token) → ParseAtomGD toks
  paG-extra  : (toks : List Token) →
               Maybe (Σ[ a ∈ R ] Σ[ rest ∈ List Token ] Extra toks a rest) → ParseAtomGD toks
  parseAtomG (TWord name ∷ rest) with name ≟s "Unit"
  ... | yes refl = just (unit , rest , pa-unit rest)
  ... | no _     = paG-extra (TWord name ∷ rest) (extraP (TWord name ∷ rest))
  parseAtomG toks = paG-extra toks (extraP toks)

  paG-extra toks (just (a , rest , ex)) = just (a , rest , pa-extra ex)
  paG-extra toks nothing                = nothing

------------------------------------------------------------------------
-- Instantiation 1: ground Type — no extra atoms.
------------------------------------------------------------------------

TypeAlg : TyAlg
TypeAlg = record
  { R = Type ; unit = Unit
  ; Extra = λ _ _ _ → ⊥
  ; extraP = λ _ → nothing }

------------------------------------------------------------------------
-- Instantiation 2: PolyType — extra atom = lowercase TVar.
------------------------------------------------------------------------

data TVarRel : List Token → PolyType → List Token → Set where
  tvar : ∀ {name rest} → isLowerWord name ≡ true → TVarRel (TWord name ∷ rest) (PTVar name) rest

tvarP : (toks : List Token) → Maybe (Σ[ a ∈ PolyType ] Σ[ rest ∈ List Token ] TVarRel toks a rest)
tvarP (TWord name ∷ rest) with isLowerWord name in eq
... | true  = just (PTVar name , rest , tvar eq)
... | false = nothing
tvarP _ = nothing

PolyAlg : TyAlg
PolyAlg = record
  { R = PolyType ; unit = PUnit
  ; Extra = TVarRel
  ; extraP = tvarP }

-- Both instantiations:
module TypeG = Gen TypeAlg
module PolyG = Gen PolyAlg
