-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.Unify
--
-- Unification algorithm for type checking.
-- Implements Robinson's unification with occurs check.
--
-- Part of OCP-0003: Verified Type Checker
------------------------------------------------------------------------

module Once.TypeCheck.Unify where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Once.Type using (PolyType; PUnit; PVoid; PInt; PFloat; PStr; PBuffer;
                              _P*_; _P+_; _P⇒[_]_; PEff; TVar;
                              PolyFunctor; PK; PId; _P⊕_; _P⊗_; Pμ-type; Pν-type;
                              Type; Quantity)
-- Unification works with PolyType (which has TVar) during type inference.
-- After inference completes, PolyType is extracted to Type.
open import Once.TypeCheck.Error using (PolyTypeError; PolyResult; pok; pfail)
  renaming (OccursCheck to OccursCheck'; UnificationError to UnificationError')
-- Note: We rename the PolyTypeError constructors to avoid ambiguity with
-- the TypeError constructors that may be imported elsewhere.
-- Usage: OccursCheck' and UnificationError' for poly type errors

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

-- | A substitution maps type variable names to PolyTypes
-- Unification works with PolyType during inference; results extracted later.
Subst : Set
Subst = List (String × PolyType)

-- | Empty substitution
emptySubst : Subst
emptySubst = []

-- | Singleton substitution: [x ↦ T]
singleSubst : String → PolyType → Subst
singleSubst x T = (x , T) ∷ []

-- | Lookup a variable in a substitution
lookupSubst : String → Subst → Maybe PolyType
lookupSubst x [] = nothing
lookupSubst x ((y , T) ∷ σ) with x ≟ y
... | yes _ = just T
... | no  _ = lookupSubst x σ

------------------------------------------------------------------------
-- Applying Substitutions
------------------------------------------------------------------------

-- | Apply a substitution to a PolyType
mutual
  applySubstF : Subst → PolyFunctor → PolyFunctor
  applySubstF σ (PK A) = PK (applySubst σ A)
  applySubstF _ PId = PId
  applySubstF σ (F P⊕ G) = applySubstF σ F P⊕ applySubstF σ G
  applySubstF σ (F P⊗ G) = applySubstF σ F P⊗ applySubstF σ G

  applySubst : Subst → PolyType → PolyType
  applySubst σ PUnit = PUnit
  applySubst σ PVoid = PVoid
  applySubst σ PInt = PInt
  applySubst σ PFloat = PFloat
  applySubst σ PStr = PStr
  applySubst σ PBuffer = PBuffer
  applySubst σ (A P* B) = applySubst σ A P* applySubst σ B
  applySubst σ (A P+ B) = applySubst σ A P+ applySubst σ B
  applySubst σ (A P⇒[ q ] B) = applySubst σ A P⇒[ q ] applySubst σ B
  applySubst σ (PEff A B) = PEff (applySubst σ A) (applySubst σ B)
  applySubst σ (Pμ-type F) = Pμ-type (applySubstF σ F)
  applySubst σ (Pν-type F) = Pν-type (applySubstF σ F)
  applySubst σ (TVar x) with lookupSubst x σ
  ... | just T  = T
  ... | nothing = TVar x

-- | Compose two substitutions: (σ₂ ∘ σ₁)(T) = σ₂(σ₁(T))
composeSubst : Subst → Subst → Subst
composeSubst σ₂ σ₁ =
  Data.List.map (λ { (x , T) → (x , applySubst σ₂ T) }) σ₁ ++ σ₂

------------------------------------------------------------------------
-- Occurs Check
------------------------------------------------------------------------

-- | Check if a type variable occurs in a PolyType
mutual
  occursF : String → PolyFunctor → Bool
  occursF x (PK A) = occurs x A
  occursF _ PId = false
  occursF x (F P⊕ G) = occursF x F ∨ occursF x G
  occursF x (F P⊗ G) = occursF x F ∨ occursF x G

  occurs : String → PolyType → Bool
  occurs x PUnit = false
  occurs x PVoid = false
  occurs x PInt = false
  occurs x PFloat = false
  occurs x PStr = false
  occurs x PBuffer = false
  occurs x (A P* B) = occurs x A ∨ occurs x B
  occurs x (A P+ B) = occurs x A ∨ occurs x B
  occurs x (A P⇒[ q ] B) = occurs x A ∨ occurs x B
  occurs x (PEff A B) = occurs x A ∨ occurs x B
  occurs x (Pμ-type F) = occursF x F
  occurs x (Pν-type F) = occursF x F
  occurs x (TVar y) with x ≟ y
  ... | yes _ = true
  ... | no  _ = false

------------------------------------------------------------------------
-- Unification
------------------------------------------------------------------------

-- | Unification result
data UnifyResult : Set where
  unified : Subst → UnifyResult
  failed  : PolyTypeError → UnifyResult

-- | Unify two PolyTypes
-- Returns a most general unifier (MGU) or an error
--
-- Note: We use TERMINATING pragma because the termination argument
-- is non-trivial (requires showing applySubst preserves a measure).
-- A proper proof would use well-founded recursion on type size.
{-# TERMINATING #-}
unify : PolyType → PolyType → UnifyResult

-- Base types unify only with themselves
unify PUnit PUnit = unified emptySubst
unify PVoid PVoid = unified emptySubst
unify PInt PInt = unified emptySubst
unify PFloat PFloat = unified emptySubst
unify PStr PStr = unified emptySubst
unify PBuffer PBuffer = unified emptySubst

-- Type variable unification (with occurs check)
unify (TVar x) (TVar y) with x ≟ y
... | yes _ = unified emptySubst  -- Same variable
... | no  _ = unified (singleSubst x (TVar y))  -- Different variables

unify (TVar x) T with occurs x T
... | true  = failed (OccursCheck' x T)
... | false = unified (singleSubst x T)

unify T (TVar x) with occurs x T
... | true  = failed (OccursCheck' x T)
... | false = unified (singleSubst x T)

-- Product types
unify (A₁ P* B₁) (A₂ P* B₂) with unify A₁ A₂
... | failed err = failed err
... | unified σ₁ with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂)
...   | failed err = failed err
...   | unified σ₂ = unified (composeSubst σ₂ σ₁)

-- Sum types
unify (A₁ P+ B₁) (A₂ P+ B₂) with unify A₁ A₂
... | failed err = failed err
... | unified σ₁ with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂)
...   | failed err = failed err
...   | unified σ₂ = unified (composeSubst σ₂ σ₁)

-- Function types (graded arrows)
unify (A₁ P⇒[ q₁ ] B₁) (A₂ P⇒[ q₂ ] B₂) with unify A₁ A₂
... | failed err = failed err
... | unified σ₁ with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂)
...   | failed err = failed err
...   | unified σ₂ = unified (composeSubst σ₂ σ₁)

-- Effectful types
unify (PEff A₁ B₁) (PEff A₂ B₂) with unify A₁ A₂
... | failed err = failed err
... | unified σ₁ with unify (applySubst σ₁ B₁) (applySubst σ₁ B₂)
...   | failed err = failed err
...   | unified σ₂ = unified (composeSubst σ₂ σ₁)

-- Everything else fails
unify A B = failed (UnificationError' A B)

------------------------------------------------------------------------
-- Convenience: Result-based unification
------------------------------------------------------------------------

-- | Unify returning PolyResult monad
unifyPolyResult : PolyType → PolyType → PolyResult Subst
unifyPolyResult A B with unify A B
... | unified σ = pok σ
... | failed e  = pfail e