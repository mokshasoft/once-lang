-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Context
--
-- Named typing contexts for type checking.
-- Uses association lists mapping variable names to types.
--
-- Part of OCP-0003: Verified Type Checker
------------------------------------------------------------------------

module Once.TypeCheck.Context where

open import Once.Spec.Type using (Ty)
open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Spec.Grade using (Quantity; Many)
open import Once.Spec.Type using (Type)
open import Once.TypeCheck.Scope using (Binding; mkBinding; Ctx)
open Binding

------------------------------------------------------------------------
-- Bindings
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Named Typing Context
------------------------------------------------------------------------

-- | Empty context
∅ : ∀ {m} → Ctx m
∅ = []

-- | Extend context with a new binding
-- Default to unrestricted (Many) usage
_,_∷_ : ∀ {m} → Ctx m → String → Ty m → Ctx m
Γ , x ∷ A = mkBinding x A Many ∷ Γ

-- | Extend context with quantity
_,_∷_^_ : ∀ {m} → Ctx m → String → Ty m → Quantity → Ctx m
Γ , x ∷ A ^ q = mkBinding x A q ∷ Γ

infixl 5 _,_∷_
infixl 5 _,_∷_^_

------------------------------------------------------------------------
-- Context Lookup
------------------------------------------------------------------------

-- | Result of looking up a variable in context
data LookupResult {m} : Set where
  found    : (A : Ty m) → (q : Quantity) → (idx : ℕ) → LookupResult
  notFound : LookupResult

-- | Look up a variable by name
-- Returns the type, quantity, and de Bruijn index
lookup : ∀ {m} → String → Ctx m → LookupResult
lookup x [] = notFound
lookup x (b ∷ Γ) with x ≟ name b
... | yes _ = found (type b) (quantity b) 0
... | no  _ with lookup x Γ
...   | found A q i = found A q (suc i)
...   | notFound    = notFound

-- | Check if a variable is bound in context
isBound : ∀ {m} → String → Ctx m → Bool
isBound x Γ with lookup x Γ
... | found _ _ _ = true
... | notFound    = false

------------------------------------------------------------------------
-- Context Properties
------------------------------------------------------------------------

-- | Length of context (number of bindings)
ctxLength : ∀ {m} → Ctx m → ℕ
ctxLength = length

-- | Get all variable names in context
names : ∀ {m} → Ctx m → List String
names [] = []
names (b ∷ Γ) = name b ∷ names Γ

------------------------------------------------------------------------
-- Well-Scoped Evidence
------------------------------------------------------------------------

-- | Evidence that variable x is at position i in context Γ having type A
data _∈_at_⦂_ {m} (x : String) : Ctx m → ℕ → Ty m → Set where
  here  : ∀ {Γ A q}
        → x ∈ (mkBinding x A q ∷ Γ) at 0 ⦂ A

  there : ∀ {Γ y A B q i}
        → x ∈ Γ at i ⦂ A
        → x ∈ (mkBinding y B q ∷ Γ) at (suc i) ⦂ A

open import Data.Product using (∃-syntax)

-- | Lookup with evidence
lookupWithEvidence : ∀ {m} → (x : String) → (Γ : Ctx m)
                   → Maybe (∃[ A ] ∃[ i ] x ∈ Γ at i ⦂ A)
lookupWithEvidence x [] = nothing
lookupWithEvidence x (mkBinding y A q ∷ Γ) with x ≟ y
... | yes refl = just (A , 0 , here)
... | no  _    with lookupWithEvidence x Γ
...   | just (A' , i , pf) = just (A' , suc i , there pf)
...   | nothing            = nothing

------------------------------------------------------------------------
-- Context Conversion (for de Bruijn indices)
------------------------------------------------------------------------

-- | Extract types from context (for de Bruijn indexed context)
-- Returns types in reverse order (newest first)
ctxTypes : ∀ {m} → Ctx m → List (Ty m)
ctxTypes [] = []
ctxTypes (b ∷ Γ) = type b ∷ ctxTypes Γ