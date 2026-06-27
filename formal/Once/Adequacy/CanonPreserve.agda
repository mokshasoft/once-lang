-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CanonPreserve — Plan 0.51 discharge (import-free fragment).
-- `canonExpr [] []` (the resolver's own-module canonicalization, RVar x →
-- RResolved (canonical [x]) for free non-builtin x) PRESERVES the declarative
-- typing judgment `⊢ᶜ`. Foundational layer: the bound/local agreement invariant
-- `BLA`, the canonExpr-RVar dispatch facts, and `classify-canon`.
------------------------------------------------------------------------

module Once.Adequacy.CanonPreserve where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Product using (_,_)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CanonicalName using (CanonicalName; canonical; showCanonical)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.Parser.Module.Resolve
  using (canonExpr; canonVar; isBuiltinName; elemStr; lookupUnaliased)
open import Once.TypeCheck.Classify
  using (NamedCtx; lookupLocal; extendNamedCtx; classifyAppHead)

------------------------------------------------------------------------
-- canonExpr-RVar dispatch (import-free: um = am = []).
------------------------------------------------------------------------

-- canonExpr bound [] [] (RVar x) = canonVar (elemStr x bound ∨ isBuiltinName x)
--   (lookupUnaliased [] x = nothing) x  — so it dispatches on the head Bool.
canon-RVar-keep : ∀ (bound : List String) (x : String) →
  (elemStr x bound ∨ isBuiltinName x) ≡ true →
  canonExpr bound [] [] (Raw.RVar x) ≡ Raw.RVar x
canon-RVar-keep bound x eq rewrite eq = refl

canon-RVar-resolve : ∀ (bound : List String) (x : String) →
  (elemStr x bound ∨ isBuiltinName x) ≡ false →
  canonExpr bound [] [] (Raw.RVar x) ≡ Raw.RResolved (canonical (x ∷ []))
canon-RVar-resolve bound x eq rewrite eq = refl

------------------------------------------------------------------------
-- Bound / local agreement: the syntactic binder list `bound` matches the
-- context's local bindings. Threaded through λ/let/case binders.
------------------------------------------------------------------------

BLA : NamedCtx → List String → Set
BLA ctx bound = ∀ x → elemStr x bound ≡ is-just (lookupLocal ctx x)

-- A name found locally is in `bound`.
bla-local : ∀ {ctx bound x A Ψ se} → BLA ctx bound →
  lookupLocal ctx x ≡ just (A , Ψ , se) → elemStr x bound ≡ true
bla-local {x = x} bla eq rewrite bla x | eq = refl

-- A name not found locally is not in `bound`.
bla-import : ∀ {ctx bound x} → BLA ctx bound →
  lookupLocal ctx x ≡ nothing → elemStr x bound ≡ false
bla-import {x = x} bla eq rewrite bla x | eq = refl
