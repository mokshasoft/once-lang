-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Laws.Monad — the meaning's monad is a lawful monad
-- (plan 0.112 C1).
--
-- `T`, the interaction-tree monad an effectful arrow denotes into (a call is
-- answered by the interpretation, a halt ends the run), satisfies the three
-- monad laws on the nose. They were proved one by one
-- (`Denotation.TraceMonadLaws`); here they are one structure, with the
-- standard library's raw monad interface beside it.
--
-- The standard library has no lawful-monad record, so `LawfulMonad` is
-- defined here: the raw operations and the three laws, at `≡`.
------------------------------------------------------------------------

module Once.Lang.Laws.Monad where

open import Effect.Monad using (RawMonad; mkRawMonad)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Lang.Trace using (T; returnT; _>>=T_)
open import Once.Denotation.TraceMonadLaws using (>>=T-identityˡ; >>=T-identityʳ; >>=T-assoc)

record LawfulMonad (M : Set → Set) : Set₁ where
  field
    return    : ∀ {X} → X → M X
    _>>=_     : ∀ {X Y} → M X → (X → M Y) → M Y
    identityˡ : ∀ {X Y} (x : X) (f : X → M Y) → (return x >>= f) ≡ f x
    identityʳ : ∀ {X} (m : M X) → (m >>= return) ≡ m
    assoc     : ∀ {X Y Z} (m : M X) (f : X → M Y) (g : Y → M Z)
              → ((m >>= f) >>= g) ≡ (m >>= λ x → f x >>= g)

  rawMonad : RawMonad M
  rawMonad = mkRawMonad M return _>>=_

T-monad : LawfulMonad T
T-monad = record
  { return    = returnT
  ; _>>=_     = _>>=T_
  ; identityˡ = >>=T-identityˡ
  ; identityʳ = >>=T-identityʳ
  ; assoc     = >>=T-assoc
  }
