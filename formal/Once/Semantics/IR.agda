-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Semantics.IR
--
-- IR-level denotational semantics for Once.
-- Interprets types as Agda Sets and IR morphisms as Agda functions.
--
-- Uses ℤ for Int (mathematical integers for arithmetic proofs).
-- Functions are plain Agda functions (not Closure records).
--
-- For machine-level semantics (with ℕ), use Once.Semantics.Machine.
------------------------------------------------------------------------

module Once.Semantics.IR where

open import Data.Integer using (ℤ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)

open import Once.Type
open import Once.CCC.IR

-- Instantiate Core with ℤ for integers and re-export
open import Once.Semantics.Core ℤ public

------------------------------------------------------------------------
-- Primitive Semantics (Parameterized)
------------------------------------------------------------------------

-- | Primitive semantics provider
--
-- Provides semantics for primitive operations (e.g., arithmetic).
-- This is a module parameter, making proofs cleaner.
--
record PrimSem : Set₁ where
  field
    evalPrim : ∀ {A B} → String → ⟦ A ⟧ → ⟦ B ⟧

open PrimSem public

------------------------------------------------------------------------
-- Evaluation of IR morphisms
------------------------------------------------------------------------

-- | Evaluation of IR morphisms (parameterized by primitive semantics)
--
-- Maps IR morphisms to Agda functions.
-- This is the morphism mapping of a functor from Once's CCC to Set.
--
eval : PrimSem → ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧

-- Category structure
eval ps id x              = x
eval ps (g ∘ f) x         = eval ps g (eval ps f x)

-- Products (AllocMode ignored in semantics)
eval ps fst (a , b)       = a
eval ps snd (a , b)       = b
eval ps (⟨ f , g ⟩ _) x   = (eval ps f x , eval ps g x)

-- Coproducts (AllocMode ignored in semantics)
eval ps (inl _) a         = inj₁ a
eval ps (inr _) b         = inj₂ b
eval ps (case f g) (inj₁ a) = eval ps f a
eval ps (case f g) (inj₂ b) = eval ps g b

-- Terminal
eval ps terminal _        = tt

-- Initial
eval ps initial ()

-- Exponential (plain functions, no Closure record)
-- curry f : IR A (B ⇒ C) creates a function capturing the input
eval ps (curry f _) a     = λ b → eval ps f (a , b)
-- apply : IR ((A ⇒ B) * A) B extracts and applies the function
eval ps apply (f , a)     = f a

-- Recursive types (Fixed point isomorphism)
eval ps (fold _) x        = wrap x
eval ps unfold x          = unwrap x

-- Effect lifting (D032)
-- arr : (A ⇒ B) → Eff A B
-- Takes a pure function and returns it as an effectful function
-- Both have the same plain function representation
eval ps arr f             = f

-- Memory management (no-op in semantics)
eval ps (free-heap _) x   = x

-- Primitives (opaque operations)
eval ps (Prim name) x     = evalPrim ps name x

------------------------------------------------------------------------
-- Backward-compatible eval (using default primitive semantics)
------------------------------------------------------------------------

-- | Postulated primitive semantics for backward compatibility
--
-- This allows existing proofs to use eval without passing PrimSem.
-- New code should prefer the parameterized version.
--
postulate
  defaultEvalPrim : ∀ {A B} → String → ⟦ A ⟧ → ⟦ B ⟧

defaultPrimSem : PrimSem
defaultPrimSem = record { evalPrim = defaultEvalPrim }

-- | Non-parameterized eval (backward compatible)
--
-- Uses default primitive semantics.
-- Prefer the parameterized version for new code.
--
eval′ : ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧
eval′ = eval defaultPrimSem

------------------------------------------------------------------------
-- KNOWN LIMITATION: Fixed Point Semantics
------------------------------------------------------------------------
--
-- The interpretation of Fix F uses a simple newtype wrapper:
--
--   ⟦ Fix F ⟧ = ⟦Fix⟧ ⟦ F ⟧
--
-- This models Fix F ≅ F, but the correct equation should be:
--
--   Fix F ≅ F[Fix F / X]   (F with recursive occurrences substituted)
--
-- For example, Nat = Fix (Unit + X) should satisfy:
--   ⟦ Nat ⟧ ≅ ⊤ ⊎ ⟦ Nat ⟧
--
-- But this model gives:
--   ⟦ Nat ⟧ = ⟦Fix⟧ (⊤ ⊎ ⟦ X ⟧)   where X is uninterpreted
--
-- A proper treatment requires modeling F as a functor with an explicit
-- recursive position (e.g., a universe of strictly positive functors).
-- See docs/formal/what-is-proven.md for options to address this.
--
------------------------------------------------------------------------