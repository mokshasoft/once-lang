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

-- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana.

-- Recursion schemes (OCP-0003: total/productive)
--
-- These use coercions between Type-level functor (⟦_⟧T) and Set-level
-- functor (⟦_⟧F) applications. The coherence is proven in Core.agda.
--
-- In: ⟦ F ⟧T (μ-type F) → μ-type F
eval ps (In {F} _) x = sem-In F (coerce-functor F (μ-type F) x)
--
-- Cata: given alg : ⟦ F ⟧T A → A, produce μ-type F → A
-- Build Set-level algebra from Type-level, then apply sem-cata
eval ps (Cata {F} {A} alg) x =
  sem-cata F (λ fa → eval ps alg (coerce-functor⁻¹ F A fa)) x
--
-- Out: ν-type F → ⟦ F ⟧T (ν-type F)
eval ps (Out {F}) x = coerce-functor⁻¹ F (ν-type F) (sem-CoOut F x)
--
-- Ana: given GUARDED coalg : A → GuardedT F A, produce A → ν-type F
-- OCP-0003: Productivity enforced by requiring GuardedT output.
eval ps (Ana {F} {A} coalg) x =
  sem-ana-guarded F (λ a → eval ps coalg a) x
--
-- Unguard: extract functor value from guarded value
eval ps (Unguard {F} {A}) x = coerce-functor⁻¹ F A (sem-unguard F x)
--
-- Guard: wrap functor value as guarded (establishes GuardedT ≅ ⟦ F ⟧T isomorphism)
eval ps (Guard {F} {A}) x = sem-guard F (coerce-functor F A x)
--
-- Hylo: Cata alg ∘ Ana coalg, computed directly without intermediate
-- OCP-0003: Uses GUARDED coalgebra for productivity
eval ps (Hylo {F} {A} {B} alg coalg) x =
  let alg-set = λ fb → eval ps alg (coerce-functor⁻¹ F B fb)
  in sem-hylo-guarded F alg-set (λ a → eval ps coalg a) x

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
-- OCP-0003: Recursion Scheme Semantics
------------------------------------------------------------------------
--
-- With OCP-0003, recursive types use polynomial functors:
--
--   μ-type F : inductive/finite data (consumed via Cata)
--   ν-type F : coinductive/infinite codata (produced via Ana)
--
-- where F : Functor is a strictly positive polynomial functor.
-- This provides proper fixed point semantics via SPF.agda.
--
-- Example: Nat = μ-type (K Unit ⊕ Id) satisfies:
--   ⟦ Nat ⟧ = ⟦μ⟧ (K Unit ⊕ Id) ≅ ⊤ ⊎ ⟦ Nat ⟧
--
------------------------------------------------------------------------