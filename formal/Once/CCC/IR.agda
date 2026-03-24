-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.IR
--
-- The core IR based on Cartesian Closed Categories.
--
-- This is THE IR for Once - the categorical foundation that everything
-- else compiles to. Surface syntax is sugar on top.
--
-- Structure:
--   - Category: id, _∘_
--   - Products: ⟨_,_⟩, fst, snd
--   - Coproducts: inl, inr, case
--   - Terminal/Initial: terminal, initial
--   - Exponentials: curry, apply
--   - Recursive types: fold, unfold
--   - Effects: arr
--   - Primitives: Prim (opaque external operations)
--   - Memory: free-heap (explicit deallocation)
------------------------------------------------------------------------

module Once.CCC.IR where

open import Data.String using (String)

-- Import and re-export Type
open import Once.Type public

-- Import WellFormedF for recursion scheme constructors
open import Once.Functor.Translate using (WellFormedF)

-- HeapRef for free-heap
open import Once.CCC.Machine.SMCore using (HeapRef)

------------------------------------------------------------------------
-- Allocation Mode
--
-- Specifies stack vs heap allocation for compound values.
-- Used by escape analysis and code generation.
------------------------------------------------------------------------

data AllocMode : Set where
  Stack : AllocMode  -- Allocate inline on stack (non-escaping)
  Heap  : AllocMode  -- Allocate on heap (escaping)

------------------------------------------------------------------------
-- IR Language
--
-- CCC-based intermediate representation.
------------------------------------------------------------------------

data IR : Type → Type → Set where
  -- Category structure
  id : ∀ {A} → IR A A
  _∘_ : ∀ {A B C} → IR B C → IR A B → IR A C

  -- Product (A * B)
  ⟨_,_⟩ : ∀ {A B C} → IR A B → IR A C → AllocMode → IR A (B * C)
  fst : ∀ {A B} → IR (A * B) A
  snd : ∀ {A B} → IR (A * B) B

  -- Coproduct (A + B)
  inl : ∀ {A B} → AllocMode → IR A (A + B)
  inr : ∀ {A B} → AllocMode → IR B (A + B)
  case : ∀ {A B C} → IR A C → IR B C → IR (A + B) C

  -- Terminal object (Unit)
  terminal : ∀ {A} → IR A Unit

  -- Initial object (Void)
  initial : ∀ {A} → IR Void A

  -- Exponential (A ⇒[ q ] B)
  curry : ∀ {A B C q} → IR (A * B) C → AllocMode → IR A (B ⇒[ q ] C)
  apply : ∀ {A B q} → IR ((A ⇒[ q ] B) * A) B

  -- Effect lifting
  arr : ∀ {A B q} → IR (A ⇒[ q ] B) (Eff A B)

  -- fold/unfold removed by OCP-0003: use In/Cata/Out/Ana instead
  -- (Total and productive by construction)

  --------------------------------------------------------------------------
  -- Recursion Schemes (OCP-0003: Total/Productive)
  --
  -- These replace general fold/unfold with structured recursion that
  -- guarantees termination (cata) or productivity (ana).
  --
  -- All constructors require WellFormedF proofs to ensure functors only
  -- use K with base types, enabling postulate-free semantic evaluation.
  --------------------------------------------------------------------------

  -- Initial algebra operations (inductive types, total recursion)
  -- In: F(μF) → μF (constructor)
  In : ∀ {F} → WellFormedF F → AllocMode → IR (⟦ F ⟧T (μ-type F)) (μ-type F)

  -- Cata: given IR morphism (F(A) → A), produce μF → A
  -- This is the universal property of initial algebras.
  -- Total by Lambek's Lemma: μF is well-founded.
  Cata : ∀ {F} → WellFormedF F → ∀ {A} → IR (⟦ F ⟧T A) A → IR (μ-type F) A

  -- Final coalgebra operations (coinductive types, productive corecursion)
  -- Out: νF → F(νF) (observation/destructor)
  Out : ∀ {F} → WellFormedF F → IR (ν-type F) (⟦ F ⟧T (ν-type F))

  -- Ana: given IR morphism (A → GuardedT F A), produce A → νF
  -- OCP-0003: Productivity enforced by requiring GuardedT output.
  -- The coalgebra must produce guarded values, guaranteeing that each
  -- unfolding step produces one F-layer before any recursive call.
  -- This makes productivity DEFINITIONAL - unguarded coalgebras cannot type-check.
  Ana : ∀ {F} → WellFormedF F → ∀ {A} → IR A (GuardedT F A) → IR A (ν-type F)

  -- Unguard: extract underlying functor value from guarded value
  -- GuardedT F A → ⟦ F ⟧T A
  -- This "consumes" the guardedness guarantee - use after Ana has processed.
  Unguard : ∀ {F} → WellFormedF F → ∀ {A} → IR (GuardedT F A) (⟦ F ⟧T A)

  --------------------------------------------------------------------------
  -- Guard: wrap functor value as guarded
  -- ⟦ F ⟧T A → GuardedT F A
  --
  -- This establishes the isomorphism: GuardedT F A ≅ ⟦ F ⟧T A
  --
  -- CATEGORICAL JUSTIFICATION:
  -- GuardedT F A is structurally isomorphic to ⟦ F ⟧T A. The Guarded
  -- constructors (GProd, GInl, GInr, GConst, GRec) mirror the functor
  -- structure exactly. Any F(A) value can be wrapped as Guarded F A.
  --
  -- The PURPOSE of requiring GuardedT in Ana's type is to ensure that
  -- coalgebras are DEFINED in a guarded way (syntactically proving that
  -- each corecursive step produces one F-layer before recursing).
  --
  -- But once you HAVE an ⟦ F ⟧T A value (e.g., from Out observing a ν-value),
  -- wrapping it as GuardedT is always valid - the value already exists.
  --
  -- This enables the Ana-Out identity law:
  --   Ana (Guard ∘ Out) ≡ id
  --
  -- Which is categorically required: (νF, Out) is the final F-coalgebra,
  -- so the unique morphism from it to itself must be the identity.
  -- Guard ∘ Out represents the same coalgebra as Out, just with the
  -- type wrapped to satisfy Ana's signature.
  --------------------------------------------------------------------------
  Guard : ∀ {F} → WellFormedF F → ∀ {A} → IR (⟦ F ⟧T A) (GuardedT F A)

  -- Hylo: fusion of cata and ana (deforestation)
  -- OCP-0003: coalg must produce GuardedT for productivity
  -- cata alg ∘ ana coalg, computed directly without intermediate structure
  Hylo : ∀ {F} → WellFormedF F → ∀ {A B} → IR (⟦ F ⟧T B) B → IR A (GuardedT F A) → IR A B

  -- Explicit heap deallocation
  -- Added by escape analysis when heap values can be freed.
  free-heap : HeapRef → IR Unit Unit

  -- Primitive operations (opaque)
  Prim : ∀ {A B} → String → IR A B

infixr 9 _∘_
infixr 4 ⟨_,_⟩