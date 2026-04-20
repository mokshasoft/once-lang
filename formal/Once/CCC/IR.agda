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

  -- Effect lifting (arrow's unit: pure → effectful)
  arr : ∀ {A B q} → IR (A ⇒[ q ] B) (Eff A B)

  -- Effect application (arrow's run: execute an effectful arrow on an input).
  -- Dual to `apply` for pure arrows. At runtime compiles to the same code
  -- as `apply` (both are function calls) — the distinction is purely type-
  -- level tracking of effectfulness. Introduced so Surface.effApp elaborates
  -- structurally via `applyEff` instead of a Eff→Arrow coercion postulate.
  applyEff : ∀ {A B} → IR ((Eff A B) * A) B

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

  -- out-μ: μF → F(μF) (destructor, inverse of In)
  -- By Lambek's Lemma, In is an isomorphism, so its inverse exists.
  -- This enables pattern-matching on μ-types inside Hylo coalgebras,
  -- which is essential for proper fusion in observation primitives.
  -- See OCP-0003 "Lambek Isomorphisms" section.
  out-μ : ∀ {F} → WellFormedF F → IR (μ-type F) (⟦ F ⟧T (μ-type F))

  -- Cata: given IR morphism (F(A) → A), produce μF → A
  -- This is the universal property of initial algebras.
  -- Total by Lambek's Lemma: μF is well-founded.
  Cata : ∀ {F} → WellFormedF F → ∀ {A} → IR (⟦ F ⟧T A) A → IR (μ-type F) A

  -- Para: paramorphism (fold with access to original substructure)
  -- Total by derivation from Cata (structural recursion on well-founded μF).
  -- The algebra receives F(μF × A), giving access to both the original
  -- substructure and the recursive result.
  Para : ∀ {F} → WellFormedF F → ∀ {A}
       → IR (⟦ F ⟧T (μ-type F * A)) A
       → IR (μ-type F) A

  -- Final coalgebra operations (coinductive types, productive corecursion)
  -- Out: νF → F(νF) (observation/destructor)
  Out : ∀ {F} → WellFormedF F → IR (ν-type F) (⟦ F ⟧T (ν-type F))

  -- in-ν: F(νF) → νF (constructor, inverse of Out)
  -- By Lambek's Lemma (dual), Out is an isomorphism, so its inverse exists.
  -- Provides symmetry with μ-type operations.
  in-ν : ∀ {F} → WellFormedF F → AllocMode → IR (⟦ F ⟧T (ν-type F)) (ν-type F)

  -- Ana: given IR morphism (A → F(A)), produce A → νF
  -- Productivity follows from IR totality: coalgebras are IR morphisms,
  -- IR morphisms are total, therefore each coalgebra step terminates and
  -- produces one F-layer. See IR/Totality.agda and IR/Productivity.agda.
  Ana : ∀ {F} → WellFormedF F → ∀ {A} → IR A (⟦ F ⟧T A) → IR A (ν-type F)

  -- Guard/Unguard removed: GuardedT was unnecessary.
  -- Productivity follows from IR totality, not type-level guardedness.
  -- See IR/Totality.agda for the proof that all IR coalgebras are "guarded".

  -- Hylo: fusion of cata and ana (deforestation) - CORRECT BY CONSTRUCTION
  -- cata alg ∘ ana coalg, computed directly without intermediate structure
  --
  -- OCP-0003: Hylo is now based on Fuse, removing the need for TerminatesOn.
  -- Termination is guaranteed by requiring μG as input:
  -- - Input is μG (well-founded inductive type)
  -- - Coalgebra produces F-layers from μG values
  -- - Recursion is structural on μG
  --
  -- Semantically: Hylo alg coalg ≡ Fuse alg (coalg ∘ In)
  -- The coalgebra wraps In to convert the pre-destructed G-layer to F-layer.
  --
  -- NO TERMINATING PRAGMA NEEDED - termination follows from Fuse!
  --
  Hylo : ∀ {F G} → WellFormedF F → WellFormedF G → ∀ {B}
       → IR (⟦ F ⟧T B) B                          -- algebra: F(B) → B
       → IR (μ-type G) (⟦ F ⟧T (μ-type G))        -- coalgebra: μG → F(μG)
       → IR (μ-type G) B

  -- Fuse: μ-anchored fusion (deforestation) - CORRECT BY CONSTRUCTION
  --
  -- OCP-0003: Structured fusion that is provably terminating.
  -- Unlike Hylo, termination is guaranteed by the type structure:
  -- - Input is μG (well-founded inductive type)
  -- - Transform receives pre-destructed G-layer via out-μ
  -- - Recursion is structural on μG - each recursive call on strict subterm
  --
  -- The transform converts G-layers to F-layers without changing recursive depth:
  --   transform : G(μG) → F(μG)
  --
  -- Semantically: Fuse alg transform = cata (alg ∘ transform)
  -- But computed via direct recursion for deforestation.
  --
  -- NO TERMINATING PRAGMA NEEDED - termination is structural!
  --
  Fuse : ∀ {F G} → WellFormedF F → WellFormedF G → ∀ {B}
       → IR (⟦ F ⟧T B) B                              -- algebra: F(B) → B
       → IR (⟦ G ⟧T (μ-type G)) (⟦ F ⟧T (μ-type G))   -- transform: G(μG) → F(μG)
       → IR (μ-type G) B

  -- Explicit heap deallocation
  -- Added by escape analysis when heap values can be freed.
  free-heap : HeapRef → IR Unit Unit

  -- Primitive operations (opaque)
  Prim : ∀ {A B} → String → IR A B

infixr 9 _∘_
infixr 4 ⟨_,_⟩