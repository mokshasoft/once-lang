------------------------------------------------------------------------
-- MinimalTheory: Entry Point for Restricted Confluence Theory
--
-- This module serves as the entry point for the theory that
-- establishes uniqueness of normal forms using standard CCC confluence
-- (not the full confluence of μ-types).
--
-- POSTULATES USED (from EstablishedMath and StandardCCC):
--   - ccc-complete, ccc-triangle : Standard CCC confluence
--   - cata-complete, cata-triangle : Cata reduction confluence
--   - cata-terminates : Termination on encoded terms
--   - encode-is-nf : Encoding of NoRedex is normal form
--
-- THESE ARE STANDARD RESULTS from Lambek & Scott, "Introduction to
-- Higher Order Categorical Logic" (for CCC) and structural arguments
-- (for cata properties).
--
-- DERIVED IN THIS THEORY:
--   - restricted-confluence : By combining cata and CCC confluence
--   - normalizer-unique     : From confluence + normal form definition
--   - fixpoint-unique       : Instantiation of normalizer-unique
------------------------------------------------------------------------

module normalizer.MinimalTheory where

------------------------------------------------------------------------
-- Core: Fixpoint Property (from TCB0)
------------------------------------------------------------------------

-- The fixpoint theorem (derived by structural induction in TCB0)
open import normalizer.TCB0
  using ( normalize          -- The normalizer
        ; noredex-fixpoint   -- NoRedex t → (normalize ∘ encode t) ⟶* encode t
        )
  public

------------------------------------------------------------------------
-- Standard CCC Confluence
------------------------------------------------------------------------

-- Standard CCC confluence from Lambek & Scott.
-- This is the CCC reduction without μ-type rules.
open import normalizer.Axioms.StandardCCC
  using ( _⟶ccc_          -- CCC-only reduction (no cata rules)
        ; _⟶*ccc_         -- Multi-step CCC reduction
        ; _⟹ccc_          -- Parallel CCC reduction
        ; ccc-complete    -- Complete development (Lambek & Scott)
        ; ccc-triangle    -- Triangle lemma (Lambek & Scott)
        ; ccc-diamond     -- Derived from triangle
        ; ccc-confluence⟹ -- Derived from strip lemma
        )
  public

------------------------------------------------------------------------
-- Supporting Theory: Cata Properties
------------------------------------------------------------------------

-- Terms without cata constructors
open import normalizer.Theory.StandardCCCExtension.CataFree
  using ( CataFree            -- Predicate: term has no cata
        ; encode-is-catafree  -- By structural induction on t
        ; ccc-preserves-catafree  -- By case analysis on reduction
        )
  public

-- Cata reductions terminate on encoded terms
open import normalizer.Theory.StandardCCCExtension.CataElimination
  using ( _⟶cata_         -- Cata-only reduction
        ; _⟶*cata_        -- Multi-step cata reduction
        ; cata-terminates -- Termination (finite depth argument)
        )
  public

-- Cata reductions have the diamond property
open import normalizer.Theory.StandardCCCExtension.CataCommutation
  using ( _⟹cata_             -- Parallel cata reduction
        ; cata-diamond        -- Derived from triangle
        ; cata-local-confluence -- Derived from diamond
        )
  public

------------------------------------------------------------------------
-- Main Results: Restricted Confluence and Uniqueness
------------------------------------------------------------------------

-- Restricted confluence for encoded terms
open import normalizer.Theory.StandardCCCExtension.RestrictedConfluence
  using ( restricted-confluence        -- From cata + CCC confluence
        ; restricted-confluence-noredex -- Same, with NoRedex precondition
        )
  public

-- Uniqueness of normal forms
open import normalizer.Theory.Uniqueness
  using ( normalizer-unique     -- From confluence + normal form definition
        ; fixpoint-unique       -- Instantiation for normalize
        ; fixpoint-is-unique-nf -- Combines existence with uniqueness
        ; canonical-normal-form -- The key compiler verification theorem
        )
  public

-- Encoding properties (from EstablishedMath)
open import normalizer.Axioms.EstablishedMath
  using ( encode-is-nf          -- Encoding of NoRedex is normal form
        )
  public

------------------------------------------------------------------------
-- Trust Summary
--
-- LEVEL 0 - TCB0:
--   - noredex-fixpoint : By structural induction on t
--   - Establishes EXISTENCE of the fixpoint
--
-- LEVEL 1 - MinimalTheory:
--   - Uses axioms from EstablishedMath/StandardCCC
--   - Derives restricted-confluence, normalizer-unique, etc.
--   - Establishes UNIQUENESS of normal forms
--
-- LEVEL 2 - Main (Full Theory):
--   - Uses all EstablishedMath axioms
--   - Establishes general correctness properties
--
-- The key insight: Level 1 requires only standard CCC confluence
-- (Lambek & Scott, 1986) plus structural termination arguments.
-- The μ-type specific reductions (cata-beta) have confluence
-- derived from the diamond property.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Dependencies
--
-- StandardCCC.agda (defines _⟶ccc_, asserts confluence)
--        ↓
-- CataFree.agda ← Encoding/Encoding.agda
--        ↓
-- CataElimination.agda ← Syntax/NoRedex.agda
--        ↓
-- CataCommutation.agda
--        ↓
-- RestrictedConfluence.agda ← TCB0 (noredex-fixpoint)
--        ↓
-- Uniqueness.agda
--        ↓
-- MinimalTheory.agda (this module)
------------------------------------------------------------------------
