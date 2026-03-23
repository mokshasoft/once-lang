------------------------------------------------------------------------
-- MinimalTheory: Entry Point for Restricted Confluence Theory
--
-- This module serves as the entry point for the minimal theory that
-- proves uniqueness of normal forms using only standard CCC confluence
-- (not the full confluence of μ-types).
--
-- POSTULATES USED:
--   - StandardCCC.ccc-complete : Complete development for CCC
--   - StandardCCC.ccc-triangle : Triangle lemma for CCC
--
-- THESE ARE STANDARD RESULTS from Lambek & Scott, "Introduction to
-- Higher Order Categorical Logic". They predate and do not require
-- μ-types.
--
-- PROVEN IN THIS THEORY:
--   - restricted-confluence : (cata TermF alg ∘ encode t) is confluent
--   - normalizer-unique     : NoRedex t → normalize ∘ encode t has unique nf
--   - fixpoint-unique       : normalize ∘ encode normalize has unique nf
------------------------------------------------------------------------

module normalizer.MinimalTheory where

------------------------------------------------------------------------
-- Core: Postulate-Free Fixpoint Property (from TCB0)
------------------------------------------------------------------------

-- The fixpoint theorem requires NO postulates
open import normalizer.TCB0
  using ( normalize          -- The normalizer
        ; noredex-fixpoint   -- NoRedex t → (normalize ∘ encode t) ⟶* encode t
        )
  public

------------------------------------------------------------------------
-- Minimal Postulate: Standard CCC Confluence
------------------------------------------------------------------------

-- This is the ONLY postulate we need beyond TCB0.
-- It states that standard CCC (without μ-types) is confluent.
-- This is Lambek & Scott's result from "Introduction to Higher Order
-- Categorical Logic" (1986).
open import normalizer.Axioms.StandardCCC
  using ( _⟶ccc_          -- CCC-only reduction (no cata rules)
        ; _⟶*ccc_         -- Multi-step CCC reduction
        ; _⟹ccc_          -- Parallel CCC reduction
        ; ccc-complete    -- POSTULATE: Complete development
        ; ccc-triangle    -- POSTULATE: Triangle lemma
        ; ccc-diamond     -- Derived: Diamond property
        ; ccc-confluence⟹ -- Derived: Parallel confluence
        )
  public

------------------------------------------------------------------------
-- Supporting Theory: Cata Properties
------------------------------------------------------------------------

-- Terms without cata constructors
open import normalizer.Theory.StandardCCCExtension.CataFree
  using ( CataFree            -- Predicate: term has no cata
        ; encode-is-catafree  -- encode t is always cata-free
        ; ccc-preserves-catafree  -- CCC reduction preserves cata-free
        )
  public

-- Cata reductions terminate on encoded terms
open import normalizer.Theory.StandardCCCExtension.CataElimination
  using ( _⟶cata_         -- Cata-only reduction
        ; _⟶*cata_        -- Multi-step cata reduction
        ; cata-terminates -- Cata reductions terminate on encoded terms
        )
  public

-- Cata reductions are locally confluent
open import normalizer.Theory.StandardCCCExtension.CataCommutation
  using ( _⟹cata_             -- Parallel cata reduction
        ; cata-diamond        -- Diamond property for cata
        ; cata-local-confluence -- Local confluence for cata
        )
  public

------------------------------------------------------------------------
-- Main Results: Restricted Confluence and Uniqueness
------------------------------------------------------------------------

-- Restricted confluence for encoded terms
open import normalizer.Theory.StandardCCCExtension.RestrictedConfluence
  using ( restricted-confluence        -- (cata TermF alg ∘ encode t) is confluent
        ; restricted-confluence-noredex -- Same, with NoRedex precondition
        )
  public

-- Uniqueness of normal forms
open import normalizer.Theory.Uniqueness
  using ( normalizer-unique     -- NoRedex t → unique normal form
        ; fixpoint-unique       -- Fixpoint has unique normal form
        ; fixpoint-is-unique-nf -- Any nf equals encode normalize
        ; canonical-normal-form -- NoRedex t → any nf is encode t (KEY)
        ; encode-is-nf          -- encode of NoRedex is normal form
        )
  public

------------------------------------------------------------------------
-- Trust Summary
--
-- LEVEL 0 - TCB0 (Postulate-Free):
--   - noredex-fixpoint : NoRedex t → (normalize ∘ encode t) ⟶* encode t
--   - This proves the EXISTENCE of the fixpoint
--
-- LEVEL 1 - MinimalTheory (Standard CCC Postulate Only):
--   - Uses: ccc-complete, ccc-triangle (Lambek & Scott)
--   - Proves:
--       • restricted-confluence
--       • normalizer-unique
--       • fixpoint-unique
--   - This proves UNIQUENESS of normal forms
--
-- LEVEL 2 - Main (Full Theory):
--   - Uses: All EstablishedMath postulates
--   - Proves: General correctness properties
--
-- The key insight is that Level 1 only requires standard CCC confluence,
-- which is well-established (Lambek & Scott, 1986) and does not involve
-- μ-types at all. The μ-type specific reductions (cata-beta) are proven
-- to be confluent by structural arguments, not postulates.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Dependencies
--
-- StandardCCC.agda (postulate)
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
