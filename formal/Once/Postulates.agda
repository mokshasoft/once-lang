-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Postulates
--
-- CENTRAL REGISTRY OF ALL ASSUMPTIONS
--
-- This module collects all postulates and known semantic gaps in the
-- Once formalization. Import from here to make dependencies explicit.
--
-- Categories:
--   P (Postulate): Explicit axiom assumed without proof
--   S (Semantic Gap): Limitation in the semantic model itself
--
-- When adding new assumptions (P2, P3, ... or S2, S3, ...):
--   1. NEEDED BY: Which modules depend on it
--   2. JUSTIFICATION: Why it's believed sound
--   3. IMPACT: What would break if it's wrong
--   4. RUNTIME EFFECT: Whether it affects execution
--   5. Update docs/formal/what-is-proven.md
--
-- To detect postulates: agda --safe <file> or grep -r "postulate" .
--
------------------------------------------------------------------------

module Once.Postulates where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type
open import Once.Semantics.Machine

------------------------------------------------------------------------
-- Postulate P1: Function Extensionality
------------------------------------------------------------------------
--
-- Two functions are equal if they agree on all inputs.
--
-- NEEDED BY: Once.Surface.Correct (elaborate-correct for lambdas)
--
-- JUSTIFICATION:
--   Function extensionality is consistent with Agda's type theory
--   and holds in most models (e.g., setoid model, cubical type theory).
--   It's used only in proof terms, which are erased during extraction.
--
-- IMPACT:
--   If function extensionality were somehow false, the elaboration
--   correctness proof for lambda expressions would be invalid.
--   However, this would also break most of mathematics, so we're
--   confident this is safe.
--
-- RUNTIME EFFECT: None (erased during extraction)
--
------------------------------------------------------------------------

postulate
  extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
                   (∀ x → f x ≡ g x) → f ≡ g

------------------------------------------------------------------------
-- Semantic Gap S1: Fixed Point Semantics
------------------------------------------------------------------------
--
-- A KNOWN SEMANTIC GAP, recorded as documentation. It lives in the
-- DEFINITION of ⟦_⟧ for Fix, below.
--
-- The current interpretation of Fix F uses a simple newtype wrapper:
--
--   record ⟦Fix⟧ (A : Set) : Set where
--     constructor wrap
--     field unwrap : A
--
--   ⟦ Fix F ⟧ = ⟦Fix⟧ ⟦ F ⟧
--
-- This models Fix F ≅ F, but the correct equation should be:
--
--   Fix F ≅ F[Fix F / X]   (F with recursive occurrences substituted)
--
-- CONSEQUENCE:
--   The proofs eval-fold-unfold and eval-unfold-fold are trivially refl.
--   They prove the wrapper isomorphism, NOT the recursive fixed point
--   property.
--
-- IMPACT:
--   Programs using Fix (like Nat, List) are not fully verified.
--   The fold/unfold operations are type-correct and operationally
--   behave correctly, but the semantic model doesn't capture the
--   true recursive structure.
--
-- RESOLUTION:
--   See docs/formal/what-is-proven.md for options:
--   - Option 1: Universe of strictly positive functors
--   - Option 2: Sized types
--   - Option 3: Well-founded recursion
--   - Option 4: QIITs
--
-- This limitation is documented here and in Once.Semantics.agda.
--
------------------------------------------------------------------------

-- A documentation marker: the limitation is intrinsic to how ⟦_⟧ is
-- defined for Fix.
