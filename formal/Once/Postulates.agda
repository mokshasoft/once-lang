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
--   T (Tool hypothesis): a fact about the tools (Agda's primitives and
--     their compiled implementation) that Agda does not export (D329)
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
open import Data.List using (List)
import Data.List as List
open import Data.Bool using (true)
open import Data.Char using (Char; isDigit)
import Data.Char as Char
open import Data.Nat using (_∸_; _<_)
open import Data.String using (String; toList; fromList; _++_)


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
-- Tool hypotheses T1, T2: the String primitives (D329)
------------------------------------------------------------------------
--
-- `primStringAppend`, `primStringToList` and `primStringFromList` are opaque
-- to Agda's conversion checker: of their properties only the injectivity of
-- `toList` and `fromList` is exported (`Agda.Builtin.String.Properties`).
-- The two facts below are the standard library's own
-- (`Data.String.Unsafe.toList-++`, `toList∘fromList`, there by `trustMe`,
-- which `--safe` rejects).
--
-- NEEDED BY: Once.Adequacy.SpecFront.Render — `showCanonical` is injective
--   on word names (plan 0.121 R13): the compiler finds a generator by its
--   rendered name, the Spec by its canonical name; and the Spec's lexer
--   builds a word by `fromList`.
--
-- JUSTIFICATION:
--   A hypothesis about the tools, not an axiom of the logic: a String is a
--   list of characters (the model the primitives are specified against),
--   and the compiled implementation (MAlonzo's `Data.Text`: `append`,
--   `unpack`, `pack`) satisfies both. Testable on the extracted code.
--
-- IMPACT:
--   If either failed, two distinct canonical names could render alike, and
--   the front-end bridges (`sound`, `complete`) would not hold as stated.
--
-- RUNTIME EFFECT: None (erased; proofs only)
--
------------------------------------------------------------------------

postulate
  toList-++      : ∀ (s t : String) → toList (s ++ t) ≡ toList s List.++ toList t
  toList∘fromList : ∀ (cs : List Char) → toList (fromList cs) ≡ cs

------------------------------------------------------------------------
-- Tool hypothesis T3: the primitive `isDigit` (D342)
------------------------------------------------------------------------
--
-- `primIsDigit` is opaque to Agda's conversion checker as well: it computes
-- on a literal character only, and nothing about it is exported. It accepts
-- the ten decimal digits only, so a digit's value is below ten.
--
-- NEEDED BY: Once.Format.Proof.LexOK — a float's fraction, read by the
--   Spec's lexer, fits its digits, so the formatter prints it back
--   (`once fmt`'s theorems, plan 0.124).
--
-- JUSTIFICATION:
--   A hypothesis about the tools, not an axiom of the logic: Agda specifies
--   `primIsDigit` as Haskell's `Data.Char.isDigit` (the ASCII digits '0'..'9'
--   only), and MAlonzo compiles it to that function. Testable on the
--   extracted code (the 1 114 112 characters can be enumerated).
--
-- IMPACT:
--   If it failed, a float literal could be printed back as another one, and
--   `once fmt`'s round trip would not hold as stated.
--
-- RUNTIME EFFECT: None (erased; proofs only)
--
------------------------------------------------------------------------

postulate
  isDigit-value : ∀ c → isDigit c ≡ true → Char.toℕ c ∸ Char.toℕ '0' < 10

------------------------------------------------------------------------
-- P2, P3, P5 (retired): the fold's universal property (`fold-unique`,
-- `fold-fusion`, plan 0.112 D3) and unfold's computation law (`unfold-out`,
-- plan 0.116 E) — PROVED in `Once.Metatheory.Recursion`, by induction on the
-- (finite) μ tree and by the ν coercions' definitions. The numbers are not
-- reused.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- P4 (retired): coherence of the core meaning — PROVED by plan 0.116 D1
-- (`Once.Metatheory.Coherence`), after D310 made a core term determine its
-- type. The number is not reused.
------------------------------------------------------------------------

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
