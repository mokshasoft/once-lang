------------------------------------------------------------------------
-- MainTheorem: The Complete Verification Structure
--
-- This module structures the full proof that the normalizer is correct.
-- Missing pieces are postulates that need to be filled in.
--
-- The main theorem: If a normalizer achieves fixpoint on its own
-- encoding, then it correctly normalizes all terms.
------------------------------------------------------------------------

module normalizer.Level0V2.MainTheorem where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding

------------------------------------------------------------------------
-- Part 1: What we have (proven with zero postulates)
------------------------------------------------------------------------

-- The encoding infrastructure
open import normalizer.Level0V2.Normalizer
  using ( refold-idempotent  -- (cata TermF In ∘ encode t) ⟶* encode t
        )

-- The reduction system
-- - _⟶_ : single-step reduction
-- - _⟶*_ : multi-step reduction
-- - ⇒→⟶* : parallel reduction implies multi-step (proven)

------------------------------------------------------------------------
-- Part 2: The Real Normalizer - DEFINED in Normalize.agda
------------------------------------------------------------------------

-- The normalizer is defined in Level0V2/Normalize.agda
-- It applies CCC reduction rules to encoded terms.
-- Structure: normalize = cata TermF normalize-step

open import normalizer.Level0V2.Normalize
  using (normalize; normalize-encoded)

-- normalize : Term TermCode' TermCode'
-- normalize-encoded : Term Unit TermCode'

------------------------------------------------------------------------
-- Part 3: Normal Forms - DEFINED
------------------------------------------------------------------------

-- A term is in normal form if no reduction rules apply
-- This is simply the negation of "can reduce"
IsNormalForm : ∀ {A B} → Term A B → Set
IsNormalForm t = ∀ {u} → ¬ (t ⟶ u)

-- Normal forms have no redexes (this IS the definition)
nf-no-redex : ∀ {A B} {t : Term A B} → IsNormalForm t → ∀ {u} → ¬ (t ⟶ u)
nf-no-redex nf = nf

-- The normalizer produces normal forms
postulate
  normalize-produces-nf : ∀ (t : Term Unit TermCode') →
                          IsNormalForm (normalize ∘ t)

------------------------------------------------------------------------
-- Part 4: Confluence (Diamond Property) - PROVEN
------------------------------------------------------------------------

-- Confluence is proven in Foundations/Confluence.agda
-- It uses the Tait-Martin-Löf technique with parallel reduction.
-- Only 2 postulates remain: complete and ⇒-to-complete

open import normalizer.Foundations.Confluence
  using (confluence)
  -- confluence : t ⟶* u → t ⟶* v → ∃[ w ] (u ⟶* w × v ⟶* w)

------------------------------------------------------------------------
-- Part 5: Strong Normalization
------------------------------------------------------------------------

-- All reduction sequences terminate
-- This follows from the structure of CCC + initial algebras

postulate
  strong-normalization : ∀ {A B} (t : Term A B) →
                         ∃[ nf ] ((t ⟶* nf) × IsNormalForm nf)

------------------------------------------------------------------------
-- Part 6: Semantic Correctness
------------------------------------------------------------------------

-- The normalizer preserves semantics
-- (normalized term is equivalent to original)

postulate
  normalize-preserves-semantics : ∀ (t : Term Unit TermCode') →
                                  ((normalize ∘ t) ⟶* t) ⊎ (t ⟶* (normalize ∘ t))
  -- Actually, we want: they reduce to the same normal form
  -- normalize-correct : ∀ t → ∃[ nf ] ((t ⟶* nf) × ((normalize ∘ t) ⟶* nf))

------------------------------------------------------------------------
-- Part 7: The Fixpoint Property
------------------------------------------------------------------------

-- The normalizer's own encoding is defined in Normalize.agda:
--   normalize-encoded : Term Unit TermCode'
--   normalize-encoded = encode normalize

-- THE KEY PROPERTY: normalizer achieves fixpoint on its own encoding
postulate
  fixpoint-property : (normalize ∘ normalize-encoded) ⟶* normalize-encoded

-- Note: For `cata TermF In`, we PROVED this (refold-idempotent).
-- For the real normalizer, we need to prove it too.

------------------------------------------------------------------------
-- Part 8: The Main Theorem
------------------------------------------------------------------------

-- The central claim from OCP-0004:
-- If a normalizer achieves fixpoint on its own encoding,
-- then it correctly normalizes all terms.

-- What "correctly normalizes" means:
record CorrectNormalizer (N : Term TermCode' TermCode') : Set where
  field
    -- N terminates on all inputs (produces a result)
    terminates : ∀ (t : Term Unit TermCode') →
                 ∃[ result ] ((N ∘ t) ⟶* result)

    -- N produces normal forms
    produces-nf : ∀ (t : Term Unit TermCode') →
                  ∀ {result} → (N ∘ t) ⟶* result → IsNormalForm result

    -- N preserves semantics (result equivalent to input)
    preserves : ∀ (t : Term Unit TermCode') →
                ∀ {result} → (N ∘ t) ⟶* result →
                ∃[ nf ] ((t ⟶* nf) × (result ⟶* nf))

-- THE MAIN THEOREM
postulate
  main-theorem : (N : Term TermCode' TermCode') →
                 (N ∘ encode N) ⟶* encode N →  -- fixpoint property
                 CorrectNormalizer N            -- implies correctness

-- Instantiation: our normalizer is correct
normalizer-correct : CorrectNormalizer normalize
normalizer-correct = main-theorem normalize fixpoint-property

------------------------------------------------------------------------
-- Summary: The Verification Path
------------------------------------------------------------------------

{-
STATUS OF EACH COMPONENT:

✓ PROVEN (zero postulates):
  - refold-idempotent (encoding infrastructure)
  - ⇒→⟶* (parallel → multi-step reduction)
  - All CCC reduction rules

○ POSTULATED (need to prove):
  - normalize (the actual normalizer)
  - IsNormalForm (definition)
  - normalize-produces-nf
  - confluence
  - strong-normalization
  - normalize-preserves-semantics
  - fixpoint-property (for real normalizer)
  - main-theorem (fixpoint ⟹ correctness)

The main theorem is the key insight from OCP-0004:
  "If a normalizer is a fixpoint of itself, it must be correct"

This follows because:
  1. CCC has unique normal forms (confluence + termination)
  2. If N(⟦N⟧) = ⟦N⟧, then ⟦N⟧ is already normal
  3. By compositionality, N correctly normalizes all terms

Once we prove main-theorem, the rest follows from the fixpoint property.
-}
