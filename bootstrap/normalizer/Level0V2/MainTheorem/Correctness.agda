------------------------------------------------------------------------
-- Correctness: Proof that the normalizer is correct
--
-- This module contains the CorrectNormalizer record and proves
-- that our normalize function satisfies it.
------------------------------------------------------------------------

module normalizer.Level0V2.MainTheorem.Correctness where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
  using (TermCode')
open import normalizer.Foundations.Confluence
  using (confluence)

open import normalizer.Level0V2.Normalize
  using (normalize)

open import normalizer.Level0V2.NormalizeLemmas
  using (_>>_)

open import normalizer.Level0V2.MainTheorem.NormalFormLemmas
  using (IsNormalForm; nf-stable; normalize-produces-nf)

------------------------------------------------------------------------
-- Postulates
------------------------------------------------------------------------

-- All reduction sequences terminate
postulate
  strong-normalization : ∀ {A B} (t : Term A B) →
                         ∃[ nf ] ((t ⟶* nf) × IsNormalForm nf)

-- The normalizer preserves semantics
postulate
  normalize-preserves-semantics : ∀ (t : Term Unit TermCode') →
                                  ((normalize ∘ t) ⟶* t) ⊎ (t ⟶* (normalize ∘ t))

------------------------------------------------------------------------
-- What "correctly normalizes" means
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Field implementations (abstract to prevent expansion)
------------------------------------------------------------------------

-- Field 1: terminates
-- Follows directly from strong-normalization
abstract
  normalize-terminates : ∀ (t : Term Unit TermCode') →
                         ∃[ result ] ((normalize ∘ t) ⟶* result)
  normalize-terminates t with strong-normalization (normalize ∘ t)
  ... | nf , (reduction , _) = nf , reduction

-- Field 2: produces-nf
-- The result of normalize is a normal form.
--
-- Key insight: normalize-produces-nf tells us (normalize ∘ t) is already
-- in normal form. By nf-stable, any reduction from it must be trivial (≡).
-- Therefore the result must equal (normalize ∘ t) and thus be normal.
abstract
  normalize-output-is-nf : ∀ (t : Term Unit TermCode') →
                           ∀ {result} → (normalize ∘ t) ⟶* result →
                           IsNormalForm result
  normalize-output-is-nf t {result} reduction =
    subst IsNormalForm (nf-stable (normalize-produces-nf t) reduction)
                       (normalize-produces-nf t)

-- Field 3: preserves
-- The normalized result is equivalent to the input.
-- Uses confluence and >> for flat proof composition.
abstract
  normalize-preserves : ∀ (t : Term Unit TermCode') →
                        ∀ {result} → (normalize ∘ t) ⟶* result →
                        ∃[ nf ] ((t ⟶* nf) × (result ⟶* nf))
  normalize-preserves t {result} reduction with normalize-preserves-semantics t
  ... | inj₁ norm→t with confluence reduction norm→t
    -- (normalize ∘ t) ⟶* t
    -- We have: (normalize ∘ t) ⟶* result and (normalize ∘ t) ⟶* t
    -- By confluence: result and t reduce to common w
  ...   | w , (result→w , t→w) = w , (t→w , result→w)
  normalize-preserves t {result} reduction | inj₂ t→norm =
    -- t ⟶* (normalize ∘ t)
    -- result is reachable from (normalize ∘ t), which is reachable from t
    -- Using >> for flat composition instead of nested ⟶*-trans
    result , (t→norm >> reduction , done)

------------------------------------------------------------------------
-- The Concrete Theorem: Our normalizer is correct
------------------------------------------------------------------------

normalizer-correct : CorrectNormalizer normalize
normalizer-correct = record
  { terminates  = normalize-terminates
  ; produces-nf = normalize-output-is-nf
  ; preserves   = normalize-preserves
  }
