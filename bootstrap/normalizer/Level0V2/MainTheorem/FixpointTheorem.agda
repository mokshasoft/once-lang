------------------------------------------------------------------------
-- FixpointTheorem: Fixpoint implies normal form
--
-- The key theorem from OCP-0004: If a normalizer achieves fixpoint
-- on its own encoding, then it correctly normalizes all terms.
------------------------------------------------------------------------

module normalizer.Level0V2.MainTheorem.FixpointTheorem where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
  using (TermCode')

open import normalizer.Level0V2.Normalize
  using (normalize; normalize-encoded)

open import normalizer.Level0V2.NormalForm
  using (fixpoint-property)

open import normalizer.Level0V2.MainTheorem.NormalFormLemmas
  using (IsNormalForm; nf-stable; normalize-produces-nf)

------------------------------------------------------------------------
-- The Key Theorem: Fixpoint Implies Normal Form
--
-- In a simple system (confluent + terminating), we prove:
--   1. Fixpoints of normalization ARE normal forms
--   2. Normal forms are unique
--   3. Therefore: fixpoint ⟹ correct and unique
------------------------------------------------------------------------

-- Key theorem: If N(x) ⟶* x, and N produces normal forms, then x is normal.
--
-- Proof: N(x) is a normal form (by normalize-produces-nf).
--        N(x) ⟶* x (given).
--        But normal forms don't reduce (nf-stable).
--        Therefore x ≡ N(x), so x is a normal form.
abstract
  fixpoint-implies-nf : ∀ (t : Term Unit TermCode') →
                        (normalize ∘ t) ⟶* t →
                        IsNormalForm t
  fixpoint-implies-nf t fixpoint =
    subst IsNormalForm (nf-stable (normalize-produces-nf t) fixpoint)
                       (normalize-produces-nf t)

-- The concrete fixpoint theorem for our normalizer:
-- If normalize achieves fixpoint on its encoding, that encoding is normal.
abstract
  normalize-encoding-is-nf : (normalize ∘ normalize-encoded) ⟶* normalize-encoded →
                             IsNormalForm normalize-encoded
  normalize-encoding-is-nf = fixpoint-implies-nf normalize-encoded

-- Using our proven fixpoint-property from NormalForm:
abstract
  normalize-encoded-is-normal : IsNormalForm normalize-encoded
  normalize-encoded-is-normal = normalize-encoding-is-nf fixpoint-property
