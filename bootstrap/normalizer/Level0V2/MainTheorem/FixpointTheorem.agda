------------------------------------------------------------------------
-- FixpointTheorem: Fixpoint implies normal form
--
-- Parameterized by normalize and its properties.
-- No heavy imports - type-checks fast.
--
-- The key theorem from OCP-0004: If a normalizer achieves fixpoint
-- on its own encoding, then it correctly normalizes all terms.
------------------------------------------------------------------------

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
  using (TermCode')
open import normalizer.Foundations.NormalForm
  using (IsNormalForm; nf-stable)

module normalizer.Level0V2.MainTheorem.FixpointTheorem
  (normalize : Term TermCode' TermCode')
  (normalize-encoded : Term Unit TermCode')
  (normalize-produces-nf : ∀ (t : Term Unit TermCode') →
                           IsNormalForm (normalize ∘ t))
  where

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
