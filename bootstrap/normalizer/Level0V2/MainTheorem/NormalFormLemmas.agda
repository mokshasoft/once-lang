------------------------------------------------------------------------
-- NormalFormLemmas: Basic normal form definitions and lemmas
--
-- This module contains fundamental normal form reasoning.
-- All proofs are wrapped in abstract to prevent term expansion.
------------------------------------------------------------------------

module normalizer.Level0V2.MainTheorem.NormalFormLemmas where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
  using (TermCode')
open import normalizer.Foundations.Confluence
  using (confluence)

open import normalizer.Level0V2.Normalize
  using (normalize)

------------------------------------------------------------------------
-- Normal Form Definition
------------------------------------------------------------------------

-- A term is in normal form if no reduction rules apply
IsNormalForm : ∀ {A B} → Term A B → Set
IsNormalForm t = ∀ {u} → ¬ (t ⟶ u)

-- Normal forms have no redexes (this IS the definition)
nf-no-redex : ∀ {A B} {t : Term A B} → IsNormalForm t → ∀ {u} → ¬ (t ⟶ u)
nf-no-redex nf = nf

------------------------------------------------------------------------
-- Postulate: The normalizer produces normal forms
------------------------------------------------------------------------

postulate
  normalize-produces-nf : ∀ (t : Term Unit TermCode') →
                          IsNormalForm (normalize ∘ t)

------------------------------------------------------------------------
-- Core Lemmas (abstract to prevent expansion)
------------------------------------------------------------------------

-- Helper: Normal forms don't reduce further
abstract
  nf-stable : ∀ {A B} {t u : Term A B} → IsNormalForm t → t ⟶* u → t ≡ u
  nf-stable nf done = refl
  nf-stable nf (step r _) = ⊥-elim (nf r)

-- Lemma: If t reduces to a normal form, that's THE normal form
-- Uses confluence to prove uniqueness
abstract
  nf-unique : ∀ {A B} {t nf1 nf2 : Term A B} →
              t ⟶* nf1 → IsNormalForm nf1 →
              t ⟶* nf2 → IsNormalForm nf2 →
              nf1 ≡ nf2
  nf-unique r1 isnf1 r2 isnf2 with confluence r1 r2
  ... | w , (nf1→w , nf2→w) with nf-stable isnf1 nf1→w | nf-stable isnf2 nf2→w
  ... | refl | refl = refl
