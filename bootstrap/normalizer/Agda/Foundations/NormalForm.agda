------------------------------------------------------------------------
-- NormalForm: General definitions and lemmas about normal forms
--
-- A term is in normal form if no reduction rules apply.
-- This module contains general reasoning that doesn't depend on
-- any specific normalizer.
------------------------------------------------------------------------

module normalizer.Foundations.NormalForm where

open import normalizer.Foundations.Types
open import normalizer.Foundations.CCC
open import normalizer.Foundations.Confluence
  using (confluence)

------------------------------------------------------------------------
-- Normal Form Definition
------------------------------------------------------------------------

-- Imported from CCC to avoid circular dependencies
-- IsNormalForm : ∀ {A B} → Term A B → Set
-- IsNormalForm t = ∀ {u} → ¬ (t ⟶ u)
open import normalizer.Foundations.CCC using (IsNormalForm) public

-- Normal forms have no redexes (this IS the definition)
nf-no-redex : ∀ {A B} {t : Term A B} → IsNormalForm t → ∀ {u} → ¬ (t ⟶ u)
nf-no-redex nf = nf

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
