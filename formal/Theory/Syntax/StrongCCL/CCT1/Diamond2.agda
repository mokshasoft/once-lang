------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.Diamond2
--
-- Diamond property for ⟹₂ (parallel reduction with eta-pair-gen +
-- congruences only, no other rule firings).
--
-- The non-linear LHS pattern of eta-pair-gen
--
--     ⟨ fst ∘ h , snd ∘ h ⟩  ⟶s  h
--
-- is the entire reason we are doing the Hindley-Rosen split. Diamond
-- ⟹₂ is the focused obligation that isolates exactly this difficulty.
--
-- DIAMOND ⟹₂ STILL HOLDS (informal argument).
--   For the worst case t = ⟨ fst ∘ h , snd ∘ h ⟩, the two ⟹₂-derivations
--   either both fire eta-pair-gen (closed by Diamond IH on h) or one
--   fires eta-pair-gen and the other a ⟹₂-⟨,⟩ congruence (closed by
--   choosing the witness ⟨ fst ∘ w , snd ∘ w ⟩ where w is the IH-derived
--   common reduct of the two h-reducts the ⟹₂-⟨,⟩ branch produces; the
--   eta-pair-gen branch reduces to that ⟨,⟩-pattern in one further
--   eta-pair-gen step). So the diamond closes via a witness that is
--   an eta-pair-gen REDEX, which the eta-pair-gen-fired branch reaches
--   via firing eta-pair-gen on its own reduct.
--
--   The proof goes through a complete-development function
--
--     _★ : Term A B → Term A B
--
--   that fires every detectable eta-pair-gen redex (using the
--   reusable DecidableEquality.≟ to test the non-linear constraint
--   h₁ ≟ h₂) and parallel-recurses into subterms.  Lemma 1 (t ⟹₂ t★)
--   plus Triangle (t ⟹₂ u → u ⟹₂ t★) yield Diamond ⟹₂ in the
--   standard way.
--
-- This module provides the obligation Diamond ⟹₂ as a postulate and
-- documents the structure of the missing proof.  Subsequent commits
-- will fill in _★, Lemma 1, and Triangle.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.Diamond2 where

open import Data.Product
  using (Σ; _,_) renaming (_×_ to _∧_)

open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Syntax.StrongCCL.CCT1.ParallelReductionSplit
  using (_⟹₂_)

------------------------------------------------------------------------
-- Diamond ⟹₂.
--
-- Stated directly. The obligation closes via _★ + Lemma 1 + Triangle
-- where _★ uses Theory.Syntax.StrongCCL.CCT1.DecidableEquality to
-- detect the non-linear eta-pair-gen pattern.
------------------------------------------------------------------------

postulate
  diamond₂ : ∀ {A B} {t u v : Term A B} →
             t ⟹₂ u → t ⟹₂ v →
             Σ (Term A B) (λ w → (u ⟹₂ w) ∧ (v ⟹₂ w))
