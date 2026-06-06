------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.ConfluenceFullViaHR
--
-- CCT1 βη confluence via Hindley-Rosen + diamond.
--
-- Combines:
--   * Diamond ⟹₁                    (Theory.Syntax.StrongCCL.CCT1.Diamond1)
--   * Diamond ⟹₂                    (Theory.Syntax.StrongCCL.CCT1.Diamond2)
--   * Commute ⟹₁ ⟹₂                (Theory.Syntax.StrongCCL.CCT1.Commute12)
--   * Theory.Derived.HindleyRosen.hindley-rosen
--   * Theory.Derived.ConfluenceFromDiamond.confluence
--   * the bridges in ParallelReductionSplit
--
-- to obtain Confluent ⟶βη* — independent of the Newman-based
-- ConfluenceFull which depends on the structurally-blocked
-- local-confluent-rest postulate (Curien curry-η critical pair).
--
-- This module pulls together a working scaffolding. The remaining
-- gap is exactly: triangle₁, diamond₂, commute₁₂ (three obligations,
-- all in stand-alone modules with focused proof structure).
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.ConfluenceFullViaHR where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _∧_)

open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Syntax.StrongCCL.CCT1.ParallelReduction using (⟶βη*-trans)
open import Theory.Syntax.StrongCCL.CCT1.ParallelReductionSplit
open import Theory.Syntax.StrongCCL.CCT1.Diamond1   using (diamond₁)
open import Theory.Syntax.StrongCCL.CCT1.Diamond2   using (diamond₂)
open import Theory.Syntax.StrongCCL.CCT1.Commute12  using (commute₁₂)

open import Theory.Derived.HindleyRosen
  using (_∪_; Commute; hindley-rosen)
open import Theory.Derived.ConfluenceFromDiamond
  using (Star; Diamond; Confluent; confluence)
  renaming (done to star-done; _∷_ to _star∷_)

------------------------------------------------------------------------
-- Pin down the relations at fixed A B (so they live in a single Set,
-- as required by the abstract Diamond / Confluent / Hindley-Rosen).
------------------------------------------------------------------------

module _ {A B : Ty} where

  R₁ : Term A B → Term A B → Set
  R₁ = _⟹₁_

  R₂ : Term A B → Term A B → Set
  R₂ = _⟹₂_

  R₁∪R₂ : Term A B → Term A B → Set
  R₁∪R₂ = R₁ ∪ R₂

  ----------------------------------------------------------------------
  -- Three Hindley-Rosen hypotheses, repackaged from the focused
  -- modules with the exact types the abstract lemma expects.
  ----------------------------------------------------------------------

  d-R₁ : Diamond R₁
  d-R₁ = diamond₁

  d-R₂ : Diamond R₂
  d-R₂ = diamond₂

  comm-R₁-R₂ : Commute R₁ R₂
  comm-R₁-R₂ = commute₁₂

  ----------------------------------------------------------------------
  -- Step 1 : Diamond (⟹₁ ∪ ⟹₂).
  ----------------------------------------------------------------------

  diamond-union : Diamond R₁∪R₂
  diamond-union = hindley-rosen R₁ R₂ d-R₁ d-R₂ comm-R₁-R₂

  ----------------------------------------------------------------------
  -- Step 2 : Confluent (Star (⟹₁ ∪ ⟹₂)).
  ----------------------------------------------------------------------

  star-union-confluent : Confluent R₁∪R₂
  star-union-confluent = confluence diamond-union

  ----------------------------------------------------------------------
  -- Bridges between Star (⟹₁ ∪ ⟹₂) and ⟶βη*.
  ----------------------------------------------------------------------

  ⟶βη*-to-Star-union : ∀ {t u : Term A B} →
                       t ⟶βη* u → Star R₁∪R₂ t u
  ⟶βη*-to-Star-union done       = star-done
  ⟶βη*-to-Star-union (r ∷ rs)   with ⟶βη-to-⟹₁⊎⟹₂ r
  ... | inj₁ r₁ = inj₁ r₁ star∷ ⟶βη*-to-Star-union rs
  ... | inj₂ r₂ = inj₂ r₂ star∷ ⟶βη*-to-Star-union rs

  Star-union-to-⟶βη* : ∀ {t u : Term A B} →
                       Star R₁∪R₂ t u → t ⟶βη* u
  Star-union-to-⟶βη* star-done            = done
  Star-union-to-⟶βη* (inj₁ r₁ star∷ rs)   =
    ⟶βη*-trans (⟹₁-to-⟶βη* r₁) (Star-union-to-⟶βη* rs)
  Star-union-to-⟶βη* (inj₂ r₂ star∷ rs)   =
    ⟶βη*-trans (⟹₂-to-⟶βη* r₂) (Star-union-to-⟶βη* rs)

  ----------------------------------------------------------------------
  -- Main theorem : Confluence of ⟶βη*.
  ----------------------------------------------------------------------

  cct1-confluence-HR : ∀ {t u v : Term A B} →
                       t ⟶βη* u → t ⟶βη* v →
                       Σ (Term A B) (λ w → (u ⟶βη* w) ∧ (v ⟶βη* w))
  cct1-confluence-HR tu tv
    with star-union-confluent (⟶βη*-to-Star-union tu) (⟶βη*-to-Star-union tv)
  ... | (w , star-uw , star-vw) =
    w , Star-union-to-⟶βη* star-uw , Star-union-to-⟶βη* star-vw
