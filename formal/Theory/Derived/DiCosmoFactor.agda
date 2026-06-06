------------------------------------------------------------------------
-- Theory.Derived.DiCosmoFactor
--
-- A factorisation lemma for confluence-of-union, in the spirit of
-- Di Cosmo (1996) §2.4 Lemma 2.7 and Hardin (1989) §2 Interpretation
-- Method.
--
-- The classical statement of Di Cosmo's Lemma 2.7 has four conditions
-- (WN R₁, R₁-NF closed under R₂, R₂ confluent on R₁-NF, R₂* commutes
-- with R₁*).  In practice the strict "R₁-NF closed under R₂" condition
-- often fails in combinator-style rewriting (e.g., CCT1's curry-comp
-- creates new R₁-redexes) — see Theory.Syntax.StrongCCL.CCT1.
-- NFClosedAnalysis for a worked counter-witness.
--
-- This module captures the REFINED formulation that the actual proof
-- machinery uses:
--
--   * WN R₁ + R₁ confluent.
--   * "R₂ over R₁" commutation (Strong-Commute below): every R₂-step
--     from x can be reflected, after R₁-normalisation on both sides,
--     as an R₂* path between R₁-NFs.
--   * Confluence of the lifted relation on R₁-NFs.
--
-- The commutation absorbs the renormalisation step that the strict
-- NFClosed variant would require.
--
-- Reference: Di Cosmo 1996 JFP §2.4; Hardin 1989 TCS 65 §2.2-§2.3.
--
-- ZERO POSTULATES at the type level. The lemma proof body is postulated
-- (its mechanisation is its own focused task).
------------------------------------------------------------------------

module Theory.Derived.DiCosmoFactor where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _∧_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Theory.Derived.ConfluenceFromDiamond using (Star; star-trans)
  renaming (done to star-done; _∷_ to _star∷_)
open import Theory.Derived.HindleyRosen using (_∪_)

------------------------------------------------------------------------
-- Auxiliary closure operations on relations
------------------------------------------------------------------------

module _ {A : Set} where

  star-single : ∀ {R : A → A → Set} {x y} → R x y → Star R x y
  star-single r = r star∷ star-done

  ----------------------------------------------------------------------
  -- Normal form predicate.
  ----------------------------------------------------------------------

  IsNF : (R : A → A → Set) → A → Set
  IsNF R x = ∀ {y} → ¬ R x y

  ----------------------------------------------------------------------
  -- Weak normalisation.
  ----------------------------------------------------------------------

  WN : (R : A → A → Set) → Set
  WN R = ∀ x → Σ A (λ nf → Star R x nf ∧ IsNF R nf)

  ----------------------------------------------------------------------
  -- Confluence of a relation R (Star-level).
  ----------------------------------------------------------------------

  ConfluenceR : (R : A → A → Set) → Set
  ConfluenceR R = ∀ {x y z} → Star R x y → Star R x z →
                  Σ A (λ w → Star R y w ∧ Star R z w)

  ----------------------------------------------------------------------
  -- Confluence of a relation S restricted to R-NFs as the carrier.
  ----------------------------------------------------------------------

  ConfOnNF : (R S : A → A → Set) → Set
  ConfOnNF R S = ∀ {x y z} → IsNF R x → Star S x y → Star S x z →
                 Σ A (λ w → Star S y w ∧ Star S z w ∧ IsNF R w)

  ----------------------------------------------------------------------
  -- Strong commutation.
  --
  -- For every x →R₂ y, given any R₁-NFs nfx and nfy with x →R₁* nfx
  -- and y →R₁* nfy, there exists a common R₁-NF w reached by R₂-only
  -- steps from nfx and (R₁ ∪ R₂)-steps from nfy.
  --
  -- Note: y's R₁-NF nfy may differ from x's nfx in interesting ways
  -- (R₂-step changed the structure). The closure point w is REACHED
  -- from nfx via R₂* (along the "lifted" R₂-step) and from nfy via
  -- R₁ ∪ R₂ steps (typically just R₂*, but occasionally R₁* if the
  -- renormalisation introduces residual structure).
  ----------------------------------------------------------------------

  StrongCommute : (R₁ R₂ : A → A → Set) → Set
  StrongCommute R₁ R₂ =
    ∀ {x y nfx nfy} →
    Star R₁ x nfx → IsNF R₁ nfx →
    R₂ x y →
    Star R₁ y nfy → IsNF R₁ nfy →
    Σ A (λ w → Star R₂ nfx w ∧ Star (R₁ ∪ R₂) nfy w ∧ IsNF R₁ w)

------------------------------------------------------------------------
-- Helper : Star (R₁ ∪ R₂) inclusion
------------------------------------------------------------------------

module _ {A : Set} {R₁ R₂ : A → A → Set} where

  star-R₁-to-union : ∀ {x y} → Star R₁ x y → Star (R₁ ∪ R₂) x y
  star-R₁-to-union star-done       = star-done
  star-R₁-to-union (r star∷ rs)    = inj₁ r star∷ star-R₁-to-union rs

  star-R₂-to-union : ∀ {x y} → Star R₂ x y → Star (R₁ ∪ R₂) x y
  star-R₂-to-union star-done       = star-done
  star-R₂-to-union (r star∷ rs)    = inj₂ r star∷ star-R₂-to-union rs

------------------------------------------------------------------------
-- Top-level statement of the refined factorisation lemma.
--
-- Given:
--   * WN R₁
--   * Confluence of R₁ (Star R₁)
--   * Strong commutation of R₂ over R₁
--   * Confluence of R₂ restricted to R₁-NF carrier
-- the union R₁ ∪ R₂ is Star-confluent.
--
-- Proof sketch (postulated):
--   1. Define φ : A → A by φ(x) = the R₁-NF reached from x (via WN +
--      Confluence-R₁ for uniqueness).
--   2. Show that any R-derivation x →R* y maps to an R₂-derivation
--      φ(x) →R₂* φ(y) via repeated application of StrongCommute.
--   3. Two R-derivations from x give two R₂-derivations from φ(x);
--      apply ConfOnNF at φ(x) to obtain a common R₁-NF w.
--      Stitch: y →R₁* φ(y) →R₂* w. Symmetric for the other side.
--
--   The argument is constructive given the four conditions; no
--   external axioms.
------------------------------------------------------------------------

module _ {A : Set} (R₁ R₂ : A → A → Set) where

  Confluent : Set
  Confluent = ConfluenceR (R₁ ∪ R₂)

  postulate
    dicosmo-factor :
      WN R₁ →
      ConfluenceR R₁ →
      StrongCommute R₁ R₂ →
      ConfOnNF R₁ R₂ →
      Confluent
