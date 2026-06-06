------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1.ConfluenceFullViaDiCosmoHardin
--
-- CCT1 βη-confluence via the refined Di Cosmo factorisation
-- (Theory.Derived.DiCosmoFactor) instantiated with Hardin's R₁/R₂
-- split (Theory.Syntax.StrongCCL.CCT1.HardinSplit).
--
-- Pulls together:
--   * HardinSplit's R₁ (β + s + restricted id-right) and R₂ (η + the
--     residual id-right cases + id-left + eta-pair + eta-pair-gen +
--     term-unique).
--   * HardinWN's WN R₁ (currently postulated via decidability gap).
--   * The four Di Cosmo conditions:
--       WN R₁                  : from HardinWN
--       ConfluenceR R₁          : TODO (Hardin's 𝒢 confluence)
--       StrongCommute R₁ R₂     : TODO (per-rule-pair diagrams)
--       ConfOnNF R₁ R₂          : TODO (R₂ on R₁-NFs is locally simpler)
--   * dicosmo-factor → Confluent ⟶βη.
--
-- This module assembles the working framework. Three large obligations
-- remain (ConfluenceR R₁, StrongCommute, ConfOnNF), each backed by
-- focused Agda work but not new theory.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1.ConfluenceFullViaDiCosmoHardin where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_) renaming (_×_ to _∧_)

open import Theory.Syntax.StrongCCL.CCT1
open import Theory.Syntax.StrongCCL.CCT1.HardinSplit
  using (_⟶R₁_; _⟶R₂_; ⟶R₁-to-⟶βη; ⟶R₂-to-⟶βη; ⟶βη-to-R₁⊎R₂)
open import Theory.Syntax.StrongCCL.CCT1.HardinWN using (wn-R₁)

open import Theory.Derived.HindleyRosen using (_∪_)
open import Theory.Derived.DiCosmoFactor
  using (WN; ConfluenceR; StrongCommute; ConfOnNF; Confluent;
         dicosmo-factor; star-R₁-to-union; star-R₂-to-union)
open import Theory.Derived.ConfluenceFromDiamond
  using (Star) renaming (done to star-done; _∷_ to _star∷_)

------------------------------------------------------------------------
-- Three obligations, postulated until discharged.
------------------------------------------------------------------------

module _ {A B : Ty} where

  R₁ : Term A B → Term A B → Set
  R₁ = _⟶R₁_

  R₂ : Term A B → Term A B → Set
  R₂ = _⟶R₂_

  postulate
    confluence-R₁  : ConfluenceR R₁
    strong-commute : StrongCommute R₁ R₂
    conf-on-nf     : ConfOnNF R₁ R₂

  ----------------------------------------------------------------------
  -- Assembly via dicosmo-factor.
  ----------------------------------------------------------------------

  star-union-confluent : Confluent R₁ R₂
  star-union-confluent =
    dicosmo-factor R₁ R₂ wn-R₁ confluence-R₁ strong-commute conf-on-nf

  ----------------------------------------------------------------------
  -- Bridges between Star (R₁ ∪ R₂) and ⟶βη*.
  ----------------------------------------------------------------------

  ⟶βη*-to-Star-union : ∀ {t u : Term A B} →
                       t ⟶βη* u → Star (R₁ ∪ R₂) t u
  ⟶βη*-to-Star-union done       = star-done
  ⟶βη*-to-Star-union (r ∷ rs)   with ⟶βη-to-R₁⊎R₂ r
  ... | inj₁ r₁ = inj₁ r₁ star∷ ⟶βη*-to-Star-union rs
  ... | inj₂ r₂ = inj₂ r₂ star∷ ⟶βη*-to-Star-union rs

  Star-union-to-⟶βη* : ∀ {t u : Term A B} →
                       Star (R₁ ∪ R₂) t u → t ⟶βη* u
  Star-union-to-⟶βη* star-done            = done
  Star-union-to-⟶βη* (inj₁ r₁ star∷ rs)   =
    ⟶βη-step (⟶R₁-to-⟶βη r₁) (Star-union-to-⟶βη* rs)
    where
    ⟶βη-step : ∀ {t u v : Term A B} → t ⟶βη u → u ⟶βη* v → t ⟶βη* v
    ⟶βη-step r rs = r ∷ rs
  Star-union-to-⟶βη* (inj₂ r₂ star∷ rs)   =
    ⟶R₂-to-⟶βη r₂ ∷ Star-union-to-⟶βη* rs

  ----------------------------------------------------------------------
  -- Main theorem : Confluence of ⟶βη*.
  ----------------------------------------------------------------------

  cct1-confluence-DiCosmoHardin :
    ∀ {t u v : Term A B} →
    t ⟶βη* u → t ⟶βη* v →
    Σ (Term A B) (λ w → (u ⟶βη* w) ∧ (v ⟶βη* w))
  cct1-confluence-DiCosmoHardin tu tv
    with star-union-confluent (⟶βη*-to-Star-union tu) (⟶βη*-to-Star-union tv)
  ... | (w , star-uw , star-vw) =
    w , Star-union-to-⟶βη* star-uw , Star-union-to-⟶βη* star-vw
