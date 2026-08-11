------------------------------------------------------------------------
-- Theory.Derived.Newman
--
-- ABSTRACT LEMMA, proved from the relation alone: a strongly normalizing
-- relation is confluent iff it is locally confluent.
--
--   Newman's lemma : SN R → LocalConfluent R → Confluent R
--
-- Here SN is formalised as accessibility: Acc R x means every R-reduct
-- of x is accessible, so there is no infinite R-chain from x. SN R
-- asserts Acc R for every element.
--
-- LocalConfluent R is the WCR (weakly Church-Rosser) property: any
-- two single steps from a common source rejoin via many-step paths.
-- Confluent R is the full CR property on Star R (reflexive-transitive
-- closure): any two Star-paths rejoin.
--
-- Proof technique:
--   By strong induction on the accessibility of the common source x,
--   case-splitting on whether either Star-path is empty. When both
--   are non-empty, local confluence closes the top, two inner IHs
--   close the left and right wings, and a third IH on the confluence
--   point closes the bottom.
------------------------------------------------------------------------

module Theory.Derived.Newman where

open import Data.Product
  using (Σ; _,_) renaming (_×_ to _∧_)
open import Theory.Derived.ConfluenceFromDiamond
  using (Star; done; _∷_; star-trans)

------------------------------------------------------------------------
-- Accessibility / strong normalization
------------------------------------------------------------------------

data Acc {A : Set} (R : A → A → Set) (x : A) : Set where
  acc : (∀ {y} → R x y → Acc R y) → Acc R x

-- Accessibility transfers along Star R.
star-acc : ∀ {A : Set} {R : A → A → Set} {x y} →
           Acc R x → Star R x y → Acc R y
star-acc a done          = a
star-acc (acc ih) (r ∷ rs) = star-acc (ih r) rs

------------------------------------------------------------------------
-- Local confluence / weak Church-Rosser (WCR) and full Confluence
------------------------------------------------------------------------

module _ {A : Set} (R : A → A → Set) where

  -- Local confluence: two single R-steps from a common source join
  -- via Star R.
  LocalConfluent : Set
  LocalConfluent = ∀ {x y z} → R x y → R x z →
                   Σ A (λ w → Star R y w ∧ Star R z w)

  -- Strong normalization: every element is accessible under R.
  SN : Set
  SN = ∀ x → Acc R x

  -- Full confluence of Star R.
  Confluent : Set
  Confluent = ∀ {x y z} → Star R x y → Star R x z →
              Σ A (λ w → Star R y w ∧ Star R z w)

------------------------------------------------------------------------
-- Newman's lemma
------------------------------------------------------------------------

module _ {A : Set} {R : A → A → Set} (lc : LocalConfluent R) where

  -- The termination story:
  --   * newman-acc recurses on the Acc argument (structural).
  --   * newman-step first walks the given Star (structurally) to obtain
  --     a smaller Acc, then hands off to newman-acc. Agda sees the
  --     mutual pair as co-recursive with a lexicographic measure
  --     (Acc, Star) that strictly decreases on every call.
  mutual
    newman-acc : ∀ {x y z} → Acc R x →
                 Star R x y → Star R x z →
                 Σ A (λ w → Star R y w ∧ Star R z w)
    newman-acc         _        done            s-xz       =
      (_ , s-xz , done)
    newman-acc {y = y} _        (r-xy₀ ∷ s-y₀y) done        =
      (y , done , r-xy₀ ∷ s-y₀y)
    newman-acc         (acc ih) (r-xx₁ ∷ s-x₁y) (r-xx₂ ∷ s-x₂z) =
      let a₁                  = ih r-xx₁
          a₂                  = ih r-xx₂
          (u  , s-x₁u , s-x₂u) = lc r-xx₁ r-xx₂
          (w₁ , s-yw₁ , s-uw₁) = newman-acc  a₁ s-x₁y s-x₁u
          (w₂ , s-uw₂ , s-zw₂) = newman-acc  a₂ s-x₂u s-x₂z
          (w  , s-w₁w , s-w₂w) = newman-step a₁ s-x₁u s-uw₁ s-uw₂
      in  (w , star-trans s-yw₁ s-w₁w , star-trans s-zw₂ s-w₂w)

    -- Descend along a Star to reach the confluence point with a still
    -- smaller Acc, then invoke newman-acc.
    newman-step : ∀ {x u y z} → Acc R x → Star R x u →
                  Star R u y → Star R u z →
                  Σ A (λ w → Star R y w ∧ Star R z w)
    newman-step a        done       s-uy s-uz = newman-acc a s-uy s-uz
    newman-step (acc ih) (r ∷ rs)   s-uy s-uz = newman-step (ih r) rs s-uy s-uz

  newman : SN R → Confluent R
  newman sn s-xy s-xz = newman-acc (sn _) s-xy s-xz
