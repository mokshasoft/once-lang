------------------------------------------------------------------------
-- Theory.Derived.ConfluenceFromDiamond
--
-- ABSTRACT LEMMA, proved from the relation alone: the diamond property
-- relation implies confluence of its reflexive-transitive closure.
--
--   If R has the diamond property,
--   then Star R is confluent (Church-Rosser).
--
-- This is the standard Takahashi / diamond-lemma argument. It is
-- purely structural and does not depend on any particular reduction
-- system. Clients at any tower level can apply it by providing:
--   (a) a parallel-reduction relation R with the diamond property,
--   (b) evidence that R's reflexive-transitive closure coincides with
--       the usual reduction closure _⟶*_.
--
-- Proof technique:
--   strip lemma : R x y → Star R x z → ∃w. Star R y w ∧ Star R z w
--               (by induction on the Star R x z step sequence)
--   confluence  : Star R x y → Star R x z → ∃w. Star R y w ∧ Star R z w
--               (by induction on the first Star, using strip)
------------------------------------------------------------------------

module Theory.Derived.ConfluenceFromDiamond where

open import Data.Product
  using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Reflexive-transitive closure of a binary relation
------------------------------------------------------------------------

data Star {A : Set} (R : A → A → Set) : A → A → Set where
  done : ∀ {x} → Star R x x
  _∷_  : ∀ {x y z} → R x y → Star R y z → Star R x z

-- Transitivity of Star
star-trans : ∀ {A : Set} {R : A → A → Set} {x y z} →
             Star R x y → Star R y z → Star R x z
star-trans done         yz = yz
star-trans (r ∷ xy)     yz = r ∷ star-trans xy yz

-- Embedding of a single step
single : ∀ {A : Set} {R : A → A → Set} {x y} → R x y → Star R x y
single r = r ∷ done

------------------------------------------------------------------------
-- Diamond and Confluence (as predicates on relations)
------------------------------------------------------------------------

module _ {A : Set} (R : A → A → Set) where

  -- Diamond: two R-steps from a common source join in one R-step each.
  Diamond : Set
  Diamond = ∀ {x y z} → R x y → R x z →
            Σ A (λ w → R y w ∧ R z w)

  -- Confluence of Star R: two Star R-paths from a common source join.
  Confluent : Set
  Confluent = ∀ {x y z} → Star R x y → Star R x z →
              Σ A (λ w → Star R y w ∧ Star R z w)

------------------------------------------------------------------------
-- The strip lemma
--
-- Given R x y (one step) and Star R x z (many steps), we can close
-- the diagram as Star R y w and Star R z w.
------------------------------------------------------------------------

module _ {A : Set} {R : A → A → Set} (d : Diamond R) where

  strip : ∀ {x y z} → R x y → Star R x z →
          Σ A (λ w → Star R y w ∧ Star R z w)
  strip {y = y} r-xy done =
    (y , done , single r-xy)
  strip r-xy (r-xz₁ ∷ star-z₁-z) =
    let (v , r-yv , r-z₁v) = d r-xy r-xz₁
        (w , star-vw , star-zw) = strip r-z₁v star-z₁-z
    in  (w , r-yv ∷ star-vw , star-zw)

  ----------------------------------------------------------------------
  -- Main theorem: confluence from diamond
  ----------------------------------------------------------------------

  confluence : Confluent R
  confluence {z = z} done           star-xz =
    (z , star-xz , done)
  confluence (r-xy₁ ∷ star-y₁-y) star-xz =
    let (v , star-y₁-v , star-z-v) = strip r-xy₁ star-xz
        (w , star-y-w  , star-v-w) = confluence star-y₁-y star-y₁-v
    in  (w , star-y-w , star-trans star-z-v star-v-w)
