------------------------------------------------------------------------
-- Theory.Derived.HindleyRosen
--
-- Hindley-Rosen lemma (structural, one-step formulation):
--
--   Given two binary relations R and S on the same set, if both have
--   the diamond property and they commute (elementary), then their
--   pointwise union R ∪ S has the diamond property.
--
--     Diamond R  ∧  Diamond S  ∧  Commute R S  ⟹  Diamond (R ∪ S)
--
-- Proof: case analysis on which sub-relation each step comes from.
-- Four cases — (R,R), (R,S), (S,R), (S,S) — closed by the diamonds
-- of R and S, and by the commutation for the mixed cases.
--
-- Composed with Theory.Derived.ConfluenceFromDiamond, this gives a
-- clean per-layer composition: at each level of the CCTower, prove
-- diamond for the NEW rules, prove commutation with prior rules, and
-- inherit diamond for the combined reduction automatically. From
-- diamond of the union, confluence of Star(R ∪ S) follows via
-- ConfluenceFromDiamond.confluence.
--
-- A pure structural lemma about abstract relations.
------------------------------------------------------------------------

module Theory.Derived.HindleyRosen where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _∧_)
open import Theory.Derived.ConfluenceFromDiamond using (Diamond)

------------------------------------------------------------------------
-- Pointwise union of relations
------------------------------------------------------------------------

module _ {A : Set} where

  _∪_ : (A → A → Set) → (A → A → Set) → (A → A → Set)
  (R ∪ S) x y = R x y ⊎ S x y

------------------------------------------------------------------------
-- Commutation
--
-- R and S commute (elementary) when any R-step and S-step from a
-- common source can be reconciled in one step each of the other
-- relation.
--
-- Stronger than necessary — the Star-level version would suffice —
-- but elementary commutation is the natural per-rule-pair obligation
-- for the tower and it trivially entails the Star-level version.
------------------------------------------------------------------------

  Commute : (R S : A → A → Set) → Set
  Commute R S =
    ∀ {x y z} → R x y → S x z → Σ A (λ w → S y w ∧ R z w)

------------------------------------------------------------------------
-- Hindley-Rosen
--
-- Given diamonds of R and S and their commutation, the union R ∪ S
-- has the diamond property. Combine with ConfluenceFromDiamond to
-- obtain confluence of the reflexive-transitive closure.
------------------------------------------------------------------------

  hindley-rosen :
    (R S : A → A → Set) →
    Diamond R → Diamond S → Commute R S →
    Diamond (R ∪ S)
  hindley-rosen R S d-R d-S comm = diamond-union
    where
    diamond-union : Diamond (R ∪ S)

    -- Case R,R: closed by diamond of R.
    diamond-union (inj₁ r1) (inj₁ r2) with d-R r1 r2
    ... | (w , r3 , r4) = (w , inj₁ r3 , inj₁ r4)

    -- Case R,S: closed by commutation (R step joined by S, S step joined by R).
    diamond-union (inj₁ r) (inj₂ s) with comm r s
    ... | (w , s' , r') = (w , inj₂ s' , inj₁ r')

    -- Case S,R: symmetric to R,S.
    diamond-union (inj₂ s) (inj₁ r) with comm r s
    ... | (w , s' , r') = (w , inj₁ r' , inj₂ s')

    -- Case S,S: closed by diamond of S.
    diamond-union (inj₂ s1) (inj₂ s2) with d-S s1 s2
    ... | (w , s3 , s4) = (w , inj₂ s3 , inj₂ s4)
