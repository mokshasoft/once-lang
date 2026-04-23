------------------------------------------------------------------------
-- Theory.Established.Rutten2000
--
-- CITATION:
--   Rutten, J.J.M.M. (2000). "Universal coalgebra: a theory of systems."
--   Theoretical Computer Science 249(1):3-80.
--
-- TOWER LEVEL: CCT4 (BCCR = BCC + μ-types + ν-types).
--
-- THEOREMS (Rutten 2000, §3–§4):
--   (A) νOut : νF → F(νF) is an isomorphism (dual to Lambek's Lemma).
--   (B) ana coalg : A → νF is the unique F-coalgebra morphism from
--       any (A, coalg) to the final coalgebra (νF, νOut).
--   (C) Coinduction principle: bisimilar elements of νF are equal.
--
-- STATUS IN THIS FORMALIZATION:
--   The iso directions and ana-β are now LAW FIELDS of
--   Theory.Systems.CCT4. This module re-exports them and keeps
--   ana-unique + coinduction as true postulates (existence /
--   uniqueness content).
------------------------------------------------------------------------

module Theory.Established.Rutten2000 where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- The Theorems
------------------------------------------------------------------------

module _ (S : CCT4Structure) where
  open CCT4Structure S

  ------------------------------------------------------------------------
  -- (A) νOut / νIn are inverse — re-exports CCT4Structure laws.
  ------------------------------------------------------------------------

  final-in-out : ∀ {F : Obj → Obj} → (νIn {F} ∘ νOut {F}) ≈ id
  final-in-out = νin-νout

  final-out-in : ∀ {F : Obj → Obj} → (νOut {F} ∘ νIn {F}) ≈ id
  final-out-in = νout-νin

  ------------------------------------------------------------------------
  -- β-rule for ana — re-exports the CCT4Structure law.
  ------------------------------------------------------------------------

  ana-β-law : ∀ {F : Obj → Obj} {A} {coalg : Hom A (F A)} →
              (νOut {F} ∘ ana {F} coalg) ≈
              (fmap {F} (ana {F} coalg) ∘ coalg)
  ana-β-law = ana-β

  ------------------------------------------------------------------------
  -- (B) ana-unique: ana coalg is the UNIQUE F-coalgebra morphism.
  ------------------------------------------------------------------------

  postulate
    ana-unique : ∀ {F : Obj → Obj} {A}
                 (coalg : Hom A (F A)) (h : Hom A (ν F)) →
                 -- Hypothesis: h is an F-coalgebra morphism
                 (νOut {F} ∘ h) ≈ (fmap {F} h ∘ coalg) →
                 h ≈ ana coalg

  ------------------------------------------------------------------------
  -- (C) Coinduction: bisimilar elements of νF are equal.
  ------------------------------------------------------------------------

  postulate
    Bisimilar : ∀ {F : Obj → Obj} →
                Hom Unit (ν F) → Hom Unit (ν F) → Set

    coinduction : ∀ {F : Obj → Obj} {x y : Hom Unit (ν F)} →
                  Bisimilar {F} x y → x ≈ y
