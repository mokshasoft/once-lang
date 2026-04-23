------------------------------------------------------------------------
-- Theory.Established.Lambek1968
--
-- CITATION:
--   Lambek, J. (1968). "A fixpoint theorem for complete categories."
--   Mathematische Zeitschrift 103:151-161.
--
-- TOWER LEVEL: CCT3 (BCC + initial algebras / μ-types).
--
-- THEOREM (Lambek 1968):
--   In any category with initial F-algebras, the structure map
--   In : F(μF) → μF is an isomorphism.
--
-- PROOF SKETCH:
--   1. (μF, In) is initial by definition.
--   2. (F(μF), fmap In) is also an F-algebra.
--   3. By initiality, there is a unique morphism h : μF → F(μF) such
--      that h ∘ In = fmap In ∘ fmap h. Call this h = Out.
--   4. Uniqueness + the initial-algebra equations give Out ∘ In = id.
--   5. The composition In ∘ Out satisfies the same equation as id on
--      (μF, In), so by uniqueness, In ∘ Out = id.
--
-- STATUS IN THIS FORMALIZATION:
--   Both iso directions are now LAW FIELDS of Theory.Systems.CCT3 —
--   `out-in` and `in-out`. Any concrete syntax that instantiates
--   CCT3Structure must prove them. This module exports them as
--   theorems-under-CCT3 for citation purposes.
--
--   cata-β is likewise a law field of CCT3Structure.
--
--   cata-unique (the universal property: every F-algebra morphism
--   into a CCT3-structure is `cata` of its algebra map) remains
--   postulated here — it is content that is NOT encoded as an
--   equation on a specific rewrite rule but rather an existence /
--   uniqueness principle over arbitrary `h`.
------------------------------------------------------------------------

module Theory.Established.Lambek1968 where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- The Theorems
------------------------------------------------------------------------

module _ (S : CCT3Structure) where
  open CCT3Structure S

  ------------------------------------------------------------------------
  -- Lambek's Lemma: In is an isomorphism.
  -- Now simply re-exports the CCT3Structure laws.
  ------------------------------------------------------------------------

  lambek-out-in : ∀ {F : Obj → Obj} → (Out {F} ∘ In {F}) ≈ id
  lambek-out-in = out-in

  lambek-in-out : ∀ {F : Obj → Obj} → (In {F} ∘ Out {F}) ≈ id
  lambek-in-out = in-out

  ------------------------------------------------------------------------
  -- β-rule for cata — re-exports the CCT3Structure law.
  ------------------------------------------------------------------------

  cata-β-law : ∀ {F : Obj → Obj} {A} {alg : Hom (F A) A} →
               (cata {F} alg ∘ In {F}) ≈ (alg ∘ fmap {F} (cata {F} alg))
  cata-β-law = cata-β

  ------------------------------------------------------------------------
  -- Universal property of cata: cata alg is the UNIQUE F-algebra
  -- morphism (μF, In) → (A, alg). Still postulated — expresses
  -- existence/uniqueness over all morphisms, not a single equation.
  ------------------------------------------------------------------------

  postulate
    cata-unique : ∀ {F : Obj → Obj} {A}
                  (alg : Hom (F A) A) (h : Hom (μ F) A) →
                  -- Hypothesis: h is an F-algebra morphism
                  (h ∘ In {F}) ≈ (alg ∘ fmap {F} h) →
                  h ≈ cata alg
