------------------------------------------------------------------------
-- Theory.Systems.CCT3
--
-- BCC + Initial Algebras (μ-types / inductive types).
--
-- Additional structure:
--   μ F      : Obj (least fixed point of F : Obj → Obj)
--   In       : F(μF) → μF
--   Out      : μF → F(μF)
--   cata     : (F A → A) → (μF → A)
--
-- Additional reduction rules:
--   cata-β  : cata alg ∘ In ⟶ alg ∘ fmap F (cata alg)
--   out-in  : Out ∘ In ⟶ id      (Lambek 1968)
--
-- This is the minimum level that supports self-encoding of morphisms
-- as data, and hence the minimum level at which the Ranzow Fixpoint
-- property is meaningful.
--
-- NOTE: F is abstracted here as a plain type-level map (Obj → Obj).
-- A full treatment would require F to be a (strictly positive) functor,
-- with fmap, identity, and composition laws. That refinement is deferred
-- to a future FunctorStructure.agda. Established results (Lambek 1968,
-- Mendler 1987) that require strict positivity carry that assumption
-- in their statements.
------------------------------------------------------------------------

module Theory.Systems.CCT3 where

open import Theory.Systems.CCT2

------------------------------------------------------------------------
-- CCT3 Structure = CCT2 + initial algebras
------------------------------------------------------------------------

record CCT3Structure : Set₁ where
  field
    bcc : CCT2Structure

  open CCT2Structure bcc public

  field
    -- Initial algebras (μ-types)
    μ    : (Obj → Obj) → Obj
    In   : ∀ {F : Obj → Obj} → Hom (F (μ F)) (μ F)
    Out  : ∀ {F : Obj → Obj} → Hom (μ F) (F (μ F))
    cata : ∀ {F : Obj → Obj} {A} → Hom (F A) A → Hom (μ F) A
