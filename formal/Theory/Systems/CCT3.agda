------------------------------------------------------------------------
-- Theory.Systems.CCT3
--
-- BCC + Initial Algebras (μ-types / inductive types), specified
-- purely equationally.
--
-- Additional structure:
--   μ F   : Obj (least fixed point of F : Obj → Obj)
--   In    : F(μF) → μF
--   Out   : μF → F(μF)
--   cata  : (F A → A) → (μF → A)
--
-- Additional laws:
--   out-in        : Out ∘ In ≈ id      (Lambek 1968, β-direction)
--   in-out        : In ∘ Out ≈ id      (Lambek 1968, η-direction)
--   cata-β        : cata alg ∘ In ≈ alg ∘ fmap F (cata alg)
--
-- This is the minimum level that supports self-encoding of morphisms
-- as data, and hence the minimum level at which the Ranzow Fixpoint
-- property is meaningful.
--
-- NOTE: F is abstracted here as a plain type-level map (Obj → Obj).
-- The functor action on morphisms (fmap) is exposed as a field;
-- strict-positivity and full functor laws are left to a future
-- FunctorStructure refinement.
--
-- Directed rewriting belongs at the Syntax level.
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
    ---------------------------------------------------------------
    -- Initial algebras (μ-types)
    ---------------------------------------------------------------

    μ    : (Obj → Obj) → Obj
    In   : ∀ {F : Obj → Obj} → Hom (F (μ F)) (μ F)
    Out  : ∀ {F : Obj → Obj} → Hom (μ F) (F (μ F))
    cata : ∀ {F : Obj → Obj} {A} → Hom (F A) A → Hom (μ F) A

    ---------------------------------------------------------------
    -- Functor action on morphisms (needed to state cata-β).
    -- Full functoriality and strict-positivity are deferred to a
    -- separate FunctorStructure.
    ---------------------------------------------------------------

    fmap : ∀ {F : Obj → Obj} {A B} → Hom A B → Hom (F A) (F B)

    ---------------------------------------------------------------
    -- Cata congruence
    ---------------------------------------------------------------

    cata-cong : ∀ {F : Obj → Obj} {A} {alg alg' : Hom (F A) A} →
                alg ≈ alg' → cata {F} alg ≈ cata {F} alg'

    ---------------------------------------------------------------
    -- Lambek's lemma (In is an iso)
    ---------------------------------------------------------------

    out-in : ∀ {F : Obj → Obj} → (Out {F} ∘ In {F}) ≈ id
    in-out : ∀ {F : Obj → Obj} → (In  {F} ∘ Out {F}) ≈ id

    ---------------------------------------------------------------
    -- Universal property of cata (β-rule)
    ---------------------------------------------------------------

    cata-β : ∀ {F : Obj → Obj} {A} {alg : Hom (F A) A} →
             (cata {F} alg ∘ In {F}) ≈ (alg ∘ fmap {F} (cata {F} alg))
