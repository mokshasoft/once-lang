------------------------------------------------------------------------
-- Theory.Systems.CCT1
--
-- Cartesian Closed Category (CCC): CCTB + exponentials, specified
-- purely equationally.
--
-- Additional generators:
--   curry : (A × B → C) → (A → B ⇒ C)
--   apply : (A ⇒ B) × A → B
--
-- Additional laws (CCC universal property of exponentials):
--   curry-β       : apply ∘ ⟨ curry f , g ⟩ ≈ f ∘ ⟨ id , g ⟩
--                   (evaluation / CCL β-form; categorical form
--                    `apply ∘ ⟨ curry f ∘ fst , snd ⟩ ≈ f` is the
--                    special case g = snd on extended context, and
--                    is derivable via curry-compose + pair-dist.)
--   curry-η       : curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ≈ f
--   curry-compose : curry f ∘ g ≈ curry (f ∘ ⟨ g ∘ fst , snd ⟩)
--   curry-apply   : curry apply ≈ id
--
-- Directed rewriting and its properties (SN, LC, CR) belong at the
-- Syntax level.
--
-- Internal language: simply-typed λ-calculus.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Theory.Systems.CCT1 where

open import Theory.Systems.CCTB

------------------------------------------------------------------------
-- CCT1 Structure = CCTB + exponentials
------------------------------------------------------------------------

record CCT1Structure : Set₁ where
  field
    base : CCTBStructure

  open CCTBStructure base public

  field
    ---------------------------------------------------------------
    -- Exponentials
    ---------------------------------------------------------------

    _⇒_   : Obj → Obj → Obj
    curry : ∀ {A B C} → Hom (A × B) C → Hom A (B ⇒ C)
    apply : ∀ {A B} → Hom ((A ⇒ B) × A) B

    ---------------------------------------------------------------
    -- Curry congruence
    ---------------------------------------------------------------

    curry-cong : ∀ {A B C} {f f' : Hom (A × B) C} →
                 f ≈ f' → curry f ≈ curry f'

    ---------------------------------------------------------------
    -- Exponential universal property
    ---------------------------------------------------------------

    curry-β : ∀ {A B C} {f : Hom (A × B) C} {g : Hom A B} →
              (apply ∘ ⟨ curry f , g ⟩) ≈ (f ∘ ⟨ id , g ⟩)

    curry-η : ∀ {A B C} {f : Hom A (B ⇒ C)} →
              curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ≈ f

    curry-compose : ∀ {A B C D} {f : Hom (B × C) D} {g : Hom A B} →
                    (curry f ∘ g) ≈ curry (f ∘ ⟨ g ∘ fst , snd ⟩)

    curry-apply : ∀ {A B} → curry (apply {A} {B}) ≈ id
