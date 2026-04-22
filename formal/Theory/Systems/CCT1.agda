------------------------------------------------------------------------
-- Theory.Systems.CCT1
--
-- Cartesian Closed Category (CCC): CCTB + exponentials.
--
-- Additional generators:
--   curry : (A × B → C) → (A → B ⇒ C)
--   apply : (A ⇒ B) × A → B
--
-- Additional reduction rules:
--   curry-β : apply ∘ ⟨curry f, g⟩ ⟶ f ∘ ⟨id, g⟩
--   curry-η : curry (apply ∘ ⟨f ∘ fst, snd⟩) ⟶ f
--
-- Internal language: simply-typed λ-calculus.
------------------------------------------------------------------------

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
    -- Exponentials
    _⇒_   : Obj → Obj → Obj
    curry : ∀ {A B C} → Hom (A × B) C → Hom A (B ⇒ C)
    apply : ∀ {A B} → Hom ((A ⇒ B) × A) B
