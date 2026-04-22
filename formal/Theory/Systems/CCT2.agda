------------------------------------------------------------------------
-- Theory.Systems.CCT2
--
-- Bicartesian Closed Category (BCC): CCT1 + coproducts.
--
-- Additional generators:
--   initial : Void → A
--   inl     : A → A + B
--   inr     : B → A + B
--   [_,_]   : (A → C) → (B → C) → (A + B → C)
--
-- Additional reduction rules:
--   case-inl : [f,g] ∘ inl ⟶ f
--   case-inr : [f,g] ∘ inr ⟶ g
--   η-case   : [inl,inr] ⟶ id
--   initial  : !f = !g (uniqueness from Void)
------------------------------------------------------------------------

module Theory.Systems.CCT2 where

open import Theory.Systems.CCT1

------------------------------------------------------------------------
-- CCT2 Structure = CCT1 + coproducts
------------------------------------------------------------------------

record CCT2Structure : Set₁ where
  field
    ccc : CCT1Structure

  open CCT1Structure ccc public

  field
    -- Initial object
    Void    : Obj
    initial : ∀ {A} → Hom Void A

    -- Binary coproducts
    _⊎_   : Obj → Obj → Obj
    inl   : ∀ {A B} → Hom A (A ⊎ B)
    inr   : ∀ {A B} → Hom B (A ⊎ B)
    [_,_] : ∀ {A B C} → Hom A C → Hom B C → Hom (A ⊎ B) C
