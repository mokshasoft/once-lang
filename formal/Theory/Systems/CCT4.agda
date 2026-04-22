------------------------------------------------------------------------
-- Theory.Systems.CCT4
--
-- Full BCCR: CCT3 + Final Coalgebras (ν-types / coinductive types).
--
-- Additional structure:
--   ν F      : Obj (greatest fixed point of F : Obj → Obj)
--   νOut     : νF → F(νF)
--   νIn      : F(νF) → νF
--   ana      : (A → F A) → (A → νF)
--
-- Additional reduction rules:
--   ana-β  : νOut ∘ ana coalg ⟶ fmap F (ana coalg) ∘ coalg
--   in-out : νIn ∘ νOut ⟶ id     (Rutten 2000, dual to Lambek)
--
-- BCCR = CCT4. This is the full categorical structure Once targets.
--
-- NOTE: Same functor caveat as CCT3. Productivity (Abel 2012) requires
-- guardedness, which is a predicate on coalgebras carried in the
-- corresponding Established module.
------------------------------------------------------------------------

module Theory.Systems.CCT4 where

open import Theory.Systems.CCT3

------------------------------------------------------------------------
-- CCT4 Structure = CCT3 + final coalgebras
------------------------------------------------------------------------

record CCT4Structure : Set₁ where
  field
    bccμ : CCT3Structure

  open CCT3Structure bccμ public

  field
    -- Final coalgebras (ν-types)
    ν    : (Obj → Obj) → Obj
    νOut : ∀ {F : Obj → Obj} → Hom (ν F) (F (ν F))
    νIn  : ∀ {F : Obj → Obj} → Hom (F (ν F)) (ν F)
    ana  : ∀ {F : Obj → Obj} {A} → Hom A (F A) → Hom A (ν F)
