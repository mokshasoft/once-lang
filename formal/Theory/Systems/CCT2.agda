------------------------------------------------------------------------
-- Theory.Systems.CCT2
--
-- Bicartesian Closed Category (BCC): CCT1 + coproducts, specified
-- purely equationally.
--
-- Additional generators:
--   initial : Void → A
--   inl     : A → A + B
--   inr     : B → A + B
--   [_,_]   : (A → C) → (B → C) → (A + B → C)
--
-- Additional laws (universal property of coproducts):
--   case-inl    : [ f , g ] ∘ inl  ≈ f
--   case-inr    : [ f , g ] ∘ inr  ≈ g
--   eta-case    : [ inl , inr ]    ≈ id
--   eta-case-gen: [ f ∘ inl , f ∘ inr ] ≈ f
--   case-dist   : h ∘ [ f , g ]    ≈ [ h ∘ f , h ∘ g ]
--   initial-unique: f ≈ g  when domain is Void
--
-- Directed rewriting and its properties (SN, LC, CR) belong at the
-- Syntax level.
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
    ---------------------------------------------------------------
    -- Initial object
    ---------------------------------------------------------------

    Void    : Obj
    initial : ∀ {A} → Hom Void A

    ---------------------------------------------------------------
    -- Binary coproducts
    ---------------------------------------------------------------

    _⊎_   : Obj → Obj → Obj
    inl   : ∀ {A B} → Hom A (A ⊎ B)
    inr   : ∀ {A B} → Hom B (A ⊎ B)
    [_,_] : ∀ {A B C} → Hom A C → Hom B C → Hom (A ⊎ B) C

    ---------------------------------------------------------------
    -- Case congruence
    ---------------------------------------------------------------

    [,]-cong : ∀ {A B C} {f f' : Hom A C} {g g' : Hom B C} →
               f ≈ f' → g ≈ g' → [ f , g ] ≈ [ f' , g' ]

    ---------------------------------------------------------------
    -- Initial universal property
    ---------------------------------------------------------------

    initial-unique : ∀ {A} {f g : Hom Void A} → f ≈ g

    ---------------------------------------------------------------
    -- Coproduct universal property (dual to products)
    ---------------------------------------------------------------

    case-inl : ∀ {A B C} {f : Hom A C} {g : Hom B C} →
               ([ f , g ] ∘ inl) ≈ f
    case-inr : ∀ {A B C} {f : Hom A C} {g : Hom B C} →
               ([ f , g ] ∘ inr) ≈ g
    eta-case : ∀ {A B} → [ inl {A} {B} , inr {A} {B} ] ≈ id
    eta-case-gen : ∀ {A B C} {f : Hom (A ⊎ B) C} →
                   [ f ∘ inl , f ∘ inr ] ≈ f
    case-dist : ∀ {A B C D} {h : Hom C D} {f : Hom A C} {g : Hom B C} →
                (h ∘ [ f , g ]) ≈ [ h ∘ f , h ∘ g ]
