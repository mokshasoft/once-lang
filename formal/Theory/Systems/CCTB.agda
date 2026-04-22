------------------------------------------------------------------------
-- Theory.Systems.CCTB
--
-- The Cartesian Category (base of the CCTower).
--
-- This module defines what a CCTB STRUCTURE is. It contains NO postulates
-- and NO established theorems — only the definitions that Established/*
-- and RanzowFixpoint modules quantify over.
--
-- Generators:
--   id, _∘_, terminal, fst, snd, ⟨_,_⟩
--
-- Reduction rules (documentation only; the reduction relation is abstract):
--   id-left   : id ∘ f ⟶ f
--   id-right  : f ∘ id ⟶ f
--   fst-pair  : fst ∘ ⟨f,g⟩ ⟶ f
--   snd-pair  : snd ∘ ⟨f,g⟩ ⟶ g
--   η-pair    : ⟨fst,snd⟩ ⟶ id
--   terminal  : !f = !g (uniqueness from A → Unit)
------------------------------------------------------------------------

module Theory.Systems.CCTB where

------------------------------------------------------------------------
-- CCTB Structure
--
-- A CCTB is any structure satisfying this record. Concrete term calculi
-- instantiate this; abstract theorems quantify over it.
------------------------------------------------------------------------

record CCTBStructure : Set₁ where
  field
    -- Objects (types) and morphisms (terms)
    Obj : Set
    Hom : Obj → Obj → Set

    -- Category structure
    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    -- Terminal object
    Unit     : Obj
    terminal : ∀ {A} → Hom A Unit

    -- Binary products
    _×_   : Obj → Obj → Obj
    fst   : ∀ {A B} → Hom (A × B) A
    snd   : ∀ {A B} → Hom (A × B) B
    ⟨_,_⟩ : ∀ {A B C} → Hom C A → Hom C B → Hom C (A × B)

    -- Reduction relation
    _⟶_  : ∀ {A B} → Hom A B → Hom A B → Set
    _⟶*_ : ∀ {A B} → Hom A B → Hom A B → Set

    -- Normal form predicate (no reduction applies)
    IsNormalForm : ∀ {A B} → Hom A B → Set
