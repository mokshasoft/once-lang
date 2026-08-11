------------------------------------------------------------------------
-- Theory.Systems.CCTB
--
-- The Cartesian Category (base of the CCTower), specified purely
-- equationally.
--
-- This module defines what a CCTB STRUCTURE is: the generators, a
-- congruence _≈_ on morphisms, and the universal-property equations
-- that any CCTB must satisfy. It is the algebraic signature alone, which
-- downstream modules (Syntax/*, Established/*, RanzowFixpoint/*)
-- quantify over.
--
-- Directed rewriting (_⟶_, _⟶*_, IsNormalForm) is NOT part of the
-- Systems level: it is an artifact of a particular *syntactic*
-- presentation and belongs in Theory.Syntax.*.
--
-- Generators:
--   id, _∘_, terminal, fst, snd, ⟨_,_⟩
--
-- Laws (the "nine CCTB equations" — every rule in the full CCTB
-- rewrite system appears here as an equation):
--   category:    id-left, id-right, assoc
--   terminal:    term-unique
--   products:    fst-pair, snd-pair, eta-pair,
--                pair-dist, eta-pair-gen
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Theory.Systems.CCTB where

------------------------------------------------------------------------
-- CCTB Structure
--
-- A CCTB is any structure satisfying this record. Concrete term
-- calculi instantiate it by:
--   (1) picking Obj / Hom / generators,
--   (2) defining _≈_ (typically as the symmetric-transitive closure
--       of their reduction relation, or equivalently as "joinable"),
--   (3) proving each equation below.
------------------------------------------------------------------------

record CCTBStructure : Set₁ where
  infixr 9 _∘_
  infix  4 _≈_
  field
    ---------------------------------------------------------------
    -- Category carrier
    ---------------------------------------------------------------

    Obj : Set
    Hom : Obj → Obj → Set

    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    ---------------------------------------------------------------
    -- Terminal object
    ---------------------------------------------------------------

    Unit     : Obj
    terminal : ∀ {A} → Hom A Unit

    ---------------------------------------------------------------
    -- Binary products
    ---------------------------------------------------------------

    _×_   : Obj → Obj → Obj
    fst   : ∀ {A B} → Hom (A × B) A
    snd   : ∀ {A B} → Hom (A × B) B
    ⟨_,_⟩ : ∀ {A B C} → Hom C A → Hom C B → Hom C (A × B)

    ---------------------------------------------------------------
    -- Equivalence on morphisms
    ---------------------------------------------------------------

    _≈_ : ∀ {A B} → Hom A B → Hom A B → Set

    ≈-refl  : ∀ {A B} {f : Hom A B} → f ≈ f
    ≈-sym   : ∀ {A B} {f g : Hom A B} → f ≈ g → g ≈ f
    ≈-trans : ∀ {A B} {f g h : Hom A B} → f ≈ g → g ≈ h → f ≈ h

    ---------------------------------------------------------------
    -- Congruences — _≈_ is compatible with the generators that
    -- have proper subterms. (id, terminal, fst, snd have no
    -- proper subterms and so need no congruence rule.)
    ---------------------------------------------------------------

    ∘-cong : ∀ {A B C} {f f' : Hom B C} {g g' : Hom A B} →
             f ≈ f' → g ≈ g' → (f ∘ g) ≈ (f' ∘ g')

    ⟨,⟩-cong : ∀ {A B C} {f f' : Hom C A} {g g' : Hom C B} →
               f ≈ f' → g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f' , g' ⟩

    ---------------------------------------------------------------
    -- Category laws
    ---------------------------------------------------------------

    id-left  : ∀ {A B} {f : Hom A B} → (id ∘ f) ≈ f
    id-right : ∀ {A B} {f : Hom A B} → (f ∘ id) ≈ f
    assoc    : ∀ {A B C D} {f : Hom C D} {g : Hom B C} {h : Hom A B} →
               ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))

    ---------------------------------------------------------------
    -- Terminal universal property
    ---------------------------------------------------------------

    term-unique : ∀ {A B} {f : Hom A B} →
                  (terminal ∘ f) ≈ terminal

    ---------------------------------------------------------------
    -- Product universal property
    --
    --   fst-pair / snd-pair : β-rules (projections reveal components)
    --   eta-pair            : η-rule (restricted: ⟨fst,snd⟩ = id)
    --   eta-pair-gen        : generalized η (surjective pairing)
    --   pair-dist           : ⟨_,_⟩ commutes with precomposition
    ---------------------------------------------------------------

    fst-pair : ∀ {A B C} {f : Hom C A} {g : Hom C B} →
               (fst ∘ ⟨ f , g ⟩) ≈ f
    snd-pair : ∀ {A B C} {f : Hom C A} {g : Hom C B} →
               (snd ∘ ⟨ f , g ⟩) ≈ g
    eta-pair : ∀ {A B} → ⟨ fst {A} {B} , snd {A} {B} ⟩ ≈ id
    eta-pair-gen : ∀ {A B C} {h : Hom C (A × B)} →
                   ⟨ fst ∘ h , snd ∘ h ⟩ ≈ h
    pair-dist : ∀ {A B C D} {f : Hom C A} {g : Hom C B} {h : Hom D C} →
                (⟨ f , g ⟩ ∘ h) ≈ ⟨ f ∘ h , g ∘ h ⟩
