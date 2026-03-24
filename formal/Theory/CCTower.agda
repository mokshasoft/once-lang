------------------------------------------------------------------------
-- Theory.CCTower
--
-- The Categorical Tower: Definition of the five levels
--
-- This module DEFINES what each level of the tower contains.
-- It does NOT postulate any properties - those are in Established/.
--
-- ┌─────────────────────────────────────────────────────────────┐
-- │  CCT4: + νF, Out, ana (final coalgebras / coinductive)      │
-- │    = Full BCCR                                              │
-- ├─────────────────────────────────────────────────────────────┤
-- │  CCT3: + μF, In, cata (initial algebras / inductive)        │
-- ├─────────────────────────────────────────────────────────────┤
-- │  CCT2: + initial, inl, inr, [_,_] (coproducts)              │
-- │    = BCC (Bicartesian Closed Category)                      │
-- ├─────────────────────────────────────────────────────────────┤
-- │  CCT1: + curry, apply (exponentials)                        │
-- │    = CCC (Cartesian Closed Category)                        │
-- ├─────────────────────────────────────────────────────────────┤
-- │  CCTB: terminal, fst, snd, ⟨_,_⟩, id, ∘                     │
-- │    = CC (Cartesian Category)                                │
-- └─────────────────────────────────────────────────────────────┘
--
-- Each level EXTENDS the previous with new structure.
------------------------------------------------------------------------

module Theory.CCTower where

------------------------------------------------------------------------
-- Tower Level Enumeration
------------------------------------------------------------------------

data TowerLevel : Set where
  CCTB : TowerLevel  -- Cartesian Category (base)
  CCT1 : TowerLevel  -- + Exponentials = CCC
  CCT2 : TowerLevel  -- + Coproducts = BCC
  CCT3 : TowerLevel  -- + Initial Algebras (μ-types)
  CCT4 : TowerLevel  -- + Final Coalgebras (ν-types) = BCCR

------------------------------------------------------------------------
-- Level Extension Relation
------------------------------------------------------------------------

data _extends_ : TowerLevel → TowerLevel → Set where
  cct1-extends-cctb : CCT1 extends CCTB
  cct2-extends-cct1 : CCT2 extends CCT1
  cct3-extends-cct2 : CCT3 extends CCT2
  cct4-extends-cct3 : CCT4 extends CCT3

-- Transitive closure: CCT4 extends everything below it
data _extends*_ : TowerLevel → TowerLevel → Set where
  ext-refl : ∀ {l} → l extends* l
  ext-step : ∀ {l m n} → l extends m → m extends* n → l extends* n

------------------------------------------------------------------------
-- CCTB: Cartesian Category (Base)
------------------------------------------------------------------------
--
-- Structure:
--   id       : A → A
--   _∘_      : (B → C) → (A → B) → (A → C)
--   terminal : A → Unit
--   fst      : A × B → A
--   snd      : A × B → B
--   ⟨_,_⟩    : (C → A) → (C → B) → (C → A × B)
--
-- Reduction rules:
--   id-left   : id ∘ f ⟶ f
--   id-right  : f ∘ id ⟶ f
--   fst-pair  : fst ∘ ⟨f,g⟩ ⟶ f
--   snd-pair  : snd ∘ ⟨f,g⟩ ⟶ g
--   η-pair    : ⟨fst,snd⟩ ⟶ id
--   terminal  : !f = !g (uniqueness)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- CCT1: + Exponentials = CCC (Cartesian Closed Category)
------------------------------------------------------------------------
--
-- Additional structure:
--   curry : (A × B → C) → (A → B ⇒ C)
--   apply : (A ⇒ B) × A → B
--
-- Additional reduction rules:
--   curry-β : apply ∘ ⟨curry f, g⟩ ⟶ f ∘ ⟨id, g⟩
--   curry-η : curry (apply ∘ ⟨f ∘ fst, snd⟩) ⟶ f
--
-- Established properties (see Established/):
--   - Confluence: Lambek & Scott (1986)
--   - Strong Normalization: Tait (1967)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- CCT2: + Coproducts = BCC (Bicartesian Closed Category)
------------------------------------------------------------------------
--
-- Additional structure:
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
--
-- Established properties:
--   - Confluence: extends CCT1 (coproducts orthogonal)
--   - Strong Normalization: extends CCT1
------------------------------------------------------------------------

------------------------------------------------------------------------
-- CCT3: + Initial Algebras (μ-types / inductive types)
------------------------------------------------------------------------
--
-- Additional structure:
--   μF   : Type (least fixed point of functor F)
--   In   : F(μF) → μF
--   Out  : μF → F(μF)
--   cata : (F A → A) → (μF → A)
--
-- Additional reduction rules:
--   cata-β : cata alg ∘ In ⟶ alg ∘ fmap (cata alg)
--   out-in : Out ∘ In ⟶ id (Lambek's Lemma)
--
-- Established properties (see Established/LambekLemma.agda):
--   - Lambek's Lemma: In is an isomorphism (Lambek 1968)
--   - cata uniqueness: universal property of initial algebras
--   - Strong Normalization: Mendler (1987), requires strict positivity
--   - Confluence: requires orthogonality argument
------------------------------------------------------------------------

------------------------------------------------------------------------
-- CCT4: + Final Coalgebras (ν-types / coinductive types) = Full BCCR
------------------------------------------------------------------------
--
-- Additional structure:
--   νF  : Type (greatest fixed point of functor F)
--   Out : νF → F(νF)
--   In  : F(νF) → νF
--   ana : (A → F A) → (A → νF)
--
-- Additional reduction rules:
--   ana-β  : Out ∘ ana coalg ⟶ fmap (ana coalg) ∘ coalg
--   in-out : In ∘ Out ⟶ id (dual to Lambek)
--
-- Established properties (see Established/CoalgebraTheorems.agda):
--   - ana uniqueness: universal property of final coalgebras (Rutten 2000)
--   - Coinduction principle: bisimulation implies equality
--   - Productivity: Abel (2012), requires guardedness
--   - Confluence: requires orthogonality argument
------------------------------------------------------------------------

------------------------------------------------------------------------
-- BCCR = CCT4
--
-- Bicartesian Closed Category with Recursion
-- The full categorical structure for Once.
------------------------------------------------------------------------

BCCR : TowerLevel
BCCR = CCT4
