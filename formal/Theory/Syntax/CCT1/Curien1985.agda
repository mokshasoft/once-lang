------------------------------------------------------------------------
-- Theory.Syntax.CCT1.Curien1985
--
-- Curien 1985 CCL at the CCT1 level: Curien combinators with the
-- ORIGINAL β-only rule set (6 rules total):
--   CCTB β:  fst-pair, snd-pair, eta-pair, id-left, id-right
--   CCT1 β:  curry-β
--
-- Confluence is proven by Takahashi's parallel-reduction + diamond
-- method in the Curien1985/{ParallelReduction, Diamond, Triangle,
-- Confluence} proof chain.
--
-- The β-only rewrite system is computationally Church-Rosser but not
-- CCC-equationally complete — the structural laws of a CCC (assoc,
-- pair-dist, eta-pair-gen, term-unique) and the η-laws of curry
-- (curry-η, curry-apply, curry-compose) are not derivable from
-- β-reduction alone. To instantiate Systems.CCT1Structure, this
-- module defines _≈_ as an inductive relation bundling:
--
--   - β-convertibility (via ⟶, which includes congruence closure),
--   - the four CCTB structural axioms,
--   - the three CCT1 η axioms.
--
-- This matches the free CCC equational theory — the same one
-- discharged by Hardin1989, just with the computational core
-- restricted to β-reduction.
--
-- Sibling at CCT1: Theory.Syntax.CCT1.Hardin1989 (β + η + structural).
------------------------------------------------------------------------

module Theory.Syntax.CCT1.Curien1985 where

open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

data Ty : Set where
  Unit : Ty
  _×_  : Ty → Ty → Ty
  _⇒_  : Ty → Ty → Ty

infixr 7 _×_
infixr 6 _⇒_

------------------------------------------------------------------------
-- Terms (Curien combinators + exponentials)
------------------------------------------------------------------------

data Term : Ty → Ty → Set where
  id       : ∀ {A}     → Term A A
  _∘_      : ∀ {A B C} → Term B C → Term A B → Term A C
  terminal : ∀ {A}     → Term A Unit
  fst      : ∀ {A B}   → Term (A × B) A
  snd      : ∀ {A B}   → Term (A × B) B
  ⟨_,_⟩    : ∀ {A B C} → Term C A → Term C B → Term C (A × B)
  curry    : ∀ {A B C} → Term (A × B) C → Term A (B ⇒ C)
  apply    : ∀ {A B}   → Term ((A ⇒ B) × A) B

infixr 9 _∘_
infix  4 ⟨_,_⟩

------------------------------------------------------------------------
-- β rules — inherited from the parameterized modules.
-- No η rules, no structural rules in Curien1985.
------------------------------------------------------------------------

import Theory.Syntax.CCTB.BaseRules as CCTB-B
open CCTB-B.Rules Ty Unit _×_ Term id _∘_ terminal fst snd ⟨_,_⟩ public
  using (fst-pair; snd-pair; eta-pair; id-left; id-right)
  renaming (_⟶β_ to _⟶β-CCTB_)

import Theory.Syntax.CCT1.BaseRules as CCT1-B
open CCT1-B.Rules Ty Unit _×_ _⇒_ Term id _∘_ fst snd ⟨_,_⟩ curry apply public
  using (curry-β)
  renaming (_⟶β_ to _⟶β-CCT1_)

------------------------------------------------------------------------
-- Union of β-rules at this level.
------------------------------------------------------------------------

data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
  from-CCTB : ∀ {A B} {f g : Term A B} → f ⟶β-CCTB g → f ⟶β g
  from-CCT1 : ∀ {A B} {f g : Term A B} → f ⟶β-CCT1 g → f ⟶β g

infix 4 _⟶β_

------------------------------------------------------------------------
-- β-only reduction = CCT1 congruence closure of the β-rule union.
-- Primary reduction relation — the subject of Takahashi's confluence.
------------------------------------------------------------------------

open import Theory.Syntax.CongruenceClosure
open CCT1-Close Ty _×_ _⇒_ Term _∘_ ⟨_,_⟩ curry _⟶β_ public
  renaming (Closed to _⟶_)

infix 4 _⟶_

data _⟶*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶ u → u ⟶* v → t ⟶* v

infix 4 _⟶*_

IsNormalForm : ∀ {A B} → Term A B → Set
IsNormalForm {A} {B} t = ∀ {u : Term A B} → ¬ (t ⟶ u)

------------------------------------------------------------------------
-- Equational theory _≈_ : β-convertibility + structural CCC axioms +
-- curry η-axioms.
------------------------------------------------------------------------

data _≈_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Equivalence structure
  ≈-refl   : ∀ {A B} {x : Term A B}     → x ≈ x
  ≈-sym    : ∀ {A B} {x y : Term A B}   → x ≈ y → y ≈ x
  ≈-trans  : ∀ {A B} {x y z : Term A B} → x ≈ y → y ≈ z → x ≈ z

  -- β-reduction lifted to equivalence
  ≈-step   : ∀ {A B} {x y : Term A B} → x ⟶ y → x ≈ y

  -- CCTB structural axioms
  ≈-assoc        : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
                   ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))
  ≈-pair-dist    : ∀ {A B C D} {f : Term C A} {g : Term C B} {h : Term D C} →
                   (⟨ f , g ⟩ ∘ h) ≈ ⟨ f ∘ h , g ∘ h ⟩
  ≈-eta-pair-gen : ∀ {A B C} {h : Term C (A × B)} →
                   ⟨ fst ∘ h , snd ∘ h ⟩ ≈ h
  ≈-term-unique  : ∀ {A B} {f : Term A B} →
                   (terminal ∘ f) ≈ terminal

  -- CCT1 η axioms
  ≈-curry-η       : ∀ {A B C} {f : Term A (B ⇒ C)} →
                    curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ≈ f
  ≈-curry-apply   : ∀ {A B} → curry (apply {A} {B}) ≈ id
  ≈-curry-compose : ∀ {A B C D} {f : Term (B × C) D} {g : Term A B} →
                    (curry f ∘ g) ≈ curry (f ∘ ⟨ g ∘ fst , snd ⟩)

  -- Congruences
  ≈-∘-congˡ   : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                f ≈ f' → (f ∘ g) ≈ (f' ∘ g)
  ≈-∘-congʳ   : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                g ≈ g' → (f ∘ g) ≈ (f ∘ g')
  ≈-⟨,⟩-congˡ : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                f ≈ f' → ⟨ f , g ⟩ ≈ ⟨ f' , g ⟩
  ≈-⟨,⟩-congʳ : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f , g' ⟩
  ≈-curry-cong : ∀ {A B C} {f f' : Term (A × B) C} →
                 f ≈ f' → curry f ≈ curry f'

infix 4 _≈_

-- Bundled congruences
≈-∘-cong : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ≈ f' → g ≈ g' → (f ∘ g) ≈ (f' ∘ g')
≈-∘-cong f≈ g≈ = ≈-trans (≈-∘-congˡ f≈) (≈-∘-congʳ g≈)

≈-⟨,⟩-cong : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
             f ≈ f' → g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f' , g' ⟩
≈-⟨,⟩-cong f≈ g≈ = ≈-trans (≈-⟨,⟩-congˡ f≈) (≈-⟨,⟩-congʳ g≈)

------------------------------------------------------------------------
-- Canonical CCT1 structure.
--
-- CCTB laws: β-rules via ≈-step, structural via _≈_ axioms.
-- CCT1 laws: curry-β via ≈-step, η-laws via _≈_ axioms.
------------------------------------------------------------------------

open import Theory.Systems.CCTB using (CCTBStructure)
open import Theory.Systems.CCT1 using (CCT1Structure)

canonical-base : CCTBStructure
canonical-base = record
  { Obj          = Ty
  ; Hom          = Term
  ; id           = id
  ; _∘_          = _∘_
  ; Unit         = Unit
  ; terminal     = terminal
  ; _×_          = _×_
  ; fst          = fst
  ; snd          = snd
  ; ⟨_,_⟩        = ⟨_,_⟩
  ; _≈_          = _≈_
  ; ≈-refl       = ≈-refl
  ; ≈-sym        = ≈-sym
  ; ≈-trans      = ≈-trans
  ; ∘-cong       = ≈-∘-cong
  ; ⟨,⟩-cong     = ≈-⟨,⟩-cong
  ; id-left      = ≈-step (base (from-CCTB id-left))
  ; id-right     = ≈-step (base (from-CCTB id-right))
  ; assoc        = ≈-assoc
  ; term-unique  = ≈-term-unique
  ; fst-pair     = ≈-step (base (from-CCTB fst-pair))
  ; snd-pair     = ≈-step (base (from-CCTB snd-pair))
  ; eta-pair     = ≈-step (base (from-CCTB eta-pair))
  ; eta-pair-gen = ≈-eta-pair-gen
  ; pair-dist    = ≈-pair-dist
  }

canonical : CCT1Structure
canonical = record
  { base          = canonical-base
  ; _⇒_           = _⇒_
  ; curry         = curry
  ; apply         = apply
  ; curry-cong    = ≈-curry-cong
  ; curry-β       = ≈-step (base (from-CCT1 curry-β))
  ; curry-η       = ≈-curry-η
  ; curry-compose = ≈-curry-compose
  ; curry-apply   = ≈-curry-apply
  }

------------------------------------------------------------------------
-- Canonical Reducible carrier (β-only directed reduction).
------------------------------------------------------------------------

open import Theory.Syntax.Reducible using (Reducible)

canonical-reducible : Reducible Ty Term
canonical-reducible = record
  { _⟶_          = _⟶_
  ; _⟶*_         = _⟶*_
  ; IsNormalForm = IsNormalForm
  }
