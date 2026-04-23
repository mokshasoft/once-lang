------------------------------------------------------------------------
-- Theory.Syntax.CCTB.Curien1985
--
-- Curien 1985 CCL at the CCTB level: Curien combinators with the
-- ORIGINAL β-only rule set (5 rules total):
--   β:  fst-pair, snd-pair, eta-pair, id-left, id-right
--
-- Confluence is proven by Takahashi's parallel-reduction + diamond
-- method in the Curien1985/{ParallelReduction, Diamond, Triangle,
-- Confluence} proof chain.
--
-- The β-only rewrite system is computationally Church-Rosser but is
-- NOT CCC-equationally complete — the structural laws of a CCC
-- (assoc, pair-dist, eta-pair-gen, term-unique) are not derivable
-- from β-reduction alone. To instantiate the Systems.CCTBStructure
-- anyway, this module defines _≈_ as an inductive relation bundling:
--
--   - β-convertibility (via ⟶, which itself includes congruence
--     closure), and
--   - the four CCTB structural axioms as postulate-style constructors.
--
-- This matches the free CCC equational theory on Curien combinators
-- — the same equational theory discharged by Hardin1989, just with
-- the computational core restricted to β-reduction.
--
-- Sibling at CCTB: Theory.Syntax.CCTB.Hardin1989 (β + η + structural).
------------------------------------------------------------------------

module Theory.Syntax.CCTB.Curien1985 where

open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

data Ty : Set where
  Unit : Ty
  _×_  : Ty → Ty → Ty

infixr 7 _×_

------------------------------------------------------------------------
-- Terms (Curien combinators)
------------------------------------------------------------------------

data Term : Ty → Ty → Set where
  id       : ∀ {A}     → Term A A
  _∘_      : ∀ {A B C} → Term B C → Term A B → Term A C
  terminal : ∀ {A}     → Term A Unit
  fst      : ∀ {A B}   → Term (A × B) A
  snd      : ∀ {A B}   → Term (A × B) B
  ⟨_,_⟩    : ∀ {A B C} → Term C A → Term C B → Term C (A × B)

infixr 9 _∘_
infix  4 ⟨_,_⟩

------------------------------------------------------------------------
-- Base rules — the 5 β-rules inherited from CCTB.BaseRules.
-- No structural rules in Curien1985.
------------------------------------------------------------------------

import Theory.Syntax.CCTB.BaseRules as B
open B.Rules Ty Unit _×_ Term id _∘_ terminal fst snd ⟨_,_⟩ public
  using (_⟶β_; fst-pair; snd-pair; eta-pair; id-left; id-right)

------------------------------------------------------------------------
-- β-only reduction = congruence closure of β-rules.
-- This is Curien1985's primary reduction relation — the subject of
-- Takahashi's diamond-property confluence proof.
------------------------------------------------------------------------

open import Theory.Syntax.CongruenceClosure
open CCTB-Close Ty _×_ Term _∘_ ⟨_,_⟩ _⟶β_ public
  renaming (Closed to _⟶_)

infix 4 _⟶_

data _⟶*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶ u → u ⟶* v → t ⟶* v

infix 4 _⟶*_

IsNormalForm : ∀ {A B} → Term A B → Set
IsNormalForm {A} {B} t = ∀ {u : Term A B} → ¬ (t ⟶ u)

------------------------------------------------------------------------
-- Equational theory _≈_ : β-convertibility + structural CCC axioms.
--
-- β-reduction alone does not prove assoc, pair-dist, eta-pair-gen,
-- or term-unique — they are independent CCC laws. We include them as
-- axiomatic constructors so that _≈_ models the full CCC equational
-- theory while _⟶_ remains the pure β-rewrite system.
------------------------------------------------------------------------

data _≈_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Equivalence structure
  ≈-refl   : ∀ {A B} {x : Term A B}     → x ≈ x
  ≈-sym    : ∀ {A B} {x y : Term A B}   → x ≈ y → y ≈ x
  ≈-trans  : ∀ {A B} {x y z : Term A B} → x ≈ y → y ≈ z → x ≈ z

  -- β-reduction lifted to equivalence (single step, either direction)
  ≈-step   : ∀ {A B} {x y : Term A B} → x ⟶ y → x ≈ y

  -- Structural CCC axioms (not derivable from β-reduction)
  ≈-assoc        : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
                   ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))
  ≈-pair-dist    : ∀ {A B C D} {f : Term C A} {g : Term C B} {h : Term D C} →
                   (⟨ f , g ⟩ ∘ h) ≈ ⟨ f ∘ h , g ∘ h ⟩
  ≈-eta-pair-gen : ∀ {A B C} {h : Term C (A × B)} →
                   ⟨ fst ∘ h , snd ∘ h ⟩ ≈ h
  ≈-term-unique  : ∀ {A B} {f : Term A B} →
                   (terminal ∘ f) ≈ terminal

  -- Congruences (so we can rewrite under subterms)
  ≈-∘-congˡ   : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                f ≈ f' → (f ∘ g) ≈ (f' ∘ g)
  ≈-∘-congʳ   : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                g ≈ g' → (f ∘ g) ≈ (f ∘ g')
  ≈-⟨,⟩-congˡ : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                f ≈ f' → ⟨ f , g ⟩ ≈ ⟨ f' , g ⟩
  ≈-⟨,⟩-congʳ : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f , g' ⟩

infix 4 _≈_

-- Bundled congruence (both sides at once)
≈-∘-cong : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ≈ f' → g ≈ g' → (f ∘ g) ≈ (f' ∘ g')
≈-∘-cong f≈ g≈ = ≈-trans (≈-∘-congˡ f≈) (≈-∘-congʳ g≈)

≈-⟨,⟩-cong : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
             f ≈ f' → g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f' , g' ⟩
≈-⟨,⟩-cong f≈ g≈ = ≈-trans (≈-⟨,⟩-congˡ f≈) (≈-⟨,⟩-congʳ g≈)

------------------------------------------------------------------------
-- Canonical CCTB structure.
--
-- β-rules are discharged by single reduction steps lifted via ≈-step.
-- Structural laws are discharged by the corresponding _≈_ axioms.
------------------------------------------------------------------------

open import Theory.Systems.CCTB using (CCTBStructure)

canonical : CCTBStructure
canonical = record
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
  ; id-left      = ≈-step (base id-left)
  ; id-right     = ≈-step (base id-right)
  ; assoc        = ≈-assoc
  ; term-unique  = ≈-term-unique
  ; fst-pair     = ≈-step (base fst-pair)
  ; snd-pair     = ≈-step (base snd-pair)
  ; eta-pair     = ≈-step (base eta-pair)
  ; eta-pair-gen = ≈-eta-pair-gen
  ; pair-dist    = ≈-pair-dist
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
