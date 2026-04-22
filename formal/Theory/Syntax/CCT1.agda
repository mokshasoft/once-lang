------------------------------------------------------------------------
-- Theory.Syntax.CCT1
--
-- Refactored POC: CCC = CCTB + exponentials.
-- Demonstrates that CCT1 needs NO β/η rule redeclaration — the CCTB
-- β/η rules come from CCTB.BaseRules (instantiated here with CCT1's
-- Term), and CCT1's new β/η (curry-β, curry-η) come from CCT1.BaseRules.
--
-- Only the congruence closure is re-stated (localized to
-- CongruenceClosure.agda; see the commentary there for why).
------------------------------------------------------------------------

module Theory.Syntax.CCT1 where

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
-- Terms
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
-- β/η rules — inherited from PARAMETERIZED modules defined at their
-- origin levels. No redeclaration.
------------------------------------------------------------------------

import Theory.Syntax.CCTB.BaseRules as CCTB-B
open CCTB-B.Rules Ty Unit _×_ Term id _∘_ terminal fst snd ⟨_,_⟩ public
  renaming (_⟶β_ to _⟶β-CCTB_)

import Theory.Syntax.CCT1.BaseRules as CCT1-B
open CCT1-B.Rules Ty Unit _×_ _⇒_ Term id _∘_ fst snd ⟨_,_⟩ curry apply public
  renaming (_⟶β_ to _⟶β-CCT1_)

------------------------------------------------------------------------
-- Union of all β/η rules at this level.
-- Structured so that Hindley-Rosen composition can later split back
-- into the CCTB component and the CCT1 component cleanly.
------------------------------------------------------------------------

data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
  from-CCTB : ∀ {A B} {f g : Term A B} → f ⟶β-CCTB g → f ⟶β g
  from-CCT1 : ∀ {A B} {f g : Term A B} → f ⟶β-CCT1 g → f ⟶β g

infix 4 _⟶β_

------------------------------------------------------------------------
-- Full reduction = CCT1 congruence closure of the unioned β-rules.
------------------------------------------------------------------------

open import Theory.Syntax.CongruenceClosure
open CCT1-Close Ty _×_ _⇒_ Term _∘_ ⟨_,_⟩ curry _⟶β_ public
  renaming (Closed to _⟶_)

infix 4 _⟶_

------------------------------------------------------------------------
-- Reflexive-transitive closure, normal form
------------------------------------------------------------------------

data _⟶*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶ u → u ⟶* v → t ⟶* v

infix 4 _⟶*_

IsNormalForm : ∀ {A B} → Term A B → Set
IsNormalForm {A} {B} t = ∀ {u : Term A B} → ¬ (t ⟶ u)

------------------------------------------------------------------------
-- Canonical structures
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
  ; _⟶_          = _⟶_
  ; _⟶*_         = _⟶*_
  ; IsNormalForm = IsNormalForm
  }

canonical : CCT1Structure
canonical = record
  { base  = canonical-base
  ; _⇒_   = _⇒_
  ; curry = curry
  ; apply = apply
  }
