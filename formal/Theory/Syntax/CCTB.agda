------------------------------------------------------------------------
-- Theory.Syntax.CCTB
--
-- Canonical Cartesian-Category syntax + reduction rules.
-- Refactored POC (Approach A, principled): β/η rules are defined
-- ONCE in Theory.Syntax.CCTB.BaseRules and instantiated here.
-- The congruence closure is provided by Theory.Syntax.CongruenceClosure
-- and applied here to the β-rules to produce the full _⟶_ relation.
------------------------------------------------------------------------

module Theory.Syntax.CCTB where

open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

data Ty : Set where
  Unit : Ty
  _×_  : Ty → Ty → Ty

infixr 7 _×_

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

infixr 9 _∘_
infix  4 ⟨_,_⟩

------------------------------------------------------------------------
-- β/η rules — inherited from the parameterized module.
-- Defined ONCE in CCTB/BaseRules; instantiated here.
------------------------------------------------------------------------

import Theory.Syntax.CCTB.BaseRules as B
open B.Rules Ty Unit _×_ Term id _∘_ terminal fst snd ⟨_,_⟩ public

------------------------------------------------------------------------
-- Full reduction = congruence closure of β-rules.
-- Closure defined ONCE in Theory.Syntax.CongruenceClosure; applied here.
------------------------------------------------------------------------

open import Theory.Syntax.CongruenceClosure
open CCTB-Close Ty _×_ Term _∘_ ⟨_,_⟩ _⟶β_ public
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
-- Canonical CCTB structure
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
  ; _⟶_          = _⟶_
  ; _⟶*_         = _⟶*_
  ; IsNormalForm = IsNormalForm
  }
