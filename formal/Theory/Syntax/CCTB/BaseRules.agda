------------------------------------------------------------------------
-- Theory.Syntax.CCTB.BaseRules
--
-- Parameterized β/η/id rules introduced at the CCTB level.
-- NO congruence rules — those live in Theory.Syntax.CongruenceClosure,
-- where they can be re-applied with the full set of subterm-carrying
-- constructors available at each level (a requirement for sound
-- propagation of reductions through arbitrary term contexts).
--
-- This module exists so that the CCTB β/η rules are written ONCE.
-- Any level with the required CCTB generators (id, ∘, fst, snd, ⟨_,_⟩,
-- terminal) instantiates this module to get the rules on its own
-- Term type.
------------------------------------------------------------------------

module Theory.Syntax.CCTB.BaseRules where

module Rules
  (Ty       : Set)
  (Unit     : Ty)
  (_×_      : Ty → Ty → Ty)
  (Term     : Ty → Ty → Set)
  (id       : ∀ {A}     → Term A A)
  (_∘_      : ∀ {A B C} → Term B C → Term A B → Term A C)
  (terminal : ∀ {A}     → Term A Unit)
  (fst      : ∀ {A B}   → Term (A × B) A)
  (snd      : ∀ {A B}   → Term (A × B) B)
  (⟨_,_⟩    : ∀ {A B C} → Term C A → Term C B → Term C (A × B))
  where

  data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
    fst-pair : ∀ {A B C} {f : Term C A} {g : Term C B} →
               (fst ∘ ⟨ f , g ⟩) ⟶β f
    snd-pair : ∀ {A B C} {f : Term C A} {g : Term C B} →
               (snd ∘ ⟨ f , g ⟩) ⟶β g
    eta-pair : ∀ {A B} → ⟨ fst {A} {B} , snd ⟩ ⟶β id
    id-left  : ∀ {A B} {f : Term A B} → (id ∘ f) ⟶β f
    id-right : ∀ {A B} {f : Term A B} → (f ∘ id) ⟶β f

  infix 4 _⟶β_
