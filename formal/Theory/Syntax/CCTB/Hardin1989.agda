------------------------------------------------------------------------
-- Theory.Syntax.CCTB.Hardin1989
--
-- Hardin 1989 strong CCL at the CCTB level: Curien combinators with
-- the full rule set that makes the rewrite system CCC-equationally
-- complete — 9 rules total:
--   β:          fst-pair, snd-pair, eta-pair, id-left, id-right
--   structural: assoc, pair-dist, eta-pair-gen, term-unique
--
-- Confluence is proven via Newman's lemma (SN + local confluence) in
-- the Hardin1989/{SN,LocalConfluence,ConfluenceFull} proof chain.
--
-- Sibling syntaxes at the CCTB level:
--   - Curien1985 : the original β-only CCL (5 rules), proven
--                  confluent via Takahashi's parallel-reduction method.
--
-- The rules are parameterized ONCE in Theory.Syntax.CCTB.BaseRules
-- and instantiated here.
--
-- This module also builds:
--   (a) the Systems.CCTB.CCTBStructure instance whose `_≈_` is the
--       reflexive-symmetric-transitive closure of the full reduction,
--       and whose law obligations are discharged by single reduction
--       steps;
--   (b) the Syntax.Reducible carrier that packages the directed
--       reduction, its reflexive-transitive closure, and the NF
--       predicate.
------------------------------------------------------------------------

module Theory.Syntax.CCTB.Hardin1989 where

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
-- Base rules — inherited from the parameterized module.
-- Defined ONCE in CCTB/BaseRules; instantiated here.
------------------------------------------------------------------------

import Theory.Syntax.CCTB.BaseRules as B
open B.Rules Ty Unit _×_ Term id _∘_ terminal fst snd ⟨_,_⟩ public

------------------------------------------------------------------------
-- Full CCTB reduction — β-rules ∪ structural rules.
-- This is Hardin1989's single reduction relation; confluence is
-- proven via Newman's lemma (SN + local confluence).
------------------------------------------------------------------------

data _⟶full-rules_ : ∀ {A B} → Term A B → Term A B → Set where
  β-step : ∀ {A B} {f g : Term A B} → f ⟶β g → f ⟶full-rules g
  s-step : ∀ {A B} {f g : Term A B} → f ⟶s g → f ⟶full-rules g

infix 4 _⟶full-rules_

open import Theory.Syntax.CongruenceClosure
module full-Closure =
  CCTB-Close Ty _×_ Term _∘_ ⟨_,_⟩ _⟶full-rules_

_⟶full_ : ∀ {A B} → Term A B → Term A B → Set
_⟶full_ = full-Closure.Closed

infix 4 _⟶full_

data _⟶full*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶full* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶full u → u ⟶full* v → t ⟶full* v

infix 4 _⟶full*_

IsFullNormalForm : ∀ {A B} → Term A B → Set
IsFullNormalForm {A} {B} t = ∀ {u : Term A B} → ¬ (t ⟶full u)

------------------------------------------------------------------------
-- Convertibility: the _≈_ that will discharge the CCTBStructure laws.
-- It is the reflexive-symmetric-transitive closure of _⟶full_.
------------------------------------------------------------------------

import Theory.Syntax.Convertibility as Conv-Mod
module Conv = Conv-Mod.Indexed Term _⟶full_
open Conv public
  using (_≈_)
  renaming ( ≈-refl to ≈-refl
           ; ≈-step to ≈-step
           ; ≈-back to ≈-back
           ; ≈-sym  to ≈-sym
           ; ≈-trans to ≈-trans
           ; step-to-≈ to ⟶-to-≈
           ; back-to-≈ to ⟵-to-≈
           )

infix 4 _≈_

------------------------------------------------------------------------
-- Congruence of _≈_ under the two subterm-carrying constructors.
-- Each one is proved by induction on the ≈ derivation, promoting each
-- reduction step via the corresponding congruence of _⟶full_.
------------------------------------------------------------------------

∘-≈-congˡ : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
            f ≈ f' → (f ∘ g) ≈ (f' ∘ g)
∘-≈-congˡ Conv.≈-refl        = Conv.≈-refl
∘-≈-congˡ (Conv.≈-step r e)  =
  Conv.≈-step (full-Closure.∘-congˡ r) (∘-≈-congˡ e)
∘-≈-congˡ (Conv.≈-back r e)  =
  Conv.≈-back (full-Closure.∘-congˡ r) (∘-≈-congˡ e)

∘-≈-congʳ : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
            g ≈ g' → (f ∘ g) ≈ (f ∘ g')
∘-≈-congʳ Conv.≈-refl        = Conv.≈-refl
∘-≈-congʳ (Conv.≈-step r e)  =
  Conv.≈-step (full-Closure.∘-congʳ r) (∘-≈-congʳ e)
∘-≈-congʳ (Conv.≈-back r e)  =
  Conv.≈-back (full-Closure.∘-congʳ r) (∘-≈-congʳ e)

∘-≈-cong : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ≈ f' → g ≈ g' → (f ∘ g) ≈ (f' ∘ g')
∘-≈-cong f≈ g≈ = ≈-trans (∘-≈-congˡ f≈) (∘-≈-congʳ g≈)

⟨,⟩-≈-congˡ : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
              f ≈ f' → ⟨ f , g ⟩ ≈ ⟨ f' , g ⟩
⟨,⟩-≈-congˡ Conv.≈-refl        = Conv.≈-refl
⟨,⟩-≈-congˡ (Conv.≈-step r e)  =
  Conv.≈-step (full-Closure.⟨,⟩-congˡ r) (⟨,⟩-≈-congˡ e)
⟨,⟩-≈-congˡ (Conv.≈-back r e)  =
  Conv.≈-back (full-Closure.⟨,⟩-congˡ r) (⟨,⟩-≈-congˡ e)

⟨,⟩-≈-congʳ : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
              g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f , g' ⟩
⟨,⟩-≈-congʳ Conv.≈-refl        = Conv.≈-refl
⟨,⟩-≈-congʳ (Conv.≈-step r e)  =
  Conv.≈-step (full-Closure.⟨,⟩-congʳ r) (⟨,⟩-≈-congʳ e)
⟨,⟩-≈-congʳ (Conv.≈-back r e)  =
  Conv.≈-back (full-Closure.⟨,⟩-congʳ r) (⟨,⟩-≈-congʳ e)

⟨,⟩-≈-cong : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
             f ≈ f' → g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f' , g' ⟩
⟨,⟩-≈-cong f≈ g≈ = ≈-trans (⟨,⟩-≈-congˡ f≈) (⟨,⟩-≈-congʳ g≈)

------------------------------------------------------------------------
-- Canonical CCTB structure.
--
-- Every CCTB law discharges by a single reduction step, so the proofs
-- are one-liners.
------------------------------------------------------------------------

open import Theory.Systems.CCTB using (CCTBStructure)

private
  -- Shorthand: lift a base rule (either β or s) into the full reduction
  -- and wrap it as an equivalence.
  β≈ : ∀ {A B} {f g : Term A B} → f ⟶β g → f ≈ g
  β≈ r = ⟶-to-≈ (full-Closure.base (β-step r))

  s≈ : ∀ {A B} {f g : Term A B} → f ⟶s g → f ≈ g
  s≈ r = ⟶-to-≈ (full-Closure.base (s-step r))

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
  ; ∘-cong       = ∘-≈-cong
  ; ⟨,⟩-cong     = ⟨,⟩-≈-cong
  ; id-left      = β≈ id-left
  ; id-right     = β≈ id-right
  ; assoc        = s≈ assoc
  ; term-unique  = s≈ term-unique
  ; fst-pair     = β≈ fst-pair
  ; snd-pair     = β≈ snd-pair
  ; eta-pair     = β≈ eta-pair
  ; eta-pair-gen = s≈ eta-pair-gen
  ; pair-dist    = s≈ pair-dist
  }

------------------------------------------------------------------------
-- Canonical Reducible carrier (directed reduction, for downstream
-- properties like SN, LC, CR, and for the Ranzow Fixpoint statement).
------------------------------------------------------------------------

open import Theory.Syntax.Reducible using (Reducible)

canonical-reducible : Reducible Ty Term
canonical-reducible = record
  { _⟶_          = _⟶full_
  ; _⟶*_         = _⟶full*_
  ; IsNormalForm = IsFullNormalForm
  }
