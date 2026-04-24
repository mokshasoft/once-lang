------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.CCT1
--
-- Hardin 1989 strong CCL at the CCT1 level: Curien combinators +
-- exponentials with the full rule set that makes the rewrite system
-- CCC-equationally complete. CCT1 adds 4 exponential rules:
--   β:  curry-β (substitution/evaluation form)
--   η:  curry-η, curry-apply, curry-compose
-- on top of Hardin1989's 9 CCTB rules.
--
-- Confluence is proven via Newman's lemma (SN via Tait + local
-- confluence) in the Hardin1989/{Tait,LocalConfluence,ConfluenceFull}
-- proof chain.
--
-- Sibling syntaxes at the CCT1 level:
--   - Curien1985 : the original β-only CCL at CCT1 (β rules + curry-β),
--                  proven confluent via Takahashi's parallel-reduction.
--
-- This module also builds:
--   (a) the Systems.CCT1.CCT1Structure instance whose `_≈_` is the
--       reflexive-symmetric-transitive closure of _⟶βη_, with every
--       law discharged by a single reduction step;
--   (b) the Syntax.Reducible carrier packaging directed reduction.
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCT1 where

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
-- β/η rules — inherited from PARAMETERIZED modules.
------------------------------------------------------------------------

import Theory.Syntax.StrongCCL.BaseRules.CCTB as CCTB-B
open CCTB-B.Rules Ty Unit _×_ Term id _∘_ terminal fst snd ⟨_,_⟩ public
  renaming (_⟶β_ to _⟶β-CCTB_)

import Theory.Syntax.StrongCCL.BaseRules.CCT1 as CCT1-B
open CCT1-B.Rules Ty Unit _×_ _⇒_ Term id _∘_ fst snd ⟨_,_⟩ curry apply public
  renaming (_⟶β_ to _⟶β-CCT1_; _⟶η_ to _⟶η-CCT1_)

------------------------------------------------------------------------
-- Union of β-rules at this level.
------------------------------------------------------------------------

data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
  from-CCTB : ∀ {A B} {f g : Term A B} → f ⟶β-CCTB g → f ⟶β g
  from-CCT1 : ∀ {A B} {f g : Term A B} → f ⟶β-CCT1 g → f ⟶β g

infix 4 _⟶β_

------------------------------------------------------------------------
-- Full β ∪ η ∪ structural reduction — Hardin1989's single reduction.
-- Confluence via Newman (SN via Tait + local confluence).
------------------------------------------------------------------------

data _⟶βη-rules_ : ∀ {A B} → Term A B → Term A B → Set where
  β-rule : ∀ {A B} {f g : Term A B} → f ⟶β g       → f ⟶βη-rules g
  η-rule : ∀ {A B} {f g : Term A B} → f ⟶η-CCT1 g  → f ⟶βη-rules g
  s-rule : ∀ {A B} {f g : Term A B} → f ⟶s g       → f ⟶βη-rules g

infix 4 _⟶βη-rules_

open import Theory.Syntax.CongruenceClosure
module βη-Closure =
  CCT1-Close Ty _×_ _⇒_ Term _∘_ ⟨_,_⟩ curry _⟶βη-rules_

_⟶βη_ : ∀ {A B} → Term A B → Term A B → Set
_⟶βη_ = βη-Closure.Closed

infix 4 _⟶βη_

data _⟶βη*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶βη* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶βη u → u ⟶βη* v → t ⟶βη* v

infix 4 _⟶βη*_

IsβηNormalForm : ∀ {A B} → Term A B → Set
IsβηNormalForm {A} {B} t = ∀ {u : Term A B} → ¬ (t ⟶βη u)

------------------------------------------------------------------------
-- Convertibility built on the full βη reduction.
------------------------------------------------------------------------

import Theory.Syntax.Convertibility as Conv-Mod
module Conv = Conv-Mod.Indexed Term _⟶βη_
open Conv public
  using (_≈_)
  renaming ( ≈-refl  to ≈-refl
           ; ≈-step  to ≈-step
           ; ≈-back  to ≈-back
           ; ≈-sym   to ≈-sym
           ; ≈-trans to ≈-trans
           ; step-to-≈ to ⟶-to-≈
           ; back-to-≈ to ⟵-to-≈
           )

infix 4 _≈_

------------------------------------------------------------------------
-- Congruences of _≈_.
------------------------------------------------------------------------

∘-≈-congˡ : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
            f ≈ f' → (f ∘ g) ≈ (f' ∘ g)
∘-≈-congˡ Conv.≈-refl        = Conv.≈-refl
∘-≈-congˡ (Conv.≈-step r e)  =
  Conv.≈-step (βη-Closure.∘-congˡ r) (∘-≈-congˡ e)
∘-≈-congˡ (Conv.≈-back r e)  =
  Conv.≈-back (βη-Closure.∘-congˡ r) (∘-≈-congˡ e)

∘-≈-congʳ : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
            g ≈ g' → (f ∘ g) ≈ (f ∘ g')
∘-≈-congʳ Conv.≈-refl        = Conv.≈-refl
∘-≈-congʳ (Conv.≈-step r e)  =
  Conv.≈-step (βη-Closure.∘-congʳ r) (∘-≈-congʳ e)
∘-≈-congʳ (Conv.≈-back r e)  =
  Conv.≈-back (βη-Closure.∘-congʳ r) (∘-≈-congʳ e)

∘-≈-cong : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ≈ f' → g ≈ g' → (f ∘ g) ≈ (f' ∘ g')
∘-≈-cong f≈ g≈ = ≈-trans (∘-≈-congˡ f≈) (∘-≈-congʳ g≈)

⟨,⟩-≈-congˡ : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
              f ≈ f' → ⟨ f , g ⟩ ≈ ⟨ f' , g ⟩
⟨,⟩-≈-congˡ Conv.≈-refl        = Conv.≈-refl
⟨,⟩-≈-congˡ (Conv.≈-step r e)  =
  Conv.≈-step (βη-Closure.⟨,⟩-congˡ r) (⟨,⟩-≈-congˡ e)
⟨,⟩-≈-congˡ (Conv.≈-back r e)  =
  Conv.≈-back (βη-Closure.⟨,⟩-congˡ r) (⟨,⟩-≈-congˡ e)

⟨,⟩-≈-congʳ : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
              g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f , g' ⟩
⟨,⟩-≈-congʳ Conv.≈-refl        = Conv.≈-refl
⟨,⟩-≈-congʳ (Conv.≈-step r e)  =
  Conv.≈-step (βη-Closure.⟨,⟩-congʳ r) (⟨,⟩-≈-congʳ e)
⟨,⟩-≈-congʳ (Conv.≈-back r e)  =
  Conv.≈-back (βη-Closure.⟨,⟩-congʳ r) (⟨,⟩-≈-congʳ e)

⟨,⟩-≈-cong : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
             f ≈ f' → g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f' , g' ⟩
⟨,⟩-≈-cong f≈ g≈ = ≈-trans (⟨,⟩-≈-congˡ f≈) (⟨,⟩-≈-congʳ g≈)

curry-≈-cong : ∀ {A B C} {f f' : Term (A × B) C} →
               f ≈ f' → curry f ≈ curry f'
curry-≈-cong Conv.≈-refl        = Conv.≈-refl
curry-≈-cong (Conv.≈-step r e)  =
  Conv.≈-step (βη-Closure.curry-cong r) (curry-≈-cong e)
curry-≈-cong (Conv.≈-back r e)  =
  Conv.≈-back (βη-Closure.curry-cong r) (curry-≈-cong e)

------------------------------------------------------------------------
-- Canonical structures.
------------------------------------------------------------------------

open import Theory.Systems.CCTB using (CCTBStructure)
open import Theory.Systems.CCT1 using (CCT1Structure)

private
  -- Lift a CCTB β-rule to an ≈-equivalence.
  cctb-β≈ : ∀ {A B} {f g : Term A B} → f ⟶β-CCTB g → f ≈ g
  cctb-β≈ r = ⟶-to-≈ (βη-Closure.base (β-rule (from-CCTB r)))

  -- Lift a CCTB structural rule to an ≈-equivalence.
  cctb-s≈ : ∀ {A B} {f g : Term A B} → f ⟶s g → f ≈ g
  cctb-s≈ r = ⟶-to-≈ (βη-Closure.base (s-rule r))

  -- Lift a CCT1 β-rule to an ≈-equivalence.
  cct1-β≈ : ∀ {A B} {f g : Term A B} → f ⟶β-CCT1 g → f ≈ g
  cct1-β≈ r = ⟶-to-≈ (βη-Closure.base (β-rule (from-CCT1 r)))

  -- Lift a CCT1 η-rule to an ≈-equivalence.
  cct1-η≈ : ∀ {A B} {f g : Term A B} → f ⟶η-CCT1 g → f ≈ g
  cct1-η≈ r = ⟶-to-≈ (βη-Closure.base (η-rule r))

-- The canonical record uses the FULL βη reduction.
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
  ; ∘-cong       = ∘-≈-cong
  ; ⟨,⟩-cong     = ⟨,⟩-≈-cong
  ; id-left      = cctb-β≈ id-left
  ; id-right     = cctb-β≈ id-right
  ; assoc        = cctb-s≈ assoc
  ; term-unique  = cctb-s≈ term-unique
  ; fst-pair     = cctb-β≈ fst-pair
  ; snd-pair     = cctb-β≈ snd-pair
  ; eta-pair     = cctb-β≈ eta-pair
  ; eta-pair-gen = cctb-s≈ eta-pair-gen
  ; pair-dist    = cctb-s≈ pair-dist
  }

canonical : CCT1Structure
canonical = record
  { base          = canonical-base
  ; _⇒_           = _⇒_
  ; curry         = curry
  ; apply         = apply
  ; curry-cong    = curry-≈-cong
  ; curry-β       = cct1-β≈ curry-β
  ; curry-η       = cct1-η≈ curry-η
  ; curry-compose = cct1-η≈ curry-compose
  ; curry-apply   = cct1-η≈ curry-apply
  }

------------------------------------------------------------------------
-- Canonical Reducible carrier.
------------------------------------------------------------------------

open import Theory.Syntax.Reducible using (Reducible)

canonical-reducible : Reducible Ty Term
canonical-reducible = record
  { _⟶_          = _⟶βη_
  ; _⟶*_         = _⟶βη*_
  ; IsNormalForm = IsβηNormalForm
  }
