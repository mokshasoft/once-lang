------------------------------------------------------------------------
-- Theory.Syntax.Bootstrap.CCTB
--
-- Takahashi-parallel CCL at the CCTB level: Curien combinators with
-- both-directions-of-assoc orientation, designed to be extendable by
-- Takahashi's parallel-reduction confluence proof.
--
-- Distinguishing features vs. Hardin1989:
--   - BOTH assoc directions as primitive rewrites (assoc-l, assoc-r).
--
-- RULES COVERED DIRECTLY:
--   id-left, id-right, assoc (= assoc-r), term-unique, fst-pair,
--   snd-pair, eta-pair, pair-dist (= pair-comp).
--
-- RULES DERIVED VIA CONVERTIBILITY:
--   eta-pair-gen: via pair-comp-reverse + eta-pair + id-left.
--
------------------------------------------------------------------------

module Theory.Syntax.Bootstrap.CCTB where

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
-- Single-step reduction (Takahashi orientation).
------------------------------------------------------------------------

data _⟶_ : ∀ {A B} → Term A B → Term A B → Set where
  id-left     : ∀ {A B} {f : Term A B} → (id ∘ f) ⟶ f
  id-right    : ∀ {A B} {f : Term A B} → (f ∘ id) ⟶ f
  assoc-l     : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
                (f ∘ (g ∘ h)) ⟶ ((f ∘ g) ∘ h)
  assoc-r     : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
                ((f ∘ g) ∘ h) ⟶ (f ∘ (g ∘ h))
  fst-pair    : ∀ {A B C} {f : Term C A} {g : Term C B} →
                (fst ∘ ⟨ f , g ⟩) ⟶ f
  snd-pair    : ∀ {A B C} {f : Term C A} {g : Term C B} →
                (snd ∘ ⟨ f , g ⟩) ⟶ g
  eta-pair    : ∀ {A B} → ⟨ fst {A} {B} , snd {A} {B} ⟩ ⟶ id
  pair-comp   : ∀ {A B C D} {f : Term C A} {g : Term C B} {h : Term D C} →
                (⟨ f , g ⟩ ∘ h) ⟶ ⟨ f ∘ h , g ∘ h ⟩
  term-unique : ∀ {A B} {f : Term A B} → (terminal ∘ f) ⟶ terminal

  ⟶-∘-l       : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                f ⟶ f' → (f ∘ g) ⟶ (f' ∘ g)
  ⟶-∘-r       : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                g ⟶ g' → (f ∘ g) ⟶ (f ∘ g')
  ⟶-pair-l    : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                f ⟶ f' → ⟨ f , g ⟩ ⟶ ⟨ f' , g ⟩
  ⟶-pair-r    : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                g ⟶ g' → ⟨ f , g ⟩ ⟶ ⟨ f , g' ⟩

infix 4 _⟶_

data _⟶*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶ u → u ⟶* v → t ⟶* v

infix 4 _⟶*_

IsNormalForm : ∀ {A B} → Term A B → Set
IsNormalForm {A} {B} t = ∀ {u : Term A B} → ¬ (t ⟶ u)

------------------------------------------------------------------------
-- Convertibility.
------------------------------------------------------------------------

import Theory.Syntax.Convertibility as Conv-Mod
module Conv = Conv-Mod.Indexed Term _⟶_
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
∘-≈-congˡ (Conv.≈-step r e)  = Conv.≈-step (⟶-∘-l r) (∘-≈-congˡ e)
∘-≈-congˡ (Conv.≈-back r e)  = Conv.≈-back (⟶-∘-l r) (∘-≈-congˡ e)

∘-≈-congʳ : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
            g ≈ g' → (f ∘ g) ≈ (f ∘ g')
∘-≈-congʳ Conv.≈-refl        = Conv.≈-refl
∘-≈-congʳ (Conv.≈-step r e)  = Conv.≈-step (⟶-∘-r r) (∘-≈-congʳ e)
∘-≈-congʳ (Conv.≈-back r e)  = Conv.≈-back (⟶-∘-r r) (∘-≈-congʳ e)

∘-≈-cong : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ≈ f' → g ≈ g' → (f ∘ g) ≈ (f' ∘ g')
∘-≈-cong f≈ g≈ = ≈-trans (∘-≈-congˡ f≈) (∘-≈-congʳ g≈)

⟨,⟩-≈-congˡ : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
              f ≈ f' → ⟨ f , g ⟩ ≈ ⟨ f' , g ⟩
⟨,⟩-≈-congˡ Conv.≈-refl        = Conv.≈-refl
⟨,⟩-≈-congˡ (Conv.≈-step r e)  = Conv.≈-step (⟶-pair-l r) (⟨,⟩-≈-congˡ e)
⟨,⟩-≈-congˡ (Conv.≈-back r e)  = Conv.≈-back (⟶-pair-l r) (⟨,⟩-≈-congˡ e)

⟨,⟩-≈-congʳ : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
              g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f , g' ⟩
⟨,⟩-≈-congʳ Conv.≈-refl        = Conv.≈-refl
⟨,⟩-≈-congʳ (Conv.≈-step r e)  = Conv.≈-step (⟶-pair-r r) (⟨,⟩-≈-congʳ e)
⟨,⟩-≈-congʳ (Conv.≈-back r e)  = Conv.≈-back (⟶-pair-r r) (⟨,⟩-≈-congʳ e)

⟨,⟩-≈-cong : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
             f ≈ f' → g ≈ g' → ⟨ f , g ⟩ ≈ ⟨ f' , g' ⟩
⟨,⟩-≈-cong f≈ g≈ = ≈-trans (⟨,⟩-≈-congˡ f≈) (⟨,⟩-≈-congʳ g≈)

------------------------------------------------------------------------
-- Derived: eta-pair-gen.
------------------------------------------------------------------------

eta-pair-gen-≈ : ∀ {A B C} {h : Term C (A × B)} →
                 ⟨ fst ∘ h , snd ∘ h ⟩ ≈ h
eta-pair-gen-≈ {h = h} =
  ≈-trans (⟵-to-≈ pair-comp)
    (≈-trans (∘-≈-congˡ (⟶-to-≈ eta-pair))
             (⟶-to-≈ id-left))

------------------------------------------------------------------------
-- Canonical structure.
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
  ; ∘-cong       = ∘-≈-cong
  ; ⟨,⟩-cong     = ⟨,⟩-≈-cong
  ; id-left      = ⟶-to-≈ id-left
  ; id-right     = ⟶-to-≈ id-right
  ; assoc        = ⟶-to-≈ assoc-r
  ; term-unique  = ⟶-to-≈ term-unique
  ; fst-pair     = ⟶-to-≈ fst-pair
  ; snd-pair     = ⟶-to-≈ snd-pair
  ; eta-pair     = ⟶-to-≈ eta-pair
  ; eta-pair-gen = eta-pair-gen-≈
  ; pair-dist    = ⟶-to-≈ pair-comp
  }

------------------------------------------------------------------------
-- Canonical Reducible carrier.
------------------------------------------------------------------------

open import Theory.Syntax.Reducible using (Reducible)

canonical-reducible : Reducible Ty Term
canonical-reducible = record
  { _⟶_          = _⟶_
  ; _⟶*_         = _⟶*_
  ; IsNormalForm = IsNormalForm
  }
