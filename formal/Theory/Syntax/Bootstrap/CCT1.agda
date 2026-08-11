------------------------------------------------------------------------
-- Theory.Syntax.Bootstrap.CCT1
--
-- Takahashi-parallel CCL at the CCT1 level: Curien combinators with
-- a rule orientation designed for Takahashi's parallel-reduction
-- confluence proof. Ported (and adapted for full Systems adequacy)
-- from the bootstrap/normalizer/Syntax/CCC.agda.
--
-- Distinguishing features vs. Hardin1989:
--
--   - BOTH directions of associativity as primitive rewrites:
--       assoc-l : f ∘ (g ∘ h) ⟶ (f ∘ g) ∘ h
--       assoc-r : (f ∘ g) ∘ h ⟶ f ∘ (g ∘ h)
--     This makes the reduction a preorder on composition, not a DAG,
--     but is convenient for the parallel-reduction proof.
--
--   - A generalized β-rule for exponentials:
--       curry-β-ext : apply ∘ ⟨curry f ∘ h, g⟩ ⟶ f ∘ ⟨h, g⟩
--     This subsumes both curry-β (take h = id) and curry-compose
--     (derivable from curry-β-ext + curry-η). No dedicated
--     curry-compose rule — which avoids the Hardin1989
--     curry-compose × curry-η critical-pair blocker.
--
--   - term-unique added to the base rule set (`terminal ∘ f ⟶ terminal`).
--     Bootstrap omits this, but it is required for CCTB adequacy.
--
-- LAWS COVERED AS REDUCTIONS:
--   id-left, id-right, assoc (via assoc-r), term-unique, fst-pair,
--   snd-pair, eta-pair, pair-dist (= pair-comp), curry-β, curry-η.
--
-- LAWS DERIVED VIA CONVERTIBILITY:
--   eta-pair-gen : pair-comp (reverse) + eta-pair + id-left
--   curry-apply  : curry-η (take f = id) + id-left + eta-pair
--   curry-compose: curry-β-ext + curry-η
--
-- RESULT: adequacy at CCTBStructure (9 laws) and CCT1Structure
-- (13 laws), each law derived from the generators above.
------------------------------------------------------------------------

module Theory.Syntax.Bootstrap.CCT1 where

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
-- Single-step reduction (Takahashi orientation).
-- All rules + congruences packed into one data type to match the
-- bootstrap presentation.
------------------------------------------------------------------------

data _⟶_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Category
  id-left     : ∀ {A B} {f : Term A B} → (id ∘ f) ⟶ f
  id-right    : ∀ {A B} {f : Term A B} → (f ∘ id) ⟶ f
  assoc-l     : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
                (f ∘ (g ∘ h)) ⟶ ((f ∘ g) ∘ h)
  assoc-r     : ∀ {A B C D} {f : Term C D} {g : Term B C} {h : Term A B} →
                ((f ∘ g) ∘ h) ⟶ (f ∘ (g ∘ h))

  -- Products
  fst-pair    : ∀ {A B C} {f : Term C A} {g : Term C B} →
                (fst ∘ ⟨ f , g ⟩) ⟶ f
  snd-pair    : ∀ {A B C} {f : Term C A} {g : Term C B} →
                (snd ∘ ⟨ f , g ⟩) ⟶ g
  eta-pair    : ∀ {A B} → ⟨ fst {A} {B} , snd {A} {B} ⟩ ⟶ id
  pair-comp   : ∀ {A B C D} {f : Term C A} {g : Term C B} {h : Term D C} →
                (⟨ f , g ⟩ ∘ h) ⟶ ⟨ f ∘ h , g ∘ h ⟩

  -- Terminal
  term-unique : ∀ {A B} {f : Term A B} → (terminal ∘ f) ⟶ terminal

  -- Exponentials
  curry-β     : ∀ {A B C} {f : Term (A × B) C} {g : Term A B} →
                (apply ∘ ⟨ curry f , g ⟩) ⟶ (f ∘ ⟨ id , g ⟩)
  curry-β-ext : ∀ {X A B C} {f : Term (A × B) C} {h : Term X A} {g : Term X B} →
                (apply ∘ ⟨ curry f ∘ h , g ⟩) ⟶ (f ∘ ⟨ h , g ⟩)
  curry-η     : ∀ {A B C} {f : Term A (B ⇒ C)} →
                curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟶ f

  -- Congruences
  ⟶-∘-l       : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                f ⟶ f' → (f ∘ g) ⟶ (f' ∘ g)
  ⟶-∘-r       : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                g ⟶ g' → (f ∘ g) ⟶ (f ∘ g')
  ⟶-pair-l    : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                f ⟶ f' → ⟨ f , g ⟩ ⟶ ⟨ f' , g ⟩
  ⟶-pair-r    : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                g ⟶ g' → ⟨ f , g ⟩ ⟶ ⟨ f , g' ⟩
  ⟶-curry     : ∀ {A B C} {f f' : Term (A × B) C} →
                f ⟶ f' → curry f ⟶ curry f'

infix 4 _⟶_

data _⟶*_ : ∀ {A B} → Term A B → Term A B → Set where
  done : ∀ {A B} {t : Term A B} → t ⟶* t
  _∷_  : ∀ {A B} {t u v : Term A B} → t ⟶ u → u ⟶* v → t ⟶* v

infix 4 _⟶*_

IsNormalForm : ∀ {A B} → Term A B → Set
IsNormalForm {A} {B} t = ∀ {u : Term A B} → ¬ (t ⟶ u)

------------------------------------------------------------------------
-- Convertibility: _≈_ = refl/sym/trans closure of _⟶_.
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
-- Congruences of _≈_ lifted from the _⟶_ congruence constructors.
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

curry-≈-cong : ∀ {A B C} {f f' : Term (A × B) C} →
               f ≈ f' → curry f ≈ curry f'
curry-≈-cong Conv.≈-refl        = Conv.≈-refl
curry-≈-cong (Conv.≈-step r e)  = Conv.≈-step (⟶-curry r) (curry-≈-cong e)
curry-≈-cong (Conv.≈-back r e)  = Conv.≈-back (⟶-curry r) (curry-≈-cong e)

------------------------------------------------------------------------
-- Laws that are DERIVED (not single-step rules in Takahashi).
------------------------------------------------------------------------

-- eta-pair-gen: ⟨fst ∘ h, snd ∘ h⟩ ≈ h
--   via pair-comp (reversed) + eta-pair under ∘-congˡ + id-left.
eta-pair-gen-≈ : ∀ {A B C} {h : Term C (A × B)} →
                 ⟨ fst ∘ h , snd ∘ h ⟩ ≈ h
eta-pair-gen-≈ {A} {B} {C} {h} =
  ≈-trans step1 (≈-trans step2 step3)
  where
    -- ⟨fst ∘ h, snd ∘ h⟩ ≈ ⟨fst, snd⟩ ∘ h  (reverse of pair-comp)
    step1 : ⟨ fst ∘ h , snd ∘ h ⟩ ≈ (⟨ fst , snd ⟩ ∘ h)
    step1 = ⟵-to-≈ pair-comp
    -- ⟨fst, snd⟩ ∘ h ≈ id ∘ h  (∘-congˡ of eta-pair)
    step2 : (⟨ fst , snd ⟩ ∘ h) ≈ (id ∘ h)
    step2 = ∘-≈-congˡ (⟶-to-≈ eta-pair)
    -- id ∘ h ≈ h  (id-left)
    step3 : (id ∘ h) ≈ h
    step3 = ⟶-to-≈ id-left

-- curry-apply: curry apply ≈ id
--   Strategy: curry-η with f = id says curry (apply ∘ ⟨id ∘ fst, snd⟩) ≈ id.
--   Since id ∘ fst ≈ fst (id-left), we have
--     ⟨id ∘ fst, snd⟩ ≈ ⟨fst, snd⟩ ≈ id (eta-pair).
--   So apply ∘ ⟨id ∘ fst, snd⟩ ≈ apply ∘ id ≈ apply (id-right).
--   Therefore curry (apply ∘ ⟨id ∘ fst, snd⟩) ≈ curry apply, so curry apply ≈ id.
curry-apply-≈ : ∀ {A B} → curry (apply {A} {B}) ≈ id
curry-apply-≈ {A} {B} =
  ≈-trans (≈-sym curry-simp) (⟶-to-≈ curry-η)
  where
    -- apply ∘ ⟨id ∘ fst, snd⟩ ≈ apply
    inner-eq : (apply {A} {B} ∘ ⟨ id ∘ fst , snd ⟩) ≈ apply
    inner-eq =
      ≈-trans
        (∘-≈-congʳ (⟨,⟩-≈-congˡ (⟶-to-≈ id-left)))  -- ⟨id ∘ fst, snd⟩ ≈ ⟨fst, snd⟩
        (≈-trans
          (∘-≈-congʳ (⟶-to-≈ eta-pair))             -- ⟨fst, snd⟩ ≈ id
          (⟶-to-≈ id-right))                        -- apply ∘ id ≈ apply
    curry-simp : curry (apply ∘ ⟨ id ∘ fst , snd ⟩) ≈ curry apply
    curry-simp = curry-≈-cong inner-eq

-- curry-compose: curry f ∘ g ≈ curry (f ∘ ⟨g ∘ fst, snd⟩)
--   Strategy: curry-η applied to curry f ∘ g gives
--     curry (apply ∘ ⟨(curry f ∘ g) ∘ fst, snd⟩) ≈ curry f ∘ g.
--   Inside the curry, we simplify:
--     (curry f ∘ g) ∘ fst ≈ curry f ∘ (g ∘ fst) via assoc-r.
--   Then apply ∘ ⟨curry f ∘ (g ∘ fst), snd⟩ ⟶ f ∘ ⟨g ∘ fst, snd⟩ via curry-β-ext.
curry-compose-≈ : ∀ {A B C D} {f : Term (B × C) D} {g : Term A B} →
                  (curry f ∘ g) ≈ curry (f ∘ ⟨ g ∘ fst , snd ⟩)
curry-compose-≈ {A} {B} {C} {D} {f} {g} =
  ≈-trans (≈-sym lhs-via-η) (curry-≈-cong via-β-ext)
  where
    -- By curry-η, curry f ∘ g ≈ curry (apply ∘ ⟨(curry f ∘ g) ∘ fst, snd⟩)
    lhs-via-η : curry (apply ∘ ⟨ (curry f ∘ g) ∘ fst , snd ⟩) ≈ (curry f ∘ g)
    lhs-via-η = ⟶-to-≈ curry-η

    -- (curry f ∘ g) ∘ fst ≈ curry f ∘ (g ∘ fst) via assoc-r
    reassoc : ((curry f ∘ g) ∘ fst) ≈ (curry f ∘ (g ∘ fst))
    reassoc = ⟶-to-≈ assoc-r

    -- apply ∘ ⟨(curry f ∘ g) ∘ fst, snd⟩ ≈ apply ∘ ⟨curry f ∘ (g ∘ fst), snd⟩
    step1 : (apply ∘ ⟨ (curry f ∘ g) ∘ fst , snd ⟩)
          ≈ (apply ∘ ⟨ curry f ∘ (g ∘ fst) , snd ⟩)
    step1 = ∘-≈-congʳ (⟨,⟩-≈-congˡ reassoc)

    -- apply ∘ ⟨curry f ∘ (g ∘ fst), snd⟩ ⟶ f ∘ ⟨g ∘ fst, snd⟩ by curry-β-ext
    step2 : (apply ∘ ⟨ curry f ∘ (g ∘ fst) , snd ⟩) ≈ (f ∘ ⟨ g ∘ fst , snd ⟩)
    step2 = ⟶-to-≈ curry-β-ext

    via-β-ext : (apply ∘ ⟨ (curry f ∘ g) ∘ fst , snd ⟩) ≈ (f ∘ ⟨ g ∘ fst , snd ⟩)
    via-β-ext = ≈-trans step1 step2

------------------------------------------------------------------------
-- Canonical structures.
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

canonical : CCT1Structure
canonical = record
  { base          = canonical-base
  ; _⇒_           = _⇒_
  ; curry         = curry
  ; apply         = apply
  ; curry-cong    = curry-≈-cong
  ; curry-β       = ⟶-to-≈ curry-β
  ; curry-η       = ⟶-to-≈ curry-η
  ; curry-compose = curry-compose-≈
  ; curry-apply   = curry-apply-≈
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
