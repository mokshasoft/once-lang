------------------------------------------------------------------------
-- Theory.Syntax.CCT4.Takahashi
--
-- Takahashi-parallel CCL at the CCT4 level: adds final coalgebras.
--
-- Extends CCT3/Takahashi with:
--   ana rules: νout-νin, νin-νout, ana-β
--
-- Adequacy: 25 laws total (CCTB 9 + CCT1 4 + CCT2 6 + CCT3 3 + CCT4 3).
-- Same NO_POSITIVITY_CHECK caveat as Hardin1989/CCT4 for μ and ν.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Syntax.CCT4.Takahashi where

open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

data Ty : Set where
  Unit : Ty
  _×_  : Ty → Ty → Ty
  _⇒_  : Ty → Ty → Ty
  Void : Ty
  _⊎_  : Ty → Ty → Ty
  μ    : (Ty → Ty) → Ty
  ν    : (Ty → Ty) → Ty

infixr 7 _×_
infixr 6 _⇒_
infixr 5 _⊎_

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
  initial  : ∀ {A}     → Term Void A
  inl      : ∀ {A B}   → Term A (A ⊎ B)
  inr      : ∀ {A B}   → Term B (A ⊎ B)
  [_,_]    : ∀ {A B C} → Term A C → Term B C → Term (A ⊎ B) C
  In       : ∀ {F : Ty → Ty} → Term (F (μ F)) (μ F)
  Out      : ∀ {F : Ty → Ty} → Term (μ F) (F (μ F))
  cata     : ∀ {F : Ty → Ty} {A} → Term (F A) A → Term (μ F) A
  fmap     : ∀ {F : Ty → Ty} {A B} → Term A B → Term (F A) (F B)
  νOut     : ∀ {F : Ty → Ty} → Term (ν F) (F (ν F))
  νIn      : ∀ {F : Ty → Ty} → Term (F (ν F)) (ν F)
  ana      : ∀ {F : Ty → Ty} {A} → Term A (F A) → Term A (ν F)

infixr 9 _∘_
infix  4 ⟨_,_⟩
infix  4 [_,_]

------------------------------------------------------------------------
-- Single-step reduction.
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

  case-inl    : ∀ {A B C} {f : Term A C} {g : Term B C} →
                ([ f , g ] ∘ inl) ⟶ f
  case-inr    : ∀ {A B C} {f : Term A C} {g : Term B C} →
                ([ f , g ] ∘ inr) ⟶ g
  eta-case    : ∀ {A B} → [ inl {A} {B} , inr {A} {B} ] ⟶ id
  case-dist   : ∀ {A B C D} {h : Term C D} {f : Term A C} {g : Term B C} →
                (h ∘ [ f , g ]) ⟶ [ h ∘ f , h ∘ g ]

  initial-unique : ∀ {A} {f : Term Void A} → f ⟶ initial

  curry-β     : ∀ {A B C} {f : Term (A × B) C} {g : Term A B} →
                (apply ∘ ⟨ curry f , g ⟩) ⟶ (f ∘ ⟨ id , g ⟩)
  curry-β-ext : ∀ {X A B C} {f : Term (A × B) C} {h : Term X A} {g : Term X B} →
                (apply ∘ ⟨ curry f ∘ h , g ⟩) ⟶ (f ∘ ⟨ h , g ⟩)
  curry-η     : ∀ {A B C} {f : Term A (B ⇒ C)} →
                curry (apply ∘ ⟨ f ∘ fst , snd ⟩) ⟶ f

  out-in      : ∀ {F : Ty → Ty} → (Out {F} ∘ In {F}) ⟶ id
  in-out      : ∀ {F : Ty → Ty} → (In  {F} ∘ Out {F}) ⟶ id
  cata-β      : ∀ {F : Ty → Ty} {A} {alg : Term (F A) A} →
                (cata {F} alg ∘ In {F}) ⟶ (alg ∘ fmap {F} (cata {F} alg))

  νin-νout    : ∀ {F : Ty → Ty} → (νIn  {F} ∘ νOut {F}) ⟶ id
  νout-νin    : ∀ {F : Ty → Ty} → (νOut {F} ∘ νIn  {F}) ⟶ id
  ana-β       : ∀ {F : Ty → Ty} {A} {coalg : Term A (F A)} →
                (νOut {F} ∘ ana {F} coalg) ⟶
                (fmap {F} (ana {F} coalg) ∘ coalg)

  ⟶-∘-l       : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
                f ⟶ f' → (f ∘ g) ⟶ (f' ∘ g)
  ⟶-∘-r       : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
                g ⟶ g' → (f ∘ g) ⟶ (f ∘ g')
  ⟶-pair-l    : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                f ⟶ f' → ⟨ f , g ⟩ ⟶ ⟨ f' , g ⟩
  ⟶-pair-r    : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                g ⟶ g' → ⟨ f , g ⟩ ⟶ ⟨ f , g' ⟩
  ⟶-case-l    : ∀ {A B C} {f f' : Term A C} {g : Term B C} →
                f ⟶ f' → [ f , g ] ⟶ [ f' , g ]
  ⟶-case-r    : ∀ {A B C} {f : Term A C} {g g' : Term B C} →
                g ⟶ g' → [ f , g ] ⟶ [ f , g' ]
  ⟶-curry     : ∀ {A B C} {f f' : Term (A × B) C} →
                f ⟶ f' → curry f ⟶ curry f'
  ⟶-cata      : ∀ {F : Ty → Ty} {A} {alg alg' : Term (F A) A} →
                alg ⟶ alg' → cata {F} alg ⟶ cata {F} alg'
  ⟶-ana       : ∀ {F : Ty → Ty} {A} {coalg coalg' : Term A (F A)} →
                coalg ⟶ coalg' → ana {F} coalg ⟶ ana {F} coalg'
  ⟶-fmap      : ∀ {F : Ty → Ty} {A B} {f f' : Term A B} →
                f ⟶ f' → fmap {F} f ⟶ fmap {F} f'

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

curry-≈-cong : ∀ {A B C} {f f' : Term (A × B) C} →
               f ≈ f' → curry f ≈ curry f'
curry-≈-cong Conv.≈-refl        = Conv.≈-refl
curry-≈-cong (Conv.≈-step r e)  = Conv.≈-step (⟶-curry r) (curry-≈-cong e)
curry-≈-cong (Conv.≈-back r e)  = Conv.≈-back (⟶-curry r) (curry-≈-cong e)

[,]-≈-congˡ : ∀ {A B C} {f f' : Term A C} {g : Term B C} →
              f ≈ f' → [ f , g ] ≈ [ f' , g ]
[,]-≈-congˡ Conv.≈-refl        = Conv.≈-refl
[,]-≈-congˡ (Conv.≈-step r e)  = Conv.≈-step (⟶-case-l r) ([,]-≈-congˡ e)
[,]-≈-congˡ (Conv.≈-back r e)  = Conv.≈-back (⟶-case-l r) ([,]-≈-congˡ e)

[,]-≈-congʳ : ∀ {A B C} {f : Term A C} {g g' : Term B C} →
              g ≈ g' → [ f , g ] ≈ [ f , g' ]
[,]-≈-congʳ Conv.≈-refl        = Conv.≈-refl
[,]-≈-congʳ (Conv.≈-step r e)  = Conv.≈-step (⟶-case-r r) ([,]-≈-congʳ e)
[,]-≈-congʳ (Conv.≈-back r e)  = Conv.≈-back (⟶-case-r r) ([,]-≈-congʳ e)

[,]-≈-cong : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
             f ≈ f' → g ≈ g' → [ f , g ] ≈ [ f' , g' ]
[,]-≈-cong f≈ g≈ = ≈-trans ([,]-≈-congˡ f≈) ([,]-≈-congʳ g≈)

cata-≈-cong : ∀ {F : Ty → Ty} {A} {alg alg' : Term (F A) A} →
              alg ≈ alg' → cata {F} alg ≈ cata {F} alg'
cata-≈-cong Conv.≈-refl        = Conv.≈-refl
cata-≈-cong (Conv.≈-step r e)  = Conv.≈-step (⟶-cata r) (cata-≈-cong e)
cata-≈-cong (Conv.≈-back r e)  = Conv.≈-back (⟶-cata r) (cata-≈-cong e)

ana-≈-cong : ∀ {F : Ty → Ty} {A} {coalg coalg' : Term A (F A)} →
             coalg ≈ coalg' → ana {F} coalg ≈ ana {F} coalg'
ana-≈-cong Conv.≈-refl        = Conv.≈-refl
ana-≈-cong (Conv.≈-step r e)  = Conv.≈-step (⟶-ana r) (ana-≈-cong e)
ana-≈-cong (Conv.≈-back r e)  = Conv.≈-back (⟶-ana r) (ana-≈-cong e)

------------------------------------------------------------------------
-- Derived laws.
------------------------------------------------------------------------

eta-pair-gen-≈ : ∀ {A B C} {h : Term C (A × B)} →
                 ⟨ fst ∘ h , snd ∘ h ⟩ ≈ h
eta-pair-gen-≈ {h = h} =
  ≈-trans (⟵-to-≈ pair-comp)
    (≈-trans (∘-≈-congˡ (⟶-to-≈ eta-pair))
             (⟶-to-≈ id-left))

eta-case-gen-≈ : ∀ {A B C} {f : Term (A ⊎ B) C} →
                 [ f ∘ inl , f ∘ inr ] ≈ f
eta-case-gen-≈ {f = f} =
  ≈-trans (⟵-to-≈ case-dist)
    (≈-trans (∘-≈-congʳ (⟶-to-≈ eta-case))
             (⟶-to-≈ id-right))

initial-unique-≈ : ∀ {A} {f g : Term Void A} → f ≈ g
initial-unique-≈ =
  ≈-trans (⟶-to-≈ initial-unique) (≈-sym (⟶-to-≈ initial-unique))

curry-apply-≈ : ∀ {A B} → curry (apply {A} {B}) ≈ id
curry-apply-≈ =
  ≈-trans (≈-sym (curry-≈-cong inner-eq)) (⟶-to-≈ curry-η)
  where
    inner-eq : (apply ∘ ⟨ id ∘ fst , snd ⟩) ≈ apply
    inner-eq =
      ≈-trans
        (∘-≈-congʳ (⟨,⟩-≈-congˡ (⟶-to-≈ id-left)))
        (≈-trans
          (∘-≈-congʳ (⟶-to-≈ eta-pair))
          (⟶-to-≈ id-right))

curry-compose-≈ : ∀ {A B C D} {f : Term (B × C) D} {g : Term A B} →
                  (curry f ∘ g) ≈ curry (f ∘ ⟨ g ∘ fst , snd ⟩)
curry-compose-≈ {f = f} {g = g} =
  ≈-trans (≈-sym (⟶-to-≈ curry-η)) (curry-≈-cong via-β-ext)
  where
    step1 : (apply ∘ ⟨ (curry f ∘ g) ∘ fst , snd ⟩)
          ≈ (apply ∘ ⟨ curry f ∘ (g ∘ fst) , snd ⟩)
    step1 = ∘-≈-congʳ (⟨,⟩-≈-congˡ (⟶-to-≈ assoc-r))
    step2 : (apply ∘ ⟨ curry f ∘ (g ∘ fst) , snd ⟩) ≈ (f ∘ ⟨ g ∘ fst , snd ⟩)
    step2 = ⟶-to-≈ curry-β-ext
    via-β-ext : (apply ∘ ⟨ (curry f ∘ g) ∘ fst , snd ⟩) ≈ (f ∘ ⟨ g ∘ fst , snd ⟩)
    via-β-ext = ≈-trans step1 step2

------------------------------------------------------------------------
-- Canonical structures.
------------------------------------------------------------------------

open import Theory.Systems.CCTB using (CCTBStructure)
open import Theory.Systems.CCT1 using (CCT1Structure)
open import Theory.Systems.CCT2 using (CCT2Structure)
open import Theory.Systems.CCT3 using (CCT3Structure)
open import Theory.Systems.CCT4 using (CCT4Structure)

canonical-base : CCTBStructure
canonical-base = record
  { Obj = Ty ; Hom = Term ; id = id ; _∘_ = _∘_
  ; Unit = Unit ; terminal = terminal
  ; _×_ = _×_ ; fst = fst ; snd = snd ; ⟨_,_⟩ = ⟨_,_⟩
  ; _≈_ = _≈_ ; ≈-refl = ≈-refl ; ≈-sym = ≈-sym ; ≈-trans = ≈-trans
  ; ∘-cong = ∘-≈-cong ; ⟨,⟩-cong = ⟨,⟩-≈-cong
  ; id-left = ⟶-to-≈ id-left ; id-right = ⟶-to-≈ id-right
  ; assoc = ⟶-to-≈ assoc-r ; term-unique = ⟶-to-≈ term-unique
  ; fst-pair = ⟶-to-≈ fst-pair ; snd-pair = ⟶-to-≈ snd-pair
  ; eta-pair = ⟶-to-≈ eta-pair ; eta-pair-gen = eta-pair-gen-≈
  ; pair-dist = ⟶-to-≈ pair-comp
  }

canonical-ccc : CCT1Structure
canonical-ccc = record
  { base = canonical-base ; _⇒_ = _⇒_
  ; curry = curry ; apply = apply ; curry-cong = curry-≈-cong
  ; curry-β = ⟶-to-≈ curry-β ; curry-η = ⟶-to-≈ curry-η
  ; curry-compose = curry-compose-≈ ; curry-apply = curry-apply-≈
  }

canonical-bcc : CCT2Structure
canonical-bcc = record
  { ccc = canonical-ccc
  ; Void = Void ; initial = initial
  ; _⊎_ = _⊎_ ; inl = inl ; inr = inr ; [_,_] = [_,_]
  ; [,]-cong = [,]-≈-cong ; initial-unique = initial-unique-≈
  ; case-inl = ⟶-to-≈ case-inl ; case-inr = ⟶-to-≈ case-inr
  ; eta-case = ⟶-to-≈ eta-case ; eta-case-gen = eta-case-gen-≈
  ; case-dist = ⟶-to-≈ case-dist
  }

canonical-bccμ : CCT3Structure
canonical-bccμ = record
  { bcc = canonical-bcc
  ; μ = μ ; In = In ; Out = Out ; cata = cata ; fmap = fmap
  ; cata-cong = cata-≈-cong
  ; out-in = ⟶-to-≈ out-in ; in-out = ⟶-to-≈ in-out
  ; cata-β = ⟶-to-≈ cata-β
  }

canonical : CCT4Structure
canonical = record
  { bccμ = canonical-bccμ
  ; ν = ν ; νOut = νOut ; νIn = νIn ; ana = ana
  ; ana-cong = ana-≈-cong
  ; νin-νout = ⟶-to-≈ νin-νout ; νout-νin = ⟶-to-≈ νout-νin
  ; ana-β = ⟶-to-≈ ana-β
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
