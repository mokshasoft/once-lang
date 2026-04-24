------------------------------------------------------------------------
-- Theory.Syntax.CCT4.Hardin1989
--
-- Hardin 1989 strong CCL at the CCT4 level: full BCCR. Adds final
-- coalgebras (ν-types) to the CCT3 structure.
--
-- CCT4 adds 3 rules on top of the 22 CCT3 rules:
--   νin-νout : νIn ∘ νOut ⟶ id
--   νout-νin : νOut ∘ νIn ⟶ id
--   ana-β    : νOut ∘ ana coalg ⟶ fmap (ana coalg) ∘ coalg
--
-- Same positivity note as CCT3: ν : (Ty → Ty) → Ty requires
-- NO_POSITIVITY_CHECK at the Ty declaration.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Syntax.CCT4.Hardin1989 where

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
-- β/η/s rules — inherited.
------------------------------------------------------------------------

import Theory.Syntax.CCTB.BaseRules as CCTB-B
open CCTB-B.Rules Ty Unit _×_ Term id _∘_ terminal fst snd ⟨_,_⟩ public
  renaming (_⟶β_ to _⟶β-CCTB_; _⟶s_ to _⟶s-CCTB_)

import Theory.Syntax.CCT1.BaseRules as CCT1-B
open CCT1-B.Rules Ty Unit _×_ _⇒_ Term id _∘_ fst snd ⟨_,_⟩ curry apply public
  renaming (_⟶β_ to _⟶β-CCT1_; _⟶η_ to _⟶η-CCT1_)

import Theory.Syntax.CCT2.BaseRules as CCT2-B
open CCT2-B.Rules Ty Unit _×_ _⇒_ Void _⊎_
                  Term id _∘_ initial inl inr [_,_] public
  renaming (_⟶β_ to _⟶β-CCT2_; _⟶s_ to _⟶s-CCT2_)

import Theory.Syntax.CCT3.BaseRules as CCT3-B
open CCT3-B.Rules Ty Term id _∘_ μ In Out cata fmap public
  renaming (_⟶β_ to _⟶β-CCT3_)

import Theory.Syntax.CCT4.BaseRules as CCT4-B
open CCT4-B.Rules Ty Term id _∘_ ν νOut νIn ana fmap public
  renaming (_⟶β_ to _⟶β-CCT4_)

------------------------------------------------------------------------
-- Unions
------------------------------------------------------------------------

data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
  from-CCTB-β : ∀ {A B} {f g : Term A B} → f ⟶β-CCTB g → f ⟶β g
  from-CCT1-β : ∀ {A B} {f g : Term A B} → f ⟶β-CCT1 g → f ⟶β g
  from-CCT2-β : ∀ {A B} {f g : Term A B} → f ⟶β-CCT2 g → f ⟶β g
  from-CCT3-β : ∀ {A B} {f g : Term A B} → f ⟶β-CCT3 g → f ⟶β g
  from-CCT4-β : ∀ {A B} {f g : Term A B} → f ⟶β-CCT4 g → f ⟶β g

infix 4 _⟶β_

data _⟶s_ : ∀ {A B} → Term A B → Term A B → Set where
  from-CCTB-s : ∀ {A B} {f g : Term A B} → f ⟶s-CCTB g → f ⟶s g
  from-CCT2-s : ∀ {A B} {f g : Term A B} → f ⟶s-CCT2 g → f ⟶s g

infix 4 _⟶s_

------------------------------------------------------------------------
-- Full reduction.
------------------------------------------------------------------------

data _⟶βη-rules_ : ∀ {A B} → Term A B → Term A B → Set where
  β-rule : ∀ {A B} {f g : Term A B} → f ⟶β g       → f ⟶βη-rules g
  η-rule : ∀ {A B} {f g : Term A B} → f ⟶η-CCT1 g  → f ⟶βη-rules g
  s-rule : ∀ {A B} {f g : Term A B} → f ⟶s g       → f ⟶βη-rules g

infix 4 _⟶βη-rules_

open import Theory.Syntax.CongruenceClosure
module βη-Closure =
  CCT4-Close Ty _×_ _⇒_ _⊎_ μ ν Term _∘_ ⟨_,_⟩ curry [_,_] cata fmap ana
             _⟶βη-rules_

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
-- Convertibility.
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

[,]-≈-congˡ : ∀ {A B C} {f f' : Term A C} {g : Term B C} →
              f ≈ f' → [ f , g ] ≈ [ f' , g ]
[,]-≈-congˡ Conv.≈-refl        = Conv.≈-refl
[,]-≈-congˡ (Conv.≈-step r e)  =
  Conv.≈-step (βη-Closure.[,]-congˡ r) ([,]-≈-congˡ e)
[,]-≈-congˡ (Conv.≈-back r e)  =
  Conv.≈-back (βη-Closure.[,]-congˡ r) ([,]-≈-congˡ e)

[,]-≈-congʳ : ∀ {A B C} {f : Term A C} {g g' : Term B C} →
              g ≈ g' → [ f , g ] ≈ [ f , g' ]
[,]-≈-congʳ Conv.≈-refl        = Conv.≈-refl
[,]-≈-congʳ (Conv.≈-step r e)  =
  Conv.≈-step (βη-Closure.[,]-congʳ r) ([,]-≈-congʳ e)
[,]-≈-congʳ (Conv.≈-back r e)  =
  Conv.≈-back (βη-Closure.[,]-congʳ r) ([,]-≈-congʳ e)

[,]-≈-cong : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
             f ≈ f' → g ≈ g' → [ f , g ] ≈ [ f' , g' ]
[,]-≈-cong f≈ g≈ = ≈-trans ([,]-≈-congˡ f≈) ([,]-≈-congʳ g≈)

cata-≈-cong : ∀ {F : Ty → Ty} {A} {alg alg' : Term (F A) A} →
              alg ≈ alg' → cata {F} alg ≈ cata {F} alg'
cata-≈-cong Conv.≈-refl        = Conv.≈-refl
cata-≈-cong (Conv.≈-step r e)  =
  Conv.≈-step (βη-Closure.cata-cong r) (cata-≈-cong e)
cata-≈-cong (Conv.≈-back r e)  =
  Conv.≈-back (βη-Closure.cata-cong r) (cata-≈-cong e)

ana-≈-cong : ∀ {F : Ty → Ty} {A} {coalg coalg' : Term A (F A)} →
             coalg ≈ coalg' → ana {F} coalg ≈ ana {F} coalg'
ana-≈-cong Conv.≈-refl        = Conv.≈-refl
ana-≈-cong (Conv.≈-step r e)  =
  Conv.≈-step (βη-Closure.ana-cong r) (ana-≈-cong e)
ana-≈-cong (Conv.≈-back r e)  =
  Conv.≈-back (βη-Closure.ana-cong r) (ana-≈-cong e)

------------------------------------------------------------------------
-- Canonical structures.
------------------------------------------------------------------------

open import Theory.Systems.CCTB using (CCTBStructure)
open import Theory.Systems.CCT1 using (CCT1Structure)
open import Theory.Systems.CCT2 using (CCT2Structure)
open import Theory.Systems.CCT3 using (CCT3Structure)
open import Theory.Systems.CCT4 using (CCT4Structure)

private
  cctb-β≈ : ∀ {A B} {f g : Term A B} → f ⟶β-CCTB g → f ≈ g
  cctb-β≈ r = ⟶-to-≈ (βη-Closure.base (β-rule (from-CCTB-β r)))

  cctb-s≈ : ∀ {A B} {f g : Term A B} → f ⟶s-CCTB g → f ≈ g
  cctb-s≈ r = ⟶-to-≈ (βη-Closure.base (s-rule (from-CCTB-s r)))

  cct1-β≈ : ∀ {A B} {f g : Term A B} → f ⟶β-CCT1 g → f ≈ g
  cct1-β≈ r = ⟶-to-≈ (βη-Closure.base (β-rule (from-CCT1-β r)))

  cct1-η≈ : ∀ {A B} {f g : Term A B} → f ⟶η-CCT1 g → f ≈ g
  cct1-η≈ r = ⟶-to-≈ (βη-Closure.base (η-rule r))

  cct2-β≈ : ∀ {A B} {f g : Term A B} → f ⟶β-CCT2 g → f ≈ g
  cct2-β≈ r = ⟶-to-≈ (βη-Closure.base (β-rule (from-CCT2-β r)))

  cct2-s≈ : ∀ {A B} {f g : Term A B} → f ⟶s-CCT2 g → f ≈ g
  cct2-s≈ r = ⟶-to-≈ (βη-Closure.base (s-rule (from-CCT2-s r)))

  cct3-β≈ : ∀ {A B} {f g : Term A B} → f ⟶β-CCT3 g → f ≈ g
  cct3-β≈ r = ⟶-to-≈ (βη-Closure.base (β-rule (from-CCT3-β r)))

  cct4-β≈ : ∀ {A B} {f g : Term A B} → f ⟶β-CCT4 g → f ≈ g
  cct4-β≈ r = ⟶-to-≈ (βη-Closure.base (β-rule (from-CCT4-β r)))

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

canonical-ccc : CCT1Structure
canonical-ccc = record
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

initial-unique-≈ : ∀ {A} {f g : Term Void A} → f ≈ g
initial-unique-≈ =
  ≈-trans (cct2-s≈ initial-unique) (≈-sym (cct2-s≈ initial-unique))

canonical-bcc : CCT2Structure
canonical-bcc = record
  { ccc            = canonical-ccc
  ; Void           = Void
  ; initial        = initial
  ; _⊎_            = _⊎_
  ; inl            = inl
  ; inr            = inr
  ; [_,_]          = [_,_]
  ; [,]-cong       = [,]-≈-cong
  ; initial-unique = initial-unique-≈
  ; case-inl       = cct2-β≈ case-inl
  ; case-inr       = cct2-β≈ case-inr
  ; eta-case       = cct2-β≈ eta-case
  ; eta-case-gen   = cct2-s≈ eta-case-gen
  ; case-dist      = cct2-s≈ case-dist
  }

canonical-bccμ : CCT3Structure
canonical-bccμ = record
  { bcc       = canonical-bcc
  ; μ         = μ
  ; In        = In
  ; Out       = Out
  ; cata      = cata
  ; fmap      = fmap
  ; cata-cong = cata-≈-cong
  ; out-in    = cct3-β≈ out-in
  ; in-out    = cct3-β≈ in-out
  ; cata-β    = cct3-β≈ cata-β
  }

canonical : CCT4Structure
canonical = record
  { bccμ     = canonical-bccμ
  ; ν        = ν
  ; νOut     = νOut
  ; νIn      = νIn
  ; ana      = ana
  ; ana-cong = ana-≈-cong
  ; νin-νout = cct4-β≈ νin-νout
  ; νout-νin = cct4-β≈ νout-νin
  ; ana-β    = cct4-β≈ ana-β
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
