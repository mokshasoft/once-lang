------------------------------------------------------------------------
-- Types: Foundation for CCC
--
-- This module defines:
--   1. Minimal prelude (no external dependencies)
--   2. Types and Functors for the CCC
--   3. Decidable equality
--
-- SELF-CONTAINED: This is the bootstrap foundation.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module normalizer.Syntax.Types where

------------------------------------------------------------------------
-- Minimal Prelude
------------------------------------------------------------------------

-- Propositional equality
data _≡_ {A : Set} : A → A → Set where
  refl : ∀ {x} → x ≡ x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B} →
        x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

-- Dependent pairs (Σ types)
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A ; snd : B fst

∃-syntax : ∀ {A : Set} → (A → Set) → Set
∃-syntax {A} B = Σ A B
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- Non-dependent pairs
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

-- Disjoint sum (Either)
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Empty type (absurdity)
data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- Unit type
record ⊤ : Set where
  constructor tt

-- Negation
¬_ : Set → Set
¬ A = A → ⊥

-- Decision type
data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

-- Inspect idiom for remembering with-pattern results
record Reveal_·_is_ {A B : Set} (f : A → B) (x : A) (y : B) : Set where
  constructor ⟪_⟫
  field eq : f x ≡ y

inspect : ∀ {A B : Set} (f : A → B) (x : A) → Reveal f · x is (f x)
inspect f x = ⟪ refl ⟫

------------------------------------------------------------------------
-- Types and Functors
------------------------------------------------------------------------

-- Mutually recursive: types can contain μF, functors can contain K Ty
data Ty : Set
data Func : Set

data Ty where
  Void : Ty              -- Initial object (empty type)
  Unit : Ty
  _*_  : Ty → Ty → Ty
  _+_  : Ty → Ty → Ty
  _⇒_  : Ty → Ty → Ty  -- Exponential (function type)
  μ_   : Func → Ty

-- Func is FIRST-ORDER and Ty-INDEPENDENT: its only constant payloads are
-- `One` (the Unit leaf) and `Kc G` (a code = the fixpoint of another
-- functor G). It can no longer hold an arbitrary `Ty` (in particular not a
-- function type), so `Fix` (Testing.Evaluator) is strictly positive with NO
-- pragma, and the model's coherence has no `⇒` case to (impossibly) invert.
-- This matches reality: codes only ever store sub-codes and Unit leaves;
-- the `⇒` type-former is encoded as DATA, never as an actual function.
data Func where
  Id  : Func
  One : Func              -- constant Unit leaf            (was `K Unit`)
  Kc  : Func → Func       -- constant code (fixpoint of G)  (was `K (μ G)`)
  _⊕_ : Func → Func → Func
  _⊗_ : Func → Func → Func

infixr 7 _*_ _⊗_
infixr 6 _+_ _⊕_
infixr 5 _⇒_

-- Functor interpretation: apply functor to a type
⟦_⟧F : Func → Ty → Ty
⟦ Id ⟧F X = X
⟦ One ⟧F X = Unit
⟦ Kc G ⟧F X = μ G
⟦ F ⊕ G ⟧F X = ⟦ F ⟧F X + ⟦ G ⟧F X
⟦ F ⊗ G ⟧F X = ⟦ F ⟧F X * ⟦ G ⟧F X

------------------------------------------------------------------------
-- Decidable Equality
------------------------------------------------------------------------

-- Mutually recursive decidable equality
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
_≟Func_ : (F G : Func) → Dec (F ≡ G)

-- Decidable equality for Ty
Void ≟Ty Void = yes refl
Void ≟Ty Unit = no (λ ())
Void ≟Ty (_ * _) = no (λ ())
Void ≟Ty (_ + _) = no (λ ())
Void ≟Ty (_ ⇒ _) = no (λ ())
Void ≟Ty (μ _) = no (λ ())

Unit ≟Ty Void = no (λ ())
Unit ≟Ty Unit = yes refl
Unit ≟Ty (_ * _) = no (λ ())
Unit ≟Ty (_ + _) = no (λ ())
Unit ≟Ty (_ ⇒ _) = no (λ ())
Unit ≟Ty (μ _) = no (λ ())

(A * B) ≟Ty Void = no (λ ())
(A * B) ≟Ty Unit = no (λ ())
(A * B) ≟Ty (C * D) with A ≟Ty C | B ≟Ty D
... | yes refl | yes refl = yes refl
... | yes refl | no neq = no (λ { refl → neq refl })
... | no neq | _ = no (λ { refl → neq refl })
(A * B) ≟Ty (_ + _) = no (λ ())
(A * B) ≟Ty (_ ⇒ _) = no (λ ())
(A * B) ≟Ty (μ _) = no (λ ())

(A + B) ≟Ty Void = no (λ ())
(A + B) ≟Ty Unit = no (λ ())
(A + B) ≟Ty (_ * _) = no (λ ())
(A + B) ≟Ty (C + D) with A ≟Ty C | B ≟Ty D
... | yes refl | yes refl = yes refl
... | yes refl | no neq = no (λ { refl → neq refl })
... | no neq | _ = no (λ { refl → neq refl })
(A + B) ≟Ty (_ ⇒ _) = no (λ ())
(A + B) ≟Ty (μ _) = no (λ ())

(A ⇒ B) ≟Ty Void = no (λ ())
(A ⇒ B) ≟Ty Unit = no (λ ())
(A ⇒ B) ≟Ty (_ * _) = no (λ ())
(A ⇒ B) ≟Ty (_ + _) = no (λ ())
(A ⇒ B) ≟Ty (C ⇒ D) with A ≟Ty C | B ≟Ty D
... | yes refl | yes refl = yes refl
... | yes refl | no neq = no (λ { refl → neq refl })
... | no neq | _ = no (λ { refl → neq refl })
(A ⇒ B) ≟Ty (μ _) = no (λ ())

(μ F) ≟Ty Void = no (λ ())
(μ F) ≟Ty Unit = no (λ ())
(μ F) ≟Ty (_ * _) = no (λ ())
(μ F) ≟Ty (_ + _) = no (λ ())
(μ F) ≟Ty (_ ⇒ _) = no (λ ())
(μ F) ≟Ty (μ G) with F ≟Func G
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })

-- Decidable equality for Func
Id ≟Func Id = yes refl
Id ≟Func One = no (λ ())
Id ≟Func (Kc _) = no (λ ())
Id ≟Func (_ ⊕ _) = no (λ ())
Id ≟Func (_ ⊗ _) = no (λ ())

One ≟Func Id = no (λ ())
One ≟Func One = yes refl
One ≟Func (Kc _) = no (λ ())
One ≟Func (_ ⊕ _) = no (λ ())
One ≟Func (_ ⊗ _) = no (λ ())

(Kc F) ≟Func Id = no (λ ())
(Kc F) ≟Func One = no (λ ())
(Kc F) ≟Func (Kc G) with F ≟Func G
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })
(Kc F) ≟Func (_ ⊕ _) = no (λ ())
(Kc F) ≟Func (_ ⊗ _) = no (λ ())

(F ⊕ G) ≟Func Id = no (λ ())
(F ⊕ G) ≟Func One = no (λ ())
(F ⊕ G) ≟Func (Kc _) = no (λ ())
(F ⊕ G) ≟Func (H ⊕ I) with F ≟Func H | G ≟Func I
... | yes refl | yes refl = yes refl
... | yes refl | no neq = no (λ { refl → neq refl })
... | no neq | _ = no (λ { refl → neq refl })
(F ⊕ G) ≟Func (_ ⊗ _) = no (λ ())

(F ⊗ G) ≟Func Id = no (λ ())
(F ⊗ G) ≟Func One = no (λ ())
(F ⊗ G) ≟Func (Kc _) = no (λ ())
(F ⊗ G) ≟Func (_ ⊕ _) = no (λ ())
(F ⊗ G) ≟Func (H ⊗ I) with F ≟Func H | G ≟Func I
... | yes refl | yes refl = yes refl
... | yes refl | no neq = no (λ { refl → neq refl })
... | no neq | _ = no (λ { refl → neq refl })

------------------------------------------------------------------------
-- Type Views
------------------------------------------------------------------------

-- View for classifying types by structure
data TyView : Ty → Set where
  tv-void   : TyView Void
  tv-unit   : TyView Unit
  tv-prod   : ∀ A B → TyView (A * B)
  tv-coprod : ∀ A B → TyView (A + B)
  tv-exp    : ∀ A B → TyView (A ⇒ B)
  tv-mu     : ∀ F → TyView (μ F)

tyView : (T : Ty) → TyView T
tyView Void = tv-void
tyView Unit = tv-unit
tyView (A * B) = tv-prod A B
tyView (A + B) = tv-coprod A B
tyView (A ⇒ B) = tv-exp A B
tyView (μ F) = tv-mu F
