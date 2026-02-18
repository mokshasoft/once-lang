------------------------------------------------------------------------
-- Once.Backend.X86v3.Types
--
-- Self-contained type definitions for X86v3 SlotMachine POC.
--
-- This module is intentionally independent from Once.Type and
-- Once.SemanticBaseMachine. X86v3 uses a simplified semantic
-- interpretation where functions are plain Agda functions (not
-- Closure records). This simplifies the SlotMachine correctness proofs.
------------------------------------------------------------------------

module Once.Backend.X86v3.Types where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Quantity (for graded function types)
------------------------------------------------------------------------

data Quantity : Set where
  Zero  : Quantity  -- Erased
  One   : Quantity  -- Linear
  Many  : Quantity  -- Unrestricted

------------------------------------------------------------------------
-- Type definition
------------------------------------------------------------------------

data Type : Set where
  Unit   : Type
  Void   : Type
  _*_    : Type → Type → Type
  _⊕_    : Type → Type → Type  -- Sum type (avoiding conflict with Data.Nat._+_)
  _⇒[_]_ : Type → Quantity → Type → Type
  Eff    : Type → Type → Type
  Fix    : Type → Type
  Int    : Type
  Float  : Type
  Str    : Type
  Buffer : Type
  TVar   : String → Type

infixr 30 _⇒[_]_
infixr 40 _⊕_
infixr 50 _*_

-- Smart constructors
_⊸_ : Type → Type → Type
A ⊸ B = A ⇒[ One ] B

_⇒_ : Type → Type → Type
A ⇒ B = A ⇒[ Many ] B

_⇒₀_ : Type → Type → Type
A ⇒₀ B = A ⇒[ Zero ] B

infixr 30 _⊸_
infixr 30 _⇒_
infixr 30 _⇒₀_

IO : Type → Type
IO A = Eff Unit A

------------------------------------------------------------------------
-- Type Slots: Stack space for unboxed representation
------------------------------------------------------------------------

type-slots : Type → ℕ
type-slots Unit = 0
type-slots Void = 0
type-slots Int = 1
type-slots Float = 1
type-slots Str = 1
type-slots Buffer = 1
type-slots (A * B) = type-slots A +ℕ type-slots B
type-slots (A ⊕ B) = 1 +ℕ (type-slots A ⊔ type-slots B)
type-slots (_ ⇒[ _ ] _) = 2  -- closure: env-ptr + code-ptr
type-slots (Eff _ B) = type-slots B
type-slots (Fix _) = 1  -- pointer to recursive structure
type-slots (TVar _) = 1  -- polymorphic = pointer

------------------------------------------------------------------------
-- Fixed Point Wrapper
------------------------------------------------------------------------

record ⟦Fix⟧ (A : Set) : Set where
  constructor wrap
  field unwrap : A

open ⟦Fix⟧ public

------------------------------------------------------------------------
-- Semantic Interpretation
--
-- Functions are plain Agda functions (simplified from Closure records).
-- This is sufficient for SlotMachine proofs since valid-closure tracks
-- the body IR directly.
------------------------------------------------------------------------

⟦_⟧ : Type → Set
⟦ Unit ⟧         = ⊤
⟦ Void ⟧         = ⊥
⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⊕ B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒[ _ ] B ⟧   = ⟦ A ⟧ → ⟦ B ⟧
⟦ Eff A B ⟧      = ⟦ A ⟧ → ⟦ B ⟧
⟦ Fix F ⟧        = ⟦Fix⟧ ⟦ F ⟧
⟦ Int ⟧          = ℕ
⟦ Float ⟧        = AgdaFloat
⟦ Str ⟧          = String
⟦ Buffer ⟧       = String
⟦ TVar _ ⟧       = ⊤

------------------------------------------------------------------------
-- Pair operations
------------------------------------------------------------------------

fst : ∀ {A B} → ⟦ A * B ⟧ → ⟦ A ⟧
fst = proj₁

snd : ∀ {A B} → ⟦ A * B ⟧ → ⟦ B ⟧
snd = proj₂

pair : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A * B ⟧
pair a b = a , b

------------------------------------------------------------------------
-- Sum operations
------------------------------------------------------------------------

inl : ∀ {A B} → ⟦ A ⟧ → ⟦ A ⊕ B ⟧
inl = inj₁

inr : ∀ {A B} → ⟦ B ⟧ → ⟦ A ⊕ B ⟧
inr = inj₂

case : ∀ {A B C} → (⟦ A ⟧ → ⟦ C ⟧) → (⟦ B ⟧ → ⟦ C ⟧) → ⟦ A ⊕ B ⟧ → ⟦ C ⟧
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

------------------------------------------------------------------------
-- Fixed point operations
------------------------------------------------------------------------

fold : ∀ {F} → ⟦ F ⟧ → ⟦ Fix F ⟧
fold x = wrap x

unfold : ∀ {F} → ⟦ Fix F ⟧ → ⟦ F ⟧
unfold (wrap x) = x

------------------------------------------------------------------------
-- Laws
------------------------------------------------------------------------

fst-pair : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) → fst (pair a b) ≡ a
fst-pair a b = refl

snd-pair : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) → snd (pair a b) ≡ b
snd-pair a b = refl

case-inl : ∀ {A B C} (f : ⟦ A ⟧ → ⟦ C ⟧) (g : ⟦ B ⟧ → ⟦ C ⟧) (a : ⟦ A ⟧) →
  case f g (inl a) ≡ f a
case-inl f g a = refl

case-inr : ∀ {A B C} (f : ⟦ A ⟧ → ⟦ C ⟧) (g : ⟦ B ⟧ → ⟦ C ⟧) (b : ⟦ B ⟧) →
  case f g (inr b) ≡ g b
case-inr f g b = refl

unfold-fold : ∀ {F} (x : ⟦ F ⟧) → unfold (fold x) ≡ x
unfold-fold x = refl

fold-unfold : ∀ {F} (x : ⟦ Fix F ⟧) → fold (unfold x) ≡ x
fold-unfold (wrap x) = refl
