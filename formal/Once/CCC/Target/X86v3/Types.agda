------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.Types
--
-- Type definitions for X86v3 SlotMachine POC.
--
-- Imports Type and Quantity from Once.Type, but provides local
-- semantic interpretation where functions are plain Agda functions
-- (not Closure records). This simplifies the SlotMachine proofs.
--
-- The main difference: Once.Type uses _+_ for sums, but X86v3 code
-- historically uses _⊕_. We provide _⊕_ = _+_ as an alias.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Types where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Import and re-export Type and Quantity from Once.Type
------------------------------------------------------------------------

open import Once.Type public
  using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Eff; Fix; Int; Float; Str; Buffer; TVar;
         Quantity; Zero; One; Many;
         _⊸_; _⇒_; _⇒₀_; IO)

------------------------------------------------------------------------
-- Sum operator alias for compatibility with existing X86v3 code
--
-- Once.Type uses _+_ for sums (standard categorical notation).
-- X86v3 code historically uses _⊕_ to avoid conflicts with Data.Nat._+_.
-- We provide _⊕_ as an alias for backwards compatibility.
------------------------------------------------------------------------

_⊕_ : Type → Type → Type
_⊕_ = _+_

infixr 40 _⊕_

------------------------------------------------------------------------
-- Type Slots: Memory representation sizes
--
-- Reference-based model: All values accessed by pointer (reference).
-- Stack vs Heap determines only WHERE allocation occurs, not HOW
-- values are represented. Both modes use identical pointer-based
-- representation.
--
-- This enables:
--   - Linear values passed by reference (zero-copy)
--   - Semantic copy only when linearity requires duplication
--   - Simplified proofs (one constructor works for both modes)
--   - Direct mapping to x86 calling conventions
--
-- See unboxed-stack-design.md for full design rationale.
------------------------------------------------------------------------

-- Reference-based representation: all compound types use fixed pointer sizes
stack-type-slots : Type → ℕ
stack-type-slots Unit = 0
stack-type-slots Void = 0
stack-type-slots Int = 1
stack-type-slots Float = 1
stack-type-slots Str = 1          -- pointer to string data
stack-type-slots Buffer = 1       -- pointer to buffer data
stack-type-slots (A * B) = 2      -- ptr to fst + ptr to snd
stack-type-slots (A + B) = 2      -- tag + ptr to payload
stack-type-slots (_ ⇒[ _ ] _) = 2 -- closure: env-ptr + code-ptr
stack-type-slots (Eff _ B) = stack-type-slots B
stack-type-slots (Fix _) = 1      -- pointer to recursive structure
stack-type-slots (TVar _) = 1     -- polymorphic = pointer

-- Heap representation: identical to stack (reference-based model)
-- Kept separate for API compatibility; both are definitionally equal.
heap-type-slots : Type → ℕ
heap-type-slots Unit = 0
heap-type-slots Void = 0
heap-type-slots Int = 1
heap-type-slots Float = 1
heap-type-slots Str = 1
heap-type-slots Buffer = 1
heap-type-slots (A * B) = 2        -- ptr to fst + ptr to snd
heap-type-slots (A + B) = 2        -- tag + ptr to payload
heap-type-slots (_ ⇒[ _ ] _) = 2   -- closure: env-ptr + code-ptr
heap-type-slots (Eff _ B) = heap-type-slots B
heap-type-slots (Fix _) = 1        -- pointer to recursive structure
heap-type-slots (TVar _) = 1       -- polymorphic = pointer

-- Legacy alias (all representations now use reference-based model)
type-slots : Type → ℕ
type-slots = stack-type-slots

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
⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
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

inl : ∀ {A B} → ⟦ A ⟧ → ⟦ A + B ⟧
inl = inj₁

inr : ∀ {A B} → ⟦ B ⟧ → ⟦ A + B ⟧
inr = inj₂

case : ∀ {A B C} → (⟦ A ⟧ → ⟦ C ⟧) → (⟦ B ⟧ → ⟦ C ⟧) → ⟦ A + B ⟧ → ⟦ C ⟧
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
