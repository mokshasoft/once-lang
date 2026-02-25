------------------------------------------------------------------------
-- Once.CCC.IR
--
-- CCC IR = Once.IR + free-heap
--
-- This is the IR used by the CCC backend after escape analysis.
-- It's identical to Once.IR except:
--   1. free-heap constructor for explicit deallocation
--   2. Uses CCC.Types for semantic interpretation
--
-- The pipeline is:
--   Once.IR (parser, optimizer) → escape analysis → CCC.IR (backend)
--
-- Prim is OPAQUE - just a name. Semantics come from:
--   - Arith proofs (for arithmetic primitives)
--   - Interpretations (for FFI primitives)
------------------------------------------------------------------------

module Once.CCC.IR where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (m<m+n; m<n+m; +-comm; n<1+n; <-trans; m+n≤o⇒m≤o; m+n≤o⇒n≤o; +-monoˡ-<; +-monoʳ-<)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

-- Use CCC Types (which re-exports Once.Type with semantic interpretation)
open import Once.CCC.Target.X86v3.Types public

-- HeapRef for free-heap
open import Once.CCC.SlotMachine using (HeapRef)

------------------------------------------------------------------------
-- Allocation Mode
--
-- Same as Once.IR.AllocMode - specifies stack vs heap allocation.
-- Escape analysis rewrites Heap → Stack where safe.
------------------------------------------------------------------------

data AllocMode : Set where
  Stack : AllocMode  -- Allocate inline on stack (non-escaping)
  Heap  : AllocMode  -- Allocate on heap (escaping)

------------------------------------------------------------------------
-- IR Language
--
-- This is Once.IR + free-heap.
--
-- Constructors match Once.IR exactly, with naming:
--   Once.IR    CCC.IR
--   --------   ------
--   fst        fst-ir
--   snd        snd-ir
--   [_,_]      case-ir
--   fold       fold-ir (+ AllocMode)
--   unfold     unfold-ir
--
-- The -ir suffix distinguishes from type constructors.
------------------------------------------------------------------------

data IR : Type → Type → Set where
  -- Category structure
  id : ∀ {A} → IR A A
  _∘_ : ∀ {A B C} → IR B C → IR A B → IR A C

  -- Product (A * B) - AllocMode specifies where pair is allocated
  ⟨_,_⟩_ : ∀ {A B C} → IR A B → IR A C → AllocMode → IR A (B * C)
  fst-ir : ∀ {A B} → IR (A * B) A
  snd-ir : ∀ {A B} → IR (A * B) B

  -- Coproduct (A + B) - AllocMode specifies where sum is allocated
  inl-ir : ∀ {A B} → AllocMode → IR A (A + B)
  inr-ir : ∀ {A B} → AllocMode → IR B (A + B)
  case-ir : ∀ {A B C} → IR A C → IR B C → IR (A + B) C

  -- Terminal object (Unit)
  terminal : ∀ {A} → IR A Unit

  -- Initial object (Void)
  initial : ∀ {A} → IR Void A

  -- Exponential (A ⇒ B) - AllocMode specifies where closure is allocated
  curry : ∀ {A B C} → IR (A * B) C → AllocMode → IR A (B ⇒ C)
  apply : ∀ {A B} → IR ((A ⇒ B) * A) B

  -- Recursive types (Fix F) - AllocMode specifies where fold is allocated
  fold-ir : ∀ {F} → AllocMode → IR F (Fix F)
  unfold-ir : ∀ {F} → IR (Fix F) F

  -- Explicit heap deallocation (NEW - not in Once.IR)
  -- Added by escape analysis when heap values can be freed.
  -- Semantically a no-op (doesn't change computed values).
  free-heap : HeapRef → IR Unit Unit

  -- Primitive operations (OPAQUE)
  -- Just a name - semantics provided externally by:
  --   - Arith proofs (arithmetic primitives)
  --   - Interpretations (FFI primitives)
  Prim : ∀ {A B} → String → IR A B

infixr 9 _∘_
infixr 4 ⟨_,_⟩_

------------------------------------------------------------------------
-- Semantic Evaluation
--
-- AllocMode is phantom in semantics - it only affects runtime memory
-- layout, not the computed values.
--
-- Prim semantics are postulated - they come from external proofs.
------------------------------------------------------------------------

-- Postulate: primitive semantics (trust boundary)
-- This is filled in by Arith proofs or Interpretation implementations.
postulate
  evalPrim : ∀ {A B} → String → ⟦ A ⟧ → ⟦ B ⟧

eval : ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧
eval id x = x
eval (g ∘ f) x = eval g (eval f x)
eval (⟨ f , g ⟩ _) x = pair (eval f x) (eval g x)  -- AllocMode ignored
eval fst-ir x = fst x
eval snd-ir x = snd x
eval (inl-ir _) x = inl x   -- AllocMode ignored
eval (inr-ir _) x = inr x   -- AllocMode ignored
eval (case-ir f g) x = case (eval f) (eval g) x
eval terminal x = tt
eval initial ()
eval (curry f _) x = λ y → eval f (pair x y)  -- AllocMode ignored
eval apply (closure , arg) = closure arg
eval (fold-ir _) x = fold x  -- AllocMode ignored
eval unfold-ir x = unfold x
eval (free-heap _) x = x  -- No-op: deallocation doesn't change semantics
eval (Prim name) x = evalPrim name x  -- Delegate to postulate

------------------------------------------------------------------------
-- Evaluation Laws
------------------------------------------------------------------------

eval-id : ∀ {A} (x : ⟦ A ⟧) → eval id x ≡ x
eval-id x = refl

eval-fst : ∀ {A B} (x : ⟦ A * B ⟧) → eval fst-ir x ≡ fst x
eval-fst x = refl

eval-snd : ∀ {A B} (x : ⟦ A * B ⟧) → eval snd-ir x ≡ snd x
eval-snd x = refl

eval-compose : ∀ {A B C} (f : IR A B) (g : IR B C) (x : ⟦ A ⟧) →
  eval (g ∘ f) x ≡ eval g (eval f x)
eval-compose f g x = refl

eval-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) (x : ⟦ A ⟧) →
  eval (⟨ f , g ⟩ m) x ≡ pair (eval f x) (eval g x)
eval-pair f g m x = refl

eval-terminal : ∀ {A} (x : ⟦ A ⟧) → eval terminal x ≡ tt
eval-terminal x = refl

-- AllocMode independence: changing AllocMode doesn't change semantics
alloc-mode-independent-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval (⟨ f , g ⟩ m₁) x ≡ eval (⟨ f , g ⟩ m₂) x
alloc-mode-independent-pair f g m₁ m₂ x = refl

alloc-mode-independent-inl : ∀ {A B} (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval (inl-ir {A} {B} m₁) x ≡ eval (inl-ir {A} {B} m₂) x
alloc-mode-independent-inl m₁ m₂ x = refl

alloc-mode-independent-inr : ∀ {A B} (m₁ m₂ : AllocMode) (x : ⟦ B ⟧) →
  eval (inr-ir {A} {B} m₁) x ≡ eval (inr-ir {A} {B} m₂) x
alloc-mode-independent-inr m₁ m₂ x = refl

alloc-mode-independent-curry : ∀ {A B C} (f : IR (A * B) C) (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval (curry f m₁) x ≡ eval (curry f m₂) x
alloc-mode-independent-curry f m₁ m₂ x = refl

------------------------------------------------------------------------
-- Size Measure for Termination
------------------------------------------------------------------------

ir-size : ∀ {A B} → IR A B → ℕ
ir-size id = 1
ir-size (g ∘ f) = 1 +ℕ ir-size g +ℕ ir-size f
ir-size (⟨ f , g ⟩ _) = 1 +ℕ ir-size f +ℕ ir-size g
ir-size fst-ir = 1
ir-size snd-ir = 1
ir-size (inl-ir _) = 1
ir-size (inr-ir _) = 1
ir-size (case-ir f g) = 1 +ℕ ir-size f +ℕ ir-size g
ir-size terminal = 1
ir-size initial = 1
ir-size (curry f _) = 2 +ℕ ir-size f
ir-size apply = 1
ir-size (fold-ir _) = 1
ir-size unfold-ir = 1
ir-size (free-heap _) = 1
ir-size (Prim _) = 1

------------------------------------------------------------------------
-- Conversion from Once.IR
--
-- Simple structural conversion. The only difference is:
--   - Once.IR.fold has no AllocMode → default to Heap
--   - Once.IR has no free-heap → never generated
--   - Once.IR.arr → maps to id (Eff is phantom)
------------------------------------------------------------------------

open import Once.IR as Once
  using ()
  renaming (IR to OnceIR; AllocMode to OnceAllocMode; Stack to OnceStack; Heap to OnceHeap)

adaptAllocMode : OnceAllocMode → AllocMode
adaptAllocMode OnceStack = Stack
adaptAllocMode OnceHeap = Heap

fromOnceIR : ∀ {A B} → OnceIR A B → IR A B
fromOnceIR Once.id = id
fromOnceIR (g Once.∘ f) = fromOnceIR g ∘ fromOnceIR f
fromOnceIR Once.fst = fst-ir
fromOnceIR Once.snd = snd-ir
fromOnceIR (Once.⟨ f , g ⟩ m) = ⟨ fromOnceIR f , fromOnceIR g ⟩ (adaptAllocMode m)
fromOnceIR (Once.inl m) = inl-ir (adaptAllocMode m)
fromOnceIR (Once.inr m) = inr-ir (adaptAllocMode m)
fromOnceIR Once.[ f , g ] = case-ir (fromOnceIR f) (fromOnceIR g)
fromOnceIR Once.terminal = terminal
fromOnceIR Once.initial = initial
fromOnceIR (Once.curry f m) = curry (fromOnceIR f) (adaptAllocMode m)
fromOnceIR Once.apply = apply
fromOnceIR Once.fold = fold-ir Heap  -- Default to Heap (conservative)
fromOnceIR Once.unfold = unfold-ir
fromOnceIR Once.arr = id  -- Eff is phantom, arr is identity at runtime
fromOnceIR (Once.Prim name) = Prim name

------------------------------------------------------------------------
-- Summary
--
-- CCC.IR = Once.IR + free-heap
--
-- Key properties:
--   - Prim is opaque (just a name)
--   - AllocMode is phantom in semantics
--   - free-heap is semantically a no-op
--   - fromOnceIR converts Once.IR → CCC.IR
------------------------------------------------------------------------
