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
open import Data.Nat.Properties using (m<m+n; m<n+m; +-comm; n<1+n; <-trans; m+n≤o⇒m≤o; m+n≤o⇒n≤o; +-monoˡ-<; +-monoʳ-<; +-assoc)
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

  -- Exponential (A ⇒[ q ] B) - AllocMode specifies where closure is allocated
  curry : ∀ {A B C q} → IR (A * B) C → AllocMode → IR A (B ⇒[ q ] C)
  apply : ∀ {A B q} → IR ((A ⇒[ q ] B) * A) B

  -- Effectful morphisms (Eff A B)
  arr : ∀ {A B q} → IR (A ⇒[ q ] B) (Eff A B)

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
-- Primitive Type Evidence
--
-- IsPrimitive: Evidence that a type is primitive (CPU-native).
-- Used by backend proofs to construct ValidAtWF without postulates.
-- CPUs only produce primitive types as results.
------------------------------------------------------------------------

data IsPrimitive : Type → Set where
  is-unit   : IsPrimitive Unit
  is-int    : IsPrimitive Int
  is-float  : IsPrimitive Float
  is-str    : IsPrimitive Str
  is-buffer : IsPrimitive Buffer

------------------------------------------------------------------------
-- Primitive Contract
--
-- PrimContractV3: Contract for primitive operations.
-- Specifies resource requirements for code generation and verification.
------------------------------------------------------------------------

record PrimContractV3 (A B : Type) : Set where
  field
    stack-requirement : ℕ
    output-mode : AllocMode
    stack-req-bounded : stack-requirement ≤ 2

open PrimContractV3 public

------------------------------------------------------------------------
-- Primitive Semantics Provider
--
-- To evaluate an IR containing Prim, you must provide a PrimSem that
-- gives semantics for each primitive name. This eliminates the need
-- for postulates - domain compilers (like Arith) provide their own
-- PrimSem implementations.
--
-- This ensures no one can "cheat" by evaluating a Prim without
-- providing its semantics.
------------------------------------------------------------------------

record PrimSem : Set₁ where
  field
    -- | Evaluate a primitive operation by name
    evalPrim : ∀ {A B} → String → ⟦ A ⟧ → ⟦ B ⟧

open PrimSem public

------------------------------------------------------------------------
-- Semantic Evaluation
--
-- AllocMode is phantom in semantics - it only affects runtime memory
-- layout, not the computed values.
--
-- eval is PARAMETERIZED by PrimSem - no postulates needed!
-- To evaluate Prim, you must provide the semantics explicitly.
------------------------------------------------------------------------

eval : PrimSem → ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧
eval ps id x = x
eval ps (g ∘ f) x = eval ps g (eval ps f x)
eval ps (⟨ f , g ⟩ _) x = pair (eval ps f x) (eval ps g x)  -- AllocMode ignored
eval ps fst-ir x = fst x
eval ps snd-ir x = snd x
eval ps (inl-ir _) x = inl x   -- AllocMode ignored
eval ps (inr-ir _) x = inr x   -- AllocMode ignored
eval ps (case-ir f g) x = case (eval ps f) (eval ps g) x
eval ps terminal x = tt
eval ps initial ()
eval ps (curry f _) x = λ y → eval ps f (pair x y)  -- AllocMode ignored
eval ps apply (closure , arg) = closure arg
eval ps arr f = f  -- Eff is phantom, same runtime representation
eval ps (fold-ir _) x = fold x  -- AllocMode ignored
eval ps unfold-ir x = unfold x
eval ps (free-heap _) x = x  -- No-op: deallocation doesn't change semantics
eval ps (Prim name) x = evalPrim ps name x  -- Use provided PrimSem

------------------------------------------------------------------------
-- Evaluation Laws
--
-- All laws are parameterized by PrimSem.
------------------------------------------------------------------------

eval-id : ∀ (ps : PrimSem) {A} (x : ⟦ A ⟧) → eval ps id x ≡ x
eval-id ps x = refl

eval-fst : ∀ (ps : PrimSem) {A B} (x : ⟦ A * B ⟧) → eval ps fst-ir x ≡ fst x
eval-fst ps x = refl

eval-snd : ∀ (ps : PrimSem) {A B} (x : ⟦ A * B ⟧) → eval ps snd-ir x ≡ snd x
eval-snd ps x = refl

eval-compose : ∀ (ps : PrimSem) {A B C} (f : IR A B) (g : IR B C) (x : ⟦ A ⟧) →
  eval ps (g ∘ f) x ≡ eval ps g (eval ps f x)
eval-compose ps f g x = refl

eval-pair : ∀ (ps : PrimSem) {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) (x : ⟦ A ⟧) →
  eval ps (⟨ f , g ⟩ m) x ≡ pair (eval ps f x) (eval ps g x)
eval-pair ps f g m x = refl

eval-terminal : ∀ (ps : PrimSem) {A} (x : ⟦ A ⟧) → eval ps terminal x ≡ tt
eval-terminal ps x = refl

-- AllocMode independence: changing AllocMode doesn't change semantics
alloc-mode-independent-pair : ∀ (ps : PrimSem) {A B C} (f : IR A B) (g : IR A C) (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval ps (⟨ f , g ⟩ m₁) x ≡ eval ps (⟨ f , g ⟩ m₂) x
alloc-mode-independent-pair ps f g m₁ m₂ x = refl

alloc-mode-independent-inl : ∀ (ps : PrimSem) {A B} (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval ps (inl-ir {A} {B} m₁) x ≡ eval ps (inl-ir {A} {B} m₂) x
alloc-mode-independent-inl ps m₁ m₂ x = refl

alloc-mode-independent-inr : ∀ (ps : PrimSem) {A B} (m₁ m₂ : AllocMode) (x : ⟦ B ⟧) →
  eval ps (inr-ir {A} {B} m₁) x ≡ eval ps (inr-ir {A} {B} m₂) x
alloc-mode-independent-inr ps m₁ m₂ x = refl

alloc-mode-independent-curry : ∀ (ps : PrimSem) {A B C q} (f : IR (A * B) C) (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval ps (curry {q = q} f m₁) x ≡ eval ps (curry {q = q} f m₂) x
alloc-mode-independent-curry ps f m₁ m₂ x = refl

------------------------------------------------------------------------
-- Stack Layout Constants
------------------------------------------------------------------------

-- | Size of a pair in slots (used for capacity calculations)
pair-slots : ℕ
pair-slots = 2

-- | Size of a closure in slots (env-ptr + code-ptr)
closure-slots : ℕ
closure-slots = 2

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
ir-size arr = 1
ir-size (fold-ir _) = 1
ir-size unfold-ir = 1
ir-size (free-heap _) = 1
ir-size (Prim _) = 1

------------------------------------------------------------------------
-- Size Bound Lemmas
--
-- Sub-IRs have smaller size than compound IRs.
-- Used by Dispatcher to prove recursive calls are within program-bound.
------------------------------------------------------------------------

-- Compose: f and g are smaller than (g ∘ f)
-- ir-size (g ∘ f) = 1 + ir-size g + ir-size f
∘-f-smaller : ∀ {A B C} (f : IR A B) (g : IR B C) → ir-size f < ir-size (g ∘ f)
∘-f-smaller f g = m<n+m (ir-size f) {suc (ir-size g)} (s≤s z≤n)

∘-g-smaller : ∀ {A B C} (f : IR A B) (g : IR B C) → ir-size g < ir-size (g ∘ f)
∘-g-smaller f g = s≤s (m≤m+n (ir-size g) (ir-size f))
  where open import Data.Nat.Properties using (m≤m+n)

-- Pair: f and g are smaller than ⟨ f , g ⟩
⟨,⟩-f-smaller : ∀ {A B C} (f : IR A B) (g : IR A C) {m : AllocMode} → ir-size f < ir-size (⟨ f , g ⟩ m)
⟨,⟩-f-smaller f g {m} = s≤s (m≤m+n (ir-size f) (ir-size g))
  where open import Data.Nat.Properties using (m≤m+n)

⟨,⟩-g-smaller : ∀ {A B C} (f : IR A B) (g : IR A C) {m : AllocMode} → ir-size g < ir-size (⟨ f , g ⟩ m)
⟨,⟩-g-smaller f g {m} = s≤s (m≤n+m (ir-size g) (ir-size f))
  where open import Data.Nat.Properties using (m≤n+m)

-- Curry: body f is smaller than (curry f m)
-- ir-size (curry f m) = 2 + ir-size f, so ir-size f < 2 + ir-size f
curry-smaller : ∀ {A B C q} (f : IR (A * B) C) {m : AllocMode} → ir-size f < ir-size (curry {q = q} f m)
curry-smaller f {m} = ≤-step (n<1+n (ir-size f))
  where open import Data.Nat.Properties using (n<1+n; ≤-step)

-- Case: f and g are smaller than (case-ir f g)
case-f-smaller : ∀ {A B C} (f : IR A C) (g : IR B C) → ir-size f < ir-size (case-ir f g)
case-f-smaller f g = s≤s (m≤m+n (ir-size f) (ir-size g))
  where open import Data.Nat.Properties using (m≤m+n)

case-g-smaller : ∀ {A B C} (f : IR A C) (g : IR B C) → ir-size g < ir-size (case-ir f g)
case-g-smaller f g = s≤s (m≤n+m (ir-size g) (ir-size f))
  where open import Data.Nat.Properties using (m≤n+m)

------------------------------------------------------------------------
-- Stack Requirement
--
-- Computes the stack slots needed to execute an IR operation.
-- Used for capacity calculations in the Dispatcher.
------------------------------------------------------------------------

ir-stack-requirement : ∀ {A B} → IR A B → ℕ
ir-stack-requirement id = 0               -- No-op: no stack needed
ir-stack-requirement (g ∘ f) = ir-stack-requirement f +ℕ ir-stack-requirement g  -- Composition: sum of sub-requirements
ir-stack-requirement (⟨ f , g ⟩ _) = ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots  -- Pair: sub-reqs + pair allocation
ir-stack-requirement fst-ir = 0           -- Projection: just returns pointer
ir-stack-requirement snd-ir = 0           -- Projection: just returns pointer
ir-stack-requirement (inl-ir _) = pair-slots     -- Sum injection: allocates tagged value
ir-stack-requirement (inr-ir _) = pair-slots     -- Sum injection: allocates tagged value
ir-stack-requirement (case-ir f g) = ir-stack-requirement f +ℕ ir-stack-requirement g  -- Case: max of branch requirements
ir-stack-requirement terminal = 0         -- Terminal: just returns unit
ir-stack-requirement initial = 0          -- Initial: unreachable (Void input)
ir-stack-requirement (curry _ _) = pair-slots    -- Closure creation: allocates closure
ir-stack-requirement apply = pair-slots          -- Function application: needs space for body
ir-stack-requirement arr = 0              -- Arr: just coerces type
ir-stack-requirement (fold-ir _) = 1             -- Fold: allocates Fix wrapper (1 slot pointer)
ir-stack-requirement unfold-ir = 0        -- Unfold: just returns unwrapped value
ir-stack-requirement (free-heap _) = 0    -- Deallocation: no stack needed
ir-stack-requirement (Prim _) = pair-slots       -- Primitives: may allocate result

-- Stack requirement for composition equals sum of sub-requirements
∘-stack-req : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-stack-requirement (g ∘ f) ≡ ir-stack-requirement f +ℕ ir-stack-requirement g
∘-stack-req f g = refl

-- Stack requirement for pair equals sum of sub-requirements plus pair-slots
⟨,⟩-stack-req : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) →
  ir-stack-requirement (⟨ f , g ⟩ m) ≡ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots
⟨,⟩-stack-req f g m = refl

-- Capacity lemma for pair: converts capacity proof to expanded form
-- Uses associativity: slot + (rf + rg + ps) = ((slot + rf) + rg) + ps
⟨,⟩-capacity-for-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) (slot cap : ℕ) →
  slot +ℕ ir-stack-requirement (⟨ f , g ⟩ m) ≤ cap →
  slot +ℕ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots ≤ cap
⟨,⟩-capacity-for-pair f g m slot cap pf =
  let rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      ps = pair-slots
      -- slot + (rf + rg + ps) = slot + ((rf + rg) + ps)
      -- We need: ((slot + rf) + rg) + ps
      step1 : slot +ℕ (rf +ℕ rg +ℕ ps) ≤ cap
      step1 = pf
      step2 : slot +ℕ ((rf +ℕ rg) +ℕ ps) ≤ cap
      step2 = step1  -- definitionally equal
      step3 : (slot +ℕ (rf +ℕ rg)) +ℕ ps ≤ cap
      step3 = subst (_≤ cap) (sym (+-assoc slot (rf +ℕ rg) ps)) step2
      step4 : ((slot +ℕ rf) +ℕ rg) +ℕ ps ≤ cap
      step4 = subst (λ x → x +ℕ ps ≤ cap) (sym (+-assoc slot rf rg)) step3
  in step4

-- | ir-stack-requirement is bounded by pair-slots * ir-size
-- TODO: Full proof requires porting type-slots-for-mode from old X86v3.IR
postulate
  ir-req-≤-pair-slots*size : ∀ {A B} (ir : IR A B) → ir-stack-requirement ir ≤ pair-slots *ℕ ir-size ir

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
fromOnceIR Once.arr = arr
fromOnceIR (Once.Prim name) = Prim name

------------------------------------------------------------------------
-- Summary
--
-- CCC.IR = Once.IR + free-heap
--
-- Key properties:
--   - Prim is opaque (just a name)
--   - eval is parameterized by PrimSem (NO postulates!)
--   - To evaluate Prim, you must provide its semantics via PrimSem
--   - This ensures no one can "cheat" - no Prim without semantics
--   - AllocMode is phantom in semantics
--   - free-heap is semantically a no-op
--   - fromOnceIR converts Once.IR → CCC.IR
--
-- Architecture:
--   - Domain compilers (Arith, etc.) provide their own PrimSem
--   - Backend uses PrimProofProvider that extends PrimSem with proofs
--   - No postulates needed anywhere in the chain!
------------------------------------------------------------------------
