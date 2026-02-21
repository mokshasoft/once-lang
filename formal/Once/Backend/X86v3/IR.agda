------------------------------------------------------------------------
-- Once.Backend.X86v3.IR
--
-- IR language definition for SlotMachine POC.
--
-- This IR includes AllocMode on allocating constructors (⟨_,_⟩, inl, inr,
-- curry) to enable stack/heap dispatch based on escape analysis results.
--
-- AllocMode is phantom in semantics (eval ignores it) but affects memory
-- layout at runtime: Stack mode uses inline unboxed representation while
-- Heap mode uses boxed pointers.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (m<m+n; m<n+m; +-comm; n<1+n; <-trans; m+n≤o⇒m≤o; m+n≤o⇒n≤o; +-monoˡ-<; +-monoʳ-<)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Once.Backend.X86v3.Types public

------------------------------------------------------------------------
-- Allocation Mode
--
-- Specifies where compound values should be allocated:
--   Stack: Inline on the stack (non-escaping values, unboxed)
--   Heap:  On the heap with pointer indirection (escaping values, boxed)
--
-- Escape analysis determines which mode to use. Initially all allocations
-- use Heap mode for safety. Escape analysis rewrites Heap → Stack for
-- values proven not to escape.
------------------------------------------------------------------------

data AllocMode : Set where
  Stack : AllocMode  -- Allocate inline on stack (non-escaping)
  Heap  : AllocMode  -- Allocate on heap (escaping)

------------------------------------------------------------------------
-- IR Language
--
-- AllocMode is embedded in allocating constructors:
--   ⟨_,_⟩_   : pair construction
--   inl-ir   : left injection
--   inr-ir   : right injection
--   curry    : closure creation
--
-- Non-allocating constructors (fst-ir, snd-ir, case-ir, apply, etc.)
-- don't need AllocMode since they consume/transform existing values.
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
  -- Note: Using _+_ from Once.Type, with _⊕_ as alias
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

  -- Primitive operations (opaque to backend)
  -- Name is for debugging/emission. Semantics handled via postulate.
  Prim : ∀ {A B} → String → IR A B

infixr 9 _∘_
infixr 4 ⟨_,_⟩_

------------------------------------------------------------------------
-- Semantic Evaluation
--
-- AllocMode is phantom in semantics - it only affects runtime memory
-- layout, not the computed values. Escape analysis preserves semantics
-- because AllocMode doesn't change eval.
------------------------------------------------------------------------

-- Postulate for Prim semantics - will be connected to external FFI
postulate
  prim-semantics : ∀ {A B} → String → ⟦ A ⟧ → ⟦ B ⟧

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
eval (Prim name) x = prim-semantics name x

------------------------------------------------------------------------
-- Evaluation Laws
--
-- These laws hold for any AllocMode since AllocMode is phantom.
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
--
-- AllocMode doesn't affect size - it's phantom for termination purposes.
------------------------------------------------------------------------

ir-size : ∀ {A B} → IR A B → ℕ
ir-size id = 1
ir-size (g ∘ f) = 1 +ℕ ir-size g +ℕ ir-size f
ir-size (⟨ f , g ⟩ _) = 1 +ℕ ir-size f +ℕ ir-size g  -- AllocMode ignored
ir-size fst-ir = 1
ir-size snd-ir = 1
ir-size (inl-ir _) = 1   -- AllocMode ignored
ir-size (inr-ir _) = 1   -- AllocMode ignored
ir-size (case-ir f g) = 1 +ℕ ir-size f +ℕ ir-size g
ir-size terminal = 1
ir-size initial = 1
ir-size (curry f _) = 2 +ℕ ir-size f  -- Extra slot for apply's pair allocation
ir-size apply = 1
ir-size (fold-ir _) = 1  -- AllocMode ignored
ir-size unfold-ir = 1
ir-size (Prim _) = 1

------------------------------------------------------------------------
-- Size Lemmas
------------------------------------------------------------------------

-- Helper: 0 < ir-size for all IR
ir-size-pos : ∀ {A B} (ir : IR A B) → 0 < ir-size ir
ir-size-pos id = s≤s z≤n
ir-size-pos (g ∘ f) = s≤s z≤n
ir-size-pos (⟨ f , g ⟩ _) = s≤s z≤n
ir-size-pos fst-ir = s≤s z≤n
ir-size-pos snd-ir = s≤s z≤n
ir-size-pos (inl-ir _) = s≤s z≤n
ir-size-pos (inr-ir _) = s≤s z≤n
ir-size-pos (case-ir f g) = s≤s z≤n
ir-size-pos terminal = s≤s z≤n
ir-size-pos initial = s≤s z≤n
ir-size-pos (curry f _) = s≤s z≤n
ir-size-pos apply = s≤s z≤n
ir-size-pos (fold-ir _) = s≤s z≤n
ir-size-pos unfold-ir = s≤s z≤n
ir-size-pos (Prim _) = s≤s z≤n

-- Helper: n ≤ m + n (flip of m≤m+n)
n≤m+n : ∀ m n → n ≤ m +ℕ n
n≤m+n m n = subst (n ≤_) (+-comm n m) (m≤m+n n m)
  where open import Data.Nat.Properties using (m≤m+n; +-comm)

-- For compose: f is smaller than g ∘ f
-- ir-size (g ∘ f) = suc (ir-size g + ir-size f)
-- Need: ir-size f < suc (ir-size g + ir-size f)
-- i.e.: ir-size f ≤ ir-size g + ir-size f
∘-f-smaller : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-size f < ir-size (g ∘ f)
∘-f-smaller f g = s≤s (n≤m+n (ir-size g) (ir-size f))

-- For compose: g is smaller than g ∘ f
-- Need: ir-size g ≤ ir-size g + ir-size f
∘-g-smaller : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-size g < ir-size (g ∘ f)
∘-g-smaller f g = s≤s (m≤m+n (ir-size g) (ir-size f))
  where open import Data.Nat.Properties using (m≤m+n)

-- For pair: f is smaller than ⟨ f , g ⟩ m
-- ir-size (⟨ f , g ⟩ m) = suc (ir-size f + ir-size g)
-- Need: ir-size f ≤ ir-size f + ir-size g
⟨,⟩-f-smaller : ∀ {A B C} (f : IR A B) (g : IR A C) {m : AllocMode} →
  ir-size f < ir-size (⟨ f , g ⟩ m)
⟨,⟩-f-smaller f g = s≤s (m≤m+n (ir-size f) (ir-size g))
  where open import Data.Nat.Properties using (m≤m+n)

-- For pair: g is smaller than ⟨ f , g ⟩ m
-- Need: ir-size g ≤ ir-size f + ir-size g
⟨,⟩-g-smaller : ∀ {A B C} (f : IR A B) (g : IR A C) {m : AllocMode} →
  ir-size g < ir-size (⟨ f , g ⟩ m)
⟨,⟩-g-smaller f g = s≤s (n≤m+n (ir-size f) (ir-size g))

-- For curry: f is smaller than curry f m
-- ir-size (curry f m) = 2 + ir-size f, so we need ir-size f < 2 + ir-size f
curry-smaller : ∀ {A B C} (f : IR (A * B) C) {m : AllocMode} →
  ir-size f < ir-size (curry f m)
curry-smaller f = <-trans (n<1+n (ir-size f)) (n<1+n (suc (ir-size f)))
  where open import Data.Nat.Properties using (<-trans)

-- For case: f is smaller than case-ir f g
-- ir-size (case-ir f g) = suc (ir-size f + ir-size g)
case-f-smaller : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size f < ir-size (case-ir f g)
case-f-smaller f g = s≤s (m≤m+n (ir-size f) (ir-size g))
  where open import Data.Nat.Properties using (m≤m+n)

-- For case: g is smaller than case-ir f g
case-g-smaller : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size g < ir-size (case-ir f g)
case-g-smaller f g = s≤s (n≤m+n (ir-size f) (ir-size g))

------------------------------------------------------------------------
-- Stack Requirement
--
-- Computes the maximum stack slots needed to execute an IR in the
-- current frame. This is used to ensure frame capacity is sufficient.
--
-- Key insight: Each IR case allocates a known number of slots:
--   - id, fst, snd, terminal: 0 (no allocation)
--   - compose: f's slots + g's slots (sequential execution)
--   - pair: f's slots + g's slots + 2 (for the pair structure)
--   - curry: 2 (for the closure structure; body runs in new frame)
--   - apply: 2 (for forming env-arg pair) + body's requirement
--
-- NOTE on apply: The body's requirement is NOT statically known at the
-- apply IR itself - it depends on which closure is being applied.
-- Two approaches:
--   1. Track max body requirement in the program (global bound)
--   2. Track body requirement in closure validity
--
-- For this definition, we use 0 for apply's "body contribution" since
-- the body runs in the same frame but its requirement must be accounted
-- for separately (via program-level capacity bounds).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Slot sizes
--
-- For unboxed representation, slot sizes depend on result types.
-- Constants kept for backwards compatibility in capacity proofs.
------------------------------------------------------------------------

-- Fixed slot size for capacity calculations (pair-slots * ir-size)
pair-slots : ℕ
pair-slots = 2

-- Closure slots (always boxed: env-ptr + code-ptr)
closure-slots : ℕ
closure-slots = 2

------------------------------------------------------------------------
-- Type slots for allocation mode
--
-- Stack mode: uses inline unboxed representation (stack-type-slots)
-- Heap mode: uses boxed pointers (heap-type-slots)
------------------------------------------------------------------------

type-slots-for-mode : AllocMode → Type → ℕ
type-slots-for-mode Stack = stack-type-slots
type-slots-for-mode Heap = heap-type-slots

-- Stack requirement for an IR (slots allocated in current frame)
-- Uses type-slots-for-mode to dispatch on AllocMode
ir-stack-requirement : ∀ {A B} → IR A B → ℕ
ir-stack-requirement id = 0
ir-stack-requirement (g ∘ f) = ir-stack-requirement f +ℕ ir-stack-requirement g
ir-stack-requirement {_} {B * C} (⟨ f , g ⟩ m) =
  ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ type-slots-for-mode m (B * C)
ir-stack-requirement fst-ir = 0
ir-stack-requirement snd-ir = 0
ir-stack-requirement {A} {A' + B} (inl-ir m) = type-slots-for-mode m (A' + B)  -- allocates tag + payload
ir-stack-requirement {B} {A + B'} (inr-ir m) = type-slots-for-mode m (A + B')  -- allocates tag + payload
ir-stack-requirement (case-ir f g) = ir-stack-requirement f +ℕ ir-stack-requirement g  -- branches are mutually exclusive
ir-stack-requirement terminal = 0
ir-stack-requirement initial = 0  -- never executed (absurd)
ir-stack-requirement {_} {B ⇒[ _ ] C} (curry f m) = type-slots-for-mode m (B ⇒[ Many ] C)  -- closure = 2 slots
ir-stack-requirement apply = pair-slots  -- forms (env, arg) pair; body requirement separate
ir-stack-requirement {_} {Fix F} (fold-ir m) = type-slots-for-mode m (Fix F)  -- Stack: inline F, Heap: pointer
ir-stack-requirement unfold-ir = 0  -- dereferences pointer, no allocation
ir-stack-requirement (Prim _) = 0  -- primitives handle their own allocation

------------------------------------------------------------------------
-- Stack Requirement Lemmas
------------------------------------------------------------------------

-- Compose: requirement is sum of components
∘-stack-req : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-stack-requirement (g ∘ f) ≡ ir-stack-requirement f +ℕ ir-stack-requirement g
∘-stack-req f g = refl

-- Pair: requirement is sum of components plus type-slots for result (mode-dependent)
⟨,⟩-stack-req : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) →
  ir-stack-requirement (⟨ f , g ⟩ m) ≡ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ type-slots-for-mode m (B * C)
⟨,⟩-stack-req f g m = refl

-- After running f in compose, g still has enough capacity
-- If we start with capacity for f + g, after f we have capacity for g
∘-capacity-after-f : ∀ {A B C} (f : IR A B) (g : IR B C) (start-slot capacity : ℕ) →
  start-slot +ℕ ir-stack-requirement (g ∘ f) ≤ capacity →
  (start-slot +ℕ ir-stack-requirement f) +ℕ ir-stack-requirement g ≤ capacity
∘-capacity-after-f f g start cap pf = subst (_≤ cap) (sym (+-assoc start (ir-stack-requirement f) (ir-stack-requirement g))) pf
  where open import Data.Nat.Properties using (+-assoc)

-- After running f and g in pair, we still have capacity for pair allocation
-- Mode-dependent version
⟨,⟩-capacity-for-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) (start-slot capacity : ℕ) →
  start-slot +ℕ ir-stack-requirement (⟨ f , g ⟩ m) ≤ capacity →
  start-slot +ℕ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ type-slots-for-mode m (B * C) ≤ capacity
⟨,⟩-capacity-for-pair {_} {B} {C} f g m start cap pf = subst (_≤ cap) eq pf
  where
    open import Data.Nat.Properties using (+-assoc)
    rf = ir-stack-requirement f
    rg = ir-stack-requirement g
    ps = type-slots-for-mode m (B * C)
    -- ir-stack-requirement (⟨ f , g ⟩ m) = rf + rg + type-slots-for-mode m (B * C)
    -- So: start + (rf + rg + ps) ≡ start + rf + rg + ps
    eq : start +ℕ (rf +ℕ rg +ℕ ps) ≡ start +ℕ rf +ℕ rg +ℕ ps
    eq = trans (sym (+-assoc start (rf +ℕ rg) ps))
               (cong (_+ℕ ps) (sym (+-assoc start rf rg)))

------------------------------------------------------------------------
-- Summary
--
--   IR           - inductive data type
--   eval         - denotational semantics
--   eval-*       - evaluation laws
--   ir-size      - structural size metric
--   *-smaller    - size ordering lemmas
--   ir-stack-requirement - stack capacity
--   *-stack-req  - requirement laws
--   *-capacity-* - capacity arithmetic
------------------------------------------------------------------------
