# Splitting Large Mutual Blocks in Agda

## The Problem

Agda's type-checking complexity for mutual blocks is **O(n²)** where n is the number of mutually recursive functions. This becomes prohibitive for large mutual blocks, especially when sized types are disabled (which provides 10-100x speedup elsewhere).

### Example Complexity

- **12 mutually recursive functions**: O(12²) = O(144)
- **8 functions in one block**: O(8²) = O(64)
- **4 functions in one block**: O(4²) = O(16)

Even with sized types disabled, an 8-function mutual block can timeout during type-checking.

### The Core Constraint

Agda requires all mutually recursive functions to be in the same `mutual` block in the same file. You cannot split mutual recursion across files directly.

## The Solution: Abstract Dispatcher Pattern

The key insight is to **break the circular dependency chain** using an abstract interface with postulates. This allows each implementation module to work independently against an abstract interface, which is later wired together concretely.

### Architecture

```
Once/Backend/X86/Correct/MutualIR/
├── Dispatcher.agda        -- Abstract interface (postulates)
├── Compose.agda          -- Implements compose using abstract dispatcher
├── Pair.agda             -- Implements pair using abstract dispatcher
├── Case.agda             -- Implements case using abstract dispatcher
└── ConcreteDispatcher.agda  -- Wires everything together (small mutual block)
```

### How It Works

1. **Abstract Interface** (`Dispatcher.agda`): Define abstract (postulated) versions of the mutual dispatcher functions
2. **Implementation Modules** (`Compose.agda`, `Pair.agda`, `Case.agda`): Each imports the abstract interface and implements its functions independently
3. **Concrete Dispatcher** (`ConcreteDispatcher.agda`): Small mutual block that instantiates the abstract interface with concrete implementations

### Complexity Reduction

For our x86 backend mutual block (12 functions):

- **Original**: O(12²) = O(144)
- **Two-file split**: O(8²) + O(4²) = O(80) ❌ Still too large
- **Abstract dispatcher**: O(2²) + O(2²) + O(3²) + O(2²) = O(21) ✅ **4x better!**

## Step-by-Step Guide

### Step 1: Create Dispatcher Interface

Create `Dispatcher.agda` with abstract postulated signatures:

```agda
module Once.Backend.X86.Correct.MutualIR.Dispatcher where

-- Standard imports
open import Once.Type
open import Once.IR
-- ... other imports

postulate
  -- | Abstract dispatcher for non-stateful IR execution
  run-ir-star-at-offset-abstract : ∀ {A B} (ir : IR A B)
      (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- | Abstract dispatcher for stateful IR execution
  run-ir-star-at-offset-s-abstract : ∀ {A B} (ir : IR A B)
      (prefix suffix : Program)
      (addr-in : Word) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ addr-in →
    encode x ≡ addr-in →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ addr-out ] ∃[ s' ] IRStarResultS ir prog s s' addr-out (length prefix)
```

**Key Point**: These are `postulate`d (abstract). Implementation modules will use these without knowing the concrete implementation.

### Step 2: Create Implementation Modules

Each implementation module imports the abstract dispatcher and implements its functions:

**`Compose.agda`**:

```agda
module Once.Backend.X86.Correct.MutualIR.Compose where

-- Import abstract dispatcher
open import Once.Backend.X86.Correct.MutualIR.Dispatcher

-- Implement compose using abstract dispatcher for recursive calls
run-compose-star-direct : ∀ {A B C} (f : IR A B) (g : IR B C)
    (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) → ...
run-compose-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  -- Use run-ir-star-at-offset-abstract for recursive call to f
  let (s₁ , res-f) = run-ir-star-at-offset-abstract f prefix' suffix' x s ...
  -- Use run-ir-star-at-offset-abstract for recursive call to g
      (s₂ , res-g) = run-ir-star-at-offset-abstract g prefix'' suffix'' y s₁ ...
  in s₂ , compose-result
```

**`Pair.agda`**:

```agda
module Once.Backend.X86.Correct.MutualIR.Pair where

open import Once.Backend.X86.Correct.MutualIR.Dispatcher

-- Implement pair using abstract dispatcher for recursive calls
run-pair-star-direct : ∀ {A B C} (f : IR A B) (g : IR A C)
    (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) → ...
run-pair-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  -- Use run-ir-star-at-offset-abstract for recursive calls
  let (s₁ , res-f) = run-ir-star-at-offset-abstract f prefix' suffix' x s ...
      (s₂ , res-g) = run-ir-star-at-offset-abstract g prefix'' suffix'' x s₁ ...
  in s₂ , pair-result
```

**`Case.agda`**:

```agda
module Once.Backend.X86.Correct.MutualIR.Case where

open import Once.Backend.X86.Correct.MutualIR.Dispatcher

-- Implement case using abstract dispatcher for recursive calls
run-case-star-direct : ∀ {A B C} (f : IR A C) (g : IR B C)
    (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) → ...
run-case-star-direct f g prefix suffix (inj₁ a) s ... =
  -- Recursive call to f using abstract dispatcher
  run-ir-star-at-offset-abstract f prefix' suffix' a s ...
run-case-star-direct f g prefix suffix (inj₂ b) s ... =
  -- Recursive call to g using abstract dispatcher
  run-ir-star-at-offset-abstract g prefix' suffix' b s ...
```

### Step 3: Wire Together with Concrete Dispatcher

Create a **small** mutual block that wires the concrete implementations to the abstract interface:

**`ConcreteDispatcher.agda`** (or main `MutualIR.agda`):

```agda
module Once.Backend.X86.Correct.MutualIR where

-- Import implementation modules
open import Once.Backend.X86.Correct.MutualIR.Compose
open import Once.Backend.X86.Correct.MutualIR.Pair
open import Once.Backend.X86.Correct.MutualIR.Case

-- Small mutual block: wire abstract to concrete
mutual
  -- Concrete dispatcher delegates to implementation modules
  run-ir-star-at-offset : ∀ {A B} (ir : IR A B)
      (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) → ...
  run-ir-star-at-offset (id {A}) prefix suffix x s ... =
    run-id-star {A} prefix suffix x s ...
  run-ir-star-at-offset (g ∘ f) prefix suffix x s ... =
    run-compose-star-direct f g prefix suffix x s ...
  run-ir-star-at-offset ⟨ f , g ⟩ prefix suffix x s ... =
    run-pair-star-direct f g prefix suffix x s ...
  run-ir-star-at-offset [ f , g ] prefix suffix x s ... =
    run-case-star-direct f g prefix suffix x s ...
  -- ... other cases

  run-ir-star-at-offset-s : ∀ {A B} (ir : IR A B)
      (prefix suffix : Program) (addr-in : Word) (x : ⟦ A ⟧) (s : State) → ...
  run-ir-star-at-offset-s (id {A}) prefix suffix addr-in x s ... =
    -- Convert non-stateful to stateful
    ...
  run-ir-star-at-offset-s (g ∘ f) prefix suffix addr-in x s ... =
    -- Use compose implementation (stateful version)
    ...
  -- ... other cases
```

**Key Point**: This mutual block is SMALL (just 2 functions: the two dispatchers). The heavy lifting is done in the separate implementation modules which type-check independently.

## Benefits

1. **Reduced Complexity**: From O(n²) to O(k₁²) + O(k₂²) + ... where kᵢ << n
2. **Independent Compilation**: Each implementation module compiles independently
3. **Better Structure**: Clear separation of concerns
4. **Maintainability**: Easier to understand and modify individual components
5. **Incremental Compilation**: Agda can cache each module separately

## Real-World Example: X86 Backend

In the Once language x86-64 backend, we had a 2423-line mutual block with 12 functions:

**Original Structure** (MutualIR.agda, O(144)):
- run-compose-star-direct (compose)
- run-compose-star-direct-s (compose stateful)
- run-pair-star-direct (pair)
- run-pair-star-direct-s (pair stateful)
- run-case-inl-star (case left)
- run-case-inr-star (case right)
- run-case-star-direct (case dispatcher)
- run-curry-star-direct (curry)
- run-apply-star-direct (apply)
- run-ir-star-at-offset (main dispatcher)
- run-ir-star-at-offset-s (stateful dispatcher)
- convert-to-stateful (helper)

**After Split** (O(21)):
- **Dispatcher.agda**: 2 postulates (abstract interface)
- **Compose.agda**: 2 functions (mutual block, O(4))
- **Pair.agda**: 2 functions (mutual block, O(4))
- **Case.agda**: 3 functions (mutual block, O(9))
- **MutualIR.agda**: 2 functions (mutual block, O(4))

Total: O(4) + O(4) + O(9) + O(4) = O(21) vs O(144) — **~7x improvement!**

## Common Pitfalls

### ❌ Circular Dependencies in Imports

```agda
-- Compose.agda
open import Once.Backend.X86.Correct.MutualIR.Pair  -- ❌ Creates circular import!

-- Pair.agda
open import Once.Backend.X86.Correct.MutualIR.Compose  -- ❌ Circular!
```

**Fix**: Both should only import `Dispatcher.agda` for recursive calls.

### ❌ Forgetting TERMINATING Pragma

If you're using an abstract dispatcher, Agda can't see the recursive structure:

```agda
{-# TERMINATING #-}
run-compose-star-direct f g ... =
  run-ir-star-at-offset-abstract f ...  -- Agda can't see f is smaller than (g ∘ f)
```

**Fix**: Use `{-# TERMINATING #-}` pragmatically. The structural recursion is guaranteed by the IR structure, but Agda can't see through the abstraction.

### ❌ Not Making the Concrete Dispatcher Small Enough

```agda
-- ❌ Still too much logic in the concrete dispatcher
run-ir-star-at-offset (g ∘ f) prefix suffix x s ... =
  -- Inline compose implementation here  -- ❌ Defeats the purpose!
  let s₁ = step (compile-x86 f) s
      s₂ = step (mov ...) s₁
      ...
  in ...
```

**Fix**: Keep the concrete dispatcher as a thin delegation layer. Put all logic in implementation modules.

## When to Use This Pattern

Use the abstract dispatcher pattern when:

1. **Large mutual blocks** (> 6 functions) causing compilation timeouts
2. **Sized types are disabled** (for performance reasons)
3. **Clear subsystems** exist within the mutual block (e.g., compose/pair/case)
4. **Structural recursion** is guaranteed (so TERMINATING is sound)

Don't use this pattern when:

1. Mutual block is small (< 4 functions) — overhead not worth it
2. No clear subsystem boundaries exist
3. Sized types are enabled and working well
4. Functions have complex interdependencies that don't factor cleanly

## Related Patterns

- **Foundation Module Pattern**: Consolidate common imports (see Foundation.agda in x86 backend)
- **Explicit Type Annotations**: Reduce type inference burden (complements this pattern)
- **TERMINATING Pragma**: Accept pragmatic compromises when structural recursion is obvious
- **StarBase Pattern**: Factor out common result types to reduce duplication

## References

- `formal/Once/Backend/X86/Correct/MutualIR/Dispatcher.agda` - Abstract interface example
- `formal/Once/Backend/X86/Correct/MutualIR.agda.backup` - Original monolithic version
- `docs/formal/plans/x86-backend-verification-plan.md` - Overall architecture

## Summary

The abstract dispatcher pattern breaks large mutual blocks into smaller, independently type-checkable pieces by:

1. Creating an abstract interface with postulates
2. Having each subsystem implement against the abstract interface
3. Wiring everything together in a small concrete mutual block

This achieves **4-7x complexity reduction** while maintaining clear architecture and enabling independent compilation.
