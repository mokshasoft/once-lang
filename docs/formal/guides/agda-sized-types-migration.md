# Migrating Away from Sized Types in Agda

## Overview

This guide explains why the Once project is transitioning away from Agda's sized types feature and how to update code that uses them.

## What Are Sized Types?

Sized types were an experimental Agda feature designed to:
- **Prove termination** of recursive functions on potentially infinite data
- **Ensure productivity** of corecursive definitions (like streams)
- **Track data structure sizes** to guarantee recursive calls are on smaller inputs

### Example of Sized Type Usage (Old Style)

```agda
{-# OPTIONS --sized-types #-}

open import Size

-- Sized streams
data Stream {i : Size} (A : Set) : Set where
  _∷_ : A → Stream {i} A → Stream {↑ i} A

-- Size annotation ∞ means "infinite size"
repeat : ∀ {A} → A → Stream {∞} A
repeat x = x ∷ repeat x

-- Size variable ensures termination
take : ∀ {i A} → ℕ → Stream {i} A → List A
take zero    _       = []
take (suc n) (x ∷ xs) = x ∷ take n xs
```

## Why We're Moving Away

### 1. **Soundness Issues**

Sized types have had **critical bugs** that broke Agda's consistency:
- Multiple soundness bugs discovered over the years
- Can lead to proofs of `⊥` (false) in some edge cases
- The feature was never fully stabilized

### 2. **Poor Interactions with Other Features**

Sized types interact poorly with:
- **Unification** - Can cause confusing type errors
- **Instance search** - Doesn't work well with type classes
- **Cubical Agda** - Incompatible with modern cubical type theory
- **Reflection** - Difficult to handle in metaprogramming

### 3. **Complexity Without Clear Benefits**

- **Confusing semantics** - Hard to understand size constraints
- **Inference issues** - Size variables often need explicit annotation
- **Maintenance burden** - Adds complexity to the codebase
- **Better alternatives exist** - Modern Agda has superior approaches

### 4. **Community Consensus**

The Agda community has largely moved away from sized types:
- Not recommended in official Agda documentation
- Rarely used in modern Agda libraries
- Being phased out of the standard library

## Modern Alternatives

### 1. **Structural Termination Checking** (Preferred)

Agda's default termination checker analyzes structural recursion patterns.

**Before (with sized types):**
```agda
{-# OPTIONS --sized-types #-}
open import Size

data Tree {i : Size} (A : Set) : Set where
  leaf : A → Tree {i} A
  node : Tree {i} A → Tree {i} A → Tree {↑ i} A

depth : ∀ {i A} → Tree {i} A → ℕ
depth (leaf x) = 0
depth (node l r) = 1 + max (depth l) (depth r)
```

**After (structural recursion):**
```agda
-- No sized types needed!
data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

-- Agda accepts this because l and r are structurally smaller
depth : ∀ {A} → Tree A → ℕ
depth (leaf x) = 0
depth (node l r) = 1 + max (depth l) (depth r)
```

### 2. **Copatterns for Coinductive Types**

For infinite data structures, use copatterns instead of sized types.

**Before (with sized types):**
```agda
{-# OPTIONS --sized-types #-}
open import Size

record Stream {i : Size} (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream {i} A

repeat : ∀ {i A} → A → Stream {i} A
Stream.head (repeat x) = x
Stream.tail (repeat x) = repeat x
```

**After (with copatterns and guardedness):**
```agda
{-# OPTIONS --guardedness #-}

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

-- Guardedness checker ensures productivity
repeat : ∀ {A} → A → Stream A
head (repeat x) = x
tail (repeat x) = repeat x

-- Pattern matching on coinductive records (copatterns)
zipWith : ∀ {A B C} → (A → B → C) → Stream A → Stream B → Stream C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)
```

### 3. **Well-Founded Recursion**

For complex termination arguments, use well-founded recursion with accessibility predicates.

**Example:**
```agda
open import Induction.WellFounded
open import Data.Nat.Properties using (<-wellFounded)

-- Ackermann function using well-founded recursion
ackermann : ℕ → ℕ → ℕ
ackermann = <-rec _ _ λ m rec-m →
  <-rec _ _ λ n rec-n →
    case m of λ where
      zero → suc n
      (suc m') → case n of λ where
        zero → rec-m m' <-m (suc zero)
        (suc n') → rec-m m' <-m (rec-n n' <-n)
```

### 4. **Termination Pragmas** (When Necessary)

As a last resort, you can explicitly mark terminating functions:

```agda
{-# TERMINATING #-}
collatz : ℕ → ℕ
collatz 0 = 0
collatz 1 = 0
collatz n with even? n
... | true  = 1 + collatz (n / 2)
... | false = 1 + collatz (3 * n + 1)
```

**Warning:** Only use this when you're certain the function terminates but Agda can't prove it!

## Migration Checklist

When removing sized types from a module:

### Step 1: Remove Sized Type Annotations

```diff
- {-# OPTIONS --sized-types #-}

  module MyModule where

- open import Size

  -- Your code here
```

### Step 2: Remove Size Parameters from Data Types

```diff
- data List {i : Size} (A : Set) : Set where
+ data List (A : Set) : Set where
    []  : List A
-   _∷_ : A → List {i} A → List {↑ i} A
+   _∷_ : A → List A → List A
```

### Step 3: Remove Size Parameters from Functions

```diff
- map : ∀ {i A B} → (A → B) → List {i} A → List {i} B
+ map : ∀ {A B} → (A → B) → List A → List B
  map f []       = []
  map f (x ∷ xs) = f x ∷ map f xs
```

### Step 4: Replace IR ∞ with IR

```diff
- compositionality : ∀ {A B C} (g : IR ∞ B C) (f : IR ∞ A B)
+ compositionality : ∀ {A B C} (g : IR B C) (f : IR A B)
                   → eval (g ∘ f) ≡ eval g ∘ eval f
```

### Step 5: Remove Size Variables from Implicit Parameters

```diff
- type-preservation : ∀ {i A B} (f : IR A B) (x : ⟦ A ⟧) → ⟦ B ⟧
+ type-preservation : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧) → ⟦ B ⟧
  type-preservation f x = eval f x
```

### Step 6: Test Compilation

```bash
cd formal/
make clean
make  # Verify everything type-checks
```

## Common Errors and Solutions

### Error: `InfectiveImport`

**Error message:**
```
Importing module M using the --sized-types flag from a module which does not.
```

**Solution:** The imported module still has sized types. Remove them from that module first.

### Error: Termination checking fails

**Before:** Sized types were helping prove termination.

**Solutions:**
1. **Restructure for structural recursion** - Make recursive calls obviously smaller
2. **Use well-founded recursion** - Provide an explicit termination proof
3. **Use `{-# TERMINATING #-}`** - Only if you're certain it terminates

### Error: Productivity checking fails (coinductive types)

**Before:** Sized types were ensuring productivity.

**Solutions:**
1. **Enable guardedness:** Add `{-# OPTIONS --guardedness #-}`
2. **Use copatterns:** Pattern match on the fields of coinductive records
3. **Restructure definition:** Ensure constructors are guarded by coinductive fields

## Examples from Once Codebase

### Example 1: TypeSystem.Soundness Module

**Before:**
```agda
{-# OPTIONS --sized-types #-}
module Once.TypeSystem.Soundness where

open import Size
open import Once.IR

compositionality : ∀ {A B C} (g : IR ∞ B C) (f : IR ∞ A B) (x : ⟦ A ⟧)
                 → eval (g ∘ f) x ≡ eval g (eval f x)
compositionality g f x = refl
```

**After:**
```agda
module Once.TypeSystem.Soundness where

open import Once.IR

compositionality : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                 → eval (g ∘ f) x ≡ eval g (eval f x)
compositionality g f x = refl
```

### Example 2: TypeSystem.Typing Module

**Before:**
```agda
{-# OPTIONS --sized-types #-}
module Once.TypeSystem.Typing where

open import Size
```

**After:**
```agda
module Once.TypeSystem.Typing where
-- Size import removed, no other changes needed
```

## Best Practices

### ✅ DO

- **Use structural recursion** whenever possible
- **Use copatterns** for coinductive types
- **Use well-founded recursion** for complex termination proofs
- **Enable `--guardedness`** for coinductive definitions
- **Document non-trivial termination arguments** in comments

### ❌ DON'T

- **Add `{-# OPTIONS --sized-types #-}`** to new modules
- **Import `Size`** module
- **Use `∞` or `↑` size constructors**
- **Add size parameters `{i : Size}`** to data types
- **Use sized types for simple structural recursion**

## Further Reading

- [Agda Documentation: Termination Checking](https://agda.readthedocs.io/en/latest/language/termination-checking.html)
- [Agda Documentation: Coinduction](https://agda.readthedocs.io/en/latest/language/coinduction.html)
- [Agda Issue #1201: Problems with sized types](https://github.com/agda/agda/issues/1201)
- [Why Sized Types Are Problematic](https://github.com/agda/agda/issues/1428)

## Summary

Sized types were an experimental feature that has proven problematic. Modern Agda provides better alternatives:

| Use Case | Old Approach | Modern Approach |
|----------|-------------|-----------------|
| Termination | Sized types | Structural recursion |
| Coinduction | Sized types | Copatterns + guardedness |
| Complex recursion | Sized types | Well-founded recursion |
| Last resort | Sized types | `{-# TERMINATING #-}` |

By migrating away from sized types, the Once codebase becomes:
- ✅ More maintainable
- ✅ More compatible with modern Agda features
- ✅ Less prone to soundness issues
- ✅ Easier for newcomers to understand

---

**Related:** See commit `053002b` for the removal of sized types from `Once.TypeSystem.Soundness` and `Once.TypeSystem.Typing` modules.
