# Type System in Once

## Current Foundation

Once's type system is built on:

1. **Natural Transformations** - Programs are morphisms in a category
2. **The 12 Generators** - Primitive operations (id, compose, fst, snd, pair, inl, inr, case, terminal, initial, curry, apply)
3. **QTT (Quantitative Type Theory)** - Quantities 0, 1, w tracking resource usage
4. **Type Signatures as Assertions** - Signatures verify, don't change meaning (D007)

## Future Direction: Refinement Types

This document summarizes a design discussion about extending Once's type system while maintaining simplicity for users who don't need advanced features.

### The Question

Should Once support sized buffers like:

```
Buffer { size <= 1024 }    -- bounded size
concat : Buffer n * Buffer m -> Buffer (n + m)   -- size arithmetic
```

### Options Considered

#### Full Dependent Types

Types that depend on values, with type-level computation:

```
Vector : Nat -> Type -> Type
head : Vector (n + 1) a -> a
matmul : Matrix n m -> Matrix m k -> Matrix n k
```

**Pros:**
- Maximum expressiveness
- Can express any invariant

**Cons:**
- Compiler complexity (type checking may require term evaluation)
- Type inference becomes limited
- Steeper learning curve
- Doesn't align with "types don't change meaning" - dependent types can affect runtime

#### Refinement Types

Properties on types, checked at compile time, fully erased:

```
Buffer { size > 0 }           -- non-empty
Buffer { size <= 1024 }       -- bounded
Int { n >= 0 }                -- natural number
```

**Pros:**
- Simpler than full dependent types
- Always erased at runtime (zero cost)
- Covers many practical cases (sizes, bounds, non-null)
- Often decidable with SMT solvers
- Aligns with "types verify, don't change meaning"

**Cons:**
- Less expressive than full dependent types
- Can't express type-level computation like `n + m`

### Categorical Models

Three models were considered for extending Once categorically:

#### LCCC (Locally Cartesian Closed Categories)

- Direct model for full dependent types
- Extends CCC (which Once already uses)
- Must buy into dependent types everywhere

#### CwF (Categories with Families)

- Explicit about contexts and substitution
- Close to how type checkers are implemented
- Can add features incrementally
- More concrete/implementation-focused

#### Comprehension Categories

- Flexible about what counts as a "type family"
- Clear separation: morphisms compute, display maps verify
- Can start simple and add dependency incrementally
- Natural fit for refinement types

### Recommended Approach: Comprehension Categories

Comprehension categories fit Once best because:

1. **Incremental** - Start with simple types, add refinements later, full dependent types possible if needed
2. **Aligns with Once philosophy** - Display maps are properties that don't affect runtime
3. **Flexible** - Choose what level of dependency to support
4. **Hides complexity** - Simple users see simple types, power users can opt in

### The Incremental Path

```
Step 1: Simple types (current)
- The 12 generators
- Product, sum, function types
- No type-level computation

Step 2: Refinement types (future)
- Properties on types: Buffer { size > 0 }
- Always erased (display maps have no runtime content)
- Decidable checking (SMT-based)

Step 3: Full dependent types (if needed)
- Type families indexed by values
- Requires QTT 0-quantity for erasure
- More complex type checking
```

### Key Principle: Simple Users Unaffected

Most users write:

```
concat : Buffer * Buffer -> Buffer
concat a b = ...
```

They never see refinements unless they want them. Power users can opt in:

```
concat : Buffer {n} * Buffer {m} -> Buffer {n + m}
```

### What Refinements Can't Express

Refinements cover:
- Size bounds: `Buffer { size <= 1024 }`
- Non-empty: `List { length > 0 }`
- Numeric ranges: `Int { n >= 0 && n < 100 }`

Full dependent types add:
- Types computed from values: `TypeFromFormat fmt`
- Type-level functions: `Vector (n + m) a`
- Proofs as values: `Sorted xs`

For Once's practical goals (buffers, bare metal), refinements likely suffice.

### Erasure Guarantees

| Level | Runtime Cost | Complexity |
|-------|--------------|------------|
| Simple types | None | Low |
| Refinements | None (always erased) | Medium |
| Full dependent | May have cost (need 0-quantity) | High |

Refinements guarantee zero runtime overhead by design.

## Decision

**Defer implementation.** Keep current simple type system for now. When extending:

1. Use **comprehension categories** as the theoretical foundation
2. Start with **refinement types** (not full dependent types)
3. Ensure **simple users are unaffected** - refinements are opt-in
4. Guarantee **erasure** - refinements have no runtime cost

This preserves Once's simplicity while providing a clear path to more expressive types if needed.

## Related Documents

- [buffers.md](buffers.md) - Buffer and String design (motivates sized types)
- [memory.md](memory.md) - QTT and resource management
- [overview.md](overview.md) - Language overview and three strata
