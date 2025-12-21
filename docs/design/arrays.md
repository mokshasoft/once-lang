# Array Design in Once

## Philosophy: Arrays Are Not Effects

**The Haskell Mistake**: Treating array mutation as an "effect" requiring IO/ST monads. This adds ceremony without benefit for systems programming.

**Once's Approach**: Arrays are values. Mutation is computation, not I/O.

## The Key Insight

Effects (`Eff`) are for interacting with the **external world**:
- Console I/O
- File system
- Network
- System calls

Array mutation is **internal computation**:
- Just moving bits in memory
- Deterministic
- No external interaction

Therefore, array operations should be **pure functions**, not wrapped in `Eff`.

## Quantitative Types Handle Mutation

Once uses Quantitative Type Theory (QTT) to track resource usage:

| Quantity | Meaning | Array Behavior |
|----------|---------|----------------|
| `^0` | Erased | Compile-time only |
| `^1` | Linear | In-place mutation |
| `^ω` | Shared | Copy-on-write |

The compiler infers quantities automatically. No annotations needed for common cases.

### Linear Arrays (^1)

When an array is used linearly (consumed exactly once), the compiler can safely mutate it in place:

```once
-- The returned array reuses the same memory as the input
write : Array A * Int * A -> Array A

-- Linear usage enables in-place update
let arr1 = write (arr, (0, 42)) in  -- arr consumed here
let arr2 = write (arr1, (1, 43)) in -- arr1 consumed here
arr2                                 -- final array
```

### Shared Arrays (^ω)

When an array is used multiple times, the compiler must copy on write to preserve referential transparency.

## API Design

### Pure Operations

All element-level operations are pure functions:

```once
-- Read element at index (unchecked)
read : Array A * Int -> A

-- Write element at index, returns updated array
write : Array A * Int * A -> Array A

-- Swap two elements, returns updated array
swap : Array A * Int * Int -> Array A

-- Get array length
length : Array A -> Int
```

### Allocation (Effectful)

Allocation interacts with the memory allocator, which is external state:

```once
-- Allocate n-element array (uses memory)
alloc : Int -> IO (Array A)

-- Free array (returns memory)
free : Array A -> IO Unit
```

### Bounds Checking (Orthogonal)

Bounds checking is a separate concern from the array type:

```once
-- Unchecked (like C) - undefined behavior on out-of-bounds
read : Array A * Int -> A
write : Array A * Int * A -> Array A

-- Checked - returns Maybe or sum type
readChecked : Array A * Int -> A + OutOfBounds
writeChecked : Array A * Int * A -> Array A + OutOfBounds
```

Users choose based on their needs:
- Unchecked for performance-critical inner loops
- Checked for safety at API boundaries

## Stratum Placement

Array primitives live in `Strata/Interpretations/Linux/` because:
- They need platform-specific C implementations
- Different on bare metal vs Linux vs WASM

But they are **pure** (not wrapped in `Eff`) because:
- Array mutation is computation, not I/O
- Deterministic behavior
- No external world interaction

Interpretations can have both:
- **Pure primitives**: arrays, arithmetic (platform-specific but deterministic)
- **Impure primitives**: files, console (platform-specific and non-deterministic)

## Comparison with Other Languages

| Language | Array Mutation | Overhead | Notes |
|----------|---------------|----------|-------|
| Haskell | IO/ST monad | High ceremony | Must lift pure code |
| Rust | Borrow checker | Compile-time | Safe but complex |
| C | Direct | None | Unsafe |
| **Once** | QTT + pure | None | Safe via linearity |

### Why Not Haskell's Approach?

Haskell conflates "state mutation" with "I/O effects":

```haskell
-- Haskell requires IO or ST for mutable arrays
writeArray :: MArray a e m => a Int e -> Int -> e -> m ()

-- Even though array writes are:
-- - Deterministic (no external interaction)
-- - Local (only affects this array)
-- - Predictable (same inputs → same outputs)
```

This adds ceremony without benefit. You need `runST` or stay in `IO` even for pure array algorithms.

### Once's Approach

```once
-- Pure function, no ceremony needed
processArray : Array Int -> Array Int
processArray = \arr ->
  let arr1 = write (arr, (0, 42)) in
  let arr2 = write (arr1, (1, 43)) in
  arr2

-- QTT ensures:
-- - Linear usage → in-place mutation (efficient)
-- - Shared usage → copy-on-write (safe)
```

## Implementation Notes

### C Code Generation

Array operations compile to direct memory access:

```c
// read : Array A * Int -> A
int64_t once_readInt(OnceBuffer arr, int64_t idx) {
    return ((int64_t*)arr.data)[idx];
}

// write : Array A * Int * A -> Array A
OnceBuffer once_writeInt(OnceBuffer arr, int64_t idx, int64_t val) {
    ((int64_t*)arr.data)[idx] = val;
    return arr;  // Same buffer, updated in place
}
```

### QTT Optimization

The compiler's linearity analysis determines copy behavior:

1. **Static analysis**: Track array usage through the program
2. **Linear path**: Generate in-place update code
3. **Shared path**: Generate copy-before-write code

This happens at compile time with zero runtime overhead for linear arrays.

## Design Decisions

- **D042**: Typed Arrays (`Array A`) - type parameter for element type
- **D044**: Pure Functional Arrays - not wrapped in `Eff`
- **D038**: Monomorphization - `read`/`write` dispatch to type-specific implementations

## See Also

- [Quantitative Types](./type-system.md#quantitative-types)
- [Effects](./io.md)
- [Decision Log](../compiler/decision-log.md)
