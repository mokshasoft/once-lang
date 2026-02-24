# Loops and Linear Iteration in Once

This document describes how iteration (loops) relates to the categorical IR, and the design choices for compiling recursive structures to efficient imperative code.

## Table of Contents

1. [The Problem](#the-problem)
2. [Fold as Iteration](#fold-as-iteration)
3. [Two Compilation Strategies](#two-compilation-strategies)
4. [Proof Architecture](#proof-architecture)
5. [The Prim Escape Hatch](#the-prim-escape-hatch)
6. [Large Records and Tuples](#large-records-and-tuples)

## The Problem

Functional programs express iteration through recursion schemes like `map`, `fold`, and `unfold`. These are elegant and compositional, but naively compiled they produce recursive function calls rather than efficient loops.

For linear types (where each element is used exactly once), we want:
```
map f xs  →  while loop (in-place iteration)
```

The question: should this transformation happen within the CCC IR, or at code generation?

## Fold as Iteration

In the categorical IR, a map over a list is:

```agda
-- List A = Fix (Unit + (A × _))
-- map f : List A → List B

map f = fold ∘ [ inl , inr ∘ (f × id) ] ∘ unfold
```

This is semantically equivalent to a while loop when the type is linear:

```c
// Equivalent imperative code
while (list != nil) {
    *current = f(*current);
    current = next(current);
}
```

The key insight: **fold over a linear functor IS iteration**. There's no sharing, no re-traversal, just sequential processing. The categorical representation doesn't need to change for this to be true.

## Two Compilation Strategies

### Strategy 1: Categorical IR + Smart Codegen

Keep the IR categorical, let code generation recognize patterns:

```
IR:     fold ∘ [ inl , inr ∘ (f × id) ]
         ↓ codegen pattern match
ASM:    while loop
```

**Advantages:**
- IR stays simple and categorical
- All CCC optimizations apply before codegen
- Fusion rules work naturally (fold ∘ unfold = id, etc.)
- CCC proofs are untouched

**The codegen recognizes:**
- fold over linear list with algebra `[inl, inr ∘ (f × id)]` → map loop
- fold over linear list with algebra `[base, combine ∘ (f × id)]` → fold loop
- Other patterns as needed

### Strategy 2: Explicit Loop via Prim

Transform to an explicit loop primitive earlier in the pipeline:

```
IR:     map f
         ↓ earlier pass
IR:     Prim "while_loop" (with f embedded)
         ↓ codegen
ASM:    while loop
```

**Advantages:**
- Explicit control over when loops are introduced
- Can inject pre-optimized loop implementations
- Useful when pattern is too complex for codegen to recognize

**Disadvantages:**
- Prim is opaque, fewer optimizations apply
- Must trust the embedded code is correct

## Proof Architecture

The critical insight is that **proofs stay local** with Strategy 1:

### Layer 1: CCC Proofs (Hard, Done)

The categorical laws are proven once:
```agda
fold ∘ unfold = id
fst ∘ ⟨ f , g ⟩ = f
-- etc.
```

These proofs are complex (~100x the rest of the compiler) but stable. Strategy 1 does not touch them.

### Layer 2: Codegen Proofs (Local, Per-Pattern)

Each codegen pattern has its own correctness proof:
```agda
-- "This while loop implements fold over this algebra"
codegen-fold-map-correct :
  ∀ f xs → exec (emit-while-loop f) xs ≡ eval (fold ∘ [inl, inr ∘ (f × id)]) xs
```

These are **translation proofs**, not categorical proofs. They show assembly/C code correctly implements the IR semantics. Much simpler and isolated.

### Why This Matters

| Change | CCC Proofs | Codegen Proofs |
|--------|------------|----------------|
| Add optimization rule | May need update | Untouched |
| Add codegen pattern | Untouched | Add new local proof |
| Add new IR construct | Complex updates | Depends on construct |

Strategy 1 keeps loop compilation in the "codegen proofs" column, avoiding CCC complexity.

## The Prim Escape Hatch

The `Prim` constructor serves as an escape hatch:

```agda
data IR : Type → Type → Set where
  -- ... categorical constructors ...
  Prim : String → IR A B  -- Opaque primitive
```

**Design philosophy:** Higher levels of the compiler can transform code to assembly and pass it through the CCC structure via Prim. The categorical core handles composition and optimization around Prims, while the Prim contents are opaque.

**Use cases:**
- Complex patterns that codegen can't recognize
- Platform-specific optimized implementations
- Pre-compiled library functions
- FFI calls

**Example:** A highly-optimized SIMD loop might be injected as:
```agda
Prim "simd_map_f32_avx512"
```

The CCC laws still apply to compositions involving this Prim, even though we can't see inside it.

## Large Records and Tuples

A related design question: how to represent records with many fields?

### Nested Tuples (Categorical)

```agda
record {a: A, b: B, c: C}  →  A × (B × C)
```

- All categorical laws apply
- Accessing field `c` requires `snd ∘ snd`
- Associativity normalization could help: `(A × B) × C ≅ A × (B × C)`

### Prim with Offsets (Pragmatic)

```agda
record {a: A, b: B, c: C}  →  Prim "MyRecord"
field_c                    →  Prim "offset_8"
```

- Struct is atomic, direct field access
- No nested tuple overhead
- Loses some optimization granularity

### Hybrid Approach

- Small tuples (2-3 fields): Nested products, full optimization
- Large records (4+ fields): Prim with offset-based access
- Can still have optimization rules: `Prim "field_a" ∘ Prim "mk_record" → extract first arg`

## Summary

1. **Fold is already iteration** for linear types - no IR change needed
2. **Codegen pattern recognition** keeps proofs local and simple
3. **Prim is the escape hatch** for complex or pre-optimized code
4. **Proof layering** (CCC vs codegen) is the key architectural insight
5. **Don't touch CCC proofs** unless absolutely necessary - that's where complexity lives
