# Memory in Once

## The Challenge

Natural transformations are substrate-independent by design. They describe **what** to compute, not **how**. But memory is the most substrate-dependent thing there is:

- Stack vs heap
- Garbage collection vs manual management
- Ownership vs borrowing
- Allocation strategies

How can Once handle memory while preserving substrate independence?

## The Proposed Solution: Quantitative Type Theory

**Once adopts Quantitative Type Theory (QTT) integrated with natural transformations.**

Quantities track resource usage at the type level:

| Quantity | Meaning | Memory Implication |
|----------|---------|-------------------|
| `0` | Erased (compile-time only) | No runtime representation |
| `1` | Linear (exactly once) | Stack allocation, no GC |
| `ω` | Unrestricted (any number) | May need GC or refcounting |

This is the same approach used in Idris 2, but integrated with Once's categorical foundation.

## Why QTT?

### The Core Insight

Quantities are **semantic**, not implementation details:

```
f : A^1 → B    -- "f uses its input exactly once"
```

This statement is true in every target language. The **mechanism** differs:

| Target | What `^1` Means |
|--------|-----------------|
| C | Value consumed, can stack allocate |
| Rust | Ownership transfer |
| JavaScript | Used once (GC still handles it) |
| Bare metal | Stack slot, no free needed |

Substrate independence preserved.

### What Quantities Give Us

1. **Guaranteed linearity** - Type system enforces it
2. **Memory safety** - Can't double-free or leak linear resources
3. **Optimization info** - Compiler knows what's copyable
4. **Choice** - Use `ω` when you need copying, `1` when you don't

## Quantities in Detail

### The Semiring

Quantities form a semiring with addition and multiplication:

```
-- Addition (using a value in multiple branches)
0 + r = r
1 + 1 = ω         -- using twice = unrestricted
ω + r = ω         -- unrestricted dominates

-- Multiplication (using a value through composition)
0 · r = 0         -- erased stays erased
1 · r = r         -- linear preserves quantity
ω · r = ω         -- unrestricted needs unrestricted
```

### How Quantities Propagate

```
-- If f uses x twice, and g uses its input once:
g : B^1 → C
f : A^ω → B       -- f copies, needs unrestricted

compose g f : A^ω → C    -- composition inherits ω
```

### The Three Quantities

**Zero (0) - Erased**

```
-- Type-level computation, no runtime cost
length : {0 n : Nat} → Vector n A → Nat

-- n exists at compile time, disappears at runtime
-- Enables dependent types without runtime overhead
```

**One (1) - Linear**

```
-- Resource must be used exactly once
openFile  : Path^1 → File^1 + Error
closeFile : File^1 → Unit

-- Can't forget to close (linear File must be consumed)
-- Can't close twice (File consumed by first close)
```

**Omega (ω) - Unrestricted**

```
-- Standard functional programming
map : (A^ω → B) → List A → List B

-- Function may be called multiple times
-- Values may be copied
```

## Generators with Quantities

The 12 generators have quantity-aware signatures:

### Category Structure

```
id : A^1 →₁ A
-- Uses input exactly once, produces output once

compose : (B^1 →₁ C)^1 → (A^1 →₁ B)^1 →₁ (A^1 →₁ C)
-- Linear in both function arguments
-- Resulting function is linear if components are
```

### Products

```
fst : (A^1 × B^0)^1 →₁ A
-- Uses the pair once
-- Extracts A (used once), discards B (must be erasable/unrestricted)

snd : (A^0 × B^1)^1 →₁ B
-- Symmetric

pair : (C^r →₁ A)^1 → (C^s →₁ B)^1 →₁ (C^{r+s} →₁ A × B)
-- If both branches use C, quantities ADD
-- pair id id : C^ω →₁ C × C  (uses C twice, needs unrestricted)
```

### Coproducts

```
inl : A^1 →₁ A + B
inr : B^1 →₁ A + B
-- Injections are linear

case : (A^1 →₁ C)^1 → (B^1 →₁ C)^1 →₁ (A + B)^1 →₁ C
-- Only ONE branch executes
-- So input can be linear (not copied between branches)
```

### Terminal and Initial

```
terminal : A^0 →₁ Unit
-- DISCARDS A, so A must be erasable or unrestricted
-- This is why linear values can't be silently dropped

initial : Void^1 →₁ A
-- Void has no values, so this is vacuously linear
```

### Exponentials

```
curry : ((A × B)^1 →₁ C)^1 →₁ (A^1 →₁ (B^1 →₁ C))
apply : ((A^1 →₁ B) × A)^1 →₁ B
```

### Key Derived Operations

```
diagonal : A^ω →₁ A × A
-- COPIES A, so A must be unrestricted
-- diagonal = pair id id

swap : (A × B)^1 →₁ B × A
-- Linear: just rearranges, no copy or discard
-- swap = pair snd fst  (but with careful quantity tracking)

constant : A^1 → B^0 →₁ A
-- Discards B, so B must be erasable
```

## Inference vs Annotation

### Default: Inference

Programmers write normal code. The compiler infers quantities:

```
-- You write
swap : A × B → B × A
swap = pair snd fst

-- Compiler infers
swap : (A × B)^1 → (B × A)^1
-- "This is linear"
```

### Optional: Annotation

When you need guarantees (API boundaries, verification):

```
-- You write with explicit quantity
export swap : (A × B)^1 → (B × A)^1
swap = pair snd fst

-- Compiler VERIFIES your claim
-- If code isn't actually linear, compile error
```

### The Workflow

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│   1. Write code (no annotations)                                │
│                                                                 │
│   2. Compiler infers quantities                                 │
│                                                                 │
│   3. Query: "once analyze myFunction"                           │
│      → Shows inferred quantities                                │
│      → Reports: "Linear: yes/no"                                │
│      → Reports: "Can compile without GC: yes/no"                │
│                                                                 │
│   4. Optionally add annotations for guarantees                  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Memory Abstractions

Raw `malloc`/`free` is problematic because nothing connects them:

```
-- Dangerous (not exposed in Once)
malloc : Size → Ptr
free   : Ptr → Unit
-- Double free? Leak? Use after free? No protection.
```

### Safe Abstractions

Once provides safe wrappers in the Interpretations layer:

**Regions**

```
-- Everything allocated in region freed together
withRegion : (Region^1 → A)^1 → External A
allocIn    : Region^1 → Size → (Ptr^1 × Region^1)

-- Usage
withRegion $ \region →
  let (ptr1, region') = allocIn region 100
      (ptr2, region'') = allocIn region' 200
  in use ptr1 ptr2    -- both freed when withRegion exits
```

**Arenas (Bump Allocation)**

```
-- Fast allocation, bulk free
withArena : Size → (Arena^1 → A)^1 → External A
bump      : Arena^1 → Size → (Ptr^1 × Arena^1)

-- Common in compilers, games, request handlers
```

**Owned Boxes**

```
-- Heap allocation with ownership tracking
Box    : Type → Type
new    : A^1 → External (Box A)^1
unbox  : (Box A)^1 → A^1
-- Box freed when consumed
```

**Borrowed References**

```
-- Temporary access without ownership transfer
Ref    : Type → Type
borrow : (Box A)^1 → (Ref A → B)^1 → (B × (Box A)^1)
-- Original Box returned after borrow scope
```

### The Primitive Layer

These abstractions are built on hidden primitives:

```
-- In Interpretations, NOT exported to users
primitive raw_malloc : Size → External (RawPtr + Null)
primitive raw_free   : RawPtr → External Unit

-- Safe abstractions use these internally
-- Users never see raw_malloc/raw_free
```

## Compilation Strategies

### Linear Code (Quantity 1)

```
f : A^1 → B^1
```

Compiles to:
- **C**: Stack allocation, pass by value or move
- **Rust**: Ownership transfer
- **LLVM**: SSA (inherently linear)
- **Bare metal**: Fixed stack slots

No GC, no refcounting, no heap.

### Unrestricted Code (Quantity ω)

```
f : A^ω → B
```

Compiles to:
- **C with GC**: Use Boehm GC or similar
- **Rust**: Clone trait, Rc/Arc
- **JavaScript**: Normal (GC built-in)
- **Bare metal**: Must use arena/region strategy

### Erased Code (Quantity 0)

```
f : {0 n : Nat} → Vector n A → ...
```

Compiles to:
- Nothing. The `n` parameter disappears entirely.
- Type-level computation only.

## Graded Natural Transformations

### Mathematical Foundation

QTT integrates with natural transformations via **graded categories**:

```
-- Standard natural transformation
α : F ⇒ G
α_A : F A → G A

-- Graded natural transformation
α : F ⇒ᵣ G
α_A : F A →ᵣ G A    -- with quantity r
```

### Graded Naturality

The naturality square still commutes, with quantities tracked:

```
        F A ───α_A──→ G A
         │             │
    F f  │             │  G f
         ↓             ↓
        F B ───α_B──→ G B

-- If f : A →ᵣ B, the whole square respects r
```

### Graded Functor Laws

```
fmap id = id                              -- still holds
fmap (compose f g) = compose (fmap f) (fmap g)  -- still holds

-- Quantities compose correctly
fmap (f : A →ᵣ B) : F A →ᵣ F B
```

### Graded Categorical Laws

All standard laws hold with quantity tracking:

```
compose f id = f
compose id f = f
compose f (compose g h) = compose (compose f g) h

-- Plus quantity laws
compose (f : B →ᵣ C) (g : A →ₛ B) : A →ᵣₛ C   -- quantities multiply
```

## Verification

### What Needs Proving

```coq
(* Semiring laws for quantities *)
Theorem quantity_semiring : Semiring Quantity.

(* Type system soundness *)
Theorem preservation :
  Γ ⊢ e : τ @ r → e ⟶ e' → Γ ⊢ e' : τ @ r.

(* Linearity guarantee *)
Theorem linear_no_copy :
  Γ ⊢ e : τ @ 1 → ¬(copies e).

(* Codegen correctness *)
Theorem compile_preserves_quantity :
  ∀ e r, quantity e = r → respects_quantity (compile e) r.
```

### Estimated Effort

| Component | Lines of Coq | Notes |
|-----------|--------------|-------|
| Semiring laws | ~200 | Well-known |
| Graded CCC | ~1000 | Extends standard CCC proofs |
| QTT type system | ~2000 | Based on Idris 2 formalization |
| Quantity inference | ~1000 | Constraint solving |
| Codegen | ~500 per target | Similar to non-QTT |
| **Total** | ~5000-8000 | 2-3x non-QTT Once |

More complex than non-QTT, but still tractable. The proofs build on existing QTT literature.

## Alternative Approaches Considered

### Option A: Linearity as External Analysis

```
-- Compiler ignores quantities
-- Separate tool analyzes after compilation
> once-analyze linearity myFunction
```

**Pros**: Simpler compiler, simpler verification
**Cons**: Can't enforce at API boundaries, two-phase workflow

### Option B: Mandatory Linear Types (Cogent-style)

```
-- All resources must be linear
-- No unrestricted types for resources
```

**Pros**: Maximum safety
**Cons**: Restrictive, some algorithms awkward

### Option C: Rust-style Ownership (Not Quantities)

```
-- Borrow checker instead of quantities
-- Lifetimes track references
```

**Pros**: Proven in practice
**Cons**: Complex, not as clean categorically, lifetimes are hard

### Chosen: Option D - QTT with Inference

```
-- Quantities in type system
-- Inference by default
-- Annotations when needed
```

**Pros**:
- Enforced at type level
- Inference hides complexity
- Clean categorical semantics
- Flexible (0, 1, ω spectrum)

**Cons**:
- More complex compiler
- More verification effort

**Why chosen**: Best fit for Once's principles. Quantities are semantic (substrate-independent), categorical (graded CCCs), and flexible (inference + optional annotation).

## Comparison with Other Systems

| System | Approach | Trade-off |
|--------|----------|-----------|
| **C** | Manual malloc/free | Unsafe, error-prone |
| **Rust** | Ownership + borrowing | Safe, complex lifetimes |
| **Haskell** | GC everywhere | Simple, but can't do bare metal |
| **Cogent** | Mandatory linearity | Safe, but restrictive |
| **Idris 2** | QTT | Flexible, complex |
| **Once** | QTT + NT + inference | Flexible, semantic, categorical |

Once's approach is closest to Idris 2, but:
- Built on natural transformations (not dependent types)
- Focused on multi-target compilation
- Inference-first (annotations optional)

## Summary

| Aspect | Once's Approach |
|--------|-----------------|
| **Foundation** | Graded natural transformations |
| **Quantities** | 0 (erased), 1 (linear), ω (unrestricted) |
| **Default** | Inference (no annotations needed) |
| **Guarantees** | Optional annotations for enforcement |
| **Memory primitives** | Safe abstractions (regions, arenas, Box) |
| **Raw malloc** | Hidden in Interpretations |
| **Substrate independence** | Preserved (quantities are semantic) |
| **Verification** | ~5-8K Coq (graded CCC laws) |

Memory in Once is **tracked by quantities, inferred by default, enforced when annotated, and abstracted safely**. The categorical foundation extends cleanly to handle resources without sacrificing substrate independence.
