# OCP-0003: Total and Productive IR via Layered Architecture

**Author:** [TBD]
**Status:** Draft
**Created:** 2026-03-10
**Updated:** 2026-03-17

---

## Summary

Restructure the IR into two distinct layers within `Once.CCC.IR`:

- **`Prim`** — The 12 CCC generators plus `Opaque` for primitive arrows (both pure `A → B` and effectful `Eff A B`)
- **`Poly`** — Polynomial functor operations: `μ`, `ν`, `In`, `Out`, `Cata`, `Ana`

Effects are **arrow-based**: the CCC structure provides arrow combinators (composition, products), and the type system distinguishes pure arrows (`A → B`) from effect arrows (`Eff A B`). The IR is about structure; types track semantics.

Remove general `Fold`/`Unfold` operations. This makes Once **total** (all functions terminate) and **productive** (all codata makes progress) by construction, while preserving all practically useful programs and enabling future dependent type extensions.

---

## Motivation

### The Problem with Turing Completeness

Once currently allows general recursion through `Fold`/`Unfold`, making it Turing complete. This means:

- Programs can loop forever (non-termination)
- No compile-time termination guarantees
- Harder to verify program properties
- Most infinite loops are bugs, not features

### The Insight

Turing completeness lets you write programs that:

1. Compute useful results (algorithms)
2. Loop forever (bugs)
3. Get stuck waiting (deadlocks)

Categories 2 and 3 are almost never intentional. A language that makes them **impossible to express** loses nothing of value while gaining strong guarantees.

### What Programs Actually Need

| Pattern | Mechanism | Example |
|---------|-----------|---------|
| Process finite data | `cata` (fold) | Sum a list |
| Generate finite data | `ana` (unfold) | Range 1..n |
| Generate infinite data | `ana` (unfold) | Stream of events |
| Transform then consume | `hylo` (fused) | Factorial |
| Fold with context | `para` | Safe tail |

These schemes cover virtually all recursive patterns in real software. General recursion adds only the ability to write bugs.

### Servers and Infinite Processes

A server that runs "forever" but handles each request correctly is not Turing complete — it's **productive codata**:

```
server : Stream Request → Stream Response
server = ana step
  where step reqs = (handleRequest (head reqs), tail reqs)
```

This is:
- Infinite (runs forever)
- Productive (always responds)
- Total (each handler terminates)
- NOT Turing complete (no unbounded computation)

### Alignment with D039 (Polynomial Functors)

Decision D039 chose **polynomial functors** for formal verification, which already requires:

- Strictly positive types only (no functions in recursive positions)
- Recursion via `cata` for termination
- Automatic `fmap` and induction principles

From `fix-semantics-options.md`:

> "Non-structural recursion: **Must use cata**" (for polynomial functors)

This proposal makes explicit in the IR what D039 already requires for verification.

### Enabling Dependent Types

Totality is **required** for consistent dependent types. All major proof assistants (Agda, Coq, Lean, Idris) enforce termination because non-termination lets you prove `False`:

```
-- If allowed, proves anything
loop : A
loop = loop

absurd : Void
absurd = loop  -- "proof" via non-termination
```

By enforcing totality through structured recursion schemes, this proposal enables Once's planned dependent type extensions (indexed types, Π/Σ, OTT, directed HoTT) without additional termination checking complexity.

---

## Proposal

### Layered IR Architecture

```
┌─────────────────────────────────────────────┐
│              User Code                      │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│           Once.CCC.IR                       │
│  ┌───────────────────────────────────────┐  │
│  │  Poly                                 │  │
│  │  μ, ν, In, Out, Cata, Ana            │  │
│  │  (total + productive)                 │  │
│  └───────────────────────────────────────┘  │
│  ┌───────────────────────────────────────┐  │
│  │  Prim                                 │  │
│  │  12 generators + Opaque               │  │
│  │  (trivially terminating)              │  │
│  └───────────────────────────────────────┘  │
│                                             │
│  Combined: IR = prim Prim.IR | poly Poly.IR │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│         Target Backends                     │
│       C, Rust, JS, WASM, ...                │
└─────────────────────────────────────────────┘
```

### Module Structure

```agda
module Once.CCC.IR where

  -- Layer 1: Primitives (trivially terminating)
  module Prim where
    data IR : Set where
      -- Category
      Id      : Type → IR
      Compose : IR → IR → IR

      -- Products
      Fst      : Type → Type → IR
      Snd      : Type → Type → IR
      Pair     : IR → IR → IR
      Terminal : Type → IR

      -- Coproducts
      Inl     : Type → Type → IR
      Inr     : Type → Type → IR
      Case    : IR → IR → IR
      Initial : Type → IR

      -- Exponentials
      Curry : Name → IR → IR
      Apply : Type → Type → IR

      -- Primitive arrows (pure A → B and effectful Eff A B)
      -- Effect distinction is in the TYPE, not the IR
      -- CCC combinators work uniformly on both arrow types
      Opaque : Name → IR

  -- Layer 2: Polynomial functors (total by construction)
  module Poly where
    -- Functor representation (polynomial functors per D039)
    data Functor : Set where
      FId    : Functor                    -- Identity: X (recursive position)
      FConst : Type → Functor             -- Constant: A
      FSum   : Functor → Functor → Functor -- Sum: F + G
      FProd  : Functor → Functor → Functor -- Product: F × G

    data IR : Set where
      -- Inductive (finite) data
      In   : Functor → IR                 -- In : F (μF) → μF
      Cata : Functor → Prim.IR → IR       -- cata alg : μF → A
                                          --   where alg : F A → A

      -- Coinductive (infinite) codata
      Out  : Functor → IR                 -- Out : νF → F (νF)
      Ana  : Functor → Prim.IR → IR       -- ana coalg : A → νF
                                          --   where coalg : A → F A

      -- Derived schemes (useful as primitives for optimization)
      Hylo : Functor → Prim.IR → Prim.IR → IR  -- hylo alg coalg : A → B
      Para : Functor → Prim.IR → IR            -- para alg : μF → A
      Apo  : Functor → Prim.IR → IR            -- apo coalg : A → νF

  -- Combined IR type (Option B: separate combined type for cleaner proofs)
  data IR : Set where
    prim : Prim.IR → IR
    poly : Poly.IR → IR
```

### Why This Structure

**Separate modules (`Prim` and `Poly`):**
- Each layer is independently verifiable
- `Prim` proofs don't mention `Poly`
- `Poly` proofs don't mention `Prim`
- Cleaner induction principles

**Combined `IR` type (not `lift`):**
- Cleaner proof structure — no `lift` case in every `Poly` proof
- True modularity — layers are isolated
- Combination happens at top level only

**`Opaque` for primitive arrows:**
- Single constructor for all external operations (arithmetic, strings, IO)
- Represents **primitive arrows** — external operations the IR doesn't look inside
- Pure vs effectful is a **typing** concern, not IR structure
- See "Arrow-Based Effects" section below

### Arrow-Based Effects

Once uses **arrows** for effects, which are more general than monads. The type system has two arrow types:

```
Pure arrow:     A → B        (function type)
Effect arrow:   Eff A B      (effectful computation from A to B)
```

**Key insight:** The CCC structure provides all arrow combinators:

| Arrow Combinator | CCC Derivation |
|------------------|----------------|
| `f >>> g` (sequence) | `Compose g f` |
| `f &&& g` (fanout) | `Pair f g` |
| `first f` | `Pair (Compose f Fst) Snd` |
| `f *** g` (parallel) | `Pair (Compose f Fst) (Compose g Snd)` |

This means **no separate arrow IR is needed** — the CCC generators work for both pure and effectful arrows. The IR is about structure (how arrows compose); the type system tracks semantics (pure vs effectful).

**`Opaque` is the primitive arrow:**

```agda
Opaque "add"      -- type: Nat → Nat → Nat      (pure arrow)
Opaque "readFile" -- type: Eff FilePath String   (effect arrow)
```

Both are "opaque arrows" — external operations the IR doesn't analyze. The type tells you which kind of arrow it is. All CCC combinators work uniformly on both.

### Type-Level Fixed Points

```agda
-- Recursive types (defined in the type system, not IR)
data RecType : Set where
  μ : Poly.Functor → RecType    -- Least fixed point (inductive/finite)
  ν : Poly.Functor → RecType    -- Greatest fixed point (coinductive/infinite)
```

### Functor Interpretation

```agda
-- ⟦F⟧ interprets a functor code as an actual type function
⟦_⟧ : Poly.Functor → Type → Type
⟦ FId ⟧ X       = X
⟦ FConst A ⟧ X  = A
⟦ FSum F G ⟧ X  = ⟦ F ⟧ X + ⟦ G ⟧ X
⟦ FProd F G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X
```

### Standard Data Types

All standard types from the Initial library are expressible:

```
-- Inductive types (finite, consumed via cata)
type Bool      = μ(FSum (FConst Unit) (FConst Unit))
type Maybe A   = μ(FSum (FConst Unit) (FConst A))
type List A    = μ(FSum (FConst Unit) (FProd (FConst A) FId))
type Nat       = μ(FSum (FConst Unit) FId)
type Tree A    = μ(FSum (FConst A) (FProd FId FId))

-- Coinductive types (infinite, produced via ana)
type Stream A  = ν(FProd (FConst A) FId)
type Colist A  = ν(FSum (FConst Unit) (FProd (FConst A) FId))
type Process I O = ν(FConst I → FProd (FConst O) FId)
```

### Guardedness Checking

For coinductive definitions (`ana`, `apo`), the compiler enforces **guardedness** to ensure productivity:

```
-- GOOD: Output produced before corecursive position
step : State → (Output × State)
step s = (produce s, next s)    -- ✓ guarded by product constructor

-- BAD: Corecursive call not behind constructor
step : State → (Output × State)
step s = step (modify s)        -- ✗ rejected: no guard
```

Guardedness ensures productivity — every corecursive definition always produces its next element when demanded.

#### Guardedness Rules

1. Every corecursive reference must appear under a constructor of the coinductive type's functor
2. No corecursive calls in function argument position
3. The "guard" is the outermost constructor of the coalgebra's result

```
-- Coalgebra for Stream: A → (A × Stream A)
-- The guard is the pair constructor (,)

-- GOOD: pair is the guard
natsCoalg n = (n, n + 1)  -- ✓ (n, ...) guards the recursive ...

-- BAD: no pair constructor
badCoalg n = if condition then badCoalg n else (n, n + 1)  -- ✗
```

### Mutual Recursion and Deadlock Prevention

#### Guarded Mutual Corecursion

Two servers exchanging messages are expressible if properly guarded:

```
-- GOOD: Each produces output before needing input from the other
serverA : Stream (Event + MsgFromB) → Stream (Response + MsgToB)
serverA = ana step
  where step events =
    let e = head events
        (out, toB) = processEvent e
    in ((out, toB), tail events)  -- ✓ produces before recurring

-- External events drive the system (no deadlock)
system : Stream Event → Stream Response
system events = filterResponses (serverA (merge (map Left events) fromB))
  where fromB = serverB (filterMsgsToB outputA)
```

#### What Cannot Be Expressed

Direct mutual function calls that would deadlock:

```
-- IMPOSSIBLE: requires general fix
handleA req = handleB req
handleB req = handleA req
```

This is **not expressible** with `cata`/`ana` — you cannot write mutually recursive functions without the structured schemes. This is a feature: the system prevents deadlocking ping-pong by construction.

#### Deadlock Analysis

| Pattern | With cata/ana | Reason |
|---------|---------------|--------|
| `f x = g x; g x = f x` | Not expressible | Needs general fix |
| Mutual streams, unguarded | Rejected | Fails guardedness |
| Mutual streams, guarded | Productive | Progress guaranteed |
| No external driver | Unproductive | Guardedness catches it |

---

## Alignment with Existing Design

### The Three Strata

The strata structure (from `libraries.md`) is preserved and clarified:

```
┌─────────────────────────────────────────────┐
│         Interpretations                     │  Effect arrows (Opaque with Eff A B types)
├─────────────────────────────────────────────┤
│         Initial                             │  Data types + operations (uses Poly)
├─────────────────────────────────────────────┤
│         Canonical                           │  Non-recursive combinators (pure Prim)
├─────────────────────────────────────────────┤
│         Once.CCC.IR.Poly                    │  μ, ν, cata, ana
├─────────────────────────────────────────────┤
│         Once.CCC.IR.Prim                    │  12 generators + Opaque (primitive arrows)
└─────────────────────────────────────────────┘
```

Note: The same `Opaque` constructor is used for both pure primitives (typed `A → B`) and effectful primitives (typed `Eff A B`). The stratum difference is in the types, not the IR structure.

### Canonical Library (Unchanged)

All morphisms in Canonical are non-recursive and remain in pure `Prim.IR`:

```
swap     : A × B → B × A           -- Pair Snd Fst
diagonal : A → A × A               -- Pair Id Id
assocL   : A × (B × C) → (A × B) × C
mirror   : A + B → B + A           -- Case Inr Inl
const    : A → B → A
flip     : (A → B → C) → B → A → C
```

No changes needed.

### Initial Library (Explicit Recursion)

Operations in Initial become explicit uses of `Poly.IR` recursion schemes:

| Current (Implicit) | Proposed (Explicit) |
|--------------------|---------------------|
| `foldr f z xs` | `Cata F (Case (const z) (uncurry f))` applied to `xs` |
| `map f xs` | `Cata F (Case (const nil) (λ(a,as) → cons (f a) as))` applied to `xs` |
| `filter p xs` | `Cata F (Case (const nil) (λ(a,as) → if p a then cons a as else as))` applied to `xs` |
| `length xs` | `Cata F (Case (const 0) (λ(_,n) → n+1))` applied to `xs` |
| `range lo hi` | `Ana F (λ(l,h) → if l >= h then inl () else inr (l, (l+1, h)))` applied to `(lo, hi)` |

The operations are the same; the recursion is now explicit and structured.

---

## Proof Engineering Benefits

### Why Option B (Separate Combined Type)

The combined `IR` type with `prim` and `poly` constructors (rather than `lift` inside `Poly`) provides cleaner proofs:

**With lift (Option A):**
```agda
poly-simulation : ∀ (p : Poly.IR) → Simulates p
poly-simulation (In ...)   = ...
poly-simulation (Cata ...) = ...
poly-simulation (lift p)   = prim-simulation p  -- appears in EVERY Poly proof
```

**With separate combined type (Option B):**
```agda
prim-simulation : ∀ (p : Prim.IR) → Simulates p  -- isolated
poly-simulation : ∀ (p : Poly.IR) → Simulates p  -- isolated

ir-simulation : ∀ (i : IR) → Simulates i
ir-simulation (prim p) = prim-simulation p
ir-simulation (poly p) = poly-simulation p
```

**Benefits:**
1. **True modularity** — `Poly` proofs don't mention `Prim` at all
2. **Cleaner induction** — each module's induction is self-contained
3. **Easier maintenance** — change `Prim` without touching `Poly` proofs
4. **Aligns with OCP-0004** — clear trust boundaries for minimal-trust verification

---

## Alignment with OCP-0004 (Minimal-Trust Verification)

The layered architecture directly supports OCP-0004's minimal TCB goal:

### Trust Boundaries

| Layer | TCB Addition | Verification |
|-------|--------------|--------------|
| `Prim.IR` | ~50 lines | CCC categorical laws (since 1960s) |
| `Poly.IR` | ~20 lines | Lambek's Lemma + coalgebra theorems (1968) |

### The IR IS Category Theory

From OCP-0004:

```
┌──────────────────────────┬──────────────────────────────────┐
│     Once Prim.IR         │     Category Theory              │
├──────────────────────────┼──────────────────────────────────┤
│ Id A                     │ id_A : A → A                    │
│ Compose g f              │ g ∘ f                           │
│ Pair f g                 │ ⟨f, g⟩ : C → A × B             │
│ Fst A B                  │ π₁ : A × B → A                  │
│ ...                      │ ...                              │
└──────────────────────────┴──────────────────────────────────┘

┌──────────────────────────┬──────────────────────────────────┐
│     Once Poly.IR         │     Category Theory              │
├──────────────────────────┼──────────────────────────────────┤
│ μF                       │ Initial F-algebra                │
│ In : F(μF) → μF          │ Algebra structure map            │
│ Cata alg                 │ Unique F-algebra morphism        │
│ νF                       │ Final F-coalgebra                │
│ Out : νF → F(νF)         │ Coalgebra structure map          │
│ Ana coalg                │ Unique F-coalgebra morphism      │
└──────────────────────────┴──────────────────────────────────┘
```

### Totality and Productivity ARE Definitional

```
Lambek's Lemma (1968):
    The structure map In : F(μF) → μF is an isomorphism.
    This means μF ≅ F(μF).
    Consequence: μF is well-founded (no infinite descent).
    Therefore: cata always terminates.

Dual (Final Coalgebras):
    The structure map Out : νF → F(νF) is an isomorphism.
    This means νF ≅ F(νF).
    Consequence: νF is productive (always has next element).
    Therefore: ana always makes progress (with guardedness).
```

These are mathematical facts, not implementation details.

---

## Dependent Types Compatibility

### Why Totality Enables Dependent Types

Dependent type systems require termination for logical consistency:

| System | Termination | Consistency |
|--------|-------------|-------------|
| Agda | Enforced by termination checker | Sound |
| Coq | Enforced by guard condition | Sound |
| Idris | Enforced by totality checker | Sound (in total mode) |
| Once + Poly | Enforced by construction | Sound |

All achieve the same result; Once achieves it structurally rather than via analysis.

### Compatibility Matrix

| Dependent Type Option | Compatibility | Notes |
|-----------------------|---------------|-------|
| **Indexed Types** | ✓ Perfect | `Vec n A` = indexed polynomial functor |
| **Simple Π/Σ** | ✓ Perfect | Type-level recursion via cata |
| **Refinement Types** | ✓ Perfect | Orthogonal to recursion |
| **OTT** | ✓ Good | Quotients as setoids, funext orthogonal |
| **Cubical** | ◐ Mostly | Standard HITs work, exotic ones need care |
| **Directed HoTT** | ✓ Best | Aligns with linearity beautifully |

---

## Impact

### Performance

| Aspect | Impact |
|--------|--------|
| Recursion overhead | Unchanged (schemes compile to loops) |
| Optimization | Improved (fusion rules are explicit) |
| Code generation | Simplified (known patterns) |
| Verification | Simplified (no termination proofs) |

### Expressivity

| | Before | After |
|---|--------|-------|
| **Least** (simplest program) | Same | Same |
| **Most** (maximum capability) | Turing complete | Total + Productive |

This is an **intentional reduction** in raw expressivity. The removed programs are:

- Infinite loops (bugs)
- Non-productive codata (bugs)
- Unstructured recursion (usually bugs)

None of these are useful programs.

### Formal Verification

| Aspect | Before | After |
|--------|--------|-------|
| Termination proofs | Required | Eliminated (by construction) |
| Productivity proofs | Required | Eliminated (by guardedness) |
| Correctness proofs | Full IR | Just verify algebras/coalgebras |
| Proof complexity | High | Reduced |

---

## Trade-offs

### Gained

- **All functions terminate** — by construction, not by analysis
- **All codata is productive** — guardedness enforced structurally
- **Simpler verification** — no termination metrics needed
- **Clearer program structure** — recursion patterns are explicit
- **Dependent types enabled** — consistent logic without extra checking
- **Deadlock-free corecursion** — unguarded mutual recursion impossible
- **Uniform arrow structure** — CCC combinators work for both pure and effectful arrows
- **Alignment with D039** — IR matches verification requirements
- **Minimal TCB** — supports OCP-0004 trust boundaries

### Lost

- **General recursion** — must use schemes (rarely a limitation)
- **Some exotic algorithms** — need restructuring (rare in practice)
- **Self-interpreters** — need fuel parameter (niche use case)
- **"Flexibility" to write bugs** — this is not actually a loss

---

## Compilation Strategy

### Poly.IR → Target Code

Recursion schemes compile to efficient target-language patterns:

#### Cata (Fold)

```c
// cata compiles to a loop consuming the structure
Value cata_list(Algebra alg, List xs) {
    Value acc = alg.nil_case;
    while (!is_nil(xs)) {
        acc = alg.cons_case(head(xs), acc);
        xs = tail(xs);
    }
    return acc;
}
```

#### Ana (Unfold)

```c
// ana compiles to demand-driven production
Stream ana_stream(Coalgebra coalg, Seed s) {
    return (Stream){
        .head = coalg(s).fst,
        .tail_thunk = { .coalg = coalg, .seed = coalg(s).snd }
    };
}
```

#### Hylo (Fused)

```c
// hylo fuses ana and cata — no intermediate structure
Value hylo(Algebra alg, Coalgebra coalg, Seed s) {
    FunctorValue fv = coalg(s);
    if (is_base_case(fv)) {
        return alg.base(fv);
    } else {
        return alg.recursive(fv.head, hylo(alg, coalg, fv.seed));
    }
}
```

### Optimization: Deforestation

The key optimization is **hylo fusion** (deforestation):

```
-- Before: allocates intermediate structure
result = cata alg (ana coalg seed)

-- After: fused, no intermediate allocation
result = hylo alg coalg seed

-- Rewrite rule (always valid)
cata alg ∘ ana coalg = hylo alg coalg
```

This is a straightforward rewrite rule that eliminates intermediate data structures.

### Backend-Specific Patterns

| Scheme | C | Rust | JavaScript |
|--------|---|------|------------|
| cata | while loop | iterator fold | reduce |
| ana | lazy struct | iterator | generator |
| hylo | fused loop | fused iterator | direct recursion |

---

## Optimizer Architecture

The layered IR naturally leads to a layered optimizer architecture.

### Phased Optimization

```
User Code
    ↓
┌─────────────────────────────┐
│ 1. Poly Optimizer           │  High-level: fusion, deforestation
└─────────────┬───────────────┘
              ↓
┌─────────────────────────────┐
│ 2. Cross-Layer Rules        │  Algebra/coalgebra optimization
└─────────────┬───────────────┘
              ↓
┌─────────────────────────────┐
│ 3. Prim Optimizer           │  Low-level: categorical laws
└─────────────┬───────────────┘
              ↓
          Code Gen
```

### Phase 1: Poly Optimizer

Handles structural transformations that change the shape of recursion:

```
-- Deforestation (the big win)
cata alg ∘ ana coalg           →  hylo alg coalg

-- Functor fusion
map f ∘ map g                  →  map (f ∘ g)
filter p ∘ filter q            →  filter (λx → p x ∧ q x)

-- Cata computation
cata alg ∘ In                  →  alg ∘ fmap (cata alg)

-- Ana computation
Out ∘ ana coalg                →  fmap (ana coalg) ∘ coalg
```

### Phase 2: Cross-Layer Rules

Optimizations that span Poly and Prim, working on the algebras and coalgebras:

```
-- Push post-processing into algebra
f ∘ cata alg                   →  cata (f ∘ alg)  -- when f is cheap

-- Simplify algebra using Prim laws
cata (case (const z) (compose f (pair fst snd)))
    →  cata (case (const z) f)  -- pair fst snd = id
```

### Phase 3: Prim Optimizer

Handles local simplifications using categorical laws:

```
-- Identity laws
compose f id                   →  f
compose id f                   →  f

-- Product laws
fst (pair f g)                 →  f
snd (pair f g)                 →  g
pair fst snd                   →  id  -- eta for products

-- Coproduct laws
case f g (inl a)               →  f a
case f g (inr b)               →  g b
case inl inr                   →  id  -- eta for coproducts

-- Exponential laws
apply (pair (curry f) g)       →  compose f (pair id g)
```

### Verification Strategy

Each optimizer phase has independent correctness proofs:

| Phase | Proof Obligation |
|-------|------------------|
| Poly | Each rule preserves denotational semantics via recursion scheme laws |
| Cross-layer | Rules preserve semantics by compositionality |
| Prim | Each rule is a categorical law (proven since 1940s) |

The composition of correct phases is correct.

---

## Future Extensions

### Session Types for Deadlock-Free Communication

The same philosophy applies to communication: deadlocks are bugs, not features.

```
┌─────────────────────────────────────────────┐
│           SessionIR (future)                │
│  Session types, duality, linear channels    │
│  (deadlock-free communication)              │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│           Once.CCC.IR.Poly                  │
│  (total + productive)                       │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│           Once.CCC.IR.Prim                  │
│  (non-recursive base)                       │
└─────────────────────────────────────────────┘
```

Each layer removes a class of bugs:

| Layer | Removes | Keeps |
|-------|---------|-------|
| Prim | (base) | All arrows (pure `A → B` and effectful `Eff A B`) |
| Poly | Infinite loops, unproductive codata | All useful recursive patterns |
| SessionIR | Communication deadlocks | All useful protocols |

The principle is consistent: **restrict expressivity to eliminate junk programs while preserving all useful ones**.

---

## Alternatives Considered

### A: Add Schemes to Prim Directly (Flat IR)

Rejected: Muddies the clean separation between non-recursive base and recursion handling. The layered approach makes the design clearer and each layer independently verifiable.

### B: Keep Fold/Unfold, Add Termination Checker

Rejected:
- Complex analysis with false negatives
- Doesn't prevent bugs by construction
- Duplicates what D039 already requires
- More implementation effort, less guarantee

### C: Use `lift` Inside Poly (Option A)

Rejected:
- Every Poly proof must handle `lift` case
- Less modular proof structure
- Layers not truly independent

### D: Layered IR with Polynomial Functors and Separate Combined Type (This Proposal)

Accepted:
- Clean separation of concerns
- Totality and productivity by construction
- Each layer independently verifiable
- Aligns with D039 verification strategy
- Enables dependent types naturally
- Best proof engineering

---

## Migration Path

### Phase 1: Define New Module Structure

- Create `Once.CCC.IR.Prim` with 12 generators + `Opaque` (primitive arrows)
- Create `Once.CCC.IR.Poly` with `Functor`, `In`, `Out`, `Cata`, `Ana`
- Define combined `IR` type
- Establish arrow-based effect typing (`A → B` vs `Eff A B`)
- Both old and new coexist temporarily

### Phase 2: Implement Guardedness Checker

- Syntactic guardedness checking for `ana`/`apo`
- Clear error messages for unguarded corecursion
- Examples and documentation

### Phase 3: Pattern Recognition

Automatically recognize existing patterns:

```agda
-- Recognize: Fold used as cata
recognizeCata : Old.IR → Maybe Poly.IR

-- Recognize: Unfold used as ana
recognizeAna : Old.IR → Maybe Poly.IR
```

### Phase 4: Code Generation

- Extend backends for `Poly.IR` constructs
- Implement hylo fusion in optimizer

### Phase 5: Deprecation

- Emit warnings for raw `Fold`/`Unfold` usage
- Provide migration guide
- Automatic rewriting where possible

### Phase 6: Remove Fold/Unfold

- Remove `Fold`/`Unfold` from IR
- Once is now total + productive by construction

### Phase 7: Formal Verification

- Agda proofs for `Poly.IR`
- Verify schemes preserve semantics
- Verify guardedness implies productivity
- Integrate with existing D039 polynomial functor proofs

---

## Open Questions

### 1. Mutual Recursive Types

How to handle mutually recursive types like `Expr`/`Decl`?

```
data Expr = ... | Let [Decl] Expr
data Decl = Decl Name Expr
```

**Likely solution:** Mutual `μ` with combined functor:

```
type ExprDeclF X Y = (ExprF X Y, DeclF X Y)
type (Expr, Decl) = μ ExprDeclF
```

### 2. Guardedness Algorithm

Which guardedness checker to use?

| Option | Complexity | Expressiveness |
|--------|------------|----------------|
| Syntactic | Low | Sufficient for most cases |
| Sized types | Medium | More flexible |
| Productivity comonads | High | Most expressive |

**Recommendation:** Start with syntactic guardedness (like Coq's guard condition), extend later if needed.

### 3. QTT Interaction

How do quantities flow through `cata`/`ana`?

**Likely semantics:**
- `cata` is linear in its `μF` argument (consumes the structure)
- `ana` with linear coalgebra produces linear stream elements
- Quantities compose through the algebra/coalgebra

### 4. Error Messages

How to explain "this recursion isn't a valid scheme" clearly?

**Approach:**
- Pattern-match common mistakes
- Suggest restructuring to valid scheme
- Provide examples of correct patterns

### 5. Arrow Laws in Type System

How to ensure `Eff A B` satisfies arrow laws?

**Arrow laws (must hold):**
- `arr id >>> f = f` (left identity)
- `f >>> arr id = f` (right identity)
- `(f >>> g) >>> h = f >>> (g >>> h)` (associativity)
- `first (arr f) = arr (f × id)` (first preserves arr)

**Likely approach:** These follow from CCC laws since arrow combinators are derived from CCC structure. The type system enforces `Eff` is used consistently; the laws are theorems, not axioms.

---

## Implementation Plan

| Phase | Deliverable |
|-------|-------------|
| 1. Module structure | `Once.CCC.IR.Prim`, `Once.CCC.IR.Poly`, combined `IR` |
| 2. Guardedness | Checker in `Once.CCC.IR.Guardedness` |
| 3. Recognition | `Fold`/`Unfold` → scheme patterns |
| 4. Backends | Code generation for `Poly.IR` |
| 5. Optimizer | Hylo fusion rule |
| 6. Migration | Warnings, guide, auto-rewrite |
| 7. Removal | Delete `Fold`/`Unfold` |
| 8. Verification | Agda proofs |

---

## Summary

This proposal restructures Once's IR into `Once.CCC.IR.Prim` and `Once.CCC.IR.Poly` to enforce totality and productivity by construction:

| Property | Mechanism |
|----------|-----------|
| **Totality** | Recursion only via `Cata` (structural) |
| **Productivity** | Corecursion only via guarded `Ana` |
| **No infinite loops** | No general `fix` |
| **No deadlocks** | Guardedness prevents unproductive mutual corecursion |
| **Arrow-based effects** | CCC provides structure, types distinguish `A → B` from `Eff A B` |
| **Dependent types ready** | Consistent logic without termination checker |
| **Verification simplified** | Proofs focus on algebras, not termination |
| **Minimal TCB** | Supports OCP-0004 trust boundaries |

The design:
- Uses `Prim` for 12 CCC generators + `Opaque` (primitive arrows, both pure and effectful)
- Uses `Poly` for polynomial functor operations
- Combines via `IR = prim Prim.IR | poly Poly.IR` for clean proofs
- Arrow-based effects: CCC structure provides arrow combinators, types distinguish `A → B` from `Eff A B`
- Aligns with D039 (polynomial functors)
- Preserves the three strata (Generators/Canonical/Initial)
- Enables planned dependent type extensions
- Opens path to session types for deadlock-free communication

**The core insight:** Turing completeness is not a feature — it's the absence of a safety guarantee. By removing general recursion and providing structured schemes, Once gains strong guarantees while losing only the ability to write bugs.

---

## References

- D039: Polynomial Functors decision (`docs/compiler/decision-log.md`)
- OCP-0004: Minimal-Trust Verification via Categorical Foundations
- `docs/formal/historical/fix-semantics-options.md`: Analysis of Fix semantics
- `docs/design/recursion-schemes.md`: Current recursion scheme documentation
- `docs/design/libraries.md`: Three strata architecture
- `docs/design/dependent-types-options.md`: Dependent type roadmap
- `docs/design/categorical-foundations.md`: Coalgebras and codata

---

## Discussion

[Comments, concerns, and resolutions will be added here as discussion proceeds.]
