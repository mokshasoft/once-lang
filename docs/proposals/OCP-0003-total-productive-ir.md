# OCP-0003: Total and Productive IR via Layered Architecture

**Author:** [TBD]
**Status:** Draft
**Created:** 2026-03-10

---

## Summary

Restructure the IR into two distinct layers: a non-recursive CCC IR (the existing 12 generators) and a new RecursionIR that provides structured recursion schemes (`cata`, `ana`, `hylo`, `para`). Remove general `Fold`/`Unfold` operations. This makes Once **total** (all functions terminate) and **productive** (all codata makes progress) by construction, while preserving all practically useful programs and enabling future dependent type extensions.

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
│            RecursionIR                      │
│   μ, ν, cata, ana + guardedness checking   │
│   (total + productive)                      │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│              CCC IR                         │
│   12 generators (unchanged, no recursion)   │
│   (trivially terminating)                   │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│         Target Backends                     │
│       C, Rust, JS, WASM, ...                │
└─────────────────────────────────────────────┘
```

### Layer 1: CCC IR (Unchanged Core)

The existing 12 categorical generators remain exactly as they are:

```haskell
data CCC_IR
  -- Category
  = Id Type
  | Compose CCC_IR CCC_IR

  -- Products
  | Fst Type Type
  | Snd Type Type
  | Pair CCC_IR CCC_IR
  | Terminal Type

  -- Coproducts
  | Inl Type Type
  | Inr Type Type
  | Case CCC_IR CCC_IR
  | Initial Type

  -- Exponentials
  | Curry Name CCC_IR
  | Apply Type Type

  -- Variables, primitives, literals (unchanged)
  | Var Name
  | LocalVar Name
  | FunRef Name
  | Prim Name Type Type
  | StringLit Text
  | Let Name CCC_IR CCC_IR

  -- Arithmetic (OCP-0001, unchanged)
  | Arith NumType ArithIR
```

**Key change:** `Fold` and `Unfold` are **removed** from this layer.

This layer is trivially total — no recursion is possible. Every program is a finite composition of generators.

### Layer 2: RecursionIR (New)

#### Type-Level Fixed Points

```haskell
-- Functor representation (polynomial functors per D039)
data Functor
  = FId                        -- Identity: X (recursive position)
  | FConst Type                -- Constant: A
  | FSum Functor Functor       -- Sum: F + G
  | FProd Functor Functor      -- Product: F × G

-- Recursive types
data RecType
  = Mu Functor        -- μF: least fixed point (inductive/finite)
  | Nu Functor        -- νF: greatest fixed point (coinductive/infinite)
```

#### Functor Interpretation

```haskell
-- ⟦F⟧ interprets a functor code as an actual type function
⟦_⟧ : Functor → Type → Type
⟦ FId ⟧ X      = X
⟦ FConst A ⟧ X = A
⟦ FSum F G ⟧ X = ⟦ F ⟧ X + ⟦ G ⟧ X
⟦ FProd F G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X
```

#### Recursion Schemes

```haskell
data RecursionIR
  -- Inductive (finite) data introduction and elimination
  = In Functor CCC_IR                    -- In : F (μF) → μF
  | Cata Functor CCC_IR CCC_IR           -- cata alg x : A
                                         --   where alg : F A → A, x : μF

  -- Coinductive (infinite) codata introduction and elimination
  | Out Functor CCC_IR                   -- Out : νF → F (νF)
  | Ana Functor CCC_IR CCC_IR            -- ana coalg seed : νF
                                         --   where coalg : A → F A, seed : A

  -- Derived schemes (expressible via cata/ana, but useful as primitives)
  | Hylo Functor CCC_IR CCC_IR CCC_IR    -- hylo alg coalg seed : B
  | Para Functor CCC_IR CCC_IR           -- para alg x : A (fold with context)
  | Apo Functor CCC_IR CCC_IR            -- apo coalg seed : νF (unfold with shortcuts)
```

#### Combined IR

```haskell
data IR
  = CCC CCC_IR
  | Rec RecursionIR
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
│         Interpretations                     │  IO primitives (platform-specific)
├─────────────────────────────────────────────┤
│         Initial                             │  Data types + operations (uses cata/ana)
├─────────────────────────────────────────────┤
│         Canonical                           │  Non-recursive combinators (pure CCC)
├─────────────────────────────────────────────┤
│         RecursionIR                         │  μ, ν, cata, ana (NEW)
├─────────────────────────────────────────────┤
│         Generators (CCC IR)                 │  12 categorical primitives
└─────────────────────────────────────────────┘
```

### Canonical Library (Unchanged)

All morphisms in Canonical are non-recursive and remain in pure CCC IR:

```
swap     : A × B → B × A           -- pair snd fst
diagonal : A → A × A               -- pair id id
assocL   : A × (B × C) → (A × B) × C
mirror   : A + B → B + A           -- case inr inl
const    : A → B → A
flip     : (A → B → C) → B → A → C
```

No changes needed.

### Initial Library (Explicit Recursion)

Operations in Initial become explicit uses of recursion schemes:

| Current (Implicit) | Proposed (Explicit) |
|--------------------|---------------------|
| `foldr f z xs` | `cata (case (const z) (uncurry f)) xs` |
| `map f xs` | `cata (case (const nil) (\(a,as) → cons (f a) as)) xs` |
| `filter p xs` | `cata (case (const nil) (\(a,as) → if p a then cons a as else as)) xs` |
| `length xs` | `cata (case (const 0) (\(_,n) → n+1)) xs` |
| `range lo hi` | `ana (\(l,h) → if l >= h then inl () else inr (l, (l+1, h))) (lo, hi)` |

The operations are the same; the recursion is now explicit and structured.

### Recursion Schemes Document

The existing `recursion-schemes.md` says:

> "They're pure derived code - no new generators needed."

This is true when you have general `fix`. Without general `fix`, the schemes become primitives — but this is exactly what D039's polynomial functor approach requires anyway.

---

## Dependent Types Compatibility

### Why Totality Enables Dependent Types

Dependent type systems require termination for logical consistency. The relationship:

| System | Termination | Consistency |
|--------|-------------|-------------|
| Agda | Enforced by termination checker | Sound |
| Coq | Enforced by guard condition | Sound |
| Idris | Enforced by totality checker | Sound (in total mode) |
| Once + RecursionIR | Enforced by construction | Sound |

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

### Indexed Types Example

```
type Vec : Nat → Type → Type
Vec zero    A = Unit
Vec (suc n) A = A × Vec n A

-- This is a family of polynomial functors indexed by n
-- VecF n A X = case n of
--   zero  → FConst Unit
--   suc m → FProd (FConst A) (VecF m A)

-- Safe head via dependent cata
head : Vec (suc n) A → A
head = cata headAlg
  where headAlg (a, _) = a
```

### Type-Level Computation

Type-level functions must terminate. With cata/ana, they terminate by construction:

```
-- Type-level append length
appendLen : Nat → Nat → Nat
appendLen = cata alg
  where alg (Inl unit) m = m           -- zero + m = m
        alg (Inr n')   m = suc (n' m)  -- suc n + m = suc (n + m)

-- The termination is STRUCTURAL via cata
-- No termination checker needed
```

### What This Enables

From `dependent-types-options.md`, Once's planned trajectory:

1. **Phase 1: Indexed Types** — `Vec n A`, `Fin n`, bounded integers
2. **Phase 2: Simple Π/Σ** — dependent functions, dependent pairs, Prop universe
3. **Phase 3: OTT or Directed** — quotients, function extensionality

All phases are compatible with polynomial functors + cata/ana. The proposal doesn't close any doors; it opens the right ones.

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

### What You Cannot Express

| Pattern | Status | Workaround |
|---------|--------|------------|
| Infinite loop | Removed | None (it's a bug) |
| Arbitrary recursion | Removed | Use appropriate scheme |
| Self-interpreter | Limited | Requires fuel parameter |
| Ackermann function | Expressible | Nested hylo |
| Non-structural recursion | Restructure | Convert to cata/ana |

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
- **Alignment with D039** — IR matches verification requirements

### Lost

- **General recursion** — must use schemes (rarely a limitation)
- **Some exotic algorithms** — need restructuring (rare in practice)
- **Self-interpreters** — need fuel parameter (niche use case)
- **"Flexibility" to write bugs** — this is not actually a loss

---

## Compilation Strategy

### RecursionIR → Target Code

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
│ 1. RecursionIR Optimizer    │  High-level: fusion, deforestation
└─────────────┬───────────────┘
              ↓
┌─────────────────────────────┐
│ 2. Cross-Layer Rules        │  Algebra/coalgebra optimization
└─────────────┬───────────────┘
              ↓
┌─────────────────────────────┐
│ 3. CCC IR Optimizer         │  Low-level: categorical laws
└─────────────┬───────────────┘
              ↓
          Code Gen
```

### Phase 1: RecursionIR Optimizer

Handles structural transformations that change the shape of recursion:

```
-- Deforestation (the big win)
cata alg ∘ ana coalg           →  hylo alg coalg

-- Functor fusion
map f ∘ map g                  →  map (f ∘ g)
filter p ∘ filter q            →  filter (λx → p x ∧ q x)
map f ∘ filter p               →  cata (case nil (λ(a,as) → if p a then cons (f a) as else as))

-- Cata computation
cata alg ∘ In                  →  alg ∘ fmap (cata alg)

-- Ana computation
Out ∘ ana coalg                →  fmap (ana coalg) ∘ coalg

-- Coalgebra composition
ana coalg ∘ f                  →  ana (coalg ∘ f)
```

### Phase 2: Cross-Layer Rules

Optimizations that span RecursionIR and CCC IR, working on the algebras and coalgebras:

```
-- Push post-processing into algebra
f ∘ cata alg                   →  cata (f ∘ alg)  -- when f is cheap

-- Pull pre-processing out of coalgebra
ana coalg ∘ f                  →  ana (coalg ∘ f)

-- Simplify algebra using CCC laws
cata (case (const z) (compose f (pair fst snd)))
    →  cata (case (const z) f)  -- pair fst snd = id
```

### Phase 3: CCC IR Optimizer

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
curry (compose apply (pair (compose f fst) snd))  →  f  -- eta
```

### Why This Order

1. **RecursionIR first** — Biggest wins. Deforestation eliminates entire intermediate data structures before we worry about small optimizations.

2. **Cross-layer second** — Once high-level structure is optimized, simplify the algebras/coalgebras that remain.

3. **CCC last** — Clean up low-level categorical compositions. These are cheap to apply and polish the final result.

### Example Optimization Trace

```
-- Original: three separate traversals
result = length (filter even (map (+1) xs))

-- Elaborate to IR
result = cata lenAlg (cata filterAlg (cata mapAlg xs))

-- Phase 1: Fuse catas (deforestation)
result = cata (lenAlg ∘ filterStep ∘ mapStep) xs
       = cata fusedAlg xs

-- Phase 2: Simplify fused algebra
fusedAlg = case (const 0) (λ(a, n) →
             let a' = a + 1
             in if even a' then n + 1 else n)

-- Phase 3: CCC cleanup (minor simplifications)
-- (algebra is already simple)

-- Result: Single traversal, no intermediate lists
```

### Verification Strategy

Each optimizer phase has independent correctness proofs:

| Phase | Proof Obligation |
|-------|------------------|
| RecursionIR | Each rule preserves denotational semantics via recursion scheme laws |
| Cross-layer | Rules preserve semantics by compositionality |
| CCC IR | Each rule is a categorical law (proven since 1940s) |

The composition of correct phases is correct.

### Implementation Notes

```haskell
-- Optimizer pipeline
optimize :: IR -> IR
optimize = cccOptimize . crossLayerOptimize . recursionOptimize

-- Each phase is a fixpoint of rule application
recursionOptimize :: IR -> IR
recursionOptimize = fixpoint applyRecursionRules

cccOptimize :: IR -> IR
cccOptimize = fixpoint applyCCCRules

-- Rules are pattern-matching rewrites
applyRecursionRules :: IR -> Maybe IR
applyRecursionRules (Compose (Cata alg) (Ana coalg seed)) =
    Just (Hylo alg coalg seed)  -- deforestation
applyRecursionRules _ = Nothing
```

---

## Future Extensions

### Session Types for Deadlock-Free Communication

The same philosophy applies to communication: deadlocks are bugs, not features.

Session types ensure communication protocols are followed correctly:

```
-- Protocol definition
type ServerProtocol = Recv Request (Send Response End)
type ClientProtocol = Send Request (Recv Response End)

-- Duality constraint (compile-time)
dual (Send A S) = Recv A (dual S)
dual (Recv A S) = Send A (dual S)
dual End        = End

-- Well-typed channels cannot deadlock
newChannel : (Channel S → IO A) → (Channel (dual S) → IO B) → IO (A × B)
```

This would add a **SessionIR** layer:

```
┌─────────────────────────────────────────────┐
│           SessionIR (future)                │
│  Session types, duality, linear channels    │
│  (deadlock-free communication)              │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│            RecursionIR                      │
│  (total + productive)                       │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│              CCC IR                         │
│  (non-recursive base)                       │
└─────────────────────────────────────────────┘
```

Each layer removes a class of bugs:

| Layer | Removes | Keeps |
|-------|---------|-------|
| CCC IR | (base) | All pure computation |
| RecursionIR | Infinite loops, unproductive codata | All useful recursive patterns |
| SessionIR | Communication deadlocks | All useful protocols |

The principle is consistent: **restrict expressivity to eliminate junk programs while preserving all useful ones**.

---

## Alternatives Considered

### A: Add Schemes to CCC IR Directly

Rejected: Muddies the clean separation between non-recursive base and recursion handling. The layered approach makes the design clearer and each layer independently verifiable.

### B: Keep Fold/Unfold, Add Termination Checker

Rejected:
- Complex analysis with false negatives
- Doesn't prevent bugs by construction
- Duplicates what D039 already requires
- More implementation effort, less guarantee

### C: Layered IR with Polynomial Functors (This Proposal)

Accepted:
- Clean separation of concerns
- Totality and productivity by construction
- Each layer independently verifiable
- Aligns with D039 verification strategy
- Enables dependent types naturally

---

## Migration Path

### Phase 1: Add RecursionIR

- Define `Functor`, `RecType`, `RecursionIR` data types
- Add to IR alongside current `Fold`/`Unfold`
- Both systems coexist temporarily

### Phase 2: Implement Guardedness Checker

- Syntactic guardedness checking for `ana`/`apo`
- Clear error messages for unguarded corecursion
- Examples and documentation

### Phase 3: Pattern Recognition

Automatically recognize existing patterns:

```haskell
-- Recognize: Fold used as cata
recognizeCata :: IR -> Maybe RecursionIR
recognizeCata (Compose (Fold f) ...) = ...

-- Recognize: Unfold used as ana
recognizeAna :: IR -> Maybe RecursionIR
recognizeAna (Compose ... (Unfold f)) = ...
```

### Phase 4: Code Generation

- Extend C backend for `cata`/`ana`
- Implement hylo fusion in optimizer
- Extend other backends (Rust, JS, WASM)

### Phase 5: Deprecation

- Emit warnings for raw `Fold`/`Unfold` usage
- Provide migration guide
- Automatic rewriting where possible

### Phase 6: Remove Fold/Unfold

- Remove `Fold`/`Unfold` from IR
- Once is now total + productive by construction

### Phase 7: Formal Verification

- Agda proofs for RecursionIR
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

### 5. Escape Hatch (If Needed)

For migration, should we provide a fuel-based escape hatch?

```haskell
-- Run up to n steps, return Nothing if exhausted
withFuel : Nat → (Unit → A) → Maybe A
```

**Recommendation:** Provide but mark as deprecated/unsafe. Remove after migration complete.

---

## Implementation Plan

| Phase | Deliverable | Effort |
|-------|-------------|--------|
| 1. Data types | `Functor`, `RecType`, `RecursionIR` in `Once/IR.hs` | 1 week |
| 2. Guardedness | Checker in `Once/Guardedness.hs` | 1-2 weeks |
| 3. Recognition | `Fold`/`Unfold` → scheme patterns | 1 week |
| 4. C backend | Code generation for schemes | 1-2 weeks |
| 5. Optimizer | Hylo fusion rule | 1 week |
| 6. Migration | Warnings, guide, auto-rewrite | 1-2 weeks |
| 7. Removal | Delete `Fold`/`Unfold` | 1 day |
| 8. Verification | Agda proofs | 2-4 weeks |

**Total estimated effort:** 8-14 weeks

---

## Summary

This proposal restructures Once's IR to enforce totality and productivity by construction:

| Property | Mechanism |
|----------|-----------|
| **Totality** | Recursion only via `cata` (structural) |
| **Productivity** | Corecursion only via guarded `ana` |
| **No infinite loops** | No general `fix` |
| **No deadlocks** | Guardedness prevents unproductive mutual corecursion |
| **Dependent types ready** | Consistent logic without termination checker |
| **Verification simplified** | Proofs focus on algebras, not termination |

The design:
- Aligns with D039 (polynomial functors)
- Preserves the three strata (Generators/Canonical/Initial)
- Enables planned dependent type extensions
- Opens path to session types for deadlock-free communication

**The core insight:** Turing completeness is not a feature — it's the absence of a safety guarantee. By removing general recursion and providing structured schemes, Once gains strong guarantees while losing only the ability to write bugs.

---

## References

- D039: Polynomial Functors decision (`docs/compiler/decision-log.md`)
- `docs/formal/historical/fix-semantics-options.md`: Analysis of Fix semantics
- `docs/design/recursion-schemes.md`: Current recursion scheme documentation
- `docs/design/libraries.md`: Three strata architecture
- `docs/design/dependent-types-options.md`: Dependent type roadmap
- `docs/design/categorical-foundations.md`: Coalgebras and codata

---

## Discussion

[Comments, concerns, and resolutions will be added here as discussion proceeds.]
