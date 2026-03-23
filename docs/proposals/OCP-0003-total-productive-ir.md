# OCP-0003: Total and Productive IR via Unified Categorical Structure

**Author:** [TBD]
**Status:** Draft
**Created:** 2026-03-10
**Updated:** 2026-03-22

---

## Summary

Define a **single unified IR** in `Once.CCC.IR` containing all CCC operations:

- **Category**: `Id`, `Compose`
- **Products**: `Fst`, `Snd`, `Pair`, `Terminal`
- **Coproducts**: `Inl`, `Inr`, `Case`, `Initial`
- **Exponentials**: `Curry`, `Apply`
- **Primitive arrows**: `Opaque` (both pure `A → B` and effectful `Eff A B`)
- **Initial algebras**: `In`, `Cata` (inductive/finite data)
- **Final coalgebras**: `Out`, `Ana` (coinductive/infinite codata)
- **Derived schemes**: `Hylo`, `Para`, `Apo` (optimizations)

Effects are **arrow-based**: the CCC structure provides arrow combinators (composition, products), and the type system distinguishes pure arrows (`A → B`) from effect arrows (`Eff A B`). The IR is about structure; types track semantics.

Remove general `Fold`/`Unfold` operations. This makes Once **total** (all functions terminate) and **productive** (all codata makes progress) by construction, while preserving all practically useful programs and enabling future dependent type extensions.

This unified IR aligns with OCP-0004's bootstrap architecture, where a single IR containing all CCC operations enables the bootstrap verifier to check traces of categorical reductions.

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

### Unified IR Architecture

```
┌─────────────────────────────────────────────┐
│              User Code                      │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│           Once.CCC.IR                       │
│                                             │
│  Category:     Id, Compose                  │
│  Products:     Fst, Snd, Pair, Terminal     │
│  Coproducts:   Inl, Inr, Case, Initial      │
│  Exponentials: Curry, Apply                 │
│  Primitives:   Opaque                       │
│  Algebras:     In, Cata (total)             │
│  Coalgebras:   Out, Ana (productive)        │
│  Derived:      Hylo, Para, Apo              │
│                                             │
│  Single unified datatype for all operations │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│         Target Backends                     │
│       C, Rust, JS, WASM, ...                │
└─────────────────────────────────────────────┘
```

This unified structure matches OCP-0004's bootstrap tower, where the verifier checks traces of categorical reductions on a single IR representation.

### Module Structure

```agda
module Once.CCC.IR where

-- Functor representation (polynomial functors per D039)
data Functor : Set where
  FId    : Functor                      -- Identity: X (recursive position)
  FConst : Type → Functor               -- Constant: A
  FSum   : Functor → Functor → Functor  -- Sum: F + G
  FProd  : Functor → Functor → Functor  -- Product: F × G

-- Guardedness type: ensures coalgebras produce guarded results
-- Only constructors (Pair, Inl, Inr) can wrap corecursive results
data Guarded (F : Functor) (A : Type) : Type where
  GProd  : Guarded F₁ A → Guarded F₂ A → Guarded (FProd F₁ F₂) A  -- product guards
  GInl   : Guarded F A → Guarded (FSum F G) A                      -- sum guards
  GInr   : Guarded G A → Guarded (FSum F G) A
  GConst : B → Guarded (FConst B) A                                -- base case
  GRec   : A → Guarded FId A                                       -- recursive position

-- Unified IR: all CCC operations in a single datatype
data IR : Type → Type → Set where
  -- Category
  Id      : IR A A
  Compose : IR B C → IR A B → IR A C

  -- Products
  Fst      : IR (A × B) A
  Snd      : IR (A × B) B
  Pair     : IR A B → IR A C → IR A (B × C)
  Terminal : IR A Unit

  -- Coproducts
  Inl     : IR A (A + B)
  Inr     : IR B (A + B)
  Case    : IR A C → IR B C → IR (A + B) C
  Initial : IR Void A

  -- Exponentials
  Curry : IR (A × B) C → IR A (B ⇒ C)
  Apply : IR ((A ⇒ B) × A) B

  -- Primitive arrows (pure A → B and effectful Eff A B)
  -- Effect distinction is in the TYPE, not the IR
  -- CCC combinators work uniformly on both arrow types
  Opaque : Name → IR A B

  -- Initial algebras (inductive/finite data)
  In   : IR (⟦ F ⟧ (μ F)) (μ F)
  Cata : (alg : IR (⟦ F ⟧ A) A) → IR (μ F) A

  -- Final coalgebras (coinductive/infinite codata)
  -- Guardedness enforced at type level: coalg must produce guarded result
  Out : IR (ν F) (⟦ F ⟧ (ν F))
  Ana : (coalg : IR A (Guarded F A)) → IR A (ν F)

  -- Derived schemes (primitive constructors for optimization)
  Hylo : IR (⟦ F ⟧ B) B → IR A (⟦ F ⟧ A) → IR A B
  Para : IR (⟦ F ⟧ (A × μ F)) A → IR (μ F) A
  Apo  : IR A (⟦ F ⟧ (A + ν F)) → IR A (ν F)
```

### Why This Structure

**Single unified IR:**
- Matches the bootstrap architecture (OCP-0004) where the verifier checks traces on one IR
- Case analysis covers all constructors directly — no artificial wrappers
- Type indices (`IR A B`) encode source and target types, enabling typed reductions
- Guardedness is part of `Ana`'s type — unguarded terms are **unconstructable**

**Philosophy: IR = Natural Transformations**

The IR should BE the categorical structure, not a representation that needs validation:

- **Cata** IS the unique F-algebra morphism from μF (totality by definition)
- **Ana** IS the unique F-coalgebra morphism to νF (productivity by definition)
- **Guardedness** is part of Ana's type — unguarded terms cannot be constructed

This means:
- No separate "guardedness checker" pass
- Invalid (non-total, non-productive) programs cannot be represented
- The type system enforces what category theory defines

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
  μ : Functor → RecType    -- Least fixed point (inductive/finite)
  ν : Functor → RecType    -- Greatest fixed point (coinductive/infinite)
```

### Functor Interpretation

```agda
-- ⟦F⟧ interprets a functor code as an actual type function
⟦_⟧ : Functor → Type → Type
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

### Guardedness as Type-Level Constraint

For coinductive definitions (`Ana`, `Apo`), guardedness is enforced **at the type level** via the `Guarded` type:

```agda
-- Guarded F A represents a value of shape F where corecursive positions are guarded
data Guarded (F : Functor) (A : Type) : Type where
  GProd  : Guarded F₁ A → Guarded F₂ A → Guarded (FProd F₁ F₂) A  -- product guards
  GInl   : Guarded F A → Guarded (FSum F G) A                      -- sum guards
  GInr   : Guarded G A → Guarded (FSum F G) A
  GConst : B → Guarded (FConst B) A                                -- base case (no recursion)
  GRec   : A → Guarded FId A                                       -- corecursive position

-- Ana only accepts guarded coalgebras — unguarded ones cannot be typed
Ana : (coalg : IR A (Guarded F A)) → IR A (ν F)
```

This is **definitional**: unguarded coalgebras simply cannot be constructed. There is no
"guardedness checker" algorithm to trust — the type system makes invalid terms unconstructable.

#### Examples

```agda
-- GOOD: coalgebra produces guarded output (constructor wraps corecursion)
streamCoalg : IR State (Guarded (FProd (FConst Output) FId) State)
streamCoalg = ... produces GProd (GConst output) (GRec nextState) ...
-- ✓ Type-checks: pair constructor guards the recursive position

-- BAD: cannot construct unguarded coalgebra
-- There is no Guarded constructor that allows corecursion without a guard
-- Such a term simply CANNOT be written — not "rejected", unconstructable
```

#### Why Type-Level Guardedness

| Approach | Adds to TCB? | When checked? |
|----------|--------------|---------------|
| Algorithmic checker | Yes (must trust checker) | Runtime/compile-time |
| Type-level constraint | No (types are definitional) | Construction time |

This aligns with OCP-0004's minimal-trust philosophy: productivity is **definitional**
(follows from the type structure), not checked by an algorithm we must trust.

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

The strata structure (from `libraries.md`) is preserved with the unified IR:

```
┌─────────────────────────────────────────────┐
│         Interpretations                     │  Effect arrows (Opaque with Eff A B types)
├─────────────────────────────────────────────┤
│         Initial                             │  Data types + operations (uses Cata/Ana)
├─────────────────────────────────────────────┤
│         Canonical                           │  Non-recursive combinators (CCC operations)
├─────────────────────────────────────────────┤
│         Once.CCC.IR                         │  Unified IR: all CCC + recursion schemes
└─────────────────────────────────────────────┘
```

Note: The same `Opaque` constructor is used for both pure primitives (typed `A → B`) and effectful primitives (typed `Eff A B`). The stratum difference is in the types, not the IR structure. The unified IR provides all operations; library strata are a matter of which subset they use.

### Canonical Library (Unchanged)

All morphisms in Canonical are non-recursive and use the CCC operations of the unified IR:

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

Operations in Initial become explicit uses of the unified IR's recursion schemes:

| Current (Implicit) | Proposed (Explicit IR) |
|--------------------|------------------------|
| `foldr f z xs` | `Cata (Case (const z) (uncurry f)) : IR (μ ListF) A` |
| `map f xs` | `Cata (Case nil (Compose cons (Pair (Compose f Fst) Snd))) : IR (μ ListF) (μ ListF)` |
| `filter p xs` | `Cata (Case nil (λ(a,as) → if p a then cons a as else as)) : IR (μ ListF) (μ ListF)` |
| `length xs` | `Cata (Case (const 0) (Compose succ Snd)) : IR (μ ListF) Nat` |
| `range lo hi` | `Ana coalg : IR (Nat × Nat) (ν StreamF)` where coalg produces `Guarded` output |

The operations are the same; the recursion is now explicit and structured. The unified IR types
(`IR A B`) make domain and codomain explicit.

---

## Proof Engineering Benefits

### Unified IR for Direct Proofs

The unified IR enables direct case analysis over all constructors:

```agda
-- Single induction covers all IR constructs
ir-simulation : ∀ {A B} (f : IR A B) → Simulates f
ir-simulation Id           = ...
ir-simulation (Compose g f) = ...
ir-simulation Fst          = ...
ir-simulation (Cata alg)   = ...
ir-simulation (Ana coalg)  = ...
-- etc.
```

**Benefits:**
1. **Direct proofs** — no wrapper overhead, case analysis is straightforward
2. **Type-indexed IR** — `IR A B` carries type information, enabling typed rewrites
3. **Definitional totality** — `Cata` is total by Lambek's Lemma, not by analysis
4. **Definitional productivity** — `Ana` with `Guarded` coalgebra is productive by construction
5. **Matches bootstrap tower** — same IR structure the verifier checks

### Guardedness as Type-Level Constraint

The `Guarded` type ensures coalgebras are guarded **by construction**:

```agda
-- This coalgebra type-checks: produces guarded output
goodCoalg : IR State (Guarded (FProd (FConst Output) FId) State)
goodCoalg = ...  -- must produce GProd (GConst output) (GRec nextState)

-- Unguarded coalgebras cannot be typed
-- No Guarded constructor allows: corecurse without a guard
```

This aligns with OCP-0004's minimal-trust philosophy: totality/productivity are **definitional** (Lambek's Lemma), not checked by an algorithm we must trust.

---

## Alignment with OCP-0004 (Minimal-Trust Verification)

The unified IR directly supports OCP-0004's minimal TCB goal and bootstrap tower architecture.

### Trust Boundaries

| IR Construct | TCB Addition | Verification |
|--------------|--------------|--------------|
| Category (Id, Compose) | ~5 lines | Identity/composition laws |
| Products (Fst, Snd, Pair, Terminal) | ~15 lines | Product universal property |
| Coproducts (Inl, Inr, Case, Initial) | ~15 lines | Coproduct universal property |
| Exponentials (Curry, Apply) | ~10 lines | Exponential adjunction |
| Initial algebras (In, Cata) | ~10 lines | Lambek's Lemma (1968) |
| Final coalgebras (Out, Ana) | ~10 lines | Dual of Lambek's Lemma |
| **Total** | ~65 lines | Well-established category theory |

### The IR IS Category Theory

From OCP-0004, the unified IR maps directly to categorical concepts:

```
┌──────────────────────────┬──────────────────────────────────┐
│     Once.CCC.IR          │     Category Theory              │
├──────────────────────────┼──────────────────────────────────┤
│ Id                       │ id_A : A → A                    │
│ Compose g f              │ g ∘ f                           │
│ Pair f g                 │ ⟨f, g⟩ : C → A × B             │
│ Fst                      │ π₁ : A × B → A                  │
│ Snd                      │ π₂ : A × B → B                  │
│ Inl                      │ ι₁ : A → A + B                  │
│ Inr                      │ ι₂ : B → A + B                  │
│ Case f g                 │ [f, g] : A + B → C              │
│ Curry f                  │ λ(f) : A → (B ⇒ C)             │
│ Apply                    │ eval : (A ⇒ B) × A → B         │
├──────────────────────────┼──────────────────────────────────┤
│ μF                       │ Initial F-algebra                │
│ In                       │ Algebra structure: F(μF) → μF    │
│ Cata alg                 │ Unique F-algebra morphism        │
│ νF                       │ Final F-coalgebra                │
│ Out                      │ Coalgebra structure: νF → F(νF)  │
│ Ana coalg                │ Unique F-coalgebra morphism      │
└──────────────────────────┴──────────────────────────────────┘
```

### Bootstrap Tower Alignment

The unified IR matches how OCP-0004's bootstrap tower actually works:

```
Level 3: Full Once compiler (compiles itself)
    ↓ uses
Level 2: Trace-checking verifier (checks Level 3 output)
    ↓ uses
Level 1: Simple trace checker (checks Level 2 output)
    ↓ uses
Level 0: Mathematical axioms (Lambek's Lemma, CCC laws)
```

Each level works with ONE unified IR representation. The verifier checks that
categorical reductions are valid — it doesn't need to know about "Prim vs Poly"
distinctions, just that each rewrite step follows CCC laws or recursion scheme laws.

### Totality and Productivity ARE Definitional

```
Lambek's Lemma (1968):
    The structure map In : F(μF) → μF is an isomorphism.
    This means μF ≅ F(μF).
    Consequence: μF is well-founded (no infinite descent).
    Therefore: Cata always terminates.

Dual (Final Coalgebras):
    The structure map Out : νF → F(νF) is an isomorphism.
    This means νF ≅ F(νF).
    Consequence: νF is productive (always has next element).
    Therefore: Ana always makes progress.

Guardedness (Type-Level):
    Ana requires: coalg : IR A (Guarded F A)
    The Guarded type ONLY allows constructor-guarded corecursion.
    Unguarded coalgebras cannot be typed — they are unconstructable.
```

These are mathematical facts, not implementation details. The unified IR makes
these facts explicit: `Cata` is total because it IS the unique algebra morphism,
and `Ana` is productive because it IS the unique coalgebra morphism with guarded
output.

---

## Dependent Types Compatibility

### Why Totality Enables Dependent Types

Dependent type systems require termination for logical consistency:

| System | Termination | Consistency |
|--------|-------------|-------------|
| Agda | Enforced by termination checker | Sound |
| Coq | Enforced by guard condition | Sound |
| Idris | Enforced by totality checker | Sound (in total mode) |
| Once (unified IR) | Enforced by construction | Sound |

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

### IR → Target Code

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

The unified IR enables a streamlined optimizer that applies all rewrite rules uniformly.

### Optimization Strategy

```
User Code
    ↓
┌─────────────────────────────┐
│ Unified IR Optimizer        │
│                             │
│ 1. Fusion rules             │  Hylo fusion, deforestation
│ 2. Categorical laws         │  CCC simplifications
│ 3. Recursion scheme laws    │  Cata/Ana computation rules
│                             │
│ All rules on single IR type │
└─────────────┬───────────────┘
              ↓
          Code Gen
```

### Fusion Rules (High-Level)

Structural transformations for recursion schemes:

```
-- Deforestation (the big win)
Compose (Cata alg) (Ana coalg)     →  Hylo alg coalg

-- Functor fusion
map f ∘ map g                      →  map (Compose f g)
filter p ∘ filter q                →  filter (λx → p x ∧ q x)

-- Cata computation (unfold definition)
Compose (Cata alg) In              →  Compose alg (fmap (Cata alg))

-- Ana computation (unfold definition)
Compose Out (Ana coalg)            →  Compose (fmap (Ana coalg)) coalg
```

### Categorical Laws (CCC Simplifications)

Local simplifications using CCC universal properties:

```
-- Identity laws
Compose f Id                       →  f
Compose Id f                       →  f

-- Product laws
Compose Fst (Pair f g)             →  f
Compose Snd (Pair f g)             →  g
Pair Fst Snd                       →  Id  -- eta for products

-- Coproduct laws
Compose (Case f g) Inl             →  f
Compose (Case f g) Inr             →  g
Case Inl Inr                       →  Id  -- eta for coproducts

-- Exponential laws
Compose Apply (Pair (Curry f) g)   →  Compose f (Pair Id g)
```

### Verification Strategy

All rules are verified uniformly on the single IR type:

| Rule Category | Proof Basis |
|---------------|-------------|
| Fusion rules | Recursion scheme laws (Cata/Ana universal properties) |
| CCC laws | Categorical universal properties (proven since 1940s) |
| Derived schemes | Definitions in terms of Cata/Ana |

The unified IR means proofs work by direct case analysis — no artificial
layer boundaries to cross.

---

## Future Extensions

### Session Types for Deadlock-Free Communication

The same philosophy applies to communication: deadlocks are bugs, not features.

```
┌─────────────────────────────────────────────┐
│           Once.CCC.IR (extended)            │
│                                             │
│  Base CCC:     Category, Products, etc.     │
│  Recursion:    Cata, Ana (total/productive) │
│  Sessions:     Send, Recv, Choice, Dual     │
│                (deadlock-free by typing)    │
└─────────────────────────────────────────────┘
```

The unified IR can be extended with session type constructors that enforce communication safety through linear types and session duality:

| Extension | Removes | Mechanism |
|-----------|---------|-----------|
| Recursion schemes | Infinite loops, unproductive codata | `Cata`/`Ana` with `Guarded` |
| Session types | Communication deadlocks | Linear channels, dual sessions |
| Both | All major bug classes | Type-level constraints |

The principle is consistent: **restrict expressivity to eliminate junk programs while preserving all useful ones**. Each extension adds constructors to the unified IR with types that make invalid programs unconstructable.

---

## Alternatives Considered

### A: Separate Prim/Poly Modules with Combined Type

Rejected:
- Creates artificial distinction not present in the bootstrap architecture
- Proofs need to cross module boundaries
- Adds `prim`/`poly` wrapper overhead in proofs
- Doesn't match how the verifier actually works

### B: Keep Fold/Unfold, Add Termination Checker

Rejected:
- Complex analysis with false negatives
- Doesn't prevent bugs by construction
- Duplicates what D039 already requires
- More implementation effort, less guarantee
- Adds to TCB (must trust the checker)

### C: Use `lift` Inside Poly Module

Rejected:
- Every Poly proof must handle `lift` case
- Less modular proof structure
- Layers not truly independent

### D: Unified IR with Type-Level Guardedness (This Proposal)

Accepted:
- Matches OCP-0004 bootstrap tower architecture
- Direct case analysis over all constructors
- Totality and productivity by construction (definitional)
- Type-indexed IR enables typed rewrites
- Guardedness enforced at type level — unguarded terms unconstructable
- Aligns with D039 verification strategy
- Enables dependent types naturally
- Minimal TCB — no guardedness checker to trust

---

## Migration Path

### Phase 1: Define Unified IR

- Create `Once.CCC.IR` with:
  - `Functor` type for polynomial functors
  - `Guarded` type for guardedness enforcement
  - Unified `IR` datatype with all constructors
- Establish arrow-based effect typing (`A → B` vs `Eff A B`)
- Both old and new IR coexist temporarily

### Phase 2: Pattern Recognition

Automatically recognize existing patterns:

```agda
-- Recognize: Fold used as Cata
recognizeCata : Old.IR → Maybe (IR (μ F) A)

-- Recognize: Unfold used as Ana
recognizeAna : Old.IR → Maybe (IR A (ν F))
```

### Phase 3: Code Generation

- Extend backends for recursion scheme constructs
- Implement Hylo fusion in optimizer
- Generate efficient loops for Cata, lazy structures for Ana

### Phase 4: Deprecation

- Emit warnings for raw `Fold`/`Unfold` usage
- Provide migration guide
- Automatic rewriting where possible

### Phase 5: Remove Fold/Unfold ✓ COMPLETE

- Remove `Fold`/`Unfold` from IR
- Once is now total + productive by construction
- Completed: 2026-03-22 (34 files updated)

### Phase 6: Formal Verification (IN PROGRESS)

**Semantic Coherence Layer** ✓ COMPLETE (2026-03-23)

The semantic coherence layer connects the postulated semantics in `Once.Semantics.Core`
to the concrete implementations in `Once.SPF`:

- **Type Unification**: `Once.SPF` now uses `Once.Type.Functor` instead of a duplicate definition
- **Functor Interpretation**: `Once.SPF` imports `⟦_⟧F` from `Once.Semantics.IR`
- **Coherence Module**: `Once.Semantics.Coherence` establishes:
  - Type coherence: `⟦μ⟧ F ≡ SPF.μ F` and `⟦ν⟧ F ≡ SPF.ν F`
  - Functor map coherence: `sem-fmap ≡ SPF.fmap` (proven)
  - Operation implementations via SPF: `sem-In`, `sem-Out`, `sem-cata`, etc.
  - Law validation: Lambek's Lemma and cata computation law
  - Functor law inheritance: `sem-fmap-id`, `sem-fmap-comp` (proven)

**Recursion Scheme Laws** ✓ COMPLETE (2026-03-23)

Semantic and IR-level laws for recursion schemes:

- **Core.agda** additions:
  - Coercion round-trip lemmas: `coerce-round-trip`, `coerce⁻¹-round-trip`
  - Identity catamorphism: `sem-cata-In-id : sem-cata F sem-In x ≡ x`
  - Identity anamorphism: `sem-ana-Out-id : sem-ana F sem-CoOut x ≡ x`
  - Hylo computation: `sem-hylo-compute` (recursive application)

- **Category/Laws.agda** documentation:
  - `eval-cata-In-id`: derivation from sem-cata-In-id
  - `eval-cata-In`: derivation from sem-cata-compute
  - `eval-hylo-unfold`: derivation from sem-hylo-compute
  - `eval-ana-Out-id`: derivation from sem-ana-Out-id

IR-level laws remain postulated (require funext), but derivations are documented.

**Remaining Work**:

- [ ] Agda proofs for guardedness enforcement
- [ ] Verify Guarded type ensures productivity
- [ ] Integrate with existing D039 polynomial functor proofs
- [ ] Align with OCP-0004 bootstrap verification
- [ ] Replace transport postulates with explicit proofs
- [ ] Full IR law proofs (requires function extensionality)

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

### 2. Guarded Type Ergonomics

The `Guarded` type enforces guardedness definitionally, but how ergonomic is it in practice?

| Concern | Possible Solution |
|---------|-------------------|
| Verbose construction | Smart constructors that build `Guarded` values |
| Pattern matching | View patterns or projection functions |
| Nested guardedness | Functorial lifting of `Guarded` |

**Recommendation:** Provide syntactic sugar that elaborates to `Guarded` constructors. Users write natural-looking coalgebras; elaboration produces typed `Guarded` terms.

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
| 1. Unified IR | `Once.CCC.IR` with `Functor`, `Guarded`, unified `IR` type |
| 2. Recognition | `Fold`/`Unfold` → scheme patterns |
| 3. Backends | Code generation for recursion schemes |
| 4. Optimizer | Hylo fusion rule, categorical simplifications |
| 5. Migration | Warnings, guide, auto-rewrite |
| 6. Removal | Delete `Fold`/`Unfold` |
| 7. Verification | Agda proofs, bootstrap tower alignment |

---

## Summary

This proposal defines a **unified IR** in `Once.CCC.IR` that enforces totality and productivity by construction:

| Property | Mechanism |
|----------|-----------|
| **Totality** | Recursion only via `Cata` (structural, by Lambek's Lemma) |
| **Productivity** | Corecursion only via `Ana` with `Guarded` coalgebra |
| **No infinite loops** | No general `fix` |
| **No deadlocks** | Type-level guardedness prevents unproductive corecursion |
| **Arrow-based effects** | CCC provides structure, types distinguish `A → B` from `Eff A B` |
| **Dependent types ready** | Consistent logic without termination checker |
| **Verification simplified** | Proofs focus on algebras, not termination |
| **Minimal TCB** | Matches OCP-0004 bootstrap tower |

The design:
- Single unified `IR : Type → Type → Set` with all CCC operations
- `Functor` type for polynomial functors (per D039)
- `Guarded` type enforces guardedness at type level — unguarded coalgebras are unconstructable
- Primitive constructors for derived schemes (`Hylo`, `Para`, `Apo`) enable direct optimization
- Arrow-based effects: CCC structure provides arrow combinators, types distinguish `A → B` from `Eff A B`
- Aligns with D039 (polynomial functors)
- Matches OCP-0004 bootstrap architecture (single IR for verifier)
- Preserves the three strata (Generators/Canonical/Initial)
- Enables planned dependent type extensions
- Opens path to session types for deadlock-free communication

**The core insight:** Turing completeness is not a feature — it's the absence of a safety guarantee. By removing general recursion and providing structured schemes, Once gains strong guarantees while losing only the ability to write bugs.

**The key principle:** The IR should BE the categorical structure, not a representation that needs validation. `Cata` IS the unique algebra morphism (totality by definition), and `Ana` IS the unique coalgebra morphism (productivity by definition with guarded output).

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
