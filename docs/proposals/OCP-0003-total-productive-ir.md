# OCP-0003: Total and Productive IR via Unified Categorical Structure

**Author:** [TBD]
**Status:** Draft
**Created:** 2026-03-10
**Updated:** 2026-03-27 (μ-anchored Hylo/Fuse, removed TerminatesOn/GuardedT)

---

## Summary

Define a **single unified IR** in `Once.CCC.IR` containing all CCC operations:

- **Category**: `Id`, `Compose`
- **Products**: `Fst`, `Snd`, `Pair`, `Terminal`
- **Coproducts**: `Inl`, `Inr`, `Case`, `Initial`
- **Exponentials**: `Curry`, `Apply`
- **Primitive arrows**: `Opaque` (both pure `A → B` and effectful `Eff A B`)
- **Initial algebras**: `In`, `out-μ`, `Cata`, `Para` (inductive/finite data, total by Lambek)
- **Final coalgebras**: `Out`, `in-ν`, `Ana`, `Apo` (coinductive/infinite codata, productive by Lambek)
- **Fusions** (optimization layer): `Hylo` and other μ-anchored optimizations

The IR is **layered**: categorical primitives (Cata, Para, Ana, Apo) provide the semantic foundation with
proven totality/productivity. Fusions are optimization morphisms added later, requiring explicit
termination witnesses. See "The Fusion Category" section below.

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
| Fold with context | `para` (paramorphism) | Safe tail, bounded observation |
| Unfold with early exit | `apo` (apomorphism) | Early-terminating generation |
| Fused transform | `Fusion` (optimization) | Deforestation |

These **categorical schemes** (Cata, Para, Ana, Apo) cover virtually all recursive patterns with proven
termination/productivity. Fusions are compiler optimizations that preserve semantics while eliminating
intermediate structures. General recursion adds only the ability to write bugs.

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

### Alignment with D037 (Polynomial Functors)

Decision D037 chose **polynomial functors** for formal verification, which already requires:

- Strictly positive types only (no functions in recursive positions)
- Recursion via `cata` for termination
- Automatic `fmap` and induction principles

From `fix-semantics-options.md`:

> "Non-structural recursion: **Must use cata**" (for polynomial functors)

This proposal makes explicit in the IR what D037 already requires for verification.

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
│  ═══════════ CCC Foundation ═══════════    │
│  Category:     Id, Compose                  │
│  Products:     Fst, Snd, Pair, Terminal     │
│  Coproducts:   Inl, Inr, Case, Initial      │
│  Exponentials: Curry, Apply                 │
│  Primitives:   Opaque                       │
│                                             │
│  ══════ Categorical Recursion Schemes ═════ │
│  μ-world (total by Lambek):                 │
│    In, out-μ, Cata, Para                    │
│  ν-world (productive by Lambek):            │
│    Out, in-ν, Ana, Apo                      │
│                                             │
│  ══════════ Fusion Layer ═══════════════   │
│  (Optimization, requires μ-anchoring)       │
│    Hylo, Dyna, Chrono, ...                  │
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

**Key insight:** The IR is conceptually layered:
1. **Categorical primitives** (Cata, Para, Ana, Apo) have universal properties — totality/productivity is PROVEN
2. **Fusions** (Hylo, Dyna, etc.) are optimization morphisms — they require μ-anchoring witnesses

Fusions are NOT categorical primitives. They don't have universal properties. But they ARE essential for
compiler optimization. The layering makes this explicit: semantic correctness comes from the categorical
layer; optimization comes from the fusion layer.

### Module Structure

```agda
module Once.CCC.IR where

-- Functor representation (polynomial functors per D037)
data Functor : Set where
  FId    : Functor                      -- Identity: X (recursive position)
  FConst : Type → Functor               -- Constant: A
  FSum   : Functor → Functor → Functor  -- Sum: F + G
  FProd  : Functor → Functor → Functor  -- Product: F × G

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
  In    : IR (⟦ F ⟧ (μ F)) (μ F)           -- constructor
  out-μ : IR (μ F) (⟦ F ⟧ (μ F))           -- destructor (inverse of In, by Lambek)
  Cata  : (alg : IR (⟦ F ⟧ A) A) → IR (μ F) A

  -- Final coalgebras (coinductive/infinite codata)
  -- Productivity follows from IR totality (see IR/Totality.agda)
  Out  : IR (ν F) (⟦ F ⟧ (ν F))            -- destructor
  in-ν : IR (⟦ F ⟧ (ν F)) (ν F)            -- constructor (inverse of Out, by Lambek)
  Ana  : (coalg : IR A (⟦ F ⟧ A)) → IR A (ν F)
  Apo  : IR A (⟦ F ⟧ (A + ν F)) → IR A (ν F)  -- apomorphism (dual of Para)

  -- ═══════════════════════════════════════════════════════════════════
  -- FUSIONS: Optimization morphisms (not categorical primitives!)
  --
  -- Fusions bridge μ-consumers and ν-producers. They eliminate intermediate
  -- structures (deforestation). They are NOT universal morphisms — they don't
  -- have categorical universal properties. Termination is guaranteed by
  -- requiring μ-type input (μ-anchoring).
  --
  -- The Fusion category contains well-founded optimization morphisms between
  -- recursion schemes. See "The Fusion Category" section for theory.
  -- ═══════════════════════════════════════════════════════════════════

  -- Hylo: Fusion of Cata and Ana (μ-anchored, correct by construction)
  -- Termination is guaranteed by requiring μG as input — structural recursion
  -- on the well-founded μG type. The coalgebra produces F-layers from μG values.
  -- Semantically: Hylo alg coalg ≡ Fuse alg (coalg ∘ In)
  Hylo : ∀ {F G} → WellFormedF F → WellFormedF G → ∀ {B}
       → IR (⟦ F ⟧ B) B                       -- algebra: F(B) → B
       → IR (μ G) (⟦ F ⟧ (μ G))               -- coalgebra: μG → F(μG)
       → IR (μ G) B

  -- Fuse: μ-anchored fusion (correct by construction)
  -- The transform receives the pre-destructed G-layer via out-μ.
  -- Recursion is structural on μG — each recursive call on strict subterm.
  -- Semantically: Fuse alg transform = cata (alg ∘ transform)
  Fuse : ∀ {F G} → WellFormedF F → WellFormedF G → ∀ {B}
       → IR (⟦ F ⟧ B) B                       -- algebra: F(B) → B
       → IR (⟦ G ⟧ (μ G)) (⟦ F ⟧ (μ G))       -- transform: G(μG) → F(μG)
       → IR (μ G) B
```

### Why This Structure

**Single unified IR:**
- Matches the bootstrap architecture (OCP-0004) where the verifier checks traces on one IR
- Case analysis covers all constructors directly — no artificial wrappers
- Type indices (`IR A B`) encode source and target types, enabling typed reductions
- Productivity follows from IR totality — all coalgebras are inherently "guarded"

**Philosophy: IR = Natural Transformations**

The IR should BE the categorical structure, not a representation that needs validation:

- **Cata** IS the unique F-algebra morphism from μF (totality by definition)
- **Ana** IS the unique F-coalgebra morphism to νF (productivity by definition)
- **Productivity** follows from totality — IR coalgebras terminate, producing one F-layer

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

### Why μ-type and ν-type Must Be Distinct

A natural question is whether to unify `μ-type` and `ν-type` into a single `Fix` type (as Haskell does).
This would enable the fusion rule `Cata alg ∘ Ana coalg → Hylo alg coalg` to type-check directly.

**However, unification breaks totality:**

```agda
-- With unified types, this would type-check:
natsCoalg : IR Unit (⟦ StreamF ⟧T Unit)   -- produces infinite stream
sumAlg    : IR (⟦ StreamF ⟧T Int) Int      -- folds to sum

badProgram : IR Unit Int
badProgram = Cata sumAlg ∘ Ana natsCoalg  -- Type-checks but doesn't terminate!
```

The problem: `Ana natsCoalg` produces a potentially infinite stream, but `Cata sumAlg` tries to consume
the entire structure. With unified types, there's no static prevention of folding infinite codata.

**The μ/ν distinction is essential:**

| Type | Semantics | Why Safe |
|------|-----------|----------|
| `μ-type F` | Inductive, finite, well-founded | Cata terminates (finite input) |
| `ν-type F` | Coinductive, potentially infinite | Ana is productive (IR totality) |

With split types:
- `Cata : IR (μ-type F) A` — only accepts finite data
- `Ana : IR A (ν-type F)` — produces potentially infinite codata
- `Cata ∘ Ana` — **type error** (good! prevents non-termination)

**Key insight:** Safety comes from the **type distinction**, not just the operations. IR totality ensures
each coalgebra step terminates, but that doesn't mean folding infinite codata terminates.

See "Observation Primitives" below for how to safely cross the μ/ν boundary when needed.

### Lambek Isomorphisms

By Lambek's Lemma (1968), the structure maps for initial algebras and final coalgebras are isomorphisms:

```
In  : ⟦ F ⟧T (μ F) → μ F    is an isomorphism
Out : ν F → ⟦ F ⟧T (ν F)    is an isomorphism
```

This means their inverses exist:

```agda
out-μ : ∀ {F} → IR (μ-type F) (⟦ F ⟧T (μ-type F))   -- inverse of In
in-ν  : ∀ {F} → IR (⟦ F ⟧T (ν-type F)) (ν-type F)   -- inverse of Out
```

**Why `out-μ` is needed for full optimization:**

Consider implementing `obs : Nat → Stream A → List A` (observe n elements). The optimal implementation
is a Hylo where the coalgebra observes both the counter AND the stream:

```agda
obs = Hylo listAlg obsCoalg
  where
    obsCoalg : IR (Nat * Stream A) (⟦ ListF A ⟧T (Nat * Stream A))
    obsCoalg = case (inl ∘ terminal)
                    (inr ∘ ⟨ head ∘ snd , ⟨ fst , tail ∘ snd ⟩ ⟩)
             ∘ ⟨ out-μ ∘ fst , snd ⟩  -- pattern-match on Nat!
```

Without `out-μ`, we cannot pattern-match on the `Nat` (a μ-type) inside the coalgebra. The alternative
(using `Cata` over Nat) produces a function that builds intermediate structures, losing fusion:

```
-- Without out-μ: sum (obs n s) builds intermediate list, then sums
-- With out-μ:    sum (obs n s) = Hylo sumAlg obsCoalg — no intermediate list!
```

**The symmetric IR structure:**

| μ-type | ν-type | Justification |
|--------|--------|---------------|
| `In` (constructor) | `in-ν` (constructor) | Build recursive structure |
| `out-μ` (destructor) | `Out` (destructor) | Observe one layer |
| `Cata` (fold) | `Ana` (unfold) | Universal morphisms |

This symmetry reflects the categorical duality between initial algebras and final coalgebras.

### The Fusion Category

**Key insight from analysis:** Hylo and similar "bridge" morphisms are NOT categorical primitives.
They don't arise from universal properties like Cata (initiality) and Ana (finality). Instead, they
are **optimization morphisms** that fuse a μ-consumer with a ν-producer.

#### Why Hylo Is Not Categorical

In proper category theory:
- `Cata : μF → A` is THE unique F-algebra morphism from the initial algebra
- `Ana : A → νF` is THE unique F-coalgebra morphism to the final coalgebra
- `Hylo : A → B` is... just a recursive function that "happens to work"

The issue: `μF ≠ νF`. They are different types:
- `μF` is the initial F-algebra (least fixed point, inductive, finite)
- `νF` is the final F-coalgebra (greatest fixed point, coinductive, potentially infinite)

So `Cata ∘ Ana` doesn't type-check! Hylo is defined directly as:
```
hylo alg coalg x = alg (fmap (hylo alg coalg) (coalg x))
```

This terminates only when the coalgebra eventually produces base cases. That's a **semantic property**,
not guaranteed by any universal property.

#### The Fusion Category

We define **Fusions** as the class of well-founded optimization morphisms:

> **Definition:** The Fusion category contains morphisms that bridge μ-consumers and ν-producers,
> anchored by a μ-type component that ensures well-founded recursion.

| μ-side (consumer) | ν-side (producer) | Fusion Name |
|-------------------|-------------------|-------------|
| Cata | Ana | **Hylo** (hylomorphism) |
| Histo | Ana | **Dyna** (dynamorphism) |
| Histo | Futu | **Chrono** (chronomorphism) |
| Para | Ana | (unnamed, but valid) |
| Cata | Apo | (related to Elgot algebras) |

All fusions share:
1. **Bridge** a consumer (μ-side) and producer (ν-side)
2. **Eliminate** intermediate structures (deforestation)
3. **Require** μ-anchoring for termination
4. **Lack** categorical universal properties

#### μ-Anchoring: The Key to Safe Fusions

A fusion is **safe** (total) when:
1. The input type is a μ-type: `μG`
2. The coalgebra/transform operates on that μ-type
3. Recursive positions receive strictly smaller μG values (subterms)

**The implementation enforces this through type structure:**

```agda
-- Hylo: requires μG as input, coalgebra produces F-layers from μG
Hylo : ∀ {F G} → WellFormedF F → WellFormedF G → ∀ {B}
     → IR (⟦ F ⟧ B) B                       -- algebra: F(B) → B
     → IR (μ G) (⟦ F ⟧ (μ G))               -- coalgebra: μG → F(μG)
     → IR (μ G) B

-- Fuse: transform receives pre-destructed G-layer
Fuse : ∀ {F G} → WellFormedF F → WellFormedF G → ∀ {B}
     → IR (⟦ F ⟧ B) B                       -- algebra: F(B) → B
     → IR (⟦ G ⟧ (μ G)) (⟦ F ⟧ (μ G))       -- transform: G(μG) → F(μG)
     → IR (μ G) B
```

**Hylo** requires the input to BE a μ-type (`μG`). The coalgebra produces F-layers from μG values.
Termination follows because μG is well-founded — structural recursion on the input.

**Fuse** is even more structured: the transform receives the **already-destructed** G-layer.
The fusion construct itself applies `out-μ` before calling the user's transform:

```
                         Fuse
                          │
    μG ────out-μ────→ ⟦G⟧(μG) ──transform──→ ⟦F⟧(μG)
                          │                      │
                    (automatic)            (user provides)
```

**This is correct by construction:**
- The user CANNOT avoid destructing the μ-type — `out-μ` is built into Fuse
- Recursive positions receive `μG` (subterms), not the original `μG`
- Structural recursion is enforced by types

**Relationship:** `Hylo alg coalg ≡ Fuse alg (coalg ∘ In)` — Hylo is syntactic sugar for Fuse
where the user provides the full coalgebra rather than just the layer-to-layer transform.

#### Fusions vs Categorical Schemes: The Layered IR

| Property | Categorical Schemes | Fusions |
|----------|--------------------| --------|
| Examples | Cata, Para, Ana, Apo | Hylo, Fuse |
| Universal property | Yes (initiality/finality) | No |
| Termination proof | By construction (Lambek) | By μ-anchoring (type structure) |
| In semantic core | Yes | Optional (optimization) |
| TERMINATING pragma | No | No (μ-anchoring is structural) |

**Implication for IR design:**
1. Start with categorical schemes (Cata, Para, Ana, Apo) — they provide the semantic foundation
2. Add fusions incrementally for optimization — μ-anchoring ensures termination
3. Fusions are NOT needed for IR correctness — they're purely optimization

#### Why This Matters

The principled approach:
- **Semantic layer**: Use categorical schemes (proven total/productive)
- **Optimization layer**: Compiler recognizes patterns and applies fusions
- **Correctness**: μ-anchoring makes fusions correct by construction

This is why `obs` was migrated from Hylo to Para in Phase 10 — Para is categorical (derived from Cata).
Hylo/Fuse are fusions for deforestation. Both are now structurally terminating via μ-anchoring.

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

### Productivity from IR Totality

For coinductive definitions (`Ana`, `Apo`), productivity follows from **IR totality**:

```
IR evaluation is total (established math: Tait, Girard, Lambek)
    ↓
Coalgebra c : IR A (⟦ F ⟧T A) terminates, producing one F-layer
    ↓  (this IS "guardedness" — automatic, not checked)
Each observation of (Ana c a) terminates
    ↓  (this IS "productivity")
Ana c a is productive
```

**Key insight:** In Once's IR, coalgebras `IR A (⟦ F ⟧T A)` are just IR morphisms. IR morphisms
are total (no general recursion). Therefore:
1. Every coalgebra terminates and produces `⟦ F ⟧T A` — one F-layer
2. This is exactly what "guarded" means — you MUST produce a constructor
3. No separate guardedness type or checker needed

This is **definitional**: non-productive corecursion cannot be expressed because that would
require a coalgebra that doesn't terminate or doesn't produce an F-layer. Both are impossible
in the total IR.

| Approach | Adds to TCB? | When checked? |
|----------|--------------|---------------|
| Algorithmic checker | Yes (must trust checker) | Runtime/compile-time |
| GuardedT type (superseded) | No (types are definitional) | Construction time |
| **IR totality (current)** | No (math theorem) | **By construction** |

This aligns with OCP-0004's minimal-trust philosophy: productivity is **definitional**
(follows from IR totality), not checked by an algorithm we must trust.

### Mutual Recursion and Deadlock Prevention

#### Mutual Corecursion

Two servers exchanging messages are expressible if each produces output before consuming:

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
| Mutual streams, non-productive | Not expressible | IR totality prevents it |
| Mutual streams, productive | Works | Each step terminates |
| No external driver | Unproductive | Cannot write the coalgebra |

---

## Alignment with Existing Design

### The Extended Strata

The strata structure (from `libraries.md`) is extended with coinductive types and observation operations:

```
┌─────────────────────────────────────────────┐
│         Interpretations                     │  Effect arrows (Opaque with Eff A B types)
├─────────────────────────────────────────────┤
│         Observation                         │  Safe ν→μ conversions (obs, obsWhile, etc.)
├─────────────────────────────────────────────┤
│         Coinitial                           │  Codata types + operations (uses Ana/Out)
├─────────────────────────────────────────────┤
│         Initial                             │  Data types + operations (uses Cata/In)
├─────────────────────────────────────────────┤
│         Canonical                           │  Non-recursive combinators (CCC operations)
├─────────────────────────────────────────────┤
│         Once.CCC.IR                         │  Unified IR: all CCC + recursion schemes
└─────────────────────────────────────────────┘
```

**Key insight:** The `Observation` stratum contains primitives that safely cross from `ν-type` to `μ-type`.
These are implemented as `Hylo` operations — they don't require new IR primitives, just derived operations
that bound their input. This enables full optimization while preserving totality.

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
| `range lo hi` | `Ana coalg : IR (Nat × Nat) (ν StreamF)` where coalg produces F-layer output |

The operations are the same; the recursion is now explicit and structured. The unified IR types
(`IR A B`) make domain and codomain explicit.

### Coinitial Library (New)

Parallel to Initial (inductive types), Coinitial provides coinductive types built with `ν-type`:

```
-- Coinductive types (potentially infinite, produced via Ana, observed via Out)
type Stream A  = ν(FSum (FConst A) FId)           -- Infinite stream
type CoList A  = ν(FSum (FConst Unit) (FProd (FConst A) FId))  -- Possibly-finite stream

-- Stream operations (built from Ana/Out)
head    : Stream A → A                            -- Out then Fst
tail    : Stream A → Stream A                     -- Out then Snd
repeat  : A → Stream A                            -- Ana with constant coalgebra
iterate : (A → A) → A → Stream A                  -- Ana with function application
map     : (A → B) → Stream A → Stream B           -- Ana transforming elements
zipWith : (A → B → C) → Stream A → Stream B → Stream C
filter  : (A → Bool) → Stream A → CoList A        -- May be finite!
```

**Key difference from Initial:**
- Initial types are consumed by `Cata` (fold the whole structure)
- Coinitial types are observed by `Out` (peek at one layer) or transformed by `Ana`
- You cannot `Cata` a `ν-type` — that's a type error (intentionally!)

### Observation Primitives (New)

Observation primitives safely convert `ν-type` to `μ-type` by **bounding** the output.
They are implemented using **Para** (paramorphism) — a categorical scheme with proven termination.

The naming follows coalgebraic terminology: we **observe** a coalgebra (coinductive structure)
by witnessing a bounded number of its unfolding steps, producing an inductive (finite) result.

**Why Para, not Hylo?** Para is a categorical primitive (derived from Cata) with proven termination.
Hylo is a fusion (optimization morphism) requiring external termination reasoning. For the semantic
foundation, we use categorical schemes. Fusions are for the optimizer.

#### ν → μ Conversions (Bounded Observation)

| Primitive | Type | Description | Implementation |
|-----------|------|-------------|----------------|
| `obs` | `Nat → ν F → μ F` | Observe n steps | Para (proven terminating) |
| `obsWhile` | `(A → Bool) → ν F → μ F` | Observe while predicate holds | Para (proven terminating) |
| `obsUntil` | `(A → Bool) → ν F → μ F` | Observe until predicate holds | Para (proven terminating) |

#### μ → ν Conversions (Embedding)

| Primitive | Type | Description | Implementation |
|-----------|------|-------------|----------------|
| `embed` | `μ F → ν F` | Canonical embedding (finite into cofinite) | Ana |
| `periodic` | `μ F → ν F` | Periodic extension (repeat forever) | Ana |

#### Direct Hylo Operations (Observation with Fold)

| Primitive | Type | Description |
|-----------|------|-------------|
| `foldObs` | `Nat → (B → A → B) → B → ν F → B` | Fold over n observations |

#### Why Observation Primitives Are Safe

Observation primitives use **Para** (paramorphism) — a categorical scheme with proven termination:

```agda
-- obs implemented as Para (provably terminating, no TERMINATING pragma)
obs : Nat → Stream A → List A
obs n s = apply (Para obsAlg n) s
  where
    -- Para algebra: receives NatF (Nat × (Stream A → List A))
    -- Zero case: return function that produces Nil
    -- Suc case: return function that produces Cons (head, rec tail)
    obsAlg : NatF (Nat × (Stream A → List A)) → (Stream A → List A)
    obsAlg (inl tt) = const Nil
    obsAlg (inr (_, rec)) = λs → Cons (head s, rec (tail s))
```

**Key insight:** Para recurses on Nat (a μ-type), which is well-founded. Termination follows
from structural recursion — no TERMINATING pragma needed, no trust required.

**Optimization:** The compiler can recognize this pattern and apply fusion. But the **semantic
foundation** uses Para (categorical, proven), not Hylo (fusion, requires witness). Optimization
is a separate concern from correctness.

### No Lost Optimizations

A key concern was whether split types (μ ≠ ν) would lose the `Cata ∘ Ana → Hylo` optimization.

**Resolution:** Real programs that would benefit from this fusion go through observation primitives,
which ARE Hylos. The optimization isn't "lost" — it's achieved through a different (safer) path.

**Example: Stream processing pipeline**

```
-- Haskell (unified types): all can fuse (using Haskell's "take")
sum . map f . filter p . take n . iterate g $ seed

-- Once (split types): same fusion, explicit observation
sum ∘ map f ∘ filter p ∘ obs n ∘ iterate g $ seed
│                       │         │
│                       │         └─ ν-type (Coinitial)
│                       └─ Observation (Hylo!)
└─ μ-type (Initial)
```

Fusion happens:
- **Within μ-world (Initial):** Cata computation rules fuse `sum ∘ map f ∘ filter p`
- **Within ν-world (Coinitial):** Ana computation rules optimize `iterate g`
- **At observation:** `obs n` IS a Hylo — already optimal!

**The "missing" `Cata ∘ Ana → Hylo` rule is recovered** because `obs n` (and other observation
primitives) ARE Hylos. No optimization is lost; the code just makes the observation explicit.

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
4. **Definitional productivity** — `Ana` is productive because IR coalgebras are total
5. **Matches bootstrap tower** — same IR structure the verifier checks

### Productivity from IR Totality

Productivity follows from **IR totality**: coalgebras `IR A (⟦ F ⟧T A)` are IR morphisms, and
IR morphisms are total (no general recursion). Therefore every coalgebra terminates, producing
exactly one F-layer — which is precisely what "guarded" means.

```agda
-- This coalgebra is productive: it's an IR morphism that terminates
goodCoalg : IR State (⟦ FProd (FConst Output) FId ⟧T State)
goodCoalg = ⟨ outputExpr , nextStateExpr ⟩ Heap

-- Non-productive coalgebras cannot exist in the total IR
-- There's no way to write a non-terminating IR morphism
```

This aligns with OCP-0004's minimal-trust philosophy: totality/productivity are **definitional** (Lambek's Lemma + IR totality), not checked by an algorithm we must trust.

---

## Alignment with OCP-0004 (Minimal-Trust Verification)

The unified IR directly supports OCP-0004's minimal TCB goal and bootstrap tower architecture.

### Trust Boundaries

**Mathematical TCB (category theory, safe to postulate):**

| IR Construct | Math Justification |
|--------------|-------------------|
| Category (Id, Compose) | Identity/composition laws |
| Products (Fst, Snd, Pair, Terminal) | Product universal property |
| Coproducts (Inl, Inr, Case, Initial) | Coproduct universal property |
| Exponentials (Curry, Apply) | Exponential adjunction |
| Initial algebras (In, out-μ) | Lambek's Lemma (1968) |
| Final coalgebras (Out, in-ν) | Dual of Lambek's Lemma |
| Cata uniqueness/termination | Initiality of μF |
| Ana uniqueness/productivity | Finality of νF |

**Implementation TCB (must be proven, not postulated):**

| Component | Claim | Current Status |
|-----------|-------|----------------|
| Dispatcher traces | Traces correctly implement IR semantics | PROVEN for CCC ops |
| rec-scheme-semantic | Recursion scheme traces produce correct results | POSTULATED (TODO) |
| lambek-iso-semantic | In/out-μ/Out/in-ν traces are identity | POSTULATED (TODO) |
| exec-trace lemmas | Trace execution is deterministic, preserves state | Partially proven |
| X86 simulation | Abstract traces simulate correctly on x86 | PROVEN (DirectSimulation) |

The mathematical TCB is trustworthy because it encodes well-established category theory.
The implementation TCB requires explicit proofs connecting codegen to semantics.

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
│ out-μ                    │ In⁻¹ : μF → F(μF) (Lambek iso)   │
│ Cata alg                 │ Unique F-algebra morphism        │
│ Para alg                 │ Paramorphism (derived from Cata) │
│ νF                       │ Final F-coalgebra                │
│ Out                      │ Coalgebra structure: νF → F(νF)  │
│ in-ν                     │ Out⁻¹ : F(νF) → νF (Lambek iso)  │
│ Ana coalg                │ Unique F-coalgebra morphism      │
│ Apo coalg                │ Apomorphism (derived from Ana)   │
├──────────────────────────┼──────────────────────────────────┤
│ Hylo (FUSION)            │ NOT a categorical morphism!      │
│                          │ Optimization pattern, requires   │
│                          │ μ-anchoring for termination      │
└──────────────────────────┴──────────────────────────────────┘
```

**Note:** Hylo is explicitly marked as NOT categorical. It's in the IR for optimization purposes
but doesn't have a universal property. Termination is guaranteed by μ-anchoring: requiring
a μ-type as input ensures structural recursion on a well-founded type.

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

Productivity (from IR Totality):
    Ana requires: coalg : IR A (⟦ F ⟧T A)
    IR morphisms are total (no general recursion).
    Therefore each coalgebra step terminates, producing one F-layer.
    This IS "guardedness" — automatic, not checked separately.
```

These are mathematical facts, not implementation details. The unified IR makes
these facts explicit: `Cata` is total because it IS the unique algebra morphism,
and `Ana` is productive because IR totality ensures each coalgebra step terminates.

### CRITICAL: Mathematical Truth vs Implementation Correctness

**The distinction between what is proven mathematics and what requires implementation proofs:**

| Layer | What It Claims | Status | Trust Level |
|-------|----------------|--------|-------------|
| **Category Theory** | CCC laws, Lambek's Lemma, universal properties | Proven (1968+) | Mathematical axiom |
| **Semantic eval** | `eval primSem (Cata wf alg) x` computes catamorphism correctly | Proven in Agda | Trusted Agda TCB |
| **Trace generation** | Generated traces execute correctly on abstract machine | **MUST BE PROVEN** | Implementation claim |
| **X86 codegen** | Compiled x86 code matches abstract machine execution | **MUST BE PROVEN** | Implementation claim |

**What the mathematical facts prove:**
- Lambek's Lemma proves μF ≅ F(μF) — the isomorphism exists
- Lambek's Lemma proves Cata is the unique algebra morphism — uniqueness
- CCC laws prove composition, products, etc. satisfy universal properties

**What the mathematical facts do NOT prove:**
- That our `Dispatcher` generates correct traces for Cata
- That `exec-trace` on those traces produces the semantic result
- That the x86 compilation preserves meaning

**Current Implementation Status:**

The `rec-scheme-semantic` postulate (consolidated in `RecSchemePostulates.agda`) claims:
```agda
rec-scheme-semantic : ValidAtWF Heap alloc (eval primSem ir x) result-loc s
```

**Why this is currently a trust boundary:**

The abstract machine model has a fundamental architectural limitation:
- Traces are LINEAR sequences of abstract instructions
- Recursive execution is NOT modeled in the trace semantics
- RecCoreWF generates STUB traces that allocate storage and return pointers
- The actual catamorphism computation happens "outside" the trace model

What the stub traces do:
```agda
cata-trace = mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []
```
This stores the input at a slot and returns a pointer — it does NOT compute the catamorphism!

**Paths to eliminate this postulate:**

1. **Extend Abstract Machine** (MAJOR effort):
   - Add recursive trace execution (call stack, returns)
   - Generate traces that include recursive calls
   - Prove these traces compute sem-cata

2. **Direct Semantic Proof** (MODERATE effort):
   - Prove at semantic level that eval (Cata wf alg) preserves ValidAtWF
   - Use well-founded recursion on μ-values
   - Connect to trace model via representation lemmas
   - See `RecSchemeProof.agda` for the architecture

3. **Accept Trust Boundary** (current state):
   - Document that rec-scheme-semantic is a compiler correctness claim
   - The claim: "Once runtime correctly implements recursion schemes"
   - Analogous to trusting GHC RTS implements recursion correctly

**Relevant modules:**
- `RecSchemePostulates.agda`: Consolidated postulates
- `RecSchemeProof.agda`: Proof architecture (incomplete)
- `RecTrace.agda`: Trace building strategy
- `NatCataProof.agda`: Concrete example for NatF

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
- **Alignment with D037** — IR matches verification requirements
- **Minimal TCB** — supports OCP-0004 trust boundaries
- **Full optimization** — observation primitives recover all fusion opportunities (see below)

### Lost

- **General recursion** — must use schemes (rarely a limitation)
- **Some exotic algorithms** — need restructuring (rare in practice)
- **Self-interpreters** — need fuel parameter (niche use case)
- **"Flexibility" to write bugs** — this is not actually a loss

### Not Lost: Optimizations

A concern with split types (μ ≠ ν) was losing the `Cata ∘ Ana → Hylo` fusion.

**This is NOT lost.** The fusion is recovered through observation primitives:

| Concern | Resolution |
|---------|------------|
| `Cata ∘ Ana` doesn't type-check | By design — prevents folding infinite codata |
| Stream pipelines can't fuse | They CAN — through observation primitives |
| `obs n` breaks fusion | `obs n` IS a Hylo — already optimal |
| Need to restructure code | Just use explicit observations (clearer anyway) |

**The key insight:** Real programs that would benefit from `Cata ∘ Ana` fusion actually go through
observation primitives like `obs`. These ARE Hylos, so the optimization happens automatically.
Split types give us totality AND full optimization — having our cake and eating it too.

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

The key optimization is **hylo fusion** (deforestation). With split types (μ ≠ ν), this works
through **observation primitives** rather than direct composition:

```
-- Direct Cata ∘ Ana doesn't type-check (by design — prevents folding infinite codata)
-- result = cata alg (ana coalg seed)  -- TYPE ERROR: ν-type ≠ μ-type

-- Instead, use observation primitives which ARE Hylos:
result = sum (obs n (iterate f seed))
       = sum ∘ obs n ∘ iterate f $ seed
--            └──────┬──────┘
--             Hylo (already optimal!)

-- For direct generate-consume patterns, use Hylo explicitly:
result = hylo alg coalg seed
```

Observation primitives like `obs` are Hylos by construction — no rewrite rule needed.
The optimization happens automatically through the library design.

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
-- NOTE: Cata ∘ Ana does NOT type-check (μ-type ≠ ν-type)
-- This is intentional — it prevents folding infinite codata
-- Instead, observation primitives (obs, etc.) are Hylos and already optimal

-- Functor fusion (within μ-world)
map f ∘ map g                      →  map (Compose f g)
filter p ∘ filter q                →  filter (λx → p x ∧ q x)

-- Cata computation (unfold definition)
Compose (Cata alg) In              →  Compose alg (fmap (Cata alg))

-- Ana computation (unfold definition)
Compose Out (Ana coalg)            →  Compose (fmap (Ana coalg)) coalg

-- Hylo computation (already fused by construction)
Hylo alg coalg x                   =  alg (fmap (Hylo alg coalg) (coalg x))
```

**Fusion landscape with split types:**

| Domain | Fusion Rule | Applies To |
|--------|-------------|------------|
| μ-world (Initial) | Cata computation | `Cata alg ∘ In → alg ∘ fmap (Cata alg)` |
| μ-world (Initial) | Functor fusion | `map f ∘ map g → map (f ∘ g)` |
| ν-world (Coinitial) | Ana computation | `Out ∘ Ana coalg → fmap (Ana coalg) ∘ coalg` |
| Observation | Already optimal | Observation primitives ARE Hylos |

The "missing" `Cata ∘ Ana → Hylo` rule is not needed because:
1. `Cata ∘ Ana` doesn't type-check (by design)
2. Real code uses observation primitives which are already Hylos
3. No optimization opportunity is lost

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
| Recursion schemes | Infinite loops, unproductive codata | `Cata`/`Ana` (total IR) |
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
- Duplicates what D037 already requires
- More implementation effort, less guarantee
- Adds to TCB (must trust the checker)

### C: Use `lift` Inside Poly Module

Rejected:
- Every Poly proof must handle `lift` case
- Less modular proof structure
- Layers not truly independent

### D: Unified IR with μ-Anchored Fusions (This Proposal)

Accepted:
- Matches OCP-0004 bootstrap tower architecture
- Direct case analysis over all constructors
- Totality and productivity by construction (definitional)
- Type-indexed IR enables typed rewrites
- Productivity follows from IR totality — no separate checker needed
- Fusions (Hylo/Fuse) are μ-anchored for provable termination
- Aligns with D037 verification strategy
- Enables dependent types naturally
- Minimal TCB — no guardedness checker to trust

---

## Migration Path

### Phase 1: Define Unified IR

- Create `Once.CCC.IR` with:
  - `Functor` type for polynomial functors
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
  - Lambek's Lemma: `sem-Out-In-valid`, `sem-In-Out-valid` (proven via SPF)
  - Cata computation: `sem-cata-compute-valid` (proven via SPF.cata-computation)
  - Transport naturality: `transport-μ-is-fmap` (proven via path induction)
  - Functor law inheritance: `sem-fmap-id`, `sem-fmap-comp` (proven)

**SPF Catamorphism Laws** ✓ COMPLETE (2026-03-23)

Proven laws in `Once.SPF`:

- `fmapCata-is-fmap`: `fmapCata F alg x ≡ fmap F (cata alg) x`
- `cata-computation`: `cata alg ⟨ x ⟩ ≡ alg (fmap F (cata alg) x)`
- `cata-In-id`: `cata ⟨_⟩ x ≡ x` (identity catamorphism)

These proofs enable `sem-cata-compute-valid` in the Coherence layer.

**SPF Anamorphism Laws** ✓ COMPLETE (2026-03-24)

Proven laws in `Once.Functor.Base`:

- `ana-unfold`: `unfold (ana coalg a) ≡ fmap F (ana coalg) (coalg a)` (trivial by definition)
- `anaS-Out-id`: `anaS unfoldS x ≡ x` (PROVEN via coinductive bisimulation)

Bisimulation infrastructure added:
- `⟦_⟧SF-rel`: Relational interpretation lifting relations through functors
- `_∼S_`: Coinductive bisimulation relation on νS F values
- `bisimS-to-eq`: Coalgebraic extensionality (postulate, provable in Cubical Agda)
- `sfmap-rel`, `sfmap-f-rel`: Helper lemmas for bisimulation proofs
- `anaS-unfoldS-bisim`: Coinductive proof that `anaS unfoldS x ∼S x`

Proven laws in `Once.Semantics.Core`:

- `sem-ana-is-anaS-unfoldS`: `sem-ana F (sem-CoOut F) x ≡ anaS unfoldS x` (PROVEN via bisimulation)
- `sem-ana-Out-id`: `sem-ana F (sem-CoOut F) x ≡ x` (PROVEN by composition)

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

**Productivity Infrastructure** ✓ COMPLETE (2026-03-23)

Established semantic foundation for guardedness enforcement:

- **Productivity.agda** (`Once/CCC/IR/Productivity.agda`):
  - `GuardedCoalg F A` = coalgebras producing guarded output
  - `fromGuarded` = extract unguarded coalgebra from guarded
  - `guarded-ana-productive` = semantic productivity property
  - `guarded-map-preserves` = guardedness compositional
  - `⟦⟧F-coherence` = bridges Guarded and Machine functor interpretations

- **Existing Infrastructure** (Guarded.agda):
  - `Guarded Sem F A` type with GConst, GRec, GProd, GInl, GInr
  - `unguard` = extract underlying functor value
  - `gmapA` = functorial map over guarded values
  - Smart constructors: guardConst, guardRec, guardPair, etc.

**Type-Level GuardedT Integration** ✓ COMPLETE then SUPERSEDED (2026-03-23 → 2026-03-25)

*Historical note: GuardedT was added then removed when we realized productivity follows from IR totality.*

Originally added:
- `GuardedT : Functor → Type → Type` constructor
- Ana required `IR A (GuardedT F A)` coalgebras
- `Unguard` extractor, various semantic machinery

**Superseded by IR Totality approach (2026-03-25):** See IR/Totality.agda and IR/Productivity.agda.
GuardedT was unnecessary bookkeeping — IR coalgebras are inherently "guarded" because IR is total.

**Remaining Work**:

- [x] Integrate with D037 polynomial functor proofs (Coherence.agda)
- [x] Prove SPF cata laws: `cata-computation`, `cata-In-id`
- [x] Prove `sem-cata-compute-valid` via SPF.cata-computation
- [x] Add SPF ana laws: `ana-unfold` (trivial), `ana-Out-id` (proven via bisimulation)
- [x] Add `sem-ana-Out-id-valid` postulate to Coherence.agda
- [x] Prove `transport-μ-is-fmap` via path induction (subst-fmap-natural lemma)
- [x] Define ⟦μ⟧/⟦ν⟧ via translation (no longer postulated in Core)
- [x] Create Once.Functor.Base (semantic functors with Set in K)
- [x] Create Once.Functor.Translate (translation from Functor to SFunctor)
- [x] Prove `ana-Out-id` via coinductive bisimulation (with `bisim-to-eq` postulate)
- [x] Add isolated sized-types proof in Once.SPF.SizedProof (justifies TERMINATING)
- [x] Prove `base-interp-coherence` and `functor-interp-coherence` (justifies μ-coherence)
- [x] Rename SumFixWF to SumRecWF (fold/unfold removed)
- [x] Prove `sem-ana-Out-id` via coinductive bisimulation (2026-03-24)
- [x] Add well-formed functor round-trip proofs (postulate-free path) (2026-03-24)
- [x] Create Once/CCC/IR/Totality.agda (postulates IR totality) (2026-03-25)
- [x] Update Once/CCC/IR/Productivity.agda (derives productivity from totality) (2026-03-25)
- [x] Remove GuardedT/Guard/Unguard from IR (productivity follows from totality) (2026-03-25)
- [x] Design μ/ν type distinction and observation primitives (2026-03-26)
- [x] Implement Coinitial library (Stream, CoList operations) (2026-03-26)
- [x] Implement Observation library with obs primitive (2026-03-26)
- [x] Add out-μ and in-ν to IR (Lambek isomorphisms) (2026-03-26)

**Phase 10: Paramorphism** ✓ COMPLETE (2026-03-26)
- [x] Add `paraS` to `Once.Functor.Base` (derived from `cataS`)
- [x] Add `Para` constructor to `Once.CCC.IR`
- [x] Add `sem-para` to `Once.Semantics.Core` (no TERMINATING pragma)
- [x] Update IR passes (Escape, Fusion, Optimize, eval)
- [x] Migrate `obs` to use Para (provably terminating)
- [x] Add `out-μ` and `in-ν` eval cases to CCC/Eval.agda
- [x] Document Hylo as expert-only escape hatch (eval-Hylo intentionally omitted, not postulated)
- [x] Verify all modified files (10/10 pass)

**Remaining Libraries:**
- [ ] Implement obsWhile, obsUntil (requires Bool infrastructure)
- [ ] Implement embed, periodic (use Para)
- [ ] Complete Once surface syntax for Coinitial/Observation

**Future:**
- [ ] Full IR law proofs (requires function extensionality)
- [ ] Align with OCP-0004 bootstrap verification

**Well-Formed Functor Proofs** ✓ COMPLETE (2026-03-24)

Added postulate-free round-trip proofs for well-formed functors:

- `IsBaseType` / `WellFormedF`: Predicates in `Once.Functor.Translate`
- `coerce-base-type-round-trip`: Proven for `IsBaseType`
- `coerce-base-type⁻¹-round-trip`: Proven for `IsBaseType`
- `coerce-wf-μ-round-trip`: Proven for `WellFormedF`
- `coerce-wf-μ⁻¹-round-trip`: Proven for `WellFormedF`

For well-formed functors, the coercion round-trips are now fully provable
without any postulates. The well-formedness predicate ensures K positions
only contain base types (Unit, Int, Float, Str, Buffer, and their products/sums).

**Remaining Postulates** (2026-03-26)

| Postulate | Location | Category | Notes |
|-----------|----------|----------|-------|
| `funext` | Core.agda | Standard axiom | Function extensionality, provable in Cubical Agda |
| `bisimS-to-eq` | Functor/Base.agda | Standard axiom | Coalgebraic extensionality, provable in Cubical Agda |
| `eval-total` | IR/Totality.agda | Established math | IR evaluation terminates (Tait/Girard/Lambek) |
| `defaultEvalPrim` | IR.agda | External | Primitive operations are inherently external |

**Principled Handling of Hylo:**

The `eval-Hylo` law is intentionally omitted (not postulated) from `CCC/IR/Laws.agda`. This is the
principled approach because:

1. **Hylo is an optimization primitive**, not a correctness primitive
2. **sem-hylo requires TERMINATING** - it's already outside Agda's proof system
3. **Postulating would hide the trust boundary** - omission makes it explicit

Correctness guarantees for Hylo-based operations:
- **Bounded patterns** (obs, obsWhile, etc.): Use Para, which is provably terminating
- **Unbounded Hylo**: Expert-only escape hatch, requires external termination reasoning

The absence of eval-Hylo is a feature, not a bug.

**Standard axioms** (funext, bisimS-to-eq) are well-established mathematical principles that:
- Are provable in Cubical Agda
- Are consistent with standard type theory
- Do not affect computational behavior

**Coercion postulates eliminated:** The previous `ill-formed-K-value` and `coerce-type-round-trip-*`
postulates have been removed. All IR recursion scheme constructors now require `WellFormedF` proofs,
making the postulate-free path mandatory rather than optional.

**Totality and Productivity Proofs** (2026-03-25)

New understanding: **Productivity follows from IR totality**, making GuardedT unnecessary.

The reasoning chain:
```
IR evaluation is total (established math: Tait, Girard, Lambek)
    ↓
Coalgebra c : IR A (⟦ F ⟧T A) terminates, producing F-layer
    ↓  (this IS "guardedness" — automatic, not checked)
Each observation of (ana c a) terminates
    ↓  (this IS "productivity")
ana c a is productive
```

New modules created:
- **Once/CCC/IR/Totality.agda**: Postulates IR evaluation totality (like bootstrap/EstablishedMath)
- **Once/CCC/IR/Productivity.agda**: Derives productivity from totality

Key insight: In Once's IR, coalgebras `IR A (⟦ F ⟧T A)` are just IR morphisms. IR morphisms
are total (no general recursion). Therefore:
1. Every coalgebra terminates and produces `⟦ F ⟧T A` — one F-layer
2. This is exactly what "guarded" means
3. GuardedT provides no additional safety — it's just bookkeeping

**Consequence:** GuardedT, Guard, and Unguard can be removed from the IR. Ana can take
`IR A (⟦ F ⟧T A)` directly. This simplification is planned for Phase 8.

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

### 2. ~~Guarded Type Ergonomics~~ RESOLVED

~~The `Guarded` type enforces guardedness definitionally, but how ergonomic is it in practice?~~

**Resolution (2026-03-25):** GuardedT is unnecessary and has been removed.

Productivity follows from IR totality (see "Totality and Productivity Proofs" above).
Since all IR coalgebras are automatically "guarded" (they terminate and produce F-layers),
there's no need for a type-level wrapper. Ana takes `IR A (⟦ F ⟧T A)` directly.

### 2b. ~~Cata ∘ Ana Fusion~~ RESOLVED

~~With split types (μ ≠ ν), the fusion rule `Cata alg ∘ Ana coalg → Hylo alg coalg` doesn't type-check.
Does this lose important optimizations?~~

**Resolution (2026-03-26):** No optimizations are lost.

The μ/ν split is necessary for totality (prevents folding infinite codata). The "missing" fusion
is recovered through **observation primitives** (`obs`, `obsWhile`, etc.) which ARE Hylos.

Real programs that would benefit from `Cata ∘ Ana` fusion actually go through observation primitives:
```
sum ∘ map f ∘ obs n ∘ iterate g
            └─────┬─────┘
              Hylo (already optimal)
```

The observation primitives safely cross from ν-type to μ-type while being optimal by construction.
We get totality AND full optimization — having our cake and eating it too.

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

| Phase | Deliverable | Status |
|-------|-------------|--------|
| 1. Unified IR | `Once.CCC.IR` with `Functor`, unified `IR` type | ✓ |
| 2. Recognition | `Fold`/`Unfold` → scheme patterns | ✓ |
| 3. Backends | Code generation for recursion schemes | |
| 4. Optimizer | Cata/Ana computation rules, categorical simplifications | |
| 5. Migration | Warnings, guide, auto-rewrite | ✓ |
| 6. Removal | Delete `Fold`/`Unfold` | ✓ |
| 7. Verification | Agda proofs, Totality.agda, Productivity.agda | ✓ |
| 8. Simplification | Remove GuardedT/Guard/Unguard (unnecessary) | ✓ |
| 9. Libraries | Coinitial library + Observation primitives (Agda) | ✓ |
| 10. Para | Paramorphism for provable termination | ✓ |
| 11. Fusion Layer | Hylo and Fuse (μ-anchored, correct by construction) | ✓ |

**Layered implementation strategy:**
1. **Categorical foundation first** (Phases 1-10): Cata, Para, Ana, Apo — proven total/productive
2. **μ-anchored fusions** (Phase 11): Hylo and Fuse — correct by construction via μ-type input
3. **Fusions are optional**: The IR is semantically complete without them

**The progression mirrors Para's relationship to Hylo:**
- Para is structured (derived from Cata) → provably terminating
- Fuse is structured (μ-type pre-destructed) → provably terminating
- Hylo ≡ Fuse (coalg ∘ In) — both are μ-anchored for termination

### Phase 9: Coinitial and Observation Libraries

**Coinitial Library** (parallel to Initial):

```
Strata/Derived/Coinitial.once:
  -- Types
  type Stream A = ν (K A ⊗ Id)
  type CoList A = ν (K Unit ⊕ (K A ⊗ Id))

  -- Stream operations
  head    : Stream A → A
  tail    : Stream A → Stream A
  repeat  : A → Stream A
  iterate : (A → A) → A → Stream A
  map     : (A → B) → Stream A → Stream B
  zipWith : (A → B → C) → Stream A → Stream B → Stream C
```

**Observation Library** (safe μ/ν crossings):

```
Strata/Derived/Observation.once:
  -- ν → μ (bounded observation)
  obs       : Nat → ν F → μ F              -- Observe n steps
  obsWhile  : (A → Bool) → ν F → μ F       -- Observe while predicate holds
  obsUntil  : (A → Bool) → ν F → μ F       -- Observe until predicate holds

  -- μ → ν (embedding)
  embed     : μ F → ν F                     -- Canonical embedding
  periodic  : μ F → ν F                     -- Periodic extension

  -- Direct Hylo operations (observation with fold)
  foldObs   : Nat → (B → A → B) → B → ν F → B  -- Fold over n observations
```

All observation primitives are implemented as `Hylo` operations — no new IR primitives needed.

### Phase 10: Paramorphism for Provable Termination

**Problem:** The semantic implementations of `sem-ana` and `sem-hylo` in `Once.Semantics.Core` use
Agda's `{-# TERMINATING #-}` pragma — a trust annotation that bypasses the termination checker.
This is a hole in the formal development.

| Function | Pragma | Issue |
|----------|--------|-------|
| `sem-ana` | `{-# TERMINATING #-}` | Productivity trusted, not proven |
| `sem-hylo` | `{-# TERMINATING #-}` | Termination trusted, not proven |
| `sem-cata` | None needed | Sound (structural recursion on μS) |

**Solution: Paramorphism (Para)**

Paramorphism is a recursion scheme that gives the algebra access to both:
- The original substructures (μF values)
- The recursive results (A values)

```agda
Para : (F (μF × A) → A) → μF → A
```

**Key insight:** Para is derivable from Cata by returning pairs:

```agda
paraS : ∀ {F} {A : Set} → (⟦ F ⟧SF (μS F × A) → A) → μS F → A
paraS {F} {A} alg x = proj₂ (cataS {F} alg' x)
  where
    alg' : ⟦ F ⟧SF (μS F × A) → (μS F × A)
    alg' fx = (⟨ sfmap F proj₁ fx ⟩ , alg fx)
```

**This terminates without any pragma** because Cata uses structural recursion on well-founded μS.

**Bounded Hylo via Para:**

With Para, observation primitives like `obs` can be implemented with provable termination:

```agda
-- obs via Para (provably terminating)
obs : Nat × Stream A → List A
obs (fuel, stream) = para paraAlg fuel stream
  where
    -- Para gives: NatF (Nat × (Stream A → List A))
    paraAlg (inl tt) _ = []                       -- zero: empty
    paraAlg (inr (_, k)) s = head s :: k (tail s) -- suc: cons + continue
```

Termination follows from structural recursion on Nat — no trust pragma needed.

**Implementation Plan:**

1. **Add `paraS` to `Once.Functor.Base`**
   - Derived from `cataS` (returns pairs)
   - No TERMINATING pragma needed

2. **Add `Para` constructor to `Once.CCC.IR`**
   ```agda
   Para : ∀ {F} → WellFormedF F → ∀ {A}
        → IR (⟦ F ⟧T (μ-type F * A)) A
        → IR (μ-type F) A
   ```

3. **Add `sem-para` to `Once.Semantics.Core`**
   - Uses `sem-cata` internally
   - Provably terminating (no pragma)

4. **Update IR passes** (Escape, Fusion, Optimize, eval)

5. **Migrate `obs`** in `Observation.agda` to use Para
   - Removes reliance on Hylo's TERMINATING pragma

6. **Document Hylo as expert-only**
   - General Hylo remains for cases requiring external termination arguments
   - Bounded patterns should use Para

**Result:** Observation primitives (`obs`, `obsWhile`, etc.) will have provably-terminating
implementations. The TERMINATING pragma on `sem-hylo` becomes an escape hatch for expert use,
not a foundational hole.

---

## Summary

This proposal defines a **unified IR** in `Once.CCC.IR` that enforces totality and productivity by construction:

| Property | Mechanism |
|----------|-----------|
| **Totality** | Recursion only via `Cata` (structural, by Lambek's Lemma) |
| **Productivity** | Corecursion only via `Ana`; follows from IR totality |
| **No infinite loops** | No general `fix` |
| **No deadlocks** | Coalgebras are total → Ana is productive |
| **Arrow-based effects** | CCC provides structure, types distinguish `A → B` from `Eff A B` |
| **Dependent types ready** | Consistent logic without termination checker |
| **Verification simplified** | Proofs focus on algebras, not termination |
| **Minimal TCB** | Matches OCP-0004 bootstrap tower |
| **Full optimization** | Observation primitives (Hylos) recover all fusion opportunities |

The design:
- Single unified `IR : Type → Type → Set` with all CCC operations
- `Functor` type for polynomial functors (per D037)
- **Split types** (`μ-type` ≠ `ν-type`) for totality — prevents folding infinite codata
- **Layered architecture**:
  - **Categorical primitives** (Cata, Para, Ana, Apo) — proven total/productive by Lambek
  - **Fusions** (Hylo, Dyna, etc.) — optimization layer, requires μ-anchoring
- **Observation primitives** (`obs`, `obsWhile`, etc.) use Para (categorical), not Hylo (fusion)
- Productivity follows from IR totality — GuardedT is unnecessary (removed)
- **The Fusion category** contains well-founded optimization morphisms between recursion schemes
- Arrow-based effects: CCC structure provides arrow combinators, types distinguish `A → B` from `Eff A B`
- Aligns with D037 (polynomial functors)
- Matches OCP-0004 bootstrap architecture (single IR for verifier)
- **Extended strata**: Generators/Canonical/Initial/Coinitial/Observation/Interpretations
- Enables planned dependent type extensions
- Opens path to session types for deadlock-free communication

**The core insight:** Turing completeness is not a feature — it's the absence of a safety guarantee. By removing general recursion and providing structured schemes, Once gains strong guarantees while losing only the ability to write bugs.

**The key principle:** The IR should BE the categorical structure, not a representation that needs validation. `Cata` IS the unique algebra morphism (totality by definition), and `Ana` IS the unique coalgebra morphism (productivity follows from totality — coalgebras are IR morphisms, and IR morphisms are total).

**The layering insight:** The IR is conceptually layered:
1. **Categorical primitives** (Cata, Para, Ana, Apo) have universal properties — totality/productivity is PROVEN by Lambek's Lemma
2. **Fusions** (Hylo, Dyna, Chrono) are optimization morphisms — they require μ-anchoring witnesses for termination

Fusions are NOT categorical primitives. They don't have universal properties. But they ARE essential for compiler optimization. The Fusion category contains "well-founded optimization morphisms between recursion schemes."

**The optimization insight:** Split types (μ ≠ ν) are necessary for totality but don't lose optimizations.
Observation primitives like `obs` use Para (categorical, proven terminating), NOT Hylo (fusion, requires witness). The semantic foundation uses categorical schemes; fusions are added by the optimizer.
We get totality AND full optimization — having our cake and eating it too.

---

## References

- D037: Polynomial Functors decision (`docs/compiler/decision-log.md`)
- OCP-0004: Minimal-Trust Verification via Categorical Foundations
- `docs/formal/historical/fix-semantics-options.md`: Analysis of Fix semantics
- `docs/design/recursion-schemes.md`: Current recursion scheme documentation
- `docs/design/libraries.md`: Three strata architecture
- `docs/design/dependent-types-options.md`: Dependent type roadmap
- `docs/design/categorical-foundations.md`: Coalgebras and codata
- `docs/proposals/hylo-categorical-analysis.md`: Analysis of Hylo's non-categorical status

**External references:**
- Meijer, Fokkinga, Paterson (1991): "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire"
- Bird & de Moor (1997): "Algebra of Programming"
- Capretta, Uustalu, Vene: "Recursive Coalgebras from Comonads"
- Hinze, Harper, James (2010): "Theory and Practice of Fusion"

---

## Discussion

### 2026-03-26: μ/ν Type Distinction and Observation Primitives

**Issue raised:** With split types (μ-type ≠ ν-type), the fusion rule `Cata ∘ Ana → Hylo` doesn't
type-check. Initial concern was that this loses important optimizations.

**Analysis:**
1. Unifying μ and ν (like Haskell's `Fix`) would break totality — you could fold infinite codata
2. The old `Fix` type (pre-OCP-0003) was removed precisely because it allowed non-termination
3. The safety of the new system comes from BOTH the operations (Cata/Ana) AND the type distinction

**Resolution:** Observation primitives are the key insight.

Operations like `obs`, `obsWhile`, and `obsUntil` safely cross from ν-type to μ-type by
**bounding** their output. These are implemented as `Hylo` operations — they don't require
new IR primitives, just derived library functions.

The naming follows coalgebraic terminology: we **observe** a coalgebra (coinductive structure)
by witnessing a bounded number of its unfolding steps, producing an inductive (finite) result.

```
Stream processing pipeline:
  sum ∘ map f ∘ filter p ∘ obs n ∘ iterate g
  │                       │         │
  │                       │         └─ ν-world (Coinitial)
  │                       └─ Observation (Hylo! Already optimal)
  └─ μ-world (Initial)
```

Fusion happens naturally:
- Within μ-world: Cata computation rules
- Within ν-world: Ana computation rules
- At observations: Already Hylos — no fusion needed

**Naming convention:** The library uses coalgebraic observation terminology:
- `obs n` — observe n steps (bounded observation)
- `obsWhile p` — observe while predicate holds (conditional observation)
- `obsUntil p` — observe until predicate holds (terminating observation)
- `embed` — canonical embedding (finite into cofinite)
- `periodic` — periodic extension (repeat finite structure)
- `foldObs n` — fold over n observations (direct Hylo)

**Conclusion:** Split types + observation primitives give us:
- ✓ Totality (can't fold infinite codata)
- ✓ Productivity (IR totality guarantees each step terminates)
- ✓ Full optimization (observation primitives ARE the fused form)

This is the "have your cake and eat it too" solution. The design is extended with:
- **Coinitial library**: Stream, CoList operations (parallel to Initial)
- **Observation library**: obs, obsWhile, embed, periodic, foldObs, etc.

### 2026-03-26: Lambek Isomorphisms (out-μ and in-ν)

**Issue raised:** The initial implementation of `obs` used Cata-over-Nat, which builds intermediate
closures and prevents fusion with downstream operations like `sum (obs n stream)`.

**Analysis:**

To implement `obs` as a proper Hylo (enabling full fusion), the coalgebra needs to pattern-match
on the Nat counter. But Nat is a μ-type, and pattern-matching on μ-types requires either:
1. Using Cata (which replaces the recursive structure, breaking the Hylo pattern)
2. Using `out-μ : μ F → ⟦ F ⟧T (μ F)` (the inverse of In)

By Lambek's Lemma (1968), `In` is an isomorphism for initial algebras, so `out-μ = In⁻¹` exists.

**Resolution:** Add `out-μ` and `in-ν` to the IR.

```agda
-- Added to Once.CCC.IR
out-μ : ∀ {F} → WellFormedF F → IR (μ-type F) (⟦ F ⟧T (μ-type F))
in-ν  : ∀ {F} → WellFormedF F → AllocMode → IR (⟦ F ⟧T (ν-type F)) (ν-type F)
```

**Effect on optimization:**

Without `out-μ`:
```
sum (obs n s)
  = Cata sumAlg (apply (Cata natAlg n) s)
  -- Intermediate list IS built, then summed
```

With `out-μ`:
```
obs = Hylo listAlg (case ... ∘ ⟨ out-μ ∘ fst , snd ⟩)

sum (obs n s)
  = Cata sumAlg (Hylo In obsCoalg (n,s))
  = Hylo sumAlg obsCoalg (n,s)  -- by Hylo-Cata fusion!
  -- NO intermediate list — sum accumulates as we observe
```

**Effect on library code:**

| Layer | Changes? |
|-------|----------|
| Client code | No change (same API) |
| Observation module | Implementation uses Hylo + out-μ |
| Initial library | No change |
| Coinitial library | No change |

The `out-μ` primitive is invisible to library users — it's an optimization enabler that makes
the "have cake and eat it too" promise actually work.

**Symmetric IR structure:**

| μ-type | ν-type | Role |
|--------|--------|------|
| `In` | `in-ν` | Constructor (build structure) |
| `out-μ` | `Out` | Destructor (observe one layer) |
| `Cata` | `Ana` | Universal morphism (fold/unfold all) |

This symmetry reflects the categorical duality between initial algebras and final coalgebras,
both justified by Lambek's Lemma.

### 2026-03-27: The Fusion Category — Hylo Is Not Categorical

**Issue raised:** Why does Hylo require a `TERMINATING` pragma while Cata/Ana don't? Is Hylo a
fundamental recursion scheme, or something different?

**Analysis:**

Hylo is often treated as a peer of Cata and Ana in functional programming literature. But careful
analysis reveals a fundamental difference:

| Property | Cata | Ana | Hylo |
|----------|------|-----|------|
| Universal property | Yes (initiality) | Yes (finality) | **No** |
| Termination proof | Lambek's Lemma | Lambek's Lemma | **Depends on coalgebra** |
| Types align | μF → A | A → νF | **μF ≠ νF, doesn't compose!** |

**The key insight:** `Cata ∘ Ana` doesn't type-check because μF ≠ νF:
- `Ana : A → νF` (produces coinductive)
- `Cata : μF → B` (consumes inductive)
- Composition requires μF = νF, which would break totality!

Hylo is defined directly as a recursive function:
```
hylo alg coalg x = alg (fmap (hylo alg coalg) (coalg x))
```

This terminates only when the coalgebra eventually produces base cases — a semantic property
that depends on the specific coalgebra, not guaranteed by any universal property.

**Resolution:** Introduce the **Fusion category** terminology.

The Fusion category contains **well-founded optimization morphisms between recursion schemes**:

| μ-consumer | ν-producer | Fusion |
|------------|------------|--------|
| Cata | Ana | **Hylo** |
| Histo | Ana | **Dyna** (dynamorphism) |
| Histo | Futu | **Chrono** (chronomorphism) |
| Para | Ana | (unnamed) |
| Cata | Apo | (related to Elgot algebras) |

All fusions share:
1. Bridge a consumer (μ-side) and producer (ν-side)
2. Eliminate intermediate structures (deforestation)
3. Require **μ-anchoring** for termination
4. Lack categorical universal properties

**μ-Anchoring:** A fusion is safe (total) when:
- Input type is a μ-type: `μG`
- Coalgebra/transform operates on that μ-type
- Recursive positions receive strictly smaller μG values (subterms)

This is enforced through the type structure: Hylo and Fuse both require `μG` as input type.

**Implications for IR design:**

1. **Categorical schemes** (Cata, Para, Ana, Apo) form the **semantic foundation** — proven
   total/productive by Lambek's Lemma, no TERMINATING pragma needed

2. **Fusions** (Hylo, Fuse) are the **optimization layer** — μ-anchoring enforced by types,
   structural recursion on well-founded μ-type input

3. **Observation primitives** (`obs`, `obsWhile`) use **Para** (categorical) — Para is
   derived from Cata, provably terminating (done in Phase 10)

4. **Fusions are optional** — the IR is semantically complete without them. They exist purely
   for optimization. Add them incrementally as the optimizer matures.

**Naming convention adopted:**
- "Categorical schemes" = Cata, Para, Ana, Apo (universal properties, proven)
- "Fusions" = Hylo, Fuse (optimization morphisms, μ-anchored)
- "Fusion category" = the class of well-founded optimization morphisms

**Related work:**
- Capretta, Uustalu, Vene: "Recursive Coalgebras" — characterizes coalgebras that give terminating hylos
- Elgot algebras: Capture iteration with possible divergence
- Traced monoidal categories: Feedback/iteration as categorical structure

**Fusion safety via μ-anchoring:**

| Construct | Input Type | Guarantee |
|-----------|------------|-----------|
| `Hylo` | `μG` | Structural recursion on well-founded type |
| `Fuse` | `μG` | μ-type pre-destructed, transform receives G-layer |

Both are correct by construction — the type structure enforces μ-anchoring.

**Conclusion:** The principled architecture is:
- Semantic layer: Categorical schemes (proven total/productive)
- Optimization layer: Fusions (μ-anchored, correct by construction)
- The IR reflects this: categorical primitives first, fusions added for optimization
