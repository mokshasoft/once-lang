# Hylo: Categorical Analysis and Principled Design

**Date:** 2026-03-26 (updated 2026-03-27)
**Status:** Incorporated into OCP-0003

**See also:** OCP-0003 "The Fusion Category" section for the adopted terminology and architecture.

---

## The Problem

We've been treating Hylo as a semantic primitive in the IR, requiring a `TerminatesOn` witness to document termination. But something feels wrong - category theory has had recursion schemes for 50+ years. Why are we inventing new machinery?

---

## What Category Theory Actually Says

### The Established Primitives

**1. Catamorphism (fold)**
```
cata : (F A → A) → μF → A
```
- μF is the **initial F-algebra** (least fixed point)
- Cata is the **unique** morphism from μF to any F-algebra
- **Total by construction**: μF is well-founded (finite, inductive)
- No termination proof needed - initiality guarantees it

**2. Anamorphism (unfold)**
```
ana : (A → F A) → A → νF
```
- νF is the **final F-coalgebra** (greatest fixed point)
- Ana is the **unique** morphism from any F-coalgebra to νF
- **Productive by construction**: νF is coinductive
- No productivity proof needed - finality guarantees it

**3. Paramorphism (fold with context)**
```
para : (F (μF × A) → A) → μF → A
```
- Derived from cata: `para alg x = π₂ (cata alg' x)` where `alg' fx = (in (fmap π₁ fx), alg fx)`
- **Total by derivation**: it's just cata with extra bookkeeping
- No additional proof needed

### The Key Insight: μF ≠ νF

In proper category theory:
```
μF = initial F-algebra  (least fixed point, inductive, finite)
νF = final F-coalgebra  (greatest fixed point, coinductive, potentially infinite)
```

These are **different objects**:
- μF values are finite (well-founded)
- νF values may be infinite (productive)

This distinction is what gives us totality (cata) and productivity (ana) guarantees.

---

## The Hylo Problem

### What is Hylo?

Hylo is often described as "cata ∘ ana" - fold after unfold:
```
hylo alg coalg = cata alg ∘ ana coalg
```

### Why This Doesn't Type-Check

```
ana coalg  : A → νF      (produces νF)
cata alg   : μF → B      (consumes μF)
```

**μF ≠ νF**, so `cata alg ∘ ana coalg` is a **type error**!

### The Direct Definition

To make Hylo work, it's typically defined directly as a recursive function:
```
hylo : (F B → B) → (A → F A) → A → B
hylo alg coalg x = alg (fmap (hylo alg coalg) (coalg x))
```

This is a **general recursive definition**. Its termination depends on:
- The coalgebra eventually producing "base cases" (F-layers with no recursive positions)
- This is NOT guaranteed by the types!

### Hylo is NOT a Categorical Primitive

Category theory gives us:
- Cata: total (by initiality of μF)
- Ana: productive (by finality of νF)

Category theory does **not** give us a general terminating Hylo. Hylo's termination depends on coalgebra behavior, which is outside the categorical universal properties.

---

## The Haskell Conflation

Haskell uses a single `Fix` type:
```haskell
newtype Fix f = Fix { unFix :: f (Fix f) }

cata :: (f a -> a) -> Fix f -> a
ana  :: (a -> f a) -> a -> Fix f
hylo :: (f b -> b) -> (a -> f a) -> a -> b
```

Here μ = ν = Fix, so `cata ∘ ana` type-checks. But this conflation:
- Loses the totality guarantee (can fold infinite structures → divergence)
- Loses the productivity guarantee (can unfold non-productively)
- Makes Hylo "work" but at the cost of potential non-termination

**This is exactly what OCP-0003 avoided by keeping μ-type ≠ ν-type.**

---

## The Principled Architecture

### Semantic Layer (Proven Total/Productive)

The semantic IR should contain only the categorical primitives:

| Construct | Type | Guarantee | Proof |
|-----------|------|-----------|-------|
| `In` | `F(μF) → μF` | - | Constructor |
| `out-μ` | `μF → F(μF)` | - | Lambek inverse |
| `Cata` | `(F A → A) → μF → A` | Total | Initiality of μF |
| `Para` | `(F(μF × A) → A) → μF → A` | Total | Derived from Cata |
| `Out` | `νF → F(νF)` | - | Destructor |
| `in-ν` | `F(νF) → νF` | - | Lambek inverse |
| `Ana` | `(A → F A) → A → νF` | Productive | Finality of νF |

**No Hylo at this layer.** Everything is mathematically grounded.

### Optimization Layer (Compilation Target)

The compiler/optimizer can recognize patterns and generate efficient code:

```
Source:           Cata sumAlg ∘ Cata mapAlg
Optimized:        Single-pass fused loop (hylo-style execution)

Source:           Para obsAlg (bounded by Nat)
Optimized:        Fused observation loop
```

The optimization is a **compilation concern**, not a semantic one. The source semantics is given by the proven-total primitives.

### Why This Works

1. **Correctness**: Semantics uses only proven-total operations
2. **Optimization**: Compiler fuses where safe
3. **No invented machinery**: We use exactly what category theory provides
4. **No trust boundaries**: No TERMINATING pragmas in semantics

---

## What About Deforestation?

The classic use of Hylo is deforestation - avoiding intermediate data structures:

```
sum (map f xs)  →  one pass, no intermediate list
```

### Without Semantic Hylo

In our architecture:
```
-- Source (semantically clear)
sum ∘ map f : List A → Nat
           = Cata sumAlg ∘ Cata (mapAlg f)

-- Both are Catas on μ-type (List), both total
-- Compiler can fuse: Cata (sumAlg ∘ fmap (Cata (mapAlg f)))
-- Or directly to a single loop
```

The deforestation happens at **compile time**, not in the semantics.

### The obs Example

```
obs : Nat × Stream A → List A
```

Currently implemented with Para (total, proven):
```
obs = Para obsAlg  -- Nat provides termination, Stream is observed
```

The Para recurses on Nat (μ-type), guaranteed to terminate. No Hylo needed!

---

## Proposed Changes

### Phase 1: Clarify the Architecture

1. Document that Cata/Para/Ana are the **semantic** primitives
2. Document that Hylo is an **optimization pattern**, not semantic

### Phase 2: Move Hylo to Optimization Layer

Option A: Remove Hylo from IR entirely
- Pros: Clean separation, no TERMINATING in semantics
- Cons: May need richer optimization infrastructure

Option B: Keep Hylo in IR but mark it as "optimization hint"
- Pros: Simpler implementation
- Cons: Mixed semantic/optimization concerns

Option C: Have two IR levels
- `IR.Semantic`: Only Cata/Para/Ana (proven)
- `IR.Optimized`: Includes fused forms (Hylo-style)
- Pros: Clean separation, explicit optimization pass
- Cons: More infrastructure

### Phase 3: Prove Optimization Correctness

For each optimization:
```
optimize : IR.Semantic A B → IR.Optimized A B
correct  : ∀ ir x → eval-optimized (optimize ir) x ≡ eval-semantic ir x
```

The correctness proof shows the optimization preserves semantics.

---

## Summary

| Question | Answer |
|----------|--------|
| Is Hylo a categorical primitive? | **No** - it's a computational pattern |
| Does category theory give us terminating Hylo? | **No** - termination depends on coalgebra behavior |
| Should Hylo be in our semantic IR? | **Probably not** - it requires TERMINATING |
| How do we get deforestation? | **Compiler optimization** on Cata/Para compositions |
| What are the true primitives? | **Cata, Para, Ana** (and In/Out/Lambek inverses) |

**The principled path**: Use exactly what category theory provides at the semantic level. Handle optimization separately. Get both mathematical strictness AND performance.

---

## Open Questions

1. What's the right IR architecture? (Single IR with optimization hints vs. two-level IR)
2. How do we express optimization rules? (Rewrite rules, fusion framework)
3. Are there Hylo patterns that can't be expressed as Para/Cata compositions?
4. Performance implications of the two-level approach?

---

## Resolution: The Fusion Category (2026-03-27)

This analysis led to the **Fusion category** terminology adopted in OCP-0003:

**Definition:** The Fusion category contains well-founded optimization morphisms between recursion schemes.

| μ-consumer | ν-producer | Fusion Name |
|------------|------------|-------------|
| Cata | Ana | **Hylo** |
| Histo | Ana | **Dyna** |
| Histo | Futu | **Chrono** |
| Para | Ana | (unnamed) |

**Key distinctions:**
- **Categorical schemes** (Cata, Para, Ana, Apo): Universal properties, proven total/productive
- **Fusions** (Hylo, Dyna, Chrono): Optimization morphisms, require μ-anchoring

**Adopted architecture:**
1. Semantic layer uses categorical schemes (no TERMINATING pragmas)
2. Optimization layer uses fusions (require TerminatesOn witnesses)
3. `obs` uses Para (categorical), not Hylo (fusion)

See OCP-0003 "The Fusion Category" section for full details.

---

## References

- Meijer, Fokkinga, Paterson: "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire" (1991)
- Bird & de Moor: "Algebra of Programming" (1997)
- Hinze, Harper, James: "Theory and Practice of Fusion" (2010)
- OCP-0003: Total and Productive IR via Unified Categorical Structure
