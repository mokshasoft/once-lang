# Optimization in Once

This document describes the theoretical foundations of optimization in Once, focusing on how natural transformations and parametricity enable principled program transformations.

## Table of Contents

1. [Introduction: Why NT Enables Optimization](#1-introduction-why-nt-enables-optimization)
2. [Parametricity and Free Theorems](#2-parametricity-and-free-theorems)
3. [The Naturality Square](#3-the-naturality-square)
4. [Functor Laws (Map Fusion)](#4-functor-laws-map-fusion)
5. [Current Optimizer Laws](#5-current-optimizer-laws)
6. [Catamorphism Fusion](#6-catamorphism-fusion)
7. [Hylomorphism Deforestation](#7-hylomorphism-deforestation)
8. [Short-Cut Fusion](#8-short-cut-fusion)
9. [Linearity and Optimization](#9-linearity-and-optimization)
10. [Architecture: IR = NT Layer](#10-architecture-ir--nt-layer)
11. [Programming for Optimization](#11-programming-for-optimization)
12. [Future Implementation Roadmap](#12-future-implementation-roadmap)

---

## 1. Introduction: Why NT Enables Optimization

Once programs are **natural transformations** - structure-preserving maps between functors. This mathematical foundation provides optimization opportunities that are impossible or unsafe in conventional languages.

### The Key Insight

Natural transformations describe **structure**, not **implementation**. When you write:

```once
swap : A * B -> B * A
swap = pair snd fst
```

You're not describing "how to swap" - you're stating the structural relationship between inputs and outputs. This abstraction enables the compiler to choose the best implementation while preserving semantics.

### Why Optimization is Safe

Three properties make optimization principled in Once:

1. **Parametricity** - Polymorphic functions must work uniformly on all types. This constraint generates "free theorems" - equations that hold by construction.

2. **Categorical Laws** - The 12 generators satisfy known algebraic laws (identity, associativity, beta, eta). These laws are rewrite rules.

3. **Bicartesian Closed Structure** - Products, coproducts, and exponentials have universal properties that determine canonical morphisms.

### The 12 Generators

Once programs reduce to compositions of:

| Generator | Type | Category Theory |
|-----------|------|-----------------|
| `id` | `A -> A` | Identity morphism |
| `compose` | `(B -> C) -> (A -> B) -> (A -> C)` | Composition |
| `fst` | `A * B -> A` | Product projection |
| `snd` | `A * B -> B` | Product projection |
| `pair` | `(C -> A) -> (C -> B) -> (C -> A * B)` | Product universal |
| `inl` | `A -> A + B` | Coproduct injection |
| `inr` | `B -> A + B` | Coproduct injection |
| `case` | `(A -> C) -> (B -> C) -> (A + B -> C)` | Coproduct universal |
| `terminal` | `A -> Unit` | Terminal morphism |
| `initial` | `Void -> A` | Initial morphism |
| `curry` | `(A * B -> C) -> (A -> (B -> C))` | Exponential adjoint |
| `apply` | `(A -> B) * A -> B` | Evaluation |

Plus `fold` and `unfold` for recursive types.

---

## 2. Parametricity and Free Theorems

### Reynolds' Abstraction Theorem

In 1983, John Reynolds proved that in a polymorphic lambda calculus, **terms respect relational structure**. This means:

> Any polymorphic function preserves whatever relations we can prove about its type parameters.

For a function `f : forall a. F a -> G a`, if we have a relation `R` between types `A` and `B`, then:

```
(x, y) in F(R)  implies  (f x, f y) in G(R)
```

### Wadler's "Theorems for Free!"

Philip Wadler (1989) showed how to derive equations from types alone. For any polymorphic function:

```
alpha : forall a. F a -> G a
```

The **free theorem** is:

```
fmap_G h . alpha = alpha . fmap_F h
```

This is exactly the **naturality condition**!

### Example: reverse

Consider `reverse : forall a. [a] -> [a]`. The free theorem says:

```
map f . reverse = reverse . map f
```

We can reverse before or after mapping - the result is the same. This isn't obvious from the implementation but follows from the type alone.

### Once-Specific Consequence

In Once, every morphism is parametric. The generators have polymorphic types, so all compositions inherit parametricity. This means:

> **Every Once program satisfies its free theorem automatically.**

No proof needed - it's a consequence of the type system.

---

## 3. The Naturality Square

### The Diagram

For a natural transformation `alpha : F => G`, the naturality condition is expressed as a commutative diagram:

```
         alpha_A
    F A ---------> G A
     |              |
F h  |              | G h
     v              v
    F B ---------> G B
         alpha_B
```

Both paths from `F A` to `G B` are equal:

```
G h . alpha_A  =  alpha_B . F h
```

### Intuition

- `F` and `G` are "containers" (functors)
- `alpha` transforms the container shape without looking at contents
- `h` transforms the contents without changing the shape
- Naturality says: transform shape then contents = transform contents then shape

### Optimization Consequence

The naturality square lets us **reorder operations**:

```
-- These are equal (naturality)
fmap h . alpha  =  alpha . fmap h

-- Optimization: choose the more efficient order
-- If alpha is expensive and h is cheap, do h first
```

### Example in Once

Consider `swap : A * B -> B * A` which transforms product structure:

```once
swap : A * B -> B * A
swap = pair snd fst
```

By naturality, for any `f : A -> A'` and `g : B -> B'`:

```
swap . bimap f g  =  bimap g f . swap
```

Where `bimap f g = pair (f . fst) (g . snd)`.

We can swap before or after applying transformations to the components.

---

## 4. Functor Laws (Map Fusion)

### The Functor Laws

A functor `F` has an operation `fmap : (A -> B) -> F A -> F B` satisfying:

```
fmap id       = id                    -- identity law
fmap (f . g)  = fmap f . fmap g       -- composition law
```

### Map Fusion

The composition law **is** map fusion:

```
map f . map g  =  map (f . g)
```

Two traversals become one. This is a direct consequence of the functor laws.

### Proof

```
map f . map g
  = fmap f . fmap g        -- definition
  = fmap (f . g)           -- functor composition law
  = map (f . g)            -- definition
```

### Efficiency Gain

```
-- Before: O(2n) - two list traversals
map toUpper . map toLower

-- After: O(n) - single traversal
map (toUpper . toLower)
```

### Once Implementation

In Once, lists are fixed points of functors. For `List A = Fix (ListF A)` where:

```
ListF A X = Unit + (A * X)
```

The `map` function is:

```once
map : (A -> B) -> List A -> List B
map f = cata (case (const nil) (\(a, bs) -> cons (f a) bs))
```

Map fusion follows from catamorphism fusion (Section 6).

### Multiple Functors

Fusion applies to any functor:

```once
-- Maybe
fmap f . fmap g = fmap (f . g)

-- Result
mapResult f . mapResult g = mapResult (f . g)

-- Tree
mapTree f . mapTree g = mapTree (f . g)
```

---

## 5. Current Optimizer Laws

The Once optimizer is formally verified in Agda (`formal/Once/Optimize.agda` and `formal/Once/Optimize/Correct.agda`). All optimizations below have machine-checked correctness proofs.

### 5.1 Identity Laws

```
id . f = f    -- left identity
f . id = f    -- right identity
```

### 5.2 Product Laws (Beta)

```
fst . ⟨f, g⟩ = f
snd . ⟨f, g⟩ = g
```

These eliminate dead code: if you build a pair then immediately project, the unused component is never computed.

### 5.3 Product Laws (Eta)

```
⟨fst, snd⟩ = id    -- on products
```

Building a pair from projections is the same as doing nothing.

### 5.4 Coproduct Laws (Beta)

```
[f, g] . inl = f
[f, g] . inr = g
```

Case analysis followed by injection reduces to the appropriate branch.

### 5.5 Coproduct Laws (Eta)

```
[inl, inr] = id    -- on coproducts
```

A case that just re-injects is the same as doing nothing.

### 5.6 Fixed Point Laws

```
fold . unfold = id : Fix F -> Fix F
unfold . fold = id : F (Fix F) -> F (Fix F)
```

Folding then immediately unfolding (or vice versa) is identity.

### 5.7 Terminal Fusion (Dead Code Elimination)

```
terminal . f = terminal    -- for any f
```

If you're going to discard the result anyway, don't compute it. This is dead code elimination expressed categorically.

### 5.8 Initial Absorption (Vacuous Code Elimination)

```
f . initial = initial    -- for any f
```

Any computation starting from `Void` (the impossible case) produces `Void`. Since `Void` has no inhabitants, this is vacuously true and the computation can be skipped.

### 5.9 Pairing Fusion (Distributivity)

```
⟨f, g⟩ . h = ⟨f . h, g . h⟩
```

Composition distributes into pair construction. This exposes beta reductions:

```
fst . ⟨f, g⟩ . h
  → fst . ⟨f . h, g . h⟩    (pairing fusion)
  → f . h                    (product beta)
```

The dead computation `g . h` is eliminated.

### 5.10 Case Fusion (Distributivity)

```
h . [f, g] = [h . f, h . g]
```

Composition distributes over case analysis. This enables post-processing to be pushed into branches.

### 5.11 Bimap Fusion (Derived)

Through multiple passes, pairing fusion + beta laws achieve bimap fusion:

```
⟨f . fst, g . snd⟩ . ⟨h, k⟩
  → ⟨f . fst . ⟨h, k⟩, g . snd . ⟨h, k⟩⟩    (pairing fusion)
  → ⟨f . h, g . k⟩                            (beta laws)
```

This fuses two product transformations into one.

### 5.12 Associativity Normalization

```
(h . g) . f  -->  h . (g . f)    -- right-associative normal form
```

Right-associativity exposes more optimization opportunities by bringing inner compositions to where outer rules can match.

### 5.13 What's Not Implemented (And Why)

**Curry-Apply Beta** (`apply . ⟨curry f . fst, snd⟩ = f`)

This is the beta law for exponentials (function types). It was attempted but removed due to complex nested pattern matching that Agda's coverage checker couldn't easily verify. The pattern `⟨curry f . fst, snd⟩` requires deep structural matching that conflicts with the simpler fusion rules.

*Impact*: Low for typical code. Most currying patterns don't produce this exact structure.

**Map Fusion** (`fmap f . fmap g = fmap (f . g)`)

Requires recognizing `fmap` patterns in the IR, which are currently compositions of projections and pairs. Will be added when recursion schemes are exposed in the surface language.

**Catamorphism/Hylomorphism Fusion**

Requires the surface language to produce `fold`/`unfold` patterns that the optimizer can recognize. Currently `fold`/`unfold` are in the IR but not produced by elaboration.

---

## 6. Catamorphism Fusion

### Definition

A catamorphism (fold) is:

```
cata : (F A -> A) -> Fix F -> A
cata alg (Fix fa) = alg (fmap (cata alg) fa)
```

### The Fusion Law

For any `h : A -> B`:

```
h . cata alg = cata alg'

-- Provided the "fusion condition" holds:
h . alg = alg' . fmap h
```

### Diagram

```
         alg
   F A -------> A
    |           |
 F h|           | h
    v           v
   F B -------> B
        alg'
```

### Why It Works

If `h` commutes with the algebra (the diagram commutes), then post-composing `h` with a fold can be absorbed into a different fold.

### Example: sum . map f

```
-- Original (two traversals)
sum . map f

-- Fusion: h = sum, alg = sum's algebra
sumAlg = case (const 0) (uncurry (+))
mapAlg f = case (const nil) (\(a, as) -> cons (f a) as)

-- Fused (single traversal)
cata (case (const 0) (\(a, n) -> f a + n))
```

### Proof Sketch

```
sum . map f
  = cata sumAlg . cata (mapAlg f)
  = cata (sumAlg . fmap (map f))     -- catamorphism definition
  = cata (case (const 0) (\(a, n) -> f a + n))  -- algebra fusion
```

---

## 7. Hylomorphism Deforestation

### Definition

A hylomorphism combines an anamorphism (unfold) and catamorphism (fold):

```
hylo : (F B -> B) -> (A -> F A) -> A -> B
hylo alg coalg seed = alg (fmap (hylo alg coalg) (coalg seed))
```

Or equivalently:

```
hylo alg coalg = cata alg . ana coalg
```

### The Deforestation Theorem

```
cata alg . ana coalg = hylo alg coalg
```

The intermediate data structure built by `ana` and consumed by `cata` can be **eliminated entirely**.

### Why "Deforestation"?

The term comes from Wadler (1990). Building a data structure creates a "tree" (or list, etc.) in memory. Fusing the producer and consumer removes this tree - hence "deforestation."

### Example: Factorial

```once
-- Naive (allocates list [n, n-1, ..., 1])
factorial n = product (countdown n)

-- Hylomorphism (no intermediate list)
factorial = hylo productAlg countdownCoalg

productAlg = case (const 1) (uncurry (*))
countdownCoalg n = if n <= 0 then inl () else inr (n, n - 1)
```

### Efficiency Gain

- Before: O(n) space for intermediate list
- After: O(1) space (tail recursion)

### Proof

The proof relies on the universal properties of initial algebras and final coalgebras. See Meijer et al. "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire" (1991).

---

## 8. Short-Cut Fusion

### GHC's Approach

GHC uses **build/foldr fusion**:

```haskell
build :: (forall b. (a -> b -> b) -> b -> b) -> [a]
build g = g (:) []

foldr :: (a -> b -> b) -> b -> [a] -> b

-- Fusion rule
foldr c n (build g) = g c n
```

### How It Works

1. **Producers** are written using `build`
2. **Consumers** are written using `foldr`
3. The rewrite rule eliminates the intermediate list

### Example

```haskell
-- Producer
map f xs = build (\c n -> foldr (c . f) n xs)

-- Consumer
sum = foldr (+) 0

-- Fusion
sum (map f xs)
  = foldr (+) 0 (build (\c n -> foldr (c . (f)) n xs))
  = (\c n -> foldr (c . f) n xs) (+) 0     -- fusion rule
  = foldr ((+) . f) 0 xs                    -- beta reduction
```

### Once Adaptation

Once could implement a similar scheme:

```once
-- Abstract list producer
build : ((A -> X -> X) -> X -> X) -> List A

-- Fusion rule
cata alg (build g) = g (curry alg) (alg (inl ()))
```

This requires:
1. Recognizing `build` patterns in IR
2. Adding the rewrite rule to the optimizer

---

## 9. Linearity and Optimization

Once's Quantitative Type Theory (QTT) assigns quantities to types:

| Quantity | Symbol | Meaning |
|----------|--------|---------|
| Zero | `0` | Erased at runtime |
| One | `1` | Used exactly once |
| Omega | `ω` | Used any number of times |

### Linearity Enables In-Place Update

When a value has quantity `1`, it's consumed exactly once. This guarantees:

- No aliasing (no other reference exists)
- Safe to mutate in place
- Deterministic deallocation

```once
-- If xs : List^1 A, can update in-place
map f xs  -- reuses xs's memory
```

### Linearity Guarantees Deforestation Safety

For hylomorphism fusion to be safe, the intermediate structure must be:
1. Created (by ana)
2. Consumed completely (by cata)
3. Never observed elsewhere

Linear types enforce this automatically! If the intermediate has quantity `1`:

```once
cata alg . ana coalg
-- ana produces Fix^1 F (linear)
-- cata consumes Fix^1 F (linear)
-- Fusion is always valid
```

### Semiring Laws Constrain Rewrites

Quantities form a semiring under addition and multiplication:

```
0 + q = q       0 * q = 0
1 + 1 = ω       1 * q = q
q + ω = ω       ω * ω = ω
```

Rewrite rules must respect these laws. For example:

```
-- If f : A^1 -> B and g : A^1 -> B, we can't do:
pair f g : A -> B * B    -- Would require A^2!

-- Unless input has quantity ω:
pair f g : A^ω -> B * B  -- Valid
```

### Graded Categories

This connects to the theory of **graded categories** (Atkey, 2018). Each morphism carries a grade (quantity), and composition multiplies grades:

```
f : A -[p]-> B
g : B -[q]-> C
-----------------
g . f : A -[p*q]-> C
```

### QTT-Aware Optimization Rules

Some optimizations are only valid for certain quantities:

```
-- Valid for any quantity:
f . id = f
fst . pair f g = f

-- Valid only for linear:
inplace_map f xs  (when xs : List^1 A)

-- Valid only for ω:
pair (f . h) (g . h) = bimap f g . pair h h  (needs duplication)
```

---

## 10. Architecture: IR = NT Layer

### The Key Realization

In Once, **the IR IS the natural transformation representation**.

```
Surface Syntax --> Parser --> AST --> Elaborator --> IR --> Optimizer --> IR --> Codegen --> C
                                                     ↑
                                          Natural transformations live here
```

### IR = Morphisms of a BCC

The 12 generators plus `fold`/`unfold` form the morphisms of a **bicartesian closed category**:

- **Cartesian**: Products with `fst`, `snd`, `pair`
- **Cocartesian**: Coproducts with `inl`, `inr`, `case`
- **Closed**: Exponentials with `curry`, `apply`
- **Initial/Terminal**: `initial`, `terminal`

Every Once program is a composition of these morphisms - literally a natural transformation expressed as a categorical term.

### Naturality is Automatic

Because Once is parametric, the naturality condition:

```
fmap h . alpha = alpha . fmap h
```

holds for all polymorphic `alpha` **by construction**. We don't need to "apply naturality" as a rewrite - it's always true.

What we CAN do is use **consequences** of naturality as rewrite rules (like map fusion).

### Optimizer = Categorical Rewrites

The optimizer applies categorical laws to IR terms:

```haskell
-- Optimize.hs applies laws like:
Fst `Compose` (Pair f g)  -->  f           -- beta
Pair Fst Snd              -->  Id          -- eta
Compose (Compose f g) h   -->  Compose f (Compose g h)  -- assoc
```

These are exactly the laws of a bicartesian closed category.

### Verified Correctness

In `formal/Once/Category/Laws.agda`, we prove these laws hold:

```agda
eval-fst-pair : eval (fst . pair f g) x ≡ eval f x
eval-pair-eta : eval (pair fst snd) x ≡ x
eval-assoc    : eval ((f . g) . h) x ≡ eval (f . (g . h)) x
```

The optimizer is semantics-preserving by construction.

---

## 11. Programming for Optimization

The optimization laws suggest specific **programming idioms** that work well with the optimizer. Writing in these styles enables automatic optimization; deviating from them produces opaque code the optimizer can't improve.

### 11.0 Realistic Impact Assessment

Before diving into guidelines, understand when optimizations actually help:

| Code Style | Impact of Current Optimizer |
|------------|----------------------------|
| **Point-free categorical** | High - patterns match directly |
| **Recursion schemes (cata/ana)** | High - fusion laws apply |
| **Applicative/Arrow style** | Medium - pairing fusion helps |
| **Let-bound imperative style** | Low - patterns rarely emerge |
| **Manual recursion** | None - opaque to optimizer |

**The honest truth**: Most of the current optimizations prepare the foundation for recursion scheme fusion. Until the surface language generates `fold`/`unfold` patterns, the primary benefits are:

1. **Dead code elimination** via beta laws and terminal fusion
2. **Simplification** of compositional code
3. **Enabling future fusion** when recursion schemes are added

The optimizer shines when you write in *categorical style* (compositions of standard combinators). If you write *imperative style* (let-bindings and manual recursion), the optimizer has little to work with.

### 11.1 Write in Fusible Style

**Do**: Use compositions of standard combinators (`map`, `filter`, `fold`, `unfold`)

```once
-- Fusible: optimizer eliminates intermediate lists
result = sum . map square . filter isPositive

-- After optimization: single traversal, O(n) time, O(1) space
```

**Avoid**: Manual recursion that hides structure

```once
-- Non-fusible: optimizer doesn't recognize the pattern
processLoop : List Int -> Int -> Int
processLoop xs acc = case xs of
  Nil -> acc
  Cons x rest -> if isPositive x
                 then processLoop rest (acc + square x)
                 else processLoop rest acc
```

Both compute the same thing, but only the first can be automatically optimized.

### 11.2 Prefer Point-Free Compositions

**Do**: Chain morphisms with `.` to expose structure

```once
-- Point-free: structure visible to optimizer
process : A -> D
process = h . g . f

-- Optimizer sees: Compose h (Compose g f)
-- Can apply: associativity, identity elimination, fusion
```

**Avoid**: Nested applications that hide composition

```once
-- Pointed: same semantics, harder to optimize
process : A -> D
process x = h (g (f x))

-- Optimizer sees: application nodes, not composition
```

### 11.3 Use Recursion Schemes

**Do**: Express recursive computations with `cata`, `ana`, `hylo`

```once
-- Hylomorphism: optimizer knows this pattern
factorial : Int -> Int
factorial = hylo productAlg countdownCoalg

-- Catamorphism: standard fold pattern
sum : List Int -> Int
sum = cata sumAlg

-- Anamorphism: standard unfold pattern
range : Int -> Int -> List Int
range lo hi = ana rangeCoalg (lo, hi)
```

**Avoid**: Raw recursion that's opaque to the optimizer

```once
-- Raw recursion: can't fuse with consumers/producers
factorial : Int -> Int
factorial n = if n <= 0 then 1 else n * factorial (n - 1)
```

### 11.4 Write Linear Code (Quantity 1)

Linear values enable in-place updates and guarantee fusion safety.

**Do**: Consume values exactly once when possible

```once
-- Linear input: optimizer can update in-place
transform : List^1 A -> List^1 B
transform = map f

-- The input list's memory is reused for output
-- No allocation, no GC pressure
```

**Avoid**: Unnecessary duplication that forces copies

```once
-- Duplication prevents in-place optimization
duplicate : List A -> List A * List A
duplicate xs = (xs, xs)  -- xs used twice

-- Now neither copy can be optimized
process = bimap (map f) (map g) . duplicate
-- Two separate traversals required
```

### 11.5 Structure as Producer → Transformer → Consumer

The classic fusible pipeline:

```once
result = consumer . transformers . producer
```

Each component has a role:
- **Producer**: Creates data (`unfold`, `range`, `iterate`, literals)
- **Transformer**: Modifies data (`map`, `filter`, `take`, `zip`)
- **Consumer**: Collapses data (`fold`, `sum`, `length`, `toList`)

```once
-- All three stages fuse into single loop
average = divide . pair sum length . filter isValid . parseNumbers

-- Computes sum and length in ONE traversal
-- No intermediate list allocated
```

### 11.6 Delay Materialization

Keep data in abstract/lazy form as long as possible.

**Do**: Compose operations before forcing results

```once
-- Good: intermediate structures stay abstract
pipeline : Seed -> Result
pipeline = consume . transform3 . transform2 . transform1 . produce

-- Nothing materializes until 'consume' forces it
-- Entire pipeline can fuse
```

**Avoid**: Forcing intermediate structures

```once
-- Bad: intermediate list materializes in memory
step1 : Seed -> List A
step1 seed = toList (produce seed)  -- Forces allocation!

step2 : List A -> Result
step2 xs = consume (transform xs)

pipeline = step2 . step1  -- Can't fuse across toList
```

### 11.7 Use Canonical Combinators

The `Canonical` library provides combinators with known fusion properties.

**Do**: Use standard combinators from Canonical

```once
-- Standard combinators: optimizer knows their laws
import Canonical.Product (swap, diagonal, bimap)
import Canonical.Function (flip, const)

process = bimap f g . swap  -- Optimizer applies bimap-swap law
```

**Avoid**: Reinventing combinators

```once
-- Custom swap: optimizer doesn't recognize it
mySwap : A * B -> B * A
mySwap p = (snd p, fst p)

-- Same semantics as 'swap' but won't trigger optimizations
```

### 11.8 The Golden Rule

> **Declare what you want, not how to compute it.**

When you write:
```once
result = sum . map square . filter isPositive . range 1 1000
```

You're declaring the *specification*. The optimizer chooses the *implementation*:
- Fuse into single loop
- Eliminate all intermediate lists
- Use in-place updates if linear
- Unroll if beneficial

When you write manual loops, you've chosen a specific implementation. The optimizer can only respect your choice, not improve it.

### 11.9 Summary Table

| Pattern | Fusible? | Why |
|---------|----------|-----|
| `f . g . h` | Yes | Composition structure visible |
| `f (g (h x))` | Partially | Applications hide structure |
| `cata alg . ana coalg` | Yes | Hylo fusion applies |
| `fold` + `map` + `unfold` | Yes | Standard fusion laws |
| Manual recursion | No | Opaque to optimizer |
| `xs` used twice | No | Duplication blocks in-place |
| `toList` mid-pipeline | No | Forces materialization |

### 11.10 Debugging Optimization

To see what optimizations fired:

```bash
# Show IR before and after optimization
once build --dump-ir example.once

# Show which rules applied
once build --trace-opt example.once
```

If expected fusion didn't happen:
1. Check for non-linear usage (duplication)
2. Check for forced materialization
3. Check that combinators are recognized (not custom reimplementations)
4. Verify pipeline is fully composed (not broken into separate bindings)

---

## 12. Implementation Status and Roadmap

### 12.1 What's Done (Verified in Agda)

The following optimizations are **implemented and proven correct** in `formal/Once/Optimize.agda`:

| Optimization | Law | Status |
|-------------|-----|--------|
| Identity (left/right) | `id . f = f`, `f . id = f` | ✓ Verified |
| Product beta | `fst . ⟨f,g⟩ = f`, `snd . ⟨f,g⟩ = g` | ✓ Verified |
| Product eta | `⟨fst, snd⟩ = id` | ✓ Verified |
| Coproduct beta | `[f,g] . inl = f`, `[f,g] . inr = g` | ✓ Verified |
| Coproduct eta | `[inl, inr] = id` | ✓ Verified |
| Fixed point | `fold . unfold = id`, `unfold . fold = id` | ✓ Verified |
| Terminal fusion | `terminal . f = terminal` | ✓ Verified |
| Initial absorption | `f . initial = initial` | ✓ Verified |
| Pairing fusion | `⟨f,g⟩ . h = ⟨f.h, g.h⟩` | ✓ Verified |
| Case fusion | `h . [f,g] = [h.f, h.g]` | ✓ Verified |
| Associativity | `(h . g) . f → h . (g . f)` | ✓ Verified |

**Postulates**: The only postulate used is **function extensionality** (funext), which is:
- Consistent with MLTT (proven via setoid models)
- Provable in Cubical Agda
- Standard practice in formalization

### 12.2 What Was Attempted But Removed

**Curry-Apply Beta** (`apply . ⟨curry f . fst, snd⟩ = f`)

This exponential beta law was implemented but removed because:
1. The nested pattern `⟨curry f . fst, snd⟩` conflicts with pairing fusion
2. Agda's coverage checker requires enumerating many sub-patterns
3. Impact is low - this pattern rarely appears in generated code

It can be added later with a dedicated pass before fusion rules.

### 12.3 What's Next

**Priority 1: Sync Haskell Optimizer**

The Haskell compiler (`compiler/src/Once/Optimize.hs`) should implement the same laws as the Agda specification. Currently they may be out of sync.

**Priority 2: Map Fusion (Bimap)**

Recognize bimap pattern: `⟨f . fst, g . snd⟩ . ⟨h . fst, k . snd⟩ → ⟨(f.h) . fst, (g.k) . snd⟩`

This is partially achieved through pairing fusion + beta, but a dedicated rule would be more direct.

**Priority 3: Surface Language Recursion Schemes**

The biggest gain requires the surface language to produce `fold`/`unfold` patterns:
- Expose `cata`, `ana`, `hylo` as surface syntax
- Elaborate list/tree operations to these patterns
- Then catamorphism fusion becomes possible

**Priority 4: Catamorphism Fusion**

```
h . cata alg = cata alg'   when h . alg = alg' . fmap h
```

Challenge: Checking the fusion condition requires type-level reasoning.

**Priority 5: Hylomorphism Deforestation**

```
cata alg . ana coalg = hylo alg coalg
```

Current `fold . unfold = id` is a special case. Full deforestation requires:
1. Recognizing producer-consumer patterns
2. Eliminating intermediate `Fix F` structures

### 12.4 Proof Requirements

Each new optimization needs:

1. **Agda implementation** in `formal/Once/Optimize.agda`
2. **Correctness proof** in `formal/Once/Optimize/Correct.agda`
3. **Haskell implementation** in `compiler/src/Once/Optimize.hs`
4. **QuickCheck property** in `compiler/test/Once/OptimizeSpec.hs`

The Agda proofs are the source of truth. The Haskell implementation should match.

---

## References

### Parametricity and Free Theorems
- Reynolds, J.C. (1983). "Types, Abstraction, and Parametric Polymorphism"
- Wadler, P. (1989). "Theorems for Free!"

### Natural Transformations
- Milewski, B. "Category Theory for Programmers" - Natural Transformations chapter
- Mac Lane, S. "Categories for the Working Mathematician"

### Fusion
- Gill, A., Launchbury, J., Peyton Jones, S. (1993). "A Short Cut to Deforestation"
- Hinze, R., Harper, T., James, D.W.H. (2010). "Theory and Practice of Fusion"

### Recursion Schemes
- Meijer, E., Fokkinga, M., Paterson, R. (1991). "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire"
- See also: [docs/design/recursion-schemes.md](recursion-schemes.md)

### Linearity and QTT
- Atkey, R. (2018). "Syntax and Semantics of Quantitative Type Theory"
- McBride, C. (2016). "I Got Plenty o' Nuttin'"

### Arrows
- Hughes, J. (2000). "Generalising Monads to Arrows"
