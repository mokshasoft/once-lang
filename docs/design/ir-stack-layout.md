# IR Stack Layout Design

## Overview

This document describes the stack layout strategy for IR execution, focusing on how composition handles statically-known and runtime-dependent output sizes.

## Terminology

- **Frontier**: The boundary in the stack where everything below is "real" output data, and everything above is scratch space.
- **Scratch**: The region above the frontier used for intermediate data. Scratch is fully reclaimed after an IR completes. We assume unbounded stack space, so scratch can grow as needed.
- **Statically-known size**: Output whose size is determinable at compile time. Determined by the output type: non-recursive types (products, sums, primitives) have static size.
- **Runtime-dependent size**: Output whose size depends on input data, only known at runtime. Determined by the output type: recursive types (involving μ) have runtime-dependent size.
- **Functor map**: A morphism f : F A → F B of the form `fmap h` for some h : A → B. Applies h independently to each element in the structure. Output[i] depends only on input[i], enabling parallel execution.
- **Size-preserving functor map**: A functor map where size(A) = size(B). Enables in-place overwrite: since each element transforms independently and the output fits in the input's space, we can overwrite as we go.
- **Linear morphism**: A morphism that reads each input exactly once. Enables reclamation: after g consumes f's output, that space is dead and can be reclaimed. Note: linearity alone does not enable in-place overwrite (see functor map).

## Core Principles

1. **Scratch reclamation**: Each IR fully reclaims its scratch data after completion.
2. **Output at frontier**: Each IR concatenates its output to the frontier and advances it.
3. **Linearity**: Intermediate results are consumed exactly once, enabling reclamation.

## Type Representations

This section defines how each type is laid out in memory. IRs produce and consume these representations.

### Primitives

Inline, fixed size. Examples: `Int`, `Bool`.

```
III
```

### Products: A × B

No header. Components are concatenated. Runtime-sized components use pointers.

| A | B | Layout |
|---|---|--------|
| static | static | `AAA BBB` |
| static | runtime | `AAA ptr→B` |
| runtime | static | `ptr→A BBB` |
| runtime | runtime | `ptr→A ptr→B` |

For static components, data is inline and offsets are known at compile time.
For runtime components, a pointer is used to allow O(1) access without traversal.

### Sums: A + B

Tag comes first, then data (inline) or pointer (for runtime-sized):

| A | B | Left layout | Right layout |
|---|---|-------------|--------------|
| static | static | `[TAG=L] AAA` | `[TAG=R] BBB` |
| static | runtime | `[TAG=L] AAA` | `[TAG=R, ptr→B]` |
| runtime | static | `[TAG=L, ptr→A]` | `[TAG=R] BBB` |
| runtime | runtime | `[TAG=L, ptr→A]` | `[TAG=R, ptr→B]` |

- **Static-sized variant**: `[TAG] data` — data inline after tag
- **Runtime-sized variant**: `[TAG, ptr→data]` — pointer needed because size varies

The tag is always first, so `case` can read it immediately and dispatch. After reading the tag, the compiler knows the exact layout (from the type) and can access the data.

### Functions: A → B

Always a 2-slot closure (fixed size, inline):

```
env* code*
```

- **env***: Pointer to captured environment (partially applied arguments)
- **code***: Pointer to compiled code

A closure is a partially applied function — it holds captured state until the remaining arguments are provided. No header — the two slots are inline data.

## IR-Specific Layouts

### compose : `(g ∘ f)(x)` = `g(f(x))`

Legend: `O` = earlier output, `F` = f output, `G` = g output, `^` = frontier

Here `f` runs first (inner), `g` runs second (outer). This matches the standard convention where alphabetical order corresponds to execution order.

The fundamental cases depend on whether `f` and `g` have statically-known or runtime-dependent output sizes.

#### Case 1: g static, f static (Optimal)

Both output sizes known at compile time.

```
Before compose:
OOOOOOOOOO
          ^ frontier

During (G reserved at frontier, F in scratch):
OOOOOOOOOOGGGGG FFFFF
          ^    ^ frontier

After (F reclaimed):
OOOOOOOOOOGGGGG
          ^    ^ frontier
```

We reserve space for `g`'s output at frontier. `f` writes in scratch above. `f` is reclaimed.

#### Case 2: g static, f runtime (Optimal)

`g`'s size known, `f`'s size runtime-dependent.

```
Before compose:
OOOOOOOOOO
          ^ frontier

During (G reserved at frontier, F in scratch):
OOOOOOOOOOGGGGG FFF...
          ^    ^ frontier (F size unknown, but in scratch)

After (F reclaimed):
OOOOOOOOOOGGGGG
          ^    ^ frontier
```

Since `g`'s size is known, we reserve space for it. `f` writes in scratch (even though `f`'s size is unknown, scratch can grow). `f` is reclaimed.

#### Case 3: g runtime, f static (Suboptimal)

`g`'s size runtime-dependent, `f`'s size known.

```
Before compose:
OOOOOOOOOO
          ^ frontier

After f (F committed at frontier):
OOOOOOOOOOFFFFF
          ^    ^ frontier

After g (G after F):
OOOOOOOOOOFFFFF GGG...
          ^           ^ frontier
          (F is dead, wasted space)
```

We can't reserve space for `g` (unknown size). `f` must commit at frontier. `g` writes after `f`. `f` is dead but stuck below frontier.

#### Case 4: g runtime, f runtime (Suboptimal)

Both sizes runtime-dependent.

```
Before compose:
OOOOOOOOOO
          ^ frontier

After f (F committed at frontier):
OOOOOOOOOOFFF...
          ^     ^ frontier

After g (G after F):
OOOOOOOOOOFFF... GGG...
          ^            ^ frontier
          (F is dead, wasted space)
```

Neither size is known. `f` commits at frontier. `g` writes after. `f` is wasted space.

#### Summary: Fundamental Cases

| Case | g (outer) | f (inner) | Optimal? | Reason |
|------|-----------|-----------|----------|--------|
| 1 | static | static | ✓ | Reserve G, F in scratch |
| 2 | static | runtime | ✓ | Reserve G, F in scratch |
| 3 | runtime | static | ✗ | Can't reserve G, F committed |
| 4 | runtime | runtime | ✗ | Can't reserve G, F committed |

**Key insight**: The determining factor is whether `g` (the outer) is statically-known. If so, we can reserve space for `g` and put `f` in scratch.

#### Functor Map Optimizations

Size-preserving functor maps can only occur in cases where g and f have the same size category:

- **Case 2 (g static, f runtime)**: If g is size-preserving, g's output depends on f's size → g would be runtime. Contradiction.
- **Case 3 (g runtime, f static)**: If g is size-preserving, g's output equals f's size → g would be static. Contradiction.

So size-preserving functor maps only apply to **cases 1 and 4**:

**Case 1 (g static, f static)**: Both sizes known and equal. Instead of reserving G and writing F to scratch, write F at frontier and transform in-place.

```
After f (at frontier, not scratch):
OOOOOOOOOOFFFFF
          ^    ^ frontier

After g (in-place transform):
OOOOOOOOOOggggg
          ^    ^ frontier
```

**Case 4 (g runtime, f runtime)**: Both sizes depend on input and are equal. F writes at frontier, g overwrites in place. No wasted space.

```
After f (at frontier):
OOOOOOOOOOFFF...
          ^     ^ frontier

After g (in-place transform):
OOOOOOOOOOggg...
          ^     ^ frontier
```

**g is cata-like (reducing)**: `g` produces smaller output than its input. Linearity allows reclaiming `f`'s excess space.

```
After f:
OOOOOOOOOOfffffff
          ^      ^ frontier

After g (G smaller, frontier retracts):
OOOOOOOOOOGGG
          ^  ^ frontier
```

**Key insight**: Size-preserving functor maps enable in-place transformation only when g and f have matching size categories (both static or both runtime). Cases 2 and 3 have mismatched categories, so in-place is impossible.

#### Compose Summary Tables

**Baseline Strategy (no linearity assumptions):**

| g (outer) \ f (inner) | f statically-known     | f runtime-dependent            |
|-----------------------|------------------------|--------------------------------|
| **g statically-known**    | Optimal (reserve G, F in scratch) | Optimal (reserve G, F in scratch) |
| **g runtime-dependent**   | Suboptimal (F committed, then G) | Suboptimal (F committed, then G) |

**With Size-Preserving Functor Map:**

Only applies when g and f have matching size categories:

| Case | g (outer) | f (inner) | Result |
|------|-----------|-----------|--------|
| 1 | static (size-preserving) | static | Optimal (in-place) |
| 2 | static | runtime | N/A (category mismatch) |
| 3 | runtime | static | N/A (category mismatch) |
| 4 | runtime (size-preserving) | runtime | Optimal (in-place) |

#### Open Questions

1. How do we statically determine if `g` is a size-preserving functor map? (We know g is static/runtime from its output type, but how do we recognize functor map structure?)

### pair : A → B → A × B

Constructs a product from two values.

**Baseline (non-linear A and B):**

Sequential evaluation, each component commits at frontier.

```
Before pair:
OOOOOOOOOO
          ^ frontier

After A (committed at frontier):
OOOOOOOOOOAAA...
          ^    ^ frontier

After B (committed at frontier):
OOOOOOOOOOAAA...BBB...
          ^          ^ frontier
```

No scratch needed for the pair operation itself (though A and B may use scratch internally).

**Optimizations:**

- **Linear components**: If A and B are linear (consumed exactly once), the pair can be represented as two pointers to existing data rather than copying.

### fst : A × B → A

Projects the first element from a pair.

**Baseline (non-linear):**

The pair exists somewhere on the stack. We copy A to the frontier.

```
Before fst (pair somewhere on stack):
OOOOOOOOOO...AAA...BBB......
                           ^ frontier

After fst (A copied to frontier):
OOOOOOOOOO...AAA...BBB......AAA...
                           ^     ^ frontier
             (pair unchanged, may be used again)
```

**Optimizations:**

- **Linear A**: Use A in place, no copy needed.
- **Linear B**: Reclaim B's space (details TBD).

### snd : A × B → B

Projects the second element from a pair.

**Baseline (non-linear):**

The pair exists somewhere on the stack. We copy B to the frontier.

```
Before snd (pair somewhere on stack):
OOOOOOOOOO...AAA...BBB......
                           ^ frontier

After snd (B copied to frontier):
OOOOOOOOOO...AAA...BBB......BBB...
                           ^     ^ frontier
             (pair unchanged, may be used again)
```

**Optimizations:**

- **Linear B**: Use B in place, no copy needed.
- **Linear A**: Reclaim A's space (details TBD).

### inl : A → A + B

Left injection into a sum type.

**Baseline (non-linear A):**

Create sum at frontier: tag first, then data (copied or via pointer).

Static A:
```
Before inl:
OOOOOOOOOO AAA
              ^ frontier

After inl (sum created at frontier):
OOOOOOOOOO AAA [TAG=L] AAA_copy
              ^                ^ frontier
           orig    sum value
```

Runtime-sized A:
```
Before inl:
OOOOOOOOOO AAA...
                ^ frontier

After inl (sum created at frontier):
OOOOOOOOOO AAA... [TAG=L, ptr→copy] AAA_copy...
                ^                              ^ frontier
              orig       sum value
```

**Optimizations:**

- **Linear A**: No copy. Header points to existing A.

### inr : B → A + B

Right injection into a sum type.

**Baseline (non-linear B):**

Create sum at frontier: tag first, then data (copied or via pointer).

Static B:
```
Before inr:
OOOOOOOOOO BBB
              ^ frontier

After inr (sum created at frontier):
OOOOOOOOOO BBB [TAG=R] BBB_copy
              ^                ^ frontier
           orig    sum value
```

Runtime-sized B:
```
Before inr:
OOOOOOOOOO BBB...
                ^ frontier

After inr (sum created at frontier):
OOOOOOOOOO BBB... [TAG=R, ptr→copy] BBB_copy...
                ^                              ^ frontier
              orig       sum value
```

**Optimizations:**

- **Linear B**: No copy. Header points to existing B.

### case : (A → C) → (B → C) → (A + B) → C

Eliminates a sum type by applying the appropriate function based on the tag.

**Example:**
```
leftHandler : Int → String
rightHandler : Bool → String

example : Int + Bool → String
example = case leftHandler rightHandler
```

**Baseline:**

Read the tag, access data (inline or via pointer), apply the appropriate function, produce C at frontier.

Static sum:
```
Before case:
OOOOOOOOOO [TAG] data
                     ^ frontier

After case (C produced at frontier):
OOOOOOOOOO [TAG] data CCC...
                     ^      ^ frontier
```

Runtime-sized sum:
```
Before case:
OOOOOOOOOO [TAG, ptr→data] data...
                                  ^ frontier

After case (C produced at frontier):
OOOOOOOOOO [TAG, ptr→data] data... CCC...
                                  ^      ^ frontier
```

**Optimizations:**

- **Linear sum**: Reclaim the sum header and data after case completes.

### curry : (A × B → C) → (A → B → C)

Converts a function on products to a curried function.

**Example:**
```
add : Int × Int → Int
curriedAdd : Int → (Int → Int)
curriedAdd = curry add

add5 : Int → Int
add5 = curriedAdd 5    -- closure: env* code* (where env* → 5)
```

**Baseline:**

Allocate 2-slot closure at frontier, store env* and code*.

```
Before curry (applied to x : A):
OOOOOOOOOO XXX
              ^ frontier

After curry (closure pushed):
OOOOOOOOOO XXX env* code*
              ^          ^ frontier
```

The env* points to the captured `x`. For nested currying, the environment is a nested structure of previously applied arguments.

### apply : (A → B) × A → B

Applies a function to an argument.

**Example:**
```
add5 : Int → Int
add5 = curriedAdd 5    -- closure: env* code*

result : Int
result = apply (add5, 3)   -- evaluates to 8
```

**Input representation:**

The input is a product `(A → B) × A`. Closure is static-sized (2 slots), A may be static or runtime:

- A static: `env* code* AAA`
- A runtime: `env* code* ptr→A`

**Baseline:**

1. Read env* from closure (first slot of input)
2. Access arg (third slot, or follow pointer if runtime)
3. Form new pair `(env, arg)` for body
4. Push child frame, execute body code
5. Pop frame, produce result at frontier

```
Before apply (A static):
OOOOOOOOOO env* code* AAA
                         ^ frontier

After apply (B produced at frontier):
OOOOOOOOOO env* code* AAA BBB...
                         ^      ^ frontier
```

**Optimizations:**

- **Linear closure**: Reclaim closure after apply completes.
- **Linear arg**: Reclaim arg after apply completes.

(To be added: ana, cata, etc.)
