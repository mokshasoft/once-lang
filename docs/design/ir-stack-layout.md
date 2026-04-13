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

## Compose: `(g ∘ f)(x)` = `g(f(x))`

Legend: `O` = earlier output, `F` = f output, `G` = g output, `^` = frontier

Here `f` runs first (inner), `g` runs second (outer). This matches the standard convention where alphabetical order corresponds to execution order.

The fundamental cases depend on whether `f` and `g` have statically-known or runtime-dependent output sizes.

### Case 1: g static, f static (Optimal)

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

### Case 2: g static, f runtime (Optimal)

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

### Case 3: g runtime, f static (Suboptimal)

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

### Case 4: g runtime, f runtime (Suboptimal)

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

### Summary: Fundamental Cases

| Case | g (outer) | f (inner) | Optimal? | Reason |
|------|-----------|-----------|----------|--------|
| 1 | static | static | ✓ | Reserve G, F in scratch |
| 2 | static | runtime | ✓ | Reserve G, F in scratch |
| 3 | runtime | static | ✗ | Can't reserve G, F committed |
| 4 | runtime | runtime | ✗ | Can't reserve G, F committed |

**Key insight**: The determining factor is whether `g` (the outer) is statically-known. If so, we can reserve space for `g` and put `f` in scratch.

### Functor Map Optimizations

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

## Summary Tables

### Baseline Strategy (no linearity assumptions)

| g (outer) \ f (inner) | f statically-known     | f runtime-dependent            |
|-----------------------|------------------------|--------------------------------|
| **g statically-known**    | Optimal (reserve G, F in scratch) | Optimal (reserve G, F in scratch) |
| **g runtime-dependent**   | Suboptimal (F committed, then G) | Suboptimal (F committed, then G) |

### With Size-Preserving Functor Map

Only applies when g and f have matching size categories:

| Case | g (outer) | f (inner) | Result |
|------|-----------|-----------|--------|
| 1 | static (size-preserving) | static | Optimal (in-place) |
| 2 | static | runtime | N/A (category mismatch) |
| 3 | runtime | static | N/A (category mismatch) |
| 4 | runtime (size-preserving) | runtime | Optimal (in-place) |

## Open Questions

1. How do we statically determine if `g` is a size-preserving functor map? (We know g is static/runtime from its output type, but how do we recognize functor map structure?)

## IR-Specific Layouts

(To be added for each IR: pair, fst, snd, inl, inr, case, curry, apply, ana, cata, etc.)
