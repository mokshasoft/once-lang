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
- **Linear morphism**: A morphism that reads each input exactly once. Enables reclamation: after f consumes g's output, that space is dead and can be reclaimed. Note: linearity alone does not enable in-place overwrite (see functor map).

## Core Principles

1. **Scratch reclamation**: Each IR fully reclaims its scratch data after completion.
2. **Output at frontier**: Each IR concatenates its output to the frontier and advances it.
3. **Linearity**: Intermediate results are consumed exactly once, enabling reclamation.

## Compose: `(f ∘ g)(x)` = `f(g(x))`

Legend: `O` = earlier output, `G` = g output, `F` = f output, `^` = frontier

The fundamental cases depend on whether `f` and `g` have statically-known or runtime-dependent output sizes.

### Case 1: f static, g static (Optimal)

Both output sizes known at compile time.

```
Before compose:
OOOOOOOOOO
          ^ frontier

During (F reserved at frontier, G in scratch):
OOOOOOOOOOFFFFF GGGGG
          ^    ^ frontier

After (G reclaimed):
OOOOOOOOOOFFFFF
          ^    ^ frontier
```

We reserve space for `f`'s output at frontier. `g` writes in scratch above. `g` is reclaimed.

### Case 2: f static, g runtime (Optimal)

`f`'s size known, `g`'s size runtime-dependent.

```
Before compose:
OOOOOOOOOO
          ^ frontier

During (F reserved at frontier, G in scratch):
OOOOOOOOOOFFFFF GGG...
          ^    ^ frontier (G size unknown, but in scratch)

After (G reclaimed):
OOOOOOOOOOFFFFF
          ^    ^ frontier
```

Since `f`'s size is known, we reserve space for it. `g` writes in scratch (even though `g`'s size is unknown, scratch can grow). `g` is reclaimed.

### Case 3: f runtime, g static (Suboptimal)

`f`'s size runtime-dependent, `g`'s size known.

```
Before compose:
OOOOOOOOOO
          ^ frontier

After g (G committed at frontier):
OOOOOOOOOOGGGGG
          ^    ^ frontier

After f (F after G):
OOOOOOOOOOGGGGG FFF...
          ^           ^ frontier
          (G is dead, wasted space)
```

We can't reserve space for `f` (unknown size). `g` must commit at frontier. `f` writes after `g`. `g` is dead but stuck below frontier.

### Case 4: f runtime, g runtime (Suboptimal)

Both sizes runtime-dependent.

```
Before compose:
OOOOOOOOOO
          ^ frontier

After g (G committed at frontier):
OOOOOOOOOOGGG...
          ^     ^ frontier

After f (F after G):
OOOOOOOOOOGGG... FFF...
          ^            ^ frontier
          (G is dead, wasted space)
```

Neither size is known. `g` commits at frontier. `f` writes after. `g` is wasted space.

### Summary: Fundamental Cases

| Case | f | g | Optimal? | Reason |
|------|---|---|----------|--------|
| 1 | static | static | ✓ | Reserve F, G in scratch |
| 2 | static | runtime | ✓ | Reserve F, G in scratch |
| 3 | runtime | static | ✗ | Can't reserve F, G committed |
| 4 | runtime | runtime | ✗ | Can't reserve F, G committed |

**Key insight**: The determining factor is whether `f` is statically-known. If so, we can reserve space for `f` and put `g` in scratch.

### Functor Map Optimizations

Size-preserving functor maps can only occur in cases where f and g have the same size category:

- **Case 2 (f static, g runtime)**: If f is size-preserving, f's output depends on g's size → f would be runtime. Contradiction.
- **Case 3 (f runtime, g static)**: If f is size-preserving, f's output equals g's size → f would be static. Contradiction.

So size-preserving functor maps only apply to **cases 1 and 4**:

**Case 1 (f static, g static)**: Both sizes known and equal. Instead of reserving F and writing G to scratch, write G at frontier and transform in-place.

```
After g (at frontier, not scratch):
OOOOOOOOOOGGGGG
          ^    ^ frontier

After f (in-place transform):
OOOOOOOOOOfffff
          ^    ^ frontier
```

**Case 4 (f runtime, g runtime)**: Both sizes depend on input and are equal. G writes at frontier, f overwrites in place. No wasted space.

```
After g (at frontier):
OOOOOOOOOOGGG...
          ^     ^ frontier

After f (in-place transform):
OOOOOOOOOOfff...
          ^     ^ frontier
```

**f is cata-like (reducing)**: `f` produces smaller output than its input. Linearity allows reclaiming `g`'s excess space.

```
After g:
OOOOOOOOOOGGGGGGG
          ^      ^ frontier

After f (F smaller, frontier retracts):
OOOOOOOOOOFFF
          ^  ^ frontier
```

**Key insight**: Size-preserving functor maps enable in-place transformation only when f and g have matching size categories (both static or both runtime). Cases 2 and 3 have mismatched categories, so in-place is impossible.

## Summary Tables

### Baseline Strategy (no linearity assumptions)

| f \ g               | g statically-known     | g runtime-dependent            |
|---------------------|------------------------|--------------------------------|
| **f statically-known**  | Optimal (reserve F, G in scratch) | Optimal (reserve F, G in scratch) |
| **f runtime-dependent** | Suboptimal (G committed, then F) | Suboptimal (G committed, then F) |

### With Size-Preserving Functor Map

Only applies when f and g have matching size categories:

| Case | f | g | Result |
|------|---|---|--------|
| 1 | static (size-preserving) | static | Optimal (in-place) |
| 2 | static | runtime | N/A (category mismatch) |
| 3 | runtime | static | N/A (category mismatch) |
| 4 | runtime (size-preserving) | runtime | Optimal (in-place) |

## Open Questions

1. How do we statically determine if `f` is a size-preserving functor map? (We know f is static/runtime from its output type, but how do we recognize functor map structure?)

## IR-Specific Layouts

(To be added for each IR: pair, fst, snd, inl, inr, case, curry, apply, ana, cata, etc.)
