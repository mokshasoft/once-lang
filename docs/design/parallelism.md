# Parallelism in Once

## Categorical Foundation

In category theory, two fundamental ways to combine computations correspond to sequential and parallel execution:

| Structure | Once Syntax | Meaning | Execution |
|-----------|-------------|---------|-----------|
| Composition | `f . g` | Do g, then f | Sequential |
| Product | `pair f g` | Compute both f and g | Potentially parallel |

This distinction is fundamental to Once's design and has direct implications for parallelism.

## Products Enable Parallelism

When you write:

```
pair f g : A -> B * C
```

The functions `f : A -> B` and `g : A -> C` are **independent** - neither depends on the other's result. This independence is exactly what enables parallel execution.

```
-- Sequential: g must complete before f starts
compose f g : A -> C

-- Parallel opportunity: f and g can run simultaneously
pair f g : A -> B * C
```

## Applicative vs Monadic Composition

This connects directly to the IO monad levels (see D026):

| Level | Operation | Parallelizable? |
|-------|-----------|-----------------|
| Functor | `fmap f x` | N/A (single operation) |
| Applicative | `both x y` | Yes - independent |
| Monad | `bind x f` | No - f depends on x's result |

```
-- Can parallelize: read two files independently
both (readFile "a.txt") (readFile "b.txt") : IO (String * String)

-- Cannot parallelize: second read depends on first
bind (readFile "config.txt") (\cfg -> readFile (getPath cfg))
```

This is why the IO documentation recommends preferring the weakest abstraction level that works - applicative operations can parallelize, monadic ones cannot.

## Day Convolution

For combining effectful computations in parallel, Once uses **Day convolution**:

```
Day F G A = exists X Y. F X * G Y * (X * Y -> A)
```

Day convolution combines two functors while preserving their independence. For `IO`:

```
day : IO A -> IO B -> IO (A * B)
day = both
```

This is the applicative `both` operation - it runs two IO operations and pairs their results.

## Parallelism and Linearity

Once's quantitative types (QTT) interact with parallelism:

| Quantity | Parallelism Implication |
|----------|------------------------|
| `0` (erased) | Compile-time only, no runtime |
| `1` (linear) | Used exactly once - safe to parallelize without synchronization |
| `ω` (unrestricted) | May need synchronization if shared |

Linear values (`A^1`) are particularly amenable to parallelism because they cannot be shared - each parallel branch owns its inputs exclusively.

```
-- Both branches use their input linearly
parallel : A^1 * B^1 -> C^1 * D^1
parallel = pair (processA . fst) (processB . snd)
```

## Parallel Patterns

### Map-Reduce

```
-- Map phase: parallel (each element independent)
mapParallel : (A -> B) -> List A -> List B

-- Reduce phase: requires associative operation
reduce : (B -> B -> B) -> B -> List B -> B

-- Combined
mapReduce : (A -> B) -> (B -> B -> B) -> B -> List A -> B
mapReduce mapper reducer init = reduce reducer init . mapParallel mapper
```

The categorical requirement: `reducer` must be associative for parallel reduction to be correct.

### Fork-Join

```
-- Fork: split into independent computations
fork : A -> (A -> B) * (A -> C) -> B * C
fork x (f, g) = pair f g x

-- Join: combine results
join : B * C -> (B -> C -> D) -> D
join (b, c) combine = combine b c
```

### Pipeline Parallelism

```
-- Three-stage pipeline
stage1 : A -> B
stage2 : B -> C
stage3 : C -> D

-- Sequential composition
pipeline : A -> D
pipeline = stage3 . stage2 . stage1

-- With buffering, stages can overlap on different inputs
```

## Streams and Parallelism

Once's coalgebraic streams (see [Time](time.md)) naturally support pipeline parallelism:

```
Stream A = A * Stream A

-- Process stream elements in parallel batches
batchProcess : Int -> (A -> B) -> Stream A -> Stream (List B)
```

Each element in a stream is independent of future elements, enabling parallel processing of batches.

## Compiler Optimizations

The Once compiler can analyze code for parallelism opportunities:

1. **Independence analysis**: Identify `pair` constructions where both branches are pure
2. **Quantity checking**: Ensure linear resources aren't incorrectly shared
3. **Effect tracking**: Only parallelize applicative (not monadic) effect compositions

```
-- Compiler can parallelize
pure : pair (expensive1 x) (expensive2 x)

-- Compiler cannot parallelize (IO, but applicative - runtime can)
io : both (readFile a) (readFile b)

-- Compiler cannot parallelize (monadic dependency)
sequential : bind (readFile a) (\x -> readFile (process x))
```

## Target-Specific Parallelism

Different compilation targets implement parallelism differently:

| Target | Parallelism Mechanism |
|--------|----------------------|
| C | pthreads, OpenMP pragmas |
| Rust | rayon, async/await |
| JavaScript | Web Workers, Promise.all |
| WASM | SharedArrayBuffer, threads proposal |
| Bare metal | Hardware parallelism, interrupts |

Once's categorical IR maps to each target's native parallelism constructs.

## Summary

| Concept | Once Approach |
|---------|---------------|
| Sequential | Composition (`f . g`) |
| Parallel opportunity | Product (`pair f g`) |
| Effectful parallel | Applicative `both`, Day convolution |
| Effectful sequential | Monadic `bind` |
| Safety | QTT quantities track sharing |
| Optimization | Compiler analyzes independence |

Parallelism in Once emerges naturally from categorical structure. Products represent independent computations, applicative functors enable parallel effects, and quantitative types ensure safe resource usage across parallel branches.
