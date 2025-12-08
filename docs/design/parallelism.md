# Parallelism in Once

## The Categorical Model

In category theory, there are two fundamental ways to combine computations:

| Combinator | Symbol | Meaning | Data Dependency |
|------------|--------|---------|-----------------|
| **Composition** | `compose f g` or `g . f` | Sequential: f then g | g depends on f's output |
| **Product** | `f * g` | Parallel: f AND g | Independent |

Once encodes both:

```
-- Sequential
compose g f       -- do f, then g

-- Parallel
pair f g          -- product: do f and g simultaneously
```

## Products = Parallelism

The categorical product `A * B` represents "A and B together". When you have:

```
pair f g : C -> A * B
-- where f : C -> A
-- and   g : C -> B
```

The computations `f` and `g` are **independent** - they both take `C` as input but don't depend on each other. A parallel runtime can execute them simultaneously.

### In Once

```
-- Construct parallel pair
result = pair f g       -- C -> A * B

-- Apply functions in parallel on product input
both = bimap f g        -- (A * C) -> (B * D)
```

## Day Convolution: Parallel Effects

Once uses **Day convolution** for parallel effect combination:

```
Day F G A = exists X Y. (F X * G Y * (X * Y -> A))
```

This says: "Run effectful computation `F` and effectful computation `G` in parallel, then combine their results."

### Monoidal Functors

The `Monoidal` typeclass captures functors that preserve this parallel structure:

```
class Monoidal F where
  unit : Unit -> F Unit
  mult : F A * F B -> F (A * B)
```

## How Parallelism Compiles

### Source Level

```
-- Two independent computations
computation = pair (fetchUser userId) (fetchPosts userId)
-- Type: IO (User * Posts)
```

### After Analysis

The compiler sees:
- `fetchUser` and `fetchPosts` are independent (no data flow between them)
- Both can start immediately
- Result is a pair

### Generated Code (conceptual)

```c
// Sequential version
User user = fetchUser(userId);
Posts posts = fetchPosts(userId);
return (Pair){user, posts};

// Parallel version (compiler optimization)
Future<User> userFuture = async(fetchUser, userId);
Future<Posts> postsFuture = async(fetchPosts, userId);
return (Pair){await(userFuture), await(postsFuture)};
```

### Bare Metal Version

```asm
; Fork two tasks
fork task1, fetchUser, userId
fork task2, fetchPosts, userId

; Wait for both
join task1, r1
join task2, r2

; Return pair
push r1
push r2
ret
```

## Parallelism Operators in Once

| Operator | Type | Meaning |
|----------|------|---------|
| `pair` | `(C -> A) -> (C -> B) -> (C -> A * B)` | Parallel pairing |
| `bimap` | `(A -> B) -> (C -> D) -> (A * C -> B * D)` | Parallel morphisms |
| `fst` | `A * B -> A` | First projection |
| `snd` | `A * B -> B` | Second projection |
| `Day` | Day convolution | Parallel effects |

## Symmetric Monoidal Categories

Once's categorical foundation is a **symmetric monoidal category**, which means:

```
A * B ≅ B * A   -- order doesn't matter (swap)
```

This is exactly the property needed for parallelism: if order doesn't matter, we can execute in any order - including simultaneously.

## Example: Parallel Effect Pipeline

```
type Query = Network * State

-- Sequential: fetch then process then store
sequential = compose store (compose process fetch)

-- Parallel: fetch user AND posts simultaneously
parallel = compose render (compose combine (pair fetchUser fetchPosts))
--                                         ^^^^^^^^^^^^^^^^^^^^^^^^^
--                                         These run in parallel!
```

## Automatic Parallelization

Because the parallel structure is **in the types**, a compiler can:

1. **Detect independence**: Products indicate no data dependency
2. **Extract parallelism**: Factor sequential code into parallel where possible
3. **Generate parallel code**: Emit threads, async, or SIMD as appropriate

### Example Transformation

```
-- Programmer writes:
compose i (compose (pair g h) f)

-- Compiler sees:
--   f must complete before (pair g h)
--   g and h are independent (product)
--   i waits for both g and h

-- Compiler generates:
fork(f) -> (fork(g) || fork(h)) -> join -> i
```

## Categories with Explicit Parallelism

For fine-grained control, Once could define:

```
-- Parallel arrow category
type Par A B = ...  -- tracks parallelism explicitly

-- With primitives:
fork : (A -> B) -> Par A B     -- mark for parallel
join : Par A B -> (A -> B)     -- synchronize
```

## Comparison with Other Approaches

| Approach | How Parallelism is Expressed |
|----------|------------------------------|
| **Threads** | Explicit `fork`/`join` |
| **Async/Await** | Explicit `async`, implicit sync |
| **Futures** | Explicit `Future`, explicit `get` |
| **Par Monad** | Explicit `par`/`pseq` |
| **Arrows** | `(***)` and `(&&&)` |
| **Once/Categorical** | Products and Day convolution |

The categorical approach makes parallelism **implicit in the structure** rather than explicit in the syntax.

## Conclusion

In Once:

1. **Sequential** = Composition (`compose`)
2. **Parallel** = Products (`pair`, Day)
3. **The types tell you** which is which
4. **Compilers can automatically parallelize** based on categorical structure

Parallelism isn't an add-on feature - it's built into the mathematical foundation. Products `*` and Day convolution are inherently parallel constructs.
