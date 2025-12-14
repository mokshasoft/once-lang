# Competitive Programming in Once

This document analyzes what's needed to implement classic competitive programming problems in Once, and what's currently possible.

## Classic Problem Categories

Based on [ICPC](https://icpc.global/worldfinals/past-problems), [Codeforces](https://codeforces.com/), and [GeeksforGeeks](https://www.geeksforgeeks.org/blogs/how-to-prepare-for-acm-icpc/), the most common problem types are:

| Category | Examples | Required Features |
|----------|----------|-------------------|
| Dynamic Programming | Fibonacci, Knapsack, LCS | Recursion, Arrays, Arithmetic |
| Graph Algorithms | BFS, DFS, Dijkstra | Graphs (nodes/edges), Queues |
| Number Theory | GCD, Primes, Factoring | Arithmetic, Loops |
| Data Structures | Stacks, Queues, Trees | Recursive types, Pattern matching |
| Sorting | QuickSort, MergeSort | Arrays, Comparisons, Recursion |
| Greedy | Activity Selection | Sorting, Comparisons |
| String | Pattern Matching, Parsing | String operations |

## What Once Currently Has

✅ **Available:**
- Product types (A * B) with fst, snd, pair
- Sum types (A + B) with inl, inr, case
- Functions with curry, apply, compose
- Recursive types via Fix, fold, unfold
- Strings and I/O primitives
- Let bindings

## What Once Needs (Added in this PR)

The following primitives have been added to enable competitive programming:

### `Strata/Interpretations/Linux/arith.once`
```once
-- Basic arithmetic
primitive add : Int * Int -> Int
primitive sub : Int * Int -> Int
primitive mul : Int * Int -> Int
primitive div : Int * Int -> Int
primitive mod : Int * Int -> Int

-- Comparisons (return 0 or 1)
primitive eq  : Int * Int -> Int
primitive lt  : Int * Int -> Int
primitive gt  : Int * Int -> Int
primitive le  : Int * Int -> Int
primitive ge  : Int * Int -> Int

-- Bitwise operations
primitive band : Int * Int -> Int
primitive bor  : Int * Int -> Int
primitive bxor : Int * Int -> Int
primitive shl  : Int * Int -> Int
primitive shr  : Int * Int -> Int
```

### `Strata/Interpretations/Linux/control.once`
```once
-- Convert Int comparison result to sum type for case branching
primitive ifZero : Int -> Unit + Unit

-- String/Int conversion
primitive parseInt : String Utf8 -> Int
primitive intToString : Int -> String Utf8
```

## What Once Still Needs

### 1. Integer Literals in Expressions
Currently, integer literals may only appear in certain contexts. Need:
```once
-- Want to write:
three : Int
three = 3

-- Currently need workarounds
```

### 2. Iteration/Loops
Once uses recursion via Fix, but ergonomic looping patterns are needed:
```once
-- Church-encoded iteration
times : Int -> (A -> A) -> A -> A
times n f x = ...  -- Apply f to x, n times

-- Or a loop primitive
primitive loop : Int * (Int -> A) -> Unit
```

### 3. Arrays/Vectors
For many algorithms, indexed collections are essential:
```once
-- Fixed-size arrays
type Array A = ...

-- Operations
primitive arrayNew : Int -> Array A
primitive arrayGet : Array A * Int -> A
primitive arraySet : Array A * Int * A -> Array A
```

## Example: GCD (What It Would Look Like)

The Euclidean algorithm in Once with the new primitives:

```once
import I.Linux.arith as A
import I.Linux.control as C

-- GCD using Euclidean algorithm
-- gcd(a, b) = if b == 0 then a else gcd(b, a mod b)
gcd : Int * Int -> Int
gcd = \ab ->
  let a = fst ab
      b = snd ab
      r = mod@A ab  -- a mod b
  in case (ifZero@C b)
       (const a)           -- b == 0: return a
       (const (gcd (pair (const b) (const r) terminal)))  -- recurse
```

**Challenge:** This recursive call doesn't work directly - Once needs explicit Fix for recursion.

### GCD with Explicit Fix
```once
-- Define recursive GCD via fixed point
type GcdF = (Int * Int -> Int) -> Int * Int -> Int

gcdStep : GcdF
gcdStep rec ab =
  let b = snd ab
      r = mod@A ab
  in case (ifZero@C b)
       (const (fst ab))
       (const (rec (pair (const b) (const r) terminal)))

-- gcd = fix gcdStep
-- (Requires the language to support Fix at function level)
```

## Example: Factorial

```once
import I.Linux.arith as A
import I.Linux.control as C

-- factorial(n) = if n == 0 then 1 else n * factorial(n-1)
-- As a Fix type:
type FactF = (Int -> Int) -> Int -> Int

factStep : FactF
factStep rec n =
  case (ifZero@C n)
    (const 1)  -- Base case: 0! = 1
    (const (mul@A (pair (const n) (const (rec (sub@A (pair (const n) (const 1) terminal)))) terminal)))
```

## Example: FizzBuzz

```once
import I.Linux.File as F
import I.Linux.arith as A
import I.Linux.control as C

fizzbuzzOne : Int -> IO Unit
fizzbuzzOne n =
  let by15 = mod@A (pair (const n) (const 15) terminal)
      by3  = mod@A (pair (const n) (const 3) terminal)
      by5  = mod@A (pair (const n) (const 5) terminal)
  in case (ifZero@C by15)
       (const (println@F "FizzBuzz"))
       (const (case (ifZero@C by3)
                (const (println@F "Fizz"))
                (const (case (ifZero@C by5)
                         (const (println@F "Buzz"))
                         (const (compose println@F (intToString@C n)))))))
       terminal
```

## Performance Considerations

### Compilation to C
Once compiles to C, so runtime performance should be comparable to C:
- No garbage collection (linear types)
- Direct function calls
- Stack-allocated pairs and sums

### Categorical Overhead
The categorical abstraction is **compile-time only**:
- `compose f g` compiles to `f(g(x))`
- `pair f g` compiles to `{f(x), g(x)}`
- No runtime overhead for morphism composition

### What Affects Performance
1. **Recursion depth** - C stack limits apply
2. **Allocation** - Pairs/sums are stack-allocated
3. **No tail-call optimization** - Deep recursion may overflow

## Benchmarking Plan

To properly benchmark Once for competitive programming:

1. **Implement standard algorithms:**
   - GCD, Factorial, Fibonacci
   - Sorting (via Fix-based lists)
   - Graph traversal

2. **Compare against:**
   - Hand-written C
   - Haskell
   - Rust

3. **Measure:**
   - Compilation time
   - Runtime performance
   - Memory usage
   - Binary size

## Conclusion

Once can express competitive programming algorithms, but currently requires:
1. ✅ Arithmetic primitives (added)
2. ✅ Control flow primitives (added)
3. ⚠️ Better integer literal syntax
4. ⚠️ Ergonomic recursion patterns
5. ❌ Array support (future work)

The categorical foundation is sound - the main gap is ergonomics and syntactic sugar for common patterns.

## Sources

- [ICPC Past Problems](https://icpc.global/worldfinals/past-problems)
- [Codeforces](https://codeforces.com/)
- [Top Classic Data Structures Problems](https://codeforces.com/blog/entry/79755)
- [How to prepare for ACM-ICPC](https://www.geeksforgeeks.org/blogs/how-to-prepare-for-acm-icpc/)
