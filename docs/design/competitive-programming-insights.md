# Competitive Programming in Once: Key Insights

## Most Common Problem Types

From ICPC, Codeforces, and competitive programming literature:

1. **Dynamic Programming** - Fibonacci, Knapsack, LCS (most frequent)
2. **Graph Algorithms** - BFS, DFS, Dijkstra
3. **Number Theory** - GCD, primes, modular arithmetic
4. **Data Structures** - Trees, heaps, segment trees
5. **Sorting** - QuickSort, MergeSort, counting sort
6. **Greedy Algorithms** - Activity selection, interval scheduling

## Once's Categorical Approach

Once expresses algorithms differently than imperative languages:

### Branching via Sum Types

Instead of `if-then-else`, Once uses sum types and `case`:

```once
-- Imperative style (not Once):
if b == 0 then a else gcd(b, a % b)

-- Once style:
case (ifZero b)
  (const a)                    -- left branch: b == 0
  (const (gcd (pair b r)))     -- right branch: recurse
```

The `ifZero : Int -> Unit + Unit` primitive converts an integer comparison into a sum type that `case` can dispatch on.

### Recursion via Fix

Once doesn't have direct recursion. Instead, use fixed points:

```once
-- Define the recursive step as a functor
type GcdF = (Int * Int -> Int) -> Int * Int -> Int

gcdStep : GcdF
gcdStep rec ab =
  case (ifZero (snd ab))
    (const (fst ab))
    (const (rec (pair (snd ab) (mod ab))))

-- The fixed point gives us the recursive function
-- gcd = fix gcdStep
```

### Composition Over Statements

Once programs are compositions of morphisms, not sequences of statements:

```once
-- Imperative: x = f(y); z = g(x); return h(z)
-- Once: compose h (compose g f)
```

## Performance Model

**Compile-time abstraction:** The categorical structure is resolved at compile time:
- `compose f g` → `f(g(x))` in C
- `pair f g` → `{f(x), g(x)}` struct
- No runtime overhead for morphism composition

**Memory model:**
- Pairs and sums are stack-allocated
- Linear types prevent garbage collection need
- Direct C function calls

**Expected performance:** Should match hand-written C for equivalent algorithms.

## What Once Needs for Competitive Programming

### Currently Available
- ✅ Product types (pairs) with fst, snd, pair
- ✅ Sum types with inl, inr, case
- ✅ Function composition
- ✅ Recursive types via Fix
- ✅ String I/O

### Added in This Analysis
- ✅ Integer arithmetic (add, sub, mul, div, mod)
- ✅ Comparisons (eq, lt, gt, le, ge)
- ✅ Bitwise operations
- ✅ Control flow (ifZero for branching)
- ✅ String/Int conversion

### Still Needed
- ⚠️ Integer literals in expressions
- ⚠️ Ergonomic recursion syntax
- ❌ Arrays/vectors for O(1) indexing
- ❌ Mutable state (for some algorithms)

## Algorithm Patterns in Once

### Pattern 1: Conditional Computation
```once
-- if cond then a else b
-- becomes:
case (ifZero cond) (const b) (const a)
-- Note: ifZero returns Left on zero, so branches are swapped
```

### Pattern 2: Recursive Functions
```once
-- Use Fix type and fold/unfold
-- Or define step function and apply fixed-point combinator
```

### Pattern 3: Accumulating Results
```once
-- Use pairs to thread state through composition
-- (value, accumulator) -> (newValue, newAccumulator)
```

### Pattern 4: Multiple Branches
```once
-- Nest case expressions or use sum-of-sums
case outer
  (case inner1 ...)
  (case inner2 ...)
```

## Benchmarking Strategy

To measure Once's competitive programming performance:

1. **Implement baseline algorithms:** GCD, factorial, Fibonacci, sorting
2. **Compare against:** Hand-written C, Haskell, Rust
3. **Metrics:** Runtime, memory usage, binary size, compile time

## Conclusion

Once can express competitive programming algorithms through its categorical foundation. The main differences from imperative languages:

1. **Branching** uses sum types instead of if-then-else
2. **Recursion** uses Fix types instead of direct self-reference
3. **State** flows through function composition, not mutation
4. **Performance** should match C (compile-time abstraction only)

The categorical approach is unconventional but mathematically principled - every Once program corresponds to a morphism in a bicartesian closed category.
