# Competitive Programming Examples in Once

This directory contains implementations of classic competitive programming problems in Once, demonstrating the language's approach to algorithms.

## Prerequisites

These examples require the arithmetic and control primitives:
- `Strata/Interpretations/Linux/arith.once` - Integer arithmetic
- `Strata/Interpretations/Linux/control.once` - Branching primitives

## Classic Problems

### 1. GCD (Greatest Common Divisor)
**Category**: Number Theory
**Technique**: Euclidean Algorithm, Recursion

### 2. Factorial
**Category**: Basic Recursion
**Technique**: Recursive computation via Fix

### 3. Fibonacci
**Category**: Dynamic Programming
**Technique**: Recursive with memoization (or iterative)

### 4. FizzBuzz
**Category**: Basic Branching
**Technique**: Integer modulo and conditional output

## Once's Approach to Algorithms

Once is a categorical language - it expresses computation through composition of morphisms rather than imperative statements. This leads to some interesting patterns:

### Branching
Instead of `if-then-else`, Once uses sum types and `case`:
```once
-- Branch on whether n is zero
-- ifZero : Int -> Unit + Unit
result = case (ifZero n) handleZero handleNonZero
```

### Recursion
Once uses Fix types and fold/unfold for recursion:
```once
-- Natural numbers as Fix (Unit + X)
type Nat = Fix (Unit + Nat)

zero : Nat
zero = fold (inl terminal)

succ : Nat -> Nat
succ n = fold (inr n)
```

### No Mutation
All computation is pure - values flow through function composition, never modified in place. This aligns well with functional algorithm implementations.

## Performance Notes

Once compiles to C, so performance should be comparable to C for equivalent algorithms. The categorical abstraction is compile-time only; at runtime it's just function calls and data structures.
