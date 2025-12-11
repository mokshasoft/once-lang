# Syntax Design in Once

## Design Goals

Once's syntax must express categorical concepts clearly while remaining practical for everyday programming. The challenge: how do you write natural transformations in a way that's both mathematically honest and readable?

## Core Syntax Elements

### Type Operators

```
A -> B      Function/morphism from A to B
A * B       Product (pair of A and B)
A + B       Coproduct/sum (either A or B)
A^1         Linear type (used exactly once)
A^0         Erased type (compile-time only)
```

### The 12 Generators

Every Once program reduces to compositions of these primitives:

```
-- Identity and composition
id      : A -> A
compose : (B -> C) -> (A -> B) -> (A -> C)

-- Products
fst     : A * B -> A
snd     : A * B -> B
pair    : (C -> A) -> (C -> B) -> (C -> A * B)

-- Coproducts
inl     : A -> A + B
inr     : B -> A + B
case    : (A -> C) -> (B -> C) -> (A + B -> C)

-- Terminal and initial
terminal : A -> Unit
initial  : Void -> A

-- Exponentials
curry   : (A * B -> C) -> (A -> (B -> C))
apply   : (A -> B) * A -> B
```

## Composition Styles

Once supports multiple ways to compose morphisms, all equivalent:

### Right-to-Left (Mathematical)

```
-- Read: "apply g, then f"
result : A -> C
result = compose f g
```

This matches standard mathematical notation where `f ∘ g` means "g then f".

### Operator Syntax

```
-- Dot operator (same as compose)
result = f . g

-- Pipeline operator (reversed)
result = g |> f
```

The pipeline operator `|>` reads left-to-right, which some find more intuitive for sequential operations.

### Comparison

| Style | Example | Reading Order |
|-------|---------|---------------|
| `compose f g` | Explicit | Right-to-left |
| `f . g` | Operator | Right-to-left |
| `g \|> f` | Pipeline | Left-to-right |

All three are equivalent - choose based on readability for your use case.

## Function Application

Once uses ML-style juxtaposition for application:

```
-- Apply f to x
f x

-- Apply f to multiple arguments (curried)
f x y z

-- Equivalent to
apply (apply (apply f x) y) z
```

Parentheses group when needed:

```
-- Apply f to the result of (g x)
f (g x)
```

## Definitions

### Simple Definitions

```
-- Define a morphism
swap : A * B -> B * A
swap = pair snd fst

-- With explicit type
double : Int -> Int
double = compose add (pair id id)
```

### Pattern Matching

For sum types, use `case`:

```
-- Handle Result type
handleResult : Result A E -> B
handleResult = case onSuccess onError
```

## Effects in Types

Once has no separate effect system. Effects appear in the type:

```
-- Pure function (no effects)
increment : Int -> Int

-- Effectful operation (returns IO)
readFile : Path -> IO (String + Error)

-- The type signature IS the effect declaration
```

This means:
- Looking at a type tells you everything about its effects
- No hidden side effects possible
- Compiler tracks effect propagation automatically

## Worked Example: Data Processing

```
-- Parse and validate input
process : String -> Result Data Error
process = compose validate parse

-- Where:
parse    : String -> Result Json Error
validate : Result Json Error -> Result Data Error

-- Using pipeline style:
process = parse |> validate
```

## Worked Example: IO Sequencing

```
-- Copy a file
copyFile : Path * Path -> IO (Unit + Error)
copyFile = compose writeFile (compose (pair snd readFile) fst)

-- More readable with bind:
copyFile paths =
  bind (readFile (snd paths)) (\contents ->
    writeFile (fst paths) contents
  )
```

## Quantitative Annotations

Linearity annotations use superscript notation:

```
-- Linear: must use exactly once
consume : Buffer^1 -> Result^1

-- Erased: compile-time only, no runtime cost
typeCheck : Type^0 -> Bool

-- Unrestricted (default): use any number of times
lookup : Key -> Map -> Value
```

## Records and Named Fields

For complex products, Once supports named fields:

```
type Person = { name : String, age : Int }

-- Access fields
getName : Person -> String
getName = .name

-- Construct
makePerson : String -> Int -> Person
makePerson n a = { name = n, age = a }
```

This desugars to products and projections.

## Summary

| Element | Syntax | Example |
|---------|--------|---------|
| Function type | `->` | `A -> B` |
| Product | `*` | `A * B` |
| Sum | `+` | `A + B` |
| Composition | `.` or `compose` | `f . g` |
| Pipeline | `\|>` | `x \|> f` |
| Application | juxtaposition | `f x` |
| Linear | `^1` | `Buffer^1` |
| Erased | `^0` | `Type^0` |

Once's syntax aims for clarity and mathematical precision. Every syntactic construct has a direct categorical interpretation, making programs easier to reason about formally.
