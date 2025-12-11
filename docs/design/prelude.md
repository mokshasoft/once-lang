# Prelude Structure in Once

## What is the Prelude?

The Prelude is the set of definitions available by default in Once programs. It consists of:

1. **Generators** - Always available, the foundation
2. **Canonical** - Morphisms from universal properties (see D021)
3. **Initial** - Standard data types as initial algebras (see D024)

The Prelude is entirely **pure** - no Interpretations are imported by default.

## Generators (Always Available)

These are the primitive morphisms:

```
-- Category
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

-- Terminal and Initial
terminal : A -> Unit
initial  : Void -> A

-- Closed
curry   : (A * B -> C) -> (A -> (B -> C))
apply   : (A -> B) * A -> B

-- Functors
fmap : (A -> B) -> F A -> F B
```

## Core Derived (Prelude)

### Basic Combinators

```
-- Identity (alias)
identity : A -> A
identity = id

-- Flip arguments
flip : (A -> B -> C) -> (B -> A -> C)
flip f b a = f a b

-- Constant function
constant : A -> B -> A
constant a _ = a

-- Swap pair
swap : A * B -> B * A
swap = pair snd fst

-- Diagonal (copy)
diagonal : A -> A * A
diagonal = pair id id

-- Composition operator
(.) : (B -> C) -> (A -> B) -> (A -> C)
(.) = compose

-- Flip composition (pipeline)
(|>) : A -> (A -> B) -> B
(|>) x f = f x

-- Application operator
($) : (A -> B) -> A -> B
($) f x = f x
```

### Boolean

```
data Bool = False | True

not : Bool -> Bool
not = case (constant True) (constant False)

and : Bool -> Bool -> Bool
and a b = case (constant False) (constant b) a

or : Bool -> Bool -> Bool
or a b = case (constant b) (constant True) a

if : Bool -> A -> A -> A
if cond then else = case (constant else) (constant then) cond
```

### Maybe

```
data Maybe A = Nothing | Just A

maybe : B -> (A -> B) -> Maybe A -> B
maybe default f = case (constant default) f

isNothing : Maybe A -> Bool
isNothing = case (constant True) (constant False)

isJust : Maybe A -> Bool
isJust = case (constant False) (constant True)

fromMaybe : A -> Maybe A -> A
fromMaybe default = maybe default id

mapMaybe : (A -> B) -> Maybe A -> Maybe B
mapMaybe f = case (constant Nothing) (compose Just f)
```

### Result

Once uses `Result` instead of `Either` for error handling, with a **success-left** convention (see D025):

```
type Result A E = A + E

ok : A -> Result A E
ok = inl

err : E -> Result A E
err = inr

-- Combinators
mapResult : (A -> B) -> Result A E -> Result B E
mapResult f = case (ok . f) err

bindResult : (A -> Result B E) -> Result A E -> Result B E
bindResult f = case f err

isOk : Result A E -> Bool
isOk = case (constant True) (constant False)

isErr : Result A E -> Bool
isErr = case (constant False) (constant True)

fromResult : A -> Result A E -> A
fromResult default = case id (constant default)
```

Note: Success is on the **left** (`inl`), error is on the **right** (`inr`). This differs from Haskell's `Either` convention.

### List

```
data List A = Nil | Cons A (List A)

-- Basic operations
null : List A -> Bool
null = case (constant True) (constant False)

head : List A -> Maybe A
head = case (constant Nothing) (compose Just fst)

tail : List A -> Maybe (List A)
tail = case (constant Nothing) (compose Just snd)

-- Fold
foldr : (A -> B -> B) -> B -> List A -> B
foldr f z = case (constant z) (\(a, as) -> f a (foldr f z as))

foldl : (B -> A -> B) -> B -> List A -> B
foldl f z = case (constant z) (\(a, as) -> foldl f (f z a) as)

-- Map
map : (A -> B) -> List A -> List B
map f = foldr (\a bs -> Cons (f a) bs) Nil

-- Filter
filter : (A -> Bool) -> List A -> List A
filter p = foldr (\a as -> if (p a) (Cons a as) as) Nil

-- Length
length : List A -> Int
length = foldr (\_ n -> n + 1) 0

-- Concatenation
append : List A -> List A -> List A
append xs ys = foldr Cons ys xs

concat : List (List A) -> List A
concat = foldr append Nil

-- Reverse
reverse : List A -> List A
reverse = foldl (flip Cons) Nil
```

### Tuple Operations

```
-- Pairs (2-tuples)
first : (A -> C) -> A * B -> C * B
first f = pair (compose f fst) snd

second : (B -> C) -> A * B -> A * C
second f = pair fst (compose f snd)

both : (A -> B) -> A * A -> B * B
both f = pair (compose f fst) (compose f snd)

-- Currying
uncurry : (A -> B -> C) -> A * B -> C
uncurry f (a, b) = f a b
```

### Function Combinators

```
-- Apply twice
twice : (A -> A) -> A -> A
twice f = compose f f

-- Apply n times
iterate : Int -> (A -> A) -> A -> A
iterate 0 _ x = x
iterate n f x = iterate (n - 1) f (f x)

-- Fixed point (for recursion)
fix : ((A -> B) -> A -> B) -> A -> B
fix f = f (fix f)

-- On combinator
on : (B -> B -> C) -> (A -> B) -> A -> A -> C
on op f x y = op (f x) (f y)
```

### Comparison

```
data Ordering = LT | EQ | GT

compare : Ord A => A -> A -> Ordering

(==) : Eq A => A -> A -> Bool
(/=) : Eq A => A -> A -> Bool

(<)  : Ord A => A -> A -> Bool
(<=) : Ord A => A -> A -> Bool
(>)  : Ord A => A -> A -> Bool
(>=) : Ord A => A -> A -> Bool

min : Ord A => A -> A -> A
max : Ord A => A -> A -> A
```

### Numeric

```
-- Basic arithmetic (for types with Num)
(+) : Num A => A -> A -> A
(-) : Num A => A -> A -> A
(*) : Num A => A -> A -> A
(/) : Fractional A => A -> A -> A

negate : Num A => A -> A
abs    : Num A => A -> A

-- Integer operations
div : Int -> Int -> Int
mod : Int -> Int -> Int

-- Common functions
sum     : Num A => List A -> A
product : Num A => List A -> A
```

## Prelude Structure Summary

```
Prelude
├── Generators (primitive)
│   ├── id, compose
│   ├── fst, snd, pair
│   ├── inl, inr, case
│   ├── terminal, initial
│   ├── curry, apply
│   └── fmap
│
├── Canonical (morphisms from universal properties)
│   ├── Product: swap, diagonal, first, second, bimap, assocL, assocR
│   ├── Coproduct: mirror, mapLeft, mapRight
│   ├── Function: flip, const, (.), (|>), (&)
│   └── Morphism: id, compose (re-exports)
│
└── Initial (data types as initial algebras)
    ├── Bool (True, False, not, and, or, if)
    ├── Maybe (Nothing, Just, maybe, fromMaybe, ...)
    ├── Result (ok, err, mapResult, bindResult, ...) -- success-left convention
    └── List (Nil, Cons, foldr, map, filter, ...)
```

See also:
- [D021](../compiler/decision-log.md#d021-canonical-as-the-standard-derived-library) - Canonical library
- [D024](../compiler/decision-log.md#d024-initial-as-the-standard-data-type-library) - Initial library
- [D025](../compiler/decision-log.md#d025-result-type-convention-success-left) - Result convention

## What's NOT in the Prelude

The Prelude is minimal by design. These are **not** included by default:

| Not in Prelude | Why | How to Get |
|----------------|-----|------------|
| IO operations | Impure | `import Interpretations.POSIX` |
| File handling | Impure | `import Interpretations.POSIX` |
| Network | Impure | `import Interpretations.Network` |
| Concurrency | Platform-specific | `import Interpretations.Threads` |
| JSON | Domain-specific | `import Derived.Data.Json` |
| Parsing | Domain-specific | `import Derived.Text.Parser` |
| Cryptography | Domain-specific | `import Derived.Crypto` |

## Import Examples

### Minimal (Just Prelude)

```
-- Uses only Prelude
-- This is the default

myFunction : List Int -> Int
myFunction = sum . filter (> 0)
```

### With Additional Derived

```
import Derived.Data.Json
import Derived.Text.Parser

parseConfig : String -> Config + Error
parseConfig = ...
```

### With Interpretations

```
import Derived.Data.Json
import Interpretations.POSIX

loadConfig : Path -> External (Config + Error)
loadConfig path = fmap parseConfig (readFile path)
```

## Design Principles

### 1. Pure by Default

The Prelude contains no IO. To do IO, you must explicitly import an Interpretation.

### 2. Minimal but Complete

The Prelude has what you need for basic programming. Domain-specific functionality is in separate modules.

### 3. Consistent Naming

Following category theory conventions:
- `fmap` not `map` for functor mapping (though `map` exists for lists)
- `compose` and `.` for composition
- `fst`, `snd` for projections
- `inl`, `inr` for injections

### 4. No Magic

Everything in the Prelude is either:
- A Generator (primitive)
- Derivable from Generators (you could write it yourself)

There are no special compiler features only available to Prelude code.

## Summary

| Aspect | Prelude Content |
|--------|-----------------|
| **Generators** | The ~12 primitives |
| **Canonical** | Morphisms: swap, diagonal, flip, const, (.), (\|>) |
| **Initial** | Types: Bool, Maybe, Result, List, Ordering |
| **Not included** | IO, parsing, JSON, networking |

The Prelude is the **pure foundation**. Everything else is explicitly imported.
