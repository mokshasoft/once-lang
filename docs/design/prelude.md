# The Prelude

## Overview

The Prelude is the set of definitions automatically available in Once programs. It provides:

1. **Generators** - The 12 primitive morphisms
2. **Canonical** - Standard morphisms from universal properties
3. **Initial** - Common data types as initial algebras

The Prelude is entirely pure - no IO operations are included by default.

## Generators

Always available, these are the foundation:

```
id       : A -> A
compose  : (B -> C) -> (A -> B) -> (A -> C)
fst      : A * B -> A
snd      : A * B -> B
pair     : (C -> A) -> (C -> B) -> (C -> A * B)
inl      : A -> A + B
inr      : B -> A + B
case     : (A -> C) -> (B -> C) -> (A + B -> C)
terminal : A -> Unit
initial  : Void -> A
curry    : (A * B -> C) -> (A -> (B -> C))
apply    : (A -> B) * A -> B
```

## Canonical Library

Morphisms derived from universal properties (see D021):

### Product Morphisms

```
swap : A * B -> B * A
swap = pair snd fst

diagonal : A -> A * A
diagonal = pair id id

assocL : A * (B * C) -> (A * B) * C
assocR : (A * B) * C -> A * (B * C)

first  : (A -> C) -> A * B -> C * B
second : (B -> C) -> A * B -> A * C
bimap  : (A -> C) -> (B -> D) -> A * B -> C * D
```

### Coproduct Morphisms

```
mirror : A + B -> B + A
mirror = case inr inl

mapLeft  : (A -> C) -> A + B -> C + B
mapRight : (B -> C) -> A + B -> A + C
```

### Function Morphisms

```
const : A -> B -> A
const a _ = a

flip : (A -> B -> C) -> B -> A -> C
flip f b a = f a b

(.) : (B -> C) -> (A -> B) -> A -> C
(.) = compose

(|>) : A -> (A -> B) -> B
x |> f = f x
```

## Initial Library

Standard data types as initial algebras (see D024):

### Bool

```
type Bool = Unit + Unit

true  : Bool
false : Bool

not : Bool -> Bool
and : Bool -> Bool -> Bool
or  : Bool -> Bool -> Bool
```

### Maybe

```
type Maybe A = Unit + A

nothing : Maybe A
just    : A -> Maybe A

maybe     : B -> (A -> B) -> Maybe A -> B
fromMaybe : A -> Maybe A -> A
isJust    : Maybe A -> Bool
isNothing : Maybe A -> Bool
```

### Result

Success-left convention (see D025):

```
type Result A E = A + E

ok  : A -> Result A E
ok = inl

err : E -> Result A E
err = inr

mapResult  : (A -> B) -> Result A E -> Result B E
bindResult : (A -> Result B E) -> Result A E -> Result B E
handle     : (A -> C) -> (E -> C) -> Result A E -> C
isOk       : Result A E -> Bool
isErr      : Result A E -> Bool
```

### List

```
type List A = Unit + (A * List A)

nil  : List A
cons : A -> List A -> List A

foldr  : (A -> B -> B) -> B -> List A -> B
foldl  : (B -> A -> B) -> B -> List A -> B
map    : (A -> B) -> List A -> List B
filter : (A -> Bool) -> List A -> List A
length : List A -> Int
append : List A -> List A -> List A
concat : List (List A) -> List A
```

## Structure

```
Prelude
├── Generators
│   └── id, compose, fst, snd, pair, inl, inr, case,
│       terminal, initial, curry, apply
│
├── Canonical
│   ├── Products: swap, diagonal, assocL, assocR, first, second, bimap
│   ├── Coproducts: mirror, mapLeft, mapRight
│   └── Functions: const, flip, (.), (|>)
│
└── Initial
    ├── Bool: true, false, not, and, or
    ├── Maybe: nothing, just, maybe, fromMaybe, ...
    ├── Result: ok, err, mapResult, bindResult, handle, ...
    └── List: nil, cons, foldr, map, filter, ...
```

## What's Not Included

The Prelude is minimal. These require explicit imports:

| Category | Not Included | Import From |
|----------|--------------|-------------|
| IO | File, network, console | Interpretations |
| Parsing | Parser combinators | Derived.Parser |
| JSON | Encoding/decoding | Derived.Json |
| Crypto | Hashing, encryption | Derived.Crypto |

### Example: Using IO

```
import Interpretations.Linux

main : Unit -> IO Unit
main _ = putLine "Hello"
```

### Example: Using JSON

```
import Derived.Json

parseConfig : String -> Result Config Error
parseConfig = ...
```

## Design Principles

### Pure by Default

No IO in the Prelude. Effects require explicit imports, making dependencies visible in the import list.

### Minimal

Only fundamental operations. Domain-specific functionality (JSON, parsing, crypto) lives in separate modules.

### Derivable

Everything in the Prelude (except generators) can be written using generators. No compiler magic.

### Standard Names

Following categorical conventions:
- `compose` for composition
- `fst`, `snd` for projections
- `inl`, `inr` for injections
- `case` for case analysis

## Related Decisions

- D021: Canonical as standard derived library
- D024: Initial as standard data type library
- D025: Result type convention (success-left)
