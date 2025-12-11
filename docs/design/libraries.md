# Code Organization in Once

## The Three Strata

Once organizes all code into three distinct layers based on purity and portability:

```
┌─────────────────────────────────────┐
│         Interpretations             │  Platform-specific IO
├─────────────────────────────────────┤
│            Derived                  │  Pure library code
├─────────────────────────────────────┤
│           Generators                │  The 12 primitives
└─────────────────────────────────────┘
```

This separation is fundamental to Once's "write once, compile anywhere" goal.

## Generators: The Foundation

The bottom stratum contains the ~12 categorical primitives that form Once's foundation:

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

These are not implemented in Once - they're the building blocks from which everything else is constructed. Every target language provides its own implementation of these operations.

## Derived: Pure Libraries

The middle stratum contains all pure code built from generators. This is where most Once code lives.

### Canonical Library

Standard morphisms derived from universal properties:

```
swap     : A * B -> B * A
diagonal : A -> A * A
assoc    : (A * B) * C -> A * (B * C)
distrib  : A * (B + C) -> (A * B) + (A * C)
```

See [Prelude](prelude.md) for the full Canonical library.

### Initial Library

Standard data types as initial algebras:

```
type Bool   = Unit + Unit
type Maybe A = Unit + A
type List A  = Unit + (A * List A)
type Result A E = A + E
```

With their standard operations:

```
-- Maybe
nothing : Maybe A
just    : A -> Maybe A
maybe   : B -> (A -> B) -> Maybe A -> B

-- List
nil    : List A
cons   : A -> List A -> List A
foldr  : (A -> B -> B) -> B -> List A -> B

-- Result (success-left convention)
ok     : A -> Result A E
err    : E -> Result A E
handle : (A -> C) -> (E -> C) -> Result A E -> C
```

### Domain Libraries

Complex functionality built entirely from generators:

**Text Processing**
```
parseJson : String -> Result Json ParseError
renderJson : Json -> String
```

**Algorithms**
```
sort   : (A -> A -> Bool) -> List A -> List A
search : (A -> Bool) -> List A -> Maybe A
```

**Data Structures**
```
insert : K -> V -> Map K V -> Map K V
lookup : K -> Map K V -> Maybe V
member : A -> Set A -> Bool
```

**Numeric**
```
add : Int -> Int -> Int
multiply : Int -> Int -> Int
```

All Derived code is:
- **Pure**: No side effects
- **Portable**: Compiles to any target
- **Verifiable**: Can be formally proven correct

## Interpretations: Platform Bindings

The top stratum contains platform-specific IO operations declared as primitives.

### Linux Interpretation

```
primitive open  : Path -> Flags -> IO (Handle + Error)
primitive read  : Handle -> Int -> IO (Bytes + Error)
primitive write : Handle -> Bytes -> IO (Unit + Error)
primitive close : Handle -> IO (Unit + Error)
```

### WASM/Browser Interpretation

```
primitive consoleLog : String -> IO Unit
primitive fetch      : Request -> IO (Response + Error)
primitive setTimeout : Int -> IO Unit -> IO Unit
```

### Bare Metal Interpretation

```
primitive gpioRead  : Pin -> IO Level
primitive gpioWrite : Pin -> Level -> IO Unit
primitive delay     : Microseconds -> IO Unit
```

### Using Interpretations

Interpretations combine primitives with Derived code:

```
-- Uses primitive + Derived JSON parser
readConfig : Path -> IO (Result Config Error)
readConfig path =
  bind (readFile path) (\text ->
    pure (parseJson text)
  )
```

## Portability Matrix

| Stratum | Portable | Target |
|---------|----------|--------|
| Generators | Yes | All |
| Derived | Yes | All |
| Interpretations | No | Specific platform |

### Maximizing Portability

Structure code to keep IO at the edges:

```
-- GOOD: Pure core, thin IO wrapper
processData : Data -> Result Report Error    -- Derived (portable)
main = bind (readInput) (pure . processData) -- Interpretation (platform-specific)

-- BAD: IO mixed throughout
processData : Path -> IO Report              -- Not portable
```

## File Organization

A typical Once project:

```
project/
  src/
    Core.once           -- Derived: pure logic
    Types.once          -- Derived: data definitions
    Main.once           -- Interpretations: IO entry point
  lib/
    Interpretations/
      Linux/            -- Linux primitives
      Browser/          -- Browser primitives
    Derived/
      Canonical/        -- morphisms from universal properties
      Initial/          -- data types as initial algebras
```

## Summary

| Stratum | Purity | Contents | Portability |
|---------|--------|----------|-------------|
| Generators | Pure | 12 primitives | Universal |
| Derived | Pure | All library code | Universal |
| Interpretations | Impure | IO primitives | Platform-specific |

The stratum system enforces a clean separation between portable pure code and platform-specific IO. Most code lives in Derived where it can be compiled to any target and formally verified.
