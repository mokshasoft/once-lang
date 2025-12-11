# Library Structure in Once

## The Three Layers

Once organizes code into three distinct layers:

```
┌─────────────────────────────────────────────────────┐
│              Interpretations                        │
│   Impure: OS, hardware, network, external world     │
├─────────────────────────────────────────────────────┤
│              Derived                                │
│   Pure: everything built from Generators            │
├─────────────────────────────────────────────────────┤
│              Generators                             │
│   Primitive morphisms (the ~12 combinators)         │
└─────────────────────────────────────────────────────┘
```

The key distinction: **Generators and Derived are pure. Interpretations are impure.**

## Layer 1: Generators

The **Generators** are the primitive morphisms from which everything else is built.

### The Complete Set

```
-- Category structure
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

-- Closed structure
curry   : (A * B -> C) -> (A -> (B -> C))
apply   : (A -> B) * A -> B
```

### For Functors and Natural Transformations

```
-- Functor mapping (for each functor F)
fmap : (A -> B) -> F A -> F B

-- Natural transformation component (for each nat trans α : F => G)
component : F A -> G A
```

### Properties

- **Universal**: Every pure Once program reduces to these
- **Minimal**: None can be derived from the others
- **Mathematical**: Standard from category theory

## Layer 2: Derived

The **Derived** layer contains everything pure built from Generators. This includes both basic constructions and complex domain libraries.

### Basic Constructions

```
-- Swap product components
swap : A * B -> B * A
swap = pair snd fst

-- Diagonal (copy)
diagonal : A -> A * A
diagonal = pair id id

-- Constant function
constant : A -> B -> A
constant a = curry fst

-- Function composition
(.) : (B -> C) -> (A -> B) -> (A -> C)
(.) = compose
```

### Standard Functors

```
-- Maybe
data Maybe A = Nothing | Just A

fmap : (A -> B) -> Maybe A -> Maybe B
fmap f = case (constant Nothing) (compose Just f)

-- List
data List A = Nil | Cons A (List A)

fmap : (A -> B) -> List A -> List B
fmap f = foldr (compose Cons (pair f id)) Nil

-- Result (success-left convention, see D025)
type Result A E = A + E

ok : A -> Result A E
ok = inl

err : E -> Result A E
err = inr

mapResult : (A -> B) -> Result A E -> Result B E
mapResult f = case (ok . f) err
```

### Recursion Schemes

```
-- Catamorphism (fold)
cata : (F A -> A) -> Fix F -> A

-- Anamorphism (unfold)
ana : (A -> F A) -> A -> Fix F

-- Hylomorphism
hylo : (F B -> B) -> (A -> F A) -> A -> B
```

### Common Patterns

```
-- Fold
foldr : (A -> B -> B) -> B -> List A -> B

-- Map
map : (A -> B) -> List A -> List B

-- Filter
filter : (A -> Bool) -> List A -> List A

-- Iterate
iterate : (A -> A) -> A -> Stream A
```

### Domain Libraries (All Pure)

These are all in Derived because they're pure - built entirely from Generators:

**Parsing**
```
-- Parser combinators
type Parser A = String -> (A * String) + ParseError

char     : Char -> Parser Char
many     : Parser A -> Parser (List A)
choice   : List (Parser A) -> Parser A
sequence : List (Parser A) -> Parser (List A)
```

**JSON**
```
data Json
  = JsonNull
  | JsonBool Bool
  | JsonNumber Number
  | JsonString String
  | JsonArray (List Json)
  | JsonObject (List (String * Json))

parseJson  : String -> Json + ParseError
renderJson : Json -> String
```

**Compression**
```
compress   : Bytes -> Bytes
decompress : Bytes -> Bytes + Error
```

**Cryptography**
```
sha256 : Bytes -> Hash
hmac   : Key -> Bytes -> Mac
```

**Data Structures**
```
-- Trees
data Tree A = Leaf A | Branch (Tree A) (Tree A)

-- Maps (balanced trees)
data Map K V = ...

insert : K -> V -> Map K V -> Map K V
lookup : K -> Map K V -> Maybe V

-- Sets
data Set A = ...

member : A -> Set A -> Bool
union  : Set A -> Set A -> Set A
```

**Mathematics**
```
-- Vectors
dot      : Vec N -> Vec N -> Number
cross    : Vec 3 -> Vec 3 -> Vec 3
normalize : Vec N -> Vec N

-- Matrices
multiply : Mat M N -> Mat N P -> Mat M P
inverse  : Mat N N -> Maybe (Mat N N)
```

All of these are **pure** - no IO, no external dependencies, portable to any target.

## Layer 3: Interpretations

The **Interpretations** layer provides primitives for the external world. This is the **only** impure layer.

### POSIX Interpretation

```
primitive open  : Path * Flags -> IO (Fd + Errno)
primitive read  : Fd * Size -> IO (Bytes + Errno)
primitive write : Fd * Bytes -> IO (Size + Errno)
primitive close : Fd -> IO (Unit + Errno)

primitive socket  : Domain * Type -> IO (Socket + Errno)
primitive connect : Socket * Address -> IO (Unit + Errno)
primitive send    : Socket * Bytes -> IO (Size + Errno)
primitive recv    : Socket * Size -> IO (Bytes + Errno)
```

### Bare Metal Interpretation

```
primitive gpio_read  : Pin -> IO Level
primitive gpio_write : Pin * Level -> IO Unit

primitive i2c_read  : Bus * Address * Size -> IO Bytes
primitive i2c_write : Bus * Address * Bytes -> IO Unit

primitive mmio_read  : Address -> IO Word
primitive mmio_write : Address * Word -> IO Unit
```

### WebAssembly Interpretation

```
primitive console_log : String -> IO Unit
primitive fetch       : Url * Options -> IO (Response + Error)
primitive set_timeout : Milliseconds * Handler -> IO TimerId
```

### Interpretation Libraries

Libraries in Interpretations use primitives + Derived:

```
-- File utilities (uses POSIX primitives + Derived)
readFile  : Path -> IO (String + Error)
writeFile : Path * String -> IO (Unit + Error)

-- HTTP client (uses socket primitives + Derived JSON parser)
httpGet   : Url -> IO (Response + Error)
httpPost  : Url * Json -> IO (Response + Error)

-- JSON file operations (combines Derived JSON with file IO)
readJsonFile : Path -> IO (Result Json Error)
readJsonFile path =
  case (err, \str -> parseJson str) (readFile path)  -- parseJson is from Derived
```

## The Pure/Impure Boundary

```
┌─────────────────────────────────────────────────────────────┐
│                                                             │
│   Derived (Pure)                                            │
│                                                             │
│   ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐       │
│   │  JSON   │  │ Crypto  │  │ Parser  │  │  Math   │       │
│   │ Parser  │  │         │  │ Combos  │  │         │       │
│   └─────────┘  └─────────┘  └─────────┘  └─────────┘       │
│         │            │            │            │            │
│         └────────────┴─────┬──────┴────────────┘            │
│                            │                                │
├────────────────────────────┼────────────────────────────────┤
│                            │                                │
│   Interpretations (Impure) │                                │
│                            ▼                                │
│   ┌─────────────────────────────────────────────┐          │
│   │  readJsonFile = fmap parseJson readFile     │          │
│   └─────────────────────────────────────────────┘          │
│                            │                                │
│                            ▼                                │
│   ┌─────────────────────────────────────────────┐          │
│   │  primitive readFile, writeFile, socket...   │          │
│   └─────────────────────────────────────────────┘          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

## Portability

| Layer | Portable? | Compile Target |
|-------|-----------|----------------|
| Generators | Yes | Any |
| Derived | Yes | Any |
| Interpretations | No | Specific platform |

Code that uses only Generators and Derived can be compiled to **any target**: C, Rust, JavaScript, WASM, bare metal, anything.

Code that uses Interpretations is tied to that platform's primitives.

## Summary

| Layer | Purity | Contains | Examples |
|-------|--------|----------|----------|
| **Generators** | Pure | ~12 primitive morphisms | `id`, `compose`, `fst`, `curry` |
| **Derived** | Pure | Everything built from Generators | `map`, `fold`, JSON, crypto, parsers |
| **Interpretations** | Impure | IO primitives for external world | File IO, network, GPIO, syscalls |

The rule is simple: **if it doesn't touch the external world, it's Derived. If it does, it's Interpretations.**
