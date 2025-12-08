# Transformation: The Write-Once Principle

## The Problem

Today, the same logic gets reimplemented in every language:

```
JSON parsers:     C, Rust, Go, Python, JavaScript, Java, Haskell, ...
HTTP clients:     C, Rust, Go, Python, JavaScript, Java, Haskell, ...
Compression:      C, Rust, Go, Python, JavaScript, Java, Haskell, ...
Cryptography:     C, Rust, Go, Python, JavaScript, Java, Haskell, ...
```

Each implementation:
- Duplicates effort
- Introduces bugs independently
- Has different edge cases
- Needs separate maintenance

This is wasteful. The **logic** is the same - only the **substrate** differs.

## The Solution: Natural Transformations

Natural transformations are **substrate-independent**. They describe pure structure:

- Morphisms (functions)
- Composition
- Products and coproducts
- No mention of memory, GC, calling conventions

This structure can be **interpreted** in any language because every language has:
- Functions
- A way to call functions in sequence
- A way to handle pairs/records
- A way to handle variants/unions

## The Write-Once Principle

**Write the logic once in Once. Compile to any target.**

```
                    Once (Derived)
                    JSON Parser
                          │
        ┌─────────┬───────┼───────┬─────────┐
        ▼         ▼       ▼       ▼         ▼
       C        Rust     JS    Haskell    WASM
    (native)  (native) (node)  (GHC)    (browser)
```

The JSON parser is written once. The **same logic** runs everywhere.

## How It Works

### Step 1: Write Pure Logic

```
-- json.once (in Derived layer)

data Json
  = JsonNull
  | JsonBool Bool
  | JsonNumber Number
  | JsonString String
  | JsonArray (List Json)
  | JsonObject (List (String * Json))

parseJson : String -> Json + ParseError
parseJson = ... composition of generators ...
```

### Step 2: Compile to Categorical IR

The Once compiler produces a categorical intermediate representation:

```
parseJson =
  Compose
    (Case handleObject handleArray handlePrimitive)
    (Compose skipWhitespace peekChar)
```

This IR is just generators and their compositions - pure structure.

### Step 3: Generate Target Code

Each backend interprets the generators:

**C Backend**
```c
JsonResult parse_json(const char* input, size_t len) {
    // Generators become C constructs
    // compose -> function calls
    // case -> switch/if
    // pair -> struct
    // fst/snd -> field access
}
```

**Rust Backend**
```rust
fn parse_json(input: &str) -> Result<Json, ParseError> {
    // compose -> function calls
    // case -> match
    // pair -> tuple
    // inl/inr -> Ok/Err
}
```

**JavaScript Backend**
```javascript
function parseJson(input) {
    // compose -> function calls
    // case -> if/switch
    // pair -> array/object
    // inl/inr -> tagged objects
}
```

**Haskell Backend**
```haskell
parseJson :: String -> Either ParseError Json
parseJson = -- direct translation, very close to source
```

## Generator Interpretation Table

Each generator has a translation for each target:

| Generator | C | Rust | JavaScript | Haskell |
|-----------|---|------|------------|---------|
| `id` | `x` | `x` | `x` | `id` |
| `compose f g` | `f(g(x))` | `f(g(x))` | `f(g(x))` | `f . g` |
| `fst` | `x.fst` | `x.0` | `x[0]` | `fst` |
| `snd` | `x.snd` | `x.1` | `x[1]` | `snd` |
| `pair f g` | `{f(x), g(x)}` | `(f(x), g(x))` | `[f(x), g(x)]` | `(,) <$> f <*> g` |
| `inl` | `{.tag=0, .val=x}` | `Left(x)` | `{tag: 'l', val: x}` | `Left` |
| `inr` | `{.tag=1, .val=x}` | `Right(x)` | `{tag: 'r', val: x}` | `Right` |
| `case f g` | `if(x.tag) g(x.val) else f(x.val)` | `match x {...}` | `x.tag === 'l' ? f(x.val) : g(x.val)` | `either f g` |
| `curry f` | `λy. f(x,y)` (closure) | `move \|y\| f(x,y)` | `y => f(x,y)` | `curry f` |
| `apply` | `f(x)` | `f(x)` | `f(x)` | `uncurry ($)` |

## Why This Works

### Mathematical Foundation

Natural transformations satisfy **equational laws**:

```
compose f id = f                    -- right identity
compose id f = f                    -- left identity
compose f (compose g h) = compose (compose f g) h  -- associativity
```

These laws hold in **every language**. So transformations preserve meaning.

### Substrate Independence

The generators describe **what** to compute, not **how**:

- `compose f g` means "do g then f" - every language can do this
- `pair f g` means "compute both" - every language can do this
- `case f g` means "branch" - every language can do this

The **how** (memory layout, calling convention, GC) is the backend's job.

## Compilation Targets

### Native Targets

| Target | Output | Use Case |
|--------|--------|----------|
| C | `.c` + `.h` | Maximum portability, embed anywhere |
| Rust | `.rs` | Memory safety, modern systems |
| LLVM IR | `.ll` | Direct compilation, optimization |
| x86_64 | `.o` / `.so` | Bare metal, max performance |
| ARM | `.o` / `.so` | Embedded, mobile |

### Managed Targets

| Target | Output | Use Case |
|--------|--------|----------|
| JavaScript | `.js` | Browser, Node.js |
| WebAssembly | `.wasm` | Browser, portable binary |
| JVM bytecode | `.class` | Java ecosystem |
| CLR | `.dll` | .NET ecosystem |

### Functional Targets

| Target | Output | Use Case |
|--------|--------|----------|
| Haskell | `.hs` | GHC ecosystem |
| OCaml | `.ml` | ML ecosystem |
| Agda/Coq | proof terms | Verification |

## Example: One Parser, Many Languages

### Once Source

```
-- parser.once

digit : Parser Char
digit = satisfy isDigit

number : Parser Int
number = fmap digitsToInt (many1 digit)

identifier : Parser String
identifier = fmap toString (pair letter (many alphaNum))
```

### Generated C

```c
ParseResult_Char digit(const char* input, size_t pos) {
    if (pos < strlen(input) && isdigit(input[pos])) {
        return (ParseResult_Char){.ok = true, .value = input[pos], .pos = pos + 1};
    }
    return (ParseResult_Char){.ok = false, .pos = pos};
}

ParseResult_Int number(const char* input, size_t pos) {
    // generated from fmap digitsToInt (many1 digit)
}
```

### Generated Rust

```rust
fn digit(input: &str, pos: usize) -> ParseResult<char> {
    input.chars().nth(pos)
        .filter(|c| c.is_digit(10))
        .map(|c| (c, pos + 1))
        .ok_or(ParseError::Expected("digit"))
}

fn number(input: &str, pos: usize) -> ParseResult<i64> {
    // generated from fmap digitsToInt (many1 digit)
}
```

### Generated JavaScript

```javascript
function digit(input, pos) {
    const c = input[pos];
    if (c && /\d/.test(c)) {
        return { ok: true, value: c, pos: pos + 1 };
    }
    return { ok: false, error: 'expected digit', pos };
}

function number(input, pos) {
    // generated from fmap digitsToInt (many1 digit)
}
```

## Interpretations and Portability

The **Derived** layer (pure) transforms to any target.

The **Interpretations** layer ties to specific platforms:

```
-- This transforms to anything
parseJson : String -> Json + Error     ✓ C, Rust, JS, WASM, ...

-- This only works where POSIX exists
readFile : Path -> External String     ✓ C (POSIX), Rust (std)
                                       ✗ Bare metal, browser

-- This only works in browser
fetch : Url -> External Response       ✓ JavaScript, WASM
                                       ✗ C, Rust (without deps)
```

## Optimization Across Targets

Because the categorical structure is known, the compiler can optimize:

### Fusion

```
-- Before: two traversals
map f (map g xs)

-- After: one traversal (functor law)
map (compose f g) xs
```

### Deforestation

```
-- Before: intermediate list
sum (map f xs)

-- After: no intermediate structure
foldl (compose (+) f) 0 xs
```

### Target-Specific Optimization

The backend can further optimize for each target:

- **C**: inline small functions, use SIMD
- **Rust**: leverage ownership for zero-copy
- **JavaScript**: use typed arrays for numbers
- **WASM**: use linear memory efficiently

## The Value Proposition

| Traditional | Once |
|-------------|------|
| Write JSON parser in C | Write JSON parser once |
| Write JSON parser in Rust | Compile to C |
| Write JSON parser in JS | Compile to Rust |
| Write JSON parser in Python | Compile to JS |
| ... | Compile to Python |
| N implementations | 1 implementation |
| N × bugs | 1 × bugs |
| N × maintenance | 1 × maintenance |

## Summary

The write-once principle:

1. **Write pure logic in Once** (Derived layer)
2. **Logic is substrate-independent** (just generators + composition)
3. **Compile to any target** (each backend interprets generators)
4. **One source of truth** (maintain once, use everywhere)

Natural transformations make this possible because they describe **structure**, not **implementation**. The structure is universal - every language can express it.
