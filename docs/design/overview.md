# Once Language

## Executive Summary

**Once** is a programming language founded on **natural transformations** from category theory. The core principle is simple: write logic once, compile to any target.

| Question | Answer |
|----------|--------|
| **What** | A language where programs are natural transformations |
| **Why** | Write once, run anywhere - no reimplementing logic per language |
| **How** | Categorical combinators as a universal computational substrate |

Natural transformations are **substrate-independent**. They describe pure structure - composition, products, sums - without mentioning memory, garbage collection, or calling conventions. This structure exists in every programming language, so Once programs compile to any target: C, Rust, JavaScript, WebAssembly, Haskell, bare metal.

## Core Principles

### 1. Natural Transformations as Foundation

Everything in Once is a morphism (function between types) or a natural transformation (structure-preserving map between functors). There are no special constructs for effects, IO, or control flow - these emerge from the categorical structure.

### 2. Three Layers

```
┌─────────────────────────────────────────────────────┐
│              Interpretations                        │
│   Impure: OS, hardware, network, external world     │
├─────────────────────────────────────────────────────┤
│              Derived                                │
│   Pure: everything built from Generators            │
├─────────────────────────────────────────────────────┤
│              Generators                             │
│   Primitive morphisms (~12 combinators)             │
└─────────────────────────────────────────────────────┘
```

- **Generators**: The minimal set of primitive morphisms
- **Derived**: All pure code (JSON parsers, crypto, data structures, algorithms)
- **Interpretations**: Platform bindings (POSIX, bare metal, WASM)

### 3. Pure/Impure Boundary

Only Interpretations touch the external world. Everything in Generators and Derived is pure, portable, and formally verifiable.

### 4. Substrate Independence

Code in Derived compiles to **any target**. A JSON parser written in Once generates correct C, Rust, JavaScript, or Haskell - from the same source.

### 5. Types are Inherent

Morphisms have types: `f : A -> B`. Type annotations are optional in syntax, but types exist - they're part of the mathematical structure.

## Key Properties

| Property | Description |
|----------|-------------|
| **No GC required** | Linear code (quantity 1) needs no garbage collection |
| **Quantitative types** | Track resource usage: 0 (erased), 1 (linear), ω (unrestricted) |
| **Formal verification** | Graded categorical laws are the spec; proofs are tractable |
| **Linearity inferred** | Compiler analyzes quantities; annotations optional |
| **FFI both directions** | Call out to C; expose Once functions to other languages |
| **Bare metal ready** | No runtime, no OS required |

## The Generators

These 12 primitive morphisms generate all computation:

```
-- Category
id      : A -> A                                    -- identity
compose : (B -> C) -> (A -> B) -> (A -> C)          -- composition

-- Products
fst     : A * B -> A                                -- first projection
snd     : A * B -> B                                -- second projection
pair    : (C -> A) -> (C -> B) -> (C -> A * B)      -- pairing

-- Coproducts
inl     : A -> A + B                                -- left injection
inr     : B -> A + B                                -- right injection
case    : (A -> C) -> (B -> C) -> (A + B -> C)      -- case analysis

-- Terminal and Initial
terminal : A -> Unit                                -- discard
initial  : Void -> A                                -- absurd

-- Closed (first-class functions)
curry   : (A * B -> C) -> (A -> (B -> C))           -- currying
apply   : (A -> B) * A -> B                         -- application
```

Every Once program reduces to these. Every target language can implement these. This is why write-once works.

## Correctness and Formal Verification

Category theory provides **equational laws**:

```
compose f id = f                      -- right identity
compose id f = f                      -- left identity
compose f (compose g h) = compose (compose f g) h  -- associativity
fmap id = id                          -- functor identity
fmap (compose f g) = compose (fmap f) (fmap g)     -- functor composition
```

A compiler is correct if it preserves these equations. The laws are the specification.

**Why verification is tractable:**
- ~12 generators to verify (not an entire language)
- Each rewrite rule is a categorical law (proofs exist since the 1940s)
- Mathematical semantics (denotational, not operational)
- Quantitative types add graded structure (well-studied in QTT literature)

Estimated proof effort: ~5,000-8,000 lines of Coq (including QTT). Compare to CompCert (C compiler): ~100,000 lines.

## Document Map

### Quick Start
- [Quickstart](quickstart.md) - 5-minute introduction to Once

### Foundations
- [Design Philosophy](design-philosophy.md) - Why natural transformations
- [Categorical Foundations](categorical-foundations.md) - Alternative abstractions (optics, profunctors, arrows)
- [Glossary](glossary.md) - Reference for types and operations
- [Prelude](prelude.md) - Standard library structure

### Architecture
- [Libraries](libraries.md) - The three-layer structure
- [IO](io.md) - Effects as functor choice
- [FFI](ffi.md) - Foreign function interface
- [Memory](memory.md) - Quantitative types, linearity, and resource management

### Compilation
- [Transformation](transformation.md) - Write-once, compile anywhere
- [Compiler](compiler.md) - Compiler architecture
- [Formal Verification](formal-verification.md) - Proving correctness

### Targets
- [Bare Metal](bare-metal.md) - No OS, no runtime
- [Unikernels](unikernels.md) - Minimal secure images

### Advanced
- [Parallelism](parallelism.md) - Products and Day convolution
- [Time](time.md) - Streams and coalgebraic time
- [Syntax](syntax-exploration.md) - Language syntax design

## Relationship to Ya

**Ya** is a Haskell library that implements Once principles as an embedded domain-specific language. It demonstrates that natural transformations work in practice.

Examples from Ya/Haskell may appear in documentation to illustrate concepts. Ya uses a positional encoding system for type names (like `T'I'II`); Once uses standard category theory names.

## Example

A JSON parser in Once (Derived layer):

```
-- Pure, no IO, portable to any target

data Json
  = JsonNull
  | JsonBool Bool
  | JsonNumber Number
  | JsonString String
  | JsonArray (List Json)
  | JsonObject (List (String * Json))

parseJson : String -> Json + ParseError
parseJson = compose validate (compose structure tokenize)
```

This compiles to:
- C: `JsonResult parse_json(const char* input, size_t len)`
- Rust: `fn parse_json(input: &str) -> Result<Json, ParseError>`
- JavaScript: `function parseJson(input) { ... }`
- Haskell: `parseJson :: String -> Either ParseError Json`

One source. Every target. That's Once.
