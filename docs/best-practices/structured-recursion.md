# Structured Recursion in Once: A Categorical Foundation

*For Haskellers who know `recursion-schemes` and want to understand why Once does it differently*

---

## Overview

If you've used `recursion-schemes` in Haskell, you know the power of `cata`, `ana`, `hylo`, and friends. Once takes these ideas seriously — not as a library pattern, but as the *only* way to write recursive code.

This document explains:
1. Why Once splits `Fix f` into `μ F` and `ν F`
2. How this split enables certain totality and productivity guarantees
3. The categorical foundations (initial algebras, final coalgebras)
4. Implementation details in the Once IR
5. Limitations and tradeoffs of this approach

**Prerequisites:** Familiarity with F-algebras, `Fix`, `cata`/`ana` from Haskell's `recursion-schemes` or similar.

**Caveat:** Once is a research language. The ideas are sound, but the implementation is evolving. This document describes the design intent; some features are not yet implemented.

---

## The Problem with `Fix`

### Haskell's Unified Fixed Point

In Haskell, we typically define:

```haskell
newtype Fix f = Fix { unFix :: f (Fix f) }

cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg = alg . fmap (cata alg) . unFix

ana :: Functor f => (a -> f a) -> a -> Fix f
ana coalg = Fix . fmap (ana coalg) . coalg
```

This is elegant but conflates two distinct concepts:

```haskell
-- These have the same type...
finiteList :: Fix (ListF Int)
finiteList = Fix (Cons 1 (Fix (Cons 2 (Fix Nil))))

infiniteList :: Fix (ListF Int)
infiniteList = ana (\n -> Cons n (n+1)) 0

-- ...but radically different behavior
sum :: Fix (ListF Int) -> Int
sum = cata $ \case Nil -> 0; Cons x acc -> x + acc

boom = sum infiniteList  -- ⊥
```

The type system permits `cata` on infinite structures. Termination is the programmer's responsibility.

### Once's Split: μ and ν

Once distinguishes:

| Once | Haskell analog | Semantics |
|------|----------------|-----------|
| `μ F` | `Fix f` (finite) | Least fixed point — initial algebra |
| `ν F` | `Fix f` (infinite) | Greatest fixed point — final coalgebra |

```once
-- These are DIFFERENT TYPES
List : Type → Type
List A = μ (K Unit ⊕ K A ⊗ Id)    -- Finite lists

Stream : Type → Type
Stream A = ν (K A ⊗ Id)           -- Infinite streams

CoList : Type → Type
CoList A = ν (K Unit ⊕ K A ⊗ Id)  -- Possibly-infinite lists
```

The key operations are type-restricted:

```once
Cata : (F A → A) → μ F → A        -- Only consumes μ
Ana  : (A → F A) → A → ν F        -- Only produces ν
```

Attempting `Cata` on a `ν`-type is a *type error*, not a runtime divergence.

---

## Categorical Foundations

### F-Algebras and F-Coalgebras

For a functor `F : C → C`:

- An **F-algebra** is a pair `(A, α : F A → A)`
- An **F-coalgebra** is a pair `(A, α : A → F A)`

F-algebras form a category where morphisms `(A, α) → (B, β)` are arrows `h : A → B` making this commute:

```
    F A ──α──→ A
     │         │
   F h         h
     ↓         ↓
    F B ──β──→ B
```

### Initial Algebras (μ)

An **initial F-algebra** `(μF, In)` has a unique morphism to every F-algebra:

```
    F(μF) ──In──→ μF
      │           │
    F(⟦α⟧)      ⟦α⟧    (unique!)
      ↓           ↓
     F A ───α───→ A
```

This unique morphism `⟦α⟧ : μF → A` is the **catamorphism** — what Once calls `Cata α`.

**Lambek's Lemma:** For an initial algebra `(μF, In)`, the map `In : F(μF) → μF` is an isomorphism.

This gives us the destructor `out-μ : μF → F(μF)`, enabling pattern matching:

```once
-- In the IR:
In    : F(μF) → μF      -- Constructor
out-μ : μF → F(μF)      -- Destructor (inverse of In)
```

### Final Coalgebras (ν)

Dually, a **final F-coalgebra** `(νF, Out)` has a unique morphism from every F-coalgebra:

```
     A ───α───→ F A
     │          │
   ⟦α⟧        F(⟦α⟧)    (unique!)
     ↓          ↓
    νF ──Out──→ F(νF)
```

This unique morphism `⟦α⟧ : A → νF` is the **anamorphism** — what Once calls `Ana α`.

Again by Lambek, `Out` is an isomorphism, giving us:

```once
Out  : νF → F(νF)       -- Destructor (observation)
in-ν : F(νF) → νF       -- Constructor (inverse of Out)
```

### Why the Split Matters

In classical domain theory (Haskell's semantics):
- `μF ≅ νF` for most functors (both are `Fix f`)
- This relies on partiality: ⊥ inhabits every type

In total languages (Once, Agda, Coq):
- `μF ≇ νF` in general
- `μF` contains only *finite* structures (well-founded)
- `νF` contains *possibly infinite* structures (productive)

The isomorphism `μF ≅ νF` holds only for functors where all inhabitants are finite (e.g., `F X = 1 + X` gives `μF ≅ νF ≅ ℕ`).

For `F X = A × X`:
- `μF ≅ 0` (no finite inhabitants — needs a base case!)
- `νF ≅ Stream A` (infinite streams)

---

## The Once IR Primitives

### Functor Representation

Once represents functors as polynomial functor codes:

```agda
data Functor : Set where
  K   : Type → Functor        -- Constant functor
  Id  : Functor               -- Identity functor
  _⊕_ : Functor → Functor → Functor  -- Coproduct
  _⊗_ : Functor → Functor → Functor  -- Product
```

These are strictly positive by construction — no `F X = X → X` disasters.

**Limitations of polynomial functors:**

This representation excludes some patterns:
- **Exponential functors:** `F X = A → X` (e.g., infinite branching trees)
- **Nested recursion:** `data Perfect a = Tip a | Branch (Perfect (a, a))`
- **GADTs:** Indexed type families
- **Higher-kinded recursion:** `Free f a`, `Cofree f a`

**Who needs these?**
| Pattern | Primary users |
|---------|---------------|
| HOAS, GADTs | PL researchers, typed DSL builders |
| Nested types | Specialized algorithm designers |
| Free monads | Effect system researchers |

**Practical assessment:** Polynomial functors cover lists, trees, options, results, streams — sufficient for application development, systems programming, and most domains.

**Note on extensibility:** The functor representation is orthogonal to the core design. Extending to richer functors (exponentials, indexed types, nested recursion) would expand *what* we can recurse over without changing *how* recursion schemes or effects work. The core design (Cata/Ana/Hylo, μ/ν split, Arrow-based effects) remains the same.

Type-level interpretation:

```agda
⟦_⟧T : Functor → Type → Type
⟦ K A ⟧T X = A
⟦ Id ⟧T X = X
⟦ F ⊕ G ⟧T X = ⟦ F ⟧T X + ⟦ G ⟧T X
⟦ F ⊗ G ⟧T X = ⟦ F ⟧T X * ⟦ G ⟧T X
```

### Recursive Type Formers

```agda
μ-type : Functor → Type    -- Least fixed point
ν-type : Functor → Type    -- Greatest fixed point
```

### IR Operations

The Once IR provides these primitives:

```agda
-- Initial algebra operations
In    : ∀ {F} → WellFormedF F → IR (⟦ F ⟧T (μ-type F)) (μ-type F)
out-μ : ∀ {F} → WellFormedF F → IR (μ-type F) (⟦ F ⟧T (μ-type F))
Cata  : ∀ {F A} → WellFormedF F → IR (⟦ F ⟧T A) A → IR (μ-type F) A

-- Final coalgebra operations
Out  : ∀ {F} → WellFormedF F → IR (ν-type F) (⟦ F ⟧T (ν-type F))
in-ν : ∀ {F} → WellFormedF F → IR (⟦ F ⟧T (ν-type F)) (ν-type F)
Ana  : ∀ {F A} → WellFormedF F → IR A (⟦ F ⟧T A) → IR A (ν-type F)

-- Fusion primitive
Hylo : ∀ {F A B} → WellFormedF F
     → IR (⟦ F ⟧T B) B → IR A (⟦ F ⟧T A) → IR A B
```

Note the `WellFormedF` proof requirement — this witnesses that the functor is strictly positive and permits recursion.

### Why `out-μ` and `in-ν`?

These are the Lambek isomorphism inverses. They're essential for:

1. **Pattern matching inside Hylo coalgebras** — `out-μ` lets you destructure a μ-type counter within a coalgebra without leaving the IR

2. **Full fusion** — Without `out-μ`, observation primitives like `obs` would need `Cata` over the bound, preventing fusion with downstream operations

Example: Implementing `obs : Nat → Stream A → List A`

```once
-- Using Hylo + out-μ (enables fusion)
obs = Hylo listAlg obsCoalg
  where
    obsCoalg (n, stream) =
      case out-μ n of           -- Pattern match on Nat
        Zero    → Nil
        Suc n'  → Cons (head stream) (n', tail stream)
    listAlg = In

-- This fuses: sum (obs 100 stream) becomes a single Hylo
```

Without `out-μ`, we'd need:
```once
-- Using Cata over Nat (breaks fusion)
obs n stream = Cata natAlg n
  where
    natAlg Zero = []
    natAlg (Suc rest) = head stream :: rest  -- But which stream?!
```

The Cata-based version has problems:
- The recursion is over `n`, but we need the stream at each step
- Requires closure allocation to capture evolving stream state
- Cannot fuse with downstream Catas (Cata-Cata doesn't fuse)

---

## Totality and Productivity

### Totality of Cata

`Cata α` is total when:
1. `α : F A → A` is total (guaranteed by IR construction)
2. The input is `μF` (finite by construction)

Since `μF` is the *least* fixed point, it contains only finite structures. Structural recursion over finite data terminates.

### Productivity of Ana

`Ana α` is productive when:
1. `α : A → F A` is total (guaranteed by IR construction)
2. Each invocation produces one F-layer

Since IR morphisms are total, `α` always returns. Each call to `α` yields one constructor, so `Ana` always makes progress.

**No guardedness checker needed.** In Agda/Coq, you need syntactic guardedness checks or sized types. In Once, productivity is a consequence of IR totality.

### The Hylo: Fused Recursion

```
Hylo α γ = Cata α ∘ Ana γ
```

But computed directly:
```
hylo α γ x = α (fmap (hylo α γ) (γ x))
```

The intermediate `μF`/`νF` structure is never built. This is deforestation by construction.

**Termination of Hylo — an honest assessment:**

Hylo termination depends on the coalgebra eventually producing base cases:
- If `γ` eventually reaches `Nil`, `Zero`, etc. → terminates
- If `γ` produces infinite structure → diverges

| Hylo pattern | Terminates? | Why |
|--------------|-------------|-----|
| `Cata alg` (id coalgebra) | Always | μ-type is finite by construction |
| `obs n` (Nat counter) | Always | Counter decreases to zero |
| `obsWhile p` | If predicate eventually fails | Depends on data + predicate |
| User-defined | Depends on coalgebra | Must ensure coalgebra terminates |

**The formal situation:** The semantics of Hylo (`sem-hylo` in `Once.Semantics.Core`) uses Agda's `{-# TERMINATING #-}` pragma — a trust annotation that tells Agda to accept termination without proof. This is a real hole in the formal development.

**The solution: Paramorphism (Para)**

Category theory provides a principled fix: **paramorphism**, which gives the algebra access to both the original substructures AND the recursive results:

```
Para : (F (μF × A) → A) → μF → A
```

Para can be derived from Cata by returning pairs, making it **terminating without any trust pragma**.

For bounded Hylos like `obs`, we can use Para on the fuel type (Nat), making termination provable:
- The fuel μ-type provides well-founded recursion
- Termination follows from structural recursion on the fuel

See `docs/design/para-bounded-hylo.md` for details.

**Practical guidance:**
- Library Hylos (`obs`, `obsWhile`, etc.) can be Para-based and provably safe
- General Hylo remains for expert use with external termination arguments
- If you can't prove your coalgebra terminates, reconsider your design

The hole is real but has a known fix. Para-based bounded Hylos close the hole for practical patterns.

---

## Boundary Crossings: ν → μ

The observation primitives safely convert coinductive to inductive:

| Primitive | Type | Semantics |
|-----------|------|-----------|
| `obs n` | `Nat → ν F → μ F` | Observe exactly n steps |
| `obsWhile p` | `(A → Bool) → ν F → μ F` | Observe while predicate holds |
| `obsUntil p` | `(A → Bool) → ν F → μ F` | Observe until predicate holds |

These can be implemented as Hylos (current) or via Para (provably terminating):

```once
-- Current implementation: Hylo with terminating coalgebra
obs : Nat → Stream A → List A
obs = Hylo In coalg
  where
    coalg : (Nat, Stream A) → ListF A (Nat, Stream A)
    coalg (n, s) = case out-μ n of
      Zero   → Nil
      Suc n' → Cons (head s) (n', tail s)

-- Future implementation: Para on Nat (provably terminating)
obs : Nat → Stream A → List A
obs (fuel, stream) = Para paraAlg fuel stream
  where
    -- Para gives us: NatF (Nat × (Stream A → List A))
    paraAlg (inl tt) _ = []
    paraAlg (inr (_, k)) s = head s :: k (tail s)
```

The Para version terminates by structural recursion on Nat — no trust pragma needed.

The μ-type bound (`Nat`) ensures the coalgebra eventually produces `Nil`.

---

## Effects and Structured Recursion

### The Core Question

How do effects (IO, database queries, external APIs) interact with the totality guarantees of structured recursion?

### Once's Answer: Arrow-Based Effects

Once uses **Arrows** (`Eff A B`) rather than monads for effects. This is a deliberate choice that aligns with the categorical foundations.

```once
-- Pure arrow (function)
A → B           -- or A ⇒[q] B with QTT

-- Effectful arrow
Eff A B         -- may perform IO, block, fail

-- Lifting
arr : (A → B) → Eff A B
```

### Recursion Schemes and Effects

The recursion schemes (`Cata`, `Ana`, `Hylo`) have pure signatures:

```once
Cata : (F A → A) → μ F → A           -- Algebra is pure
Ana  : (A → F A) → A → ν F           -- Coalgebra is pure
Hylo : (F B → B) → (A → F A) → A → B -- Both pure
```

**The key insight:** We don't need separate "effectful schemes." Effects compose naturally by choosing the right carrier type.

### Effectful Algebras

If the carrier type `A` is itself an effect type, the algebra handles effects:

```once
-- Carrier is Eff Unit Int
-- Algebra: F (Eff Unit Int) → Eff Unit Int
sumWithLogging : List Int → Eff Unit Int
sumWithLogging = Cata alg
  where
    alg : ListF Int (Eff Unit Int) → Eff Unit Int
    alg Nil = arr (const 0)
    alg (Cons x restEff) =
        arr (const x) >>> logInt      -- log this element
        >>> arr (const ()) >>> restEff -- sequence with rest
        >>> arr (+ x)                  -- add x to result
```

The recursion structure (`Cata`) is pure. The algebra sequences effects using `>>>`.

### Effectful Coalgebras

Similarly, coalgebras can produce effects:

```once
-- Carrier is Eff Unit State
-- Coalgebra: Eff State (F State) — effectful production
readLines : Handle → Eff Unit (CoList String)
readLines h = Ana coalg h
  where
    coalg : Eff Handle (CoListF String Handle)
    coalg = readLineEff >>> arr checkEOF

    checkEOF : Maybe String → CoListF String Handle
    checkEOF Nothing = CoNil
    checkEOF (Just line) = CoCons line h
```

### Why This Works

The schemes don't care what `A` is — it's just a type. If `A = Eff X Y`, then:
- The algebra receives `F (Eff X Y)` — suspended effects from recursive calls
- The algebra returns `Eff X Y` — sequencing those effects with `>>>`
- The final result is `Eff X Y` — an effectful computation

**No new primitives needed.** Effect composition (`>>>`) plus the existing schemes gives us effectful recursion.

**Convenience combinators** can be derived for common patterns:

```once
-- Derived from Cata + Arrow combinators
traverseEff : Eff A B → List A → Eff Unit (List B)
traverseEff f = Cata alg where
    alg Nil = arr (const [])
    alg (Cons a restEff) =
        f a >>> arr (\b -> (b, ()))
        >>> second restEff
        >>> arr (uncurry (::))

-- Similarly: mapEff, filterEff, foldEff, etc.
```

Like `map` is derived from `Cata`, effectful traversals are derived from `Cata` + Arrow combinators — useful convenience without new recursion schemes.

### Example: Effectful Server

```once
-- Pure version (for testing, finite input):
serverPure : List Request → List Response
serverPure = Cata alg
  where
    alg Nil = Nil
    alg (Cons req rest) = Cons (handle req) rest

-- Effectful version (each request does IO):
serverEff : List Request → Eff Unit (List Response)
serverEff = Cata alg
  where
    alg : ListF Request (Eff Unit (List Response)) → Eff Unit (List Response)
    alg Nil = arr (const Nil)
    alg (Cons req restEff) =
        handleEff req                              -- Eff Request Response
        >>> arr (\resp -> (resp, ()))
        >>> first restEff                          -- run rest in parallel? or sequence
        >>> arr (\(resp, rest) -> Cons resp rest)

    handleEff : Eff Request Response
    handleEff = arr validateRequest
            >>> queryDatabase
            >>> arr formatResponse
```

### What's Guaranteed, What's Not

| Aspect | Guarantee |
|--------|-----------|
| Recursion structure | **Total** — Cata terminates, Ana produces one layer |
| Fusion | **Structural** — Hylo fuses by construction |
| Effect sequencing | **Compositional** — `>>>` sequences effects correctly |
| Effect behavior | **Not guaranteed** — individual effects may block, fail |
| Overall computation | **Structural + effects** — you will visit every element; what happens there depends on effects |

**The discipline:** The recursion scheme guarantees the *structure* of traversal. Effects at each step are sequenced with `>>>`. The combination gives you: "I will process every request (structural), and processing involves IO (effectful)."

### Why Arrows, Not Monads?

Once's choice of Arrows over Monads has several motivations:

1. **Uniform composition**: `>>>` composes all arrows uniformly
2. **Parallel structure**: `first`, `second`, `(***)` preserve parallel composition
3. **Matches Once's core**: The IR generators are already Arrow-like
4. **Algebras work naturally**: `F (Eff X Y) → Eff X Y` composes with `>>>`

### Arrow Infrastructure

**Sequential composition** (basic):
```once
f >>> g >>> h : Eff A D           -- sequence effects
arr f >>> g : Eff A C             -- lift pure, then effect
```

**Parallel composition** (for threading state):
```once
first  : Eff A B → Eff (A * C) (B * C)   -- effect on first, keep second
second : Eff A B → Eff (C * A) (C * B)   -- effect on second, keep first
(***)  : Eff A B → Eff C D → Eff (A * C) (B * D)  -- both in parallel
```

**Branching** (ArrowChoice, for short-circuiting):
```once
left  : Eff A B → Eff (A + C) (B + C)    -- effect on left branch
right : Eff A B → Eff (C + A) (C + B)    -- effect on right branch
(|||) : Eff A C → Eff B C → Eff (A + B) C  -- choose based on input
```

**Example: short-circuit on error**
```once
validateAll : List Input → Eff Unit (Either Error (List Output))
validateAll = Cata alg where
    alg Nil = arr (const (Right []))
    alg (Cons input restEff) =
        validateOne input                      -- Eff Unit (Either Error Output)
        >>> (arr Left ||| combineWith restEff) -- short-circuit or continue

    combineWith restEff =
        arr (\out -> (out, ()))
        >>> second restEff                     -- run rest, keep output
        >>> arr (\(out, rest) -> fmap (out ::) rest)
```

**Note:** `first`, `second`, `(***)`, and `(|||)` are derivable from the IR's products and coproducts. They need to be exposed for effectful programming.

### The Complete Picture

Effects compose with recursion schemes through the carrier type:

```once
-- Pure recursion (carrier = pure type)
sum : List Int → Int
sum = Cata alg where alg Nil = 0; alg (Cons x r) = x + r

-- Effectful recursion (carrier = Eff type)
sumLogging : List Int → Eff Unit Int
sumLogging = Cata alg where
    alg Nil = arr (const 0)
    alg (Cons x restEff) = logInt x >>> restEff >>> arr (+ x)

-- Stream processing (observation + effects)
processN : Nat → Stream Request → Eff Unit (List Response)
processN n stream =
    let requests = obs n stream in  -- Pure: bound the stream
    Cata handleAlg requests          -- Effectful: process with IO

-- Infinite stream transformation (effect at boundary)
serverMain : Eff Unit Unit
serverMain =
    listenEff 8080                   -- Eff: get connection stream
    >>> arr (obs 1000)               -- Pure: bound to 1000 requests
    >>> Cata handleAlg               -- Effectful: process each
    >>> arr (const ())
```

**The principle:** Recursion schemes handle structure. Effects handle IO. They compose orthogonally:
- **Structure** (Cata/Ana/Hylo) — pure, total, determines traversal pattern
- **Effects** (`>>>`, `Eff`) — sequences IO, may block
- **Composition** — carrier type `Eff X Y` lets effects flow through structure

---

## Why No General Loops?

A common question: "What about `while` loops? Not everything is structural recursion!"

### Examining "While Loops" in Practice

| Pattern | Appears to need... | Actually is... |
|---------|-------------------|----------------|
| Server loop | `while (running)` | Stream transformation: `Stream Req → Stream Resp` |
| Game loop | `while (playing)` | Coalgebra: `State → (Frame, State)` via `Ana` |
| Newton's method | `while (!converged)` | Bounded: `obsWhile (not ∘ converged)` |
| Binary search | `while (lo < hi)` | Cata over search space structure |
| Event processing | `while (events)` | Cata over event list or stream observation |

**The pattern:** Every practical "while loop" is either:
1. **Structural recursion** over data → `Cata`
2. **Corecursion** producing data → `Ana`
3. **Bounded iteration** → `obs`, `obsWhile`, `obsUntil`
4. **Stream transformation** → composition of the above

### The Collatz Problem

What about genuine numeric iteration?

```python
# Collatz conjecture
while n != 1:
    n = n // 2 if n % 2 == 0 else 3 * n + 1
```

This is:
- An unsolved mathematical problem (does it terminate for all n?)
- Not needed in any practical application
- A red flag if it appears in production code

### The Uncomfortable Truth

If you think you need an unbounded numeric loop, you're probably:

1. **Missing the data structure** — There's a list, tree, or stream hiding in your problem. Make it explicit.

2. **Missing a bound** — For safety, you should limit iterations anyway. Use `obs n` or `obsWhile`.

3. **Writing a mathematical curiosity** — Not production code. Once isn't designed for exploring the Collatz conjecture.

### The Deeper Truth: Non-Termination Is a Bug

Consider algorithms that supposedly "need" unbounded loops:

**Dataflow analysis** ("iterate until fixpoint"):
- The lattice has finite height `h`
- With `n` nodes, at most `h × n` iterations
- Termination is guaranteed by lattice theory — the bound exists, it's just implicit
- This is `obs (h * n)` or Cata over the lattice structure

**Consensus algorithms** (Paxos, Raft):
- With synchronous network and bounded failures: terminates
- With asynchronous network: FLP impossibility theorem proves consensus is impossible
- Real implementations use timeouts → bounded
- If it doesn't terminate, that's the impossibility result, not a missing feature

**SAT solvers**:
- The search tree is finite (formula has finite size)
- DPLL explores it systematically
- Guaranteed to terminate (may be slow — NP-complete — but terminates)

**Training loops** ("until convergence"):
- Convex optimization: convergence proven mathematically → termination proven
- Non-convex: either prove convergence or bound by epochs
- Unbounded training that may never converge is not a training algorithm — it's a bug

**The principle:** If an algorithm truly may never terminate, it's not an algorithm — it's a partial function with undefined behavior on some inputs. Good algorithms have termination guarantees:
- Structural (finite data)
- Mathematical (convergence proofs)
- Explicit (bounded iterations)

Once doesn't prevent you from writing good algorithms. It prevents you from writing things that aren't algorithms at all.

### Coverage

`Cata`, `Ana`, `Hylo` plus observation primitives (`obs`, `obsWhile`, `obsUntil`) cover the recursion patterns we've encountered in practice:

- **Finite consumption** → `Cata`
- **Infinite production** → `Ana`
- **Transform (fused)** → `Hylo`
- **Bound infinite to finite** → `obs`, `obsWhile`, `obsUntil`
- **Effects at each step** → effectful carrier type with `>>>`

No general `fix` combinator needed. No explicit `while` loops.

**A challenge to the reader:** If you have a legitimate algorithm — one with proven termination — that cannot be expressed with these primitives, we'd like to see it. Every counterexample we've examined has either:
1. Had hidden structure (expressible after refactoring)
2. Lacked termination guarantees (a bug, not an algorithm)

We don't claim formal completeness — that would require defining "practical algorithm" precisely. But we do claim: *every well-founded recursive pattern we've encountered fits this model*.

---

## Additional Recursion Schemes

The core IR provides `Cata`, `Ana`, and `Hylo`. Other schemes from the literature:

| Scheme | Type | Status in Once |
|--------|------|----------------|
| **Para** (paramorphism) | `(F (μF, A) → A) → μF → A` | Derivable from Cata |
| **Apo** (apomorphism) | `(A → F (μF + A)) → A → μF` | Derivable from Ana |
| **Histo** (histomorphism) | `(F (Cofree F A) → A) → μF → A` | Requires Cofree |
| **Futu** (futumorphism) | `(A → F (Free F A)) → A → νF` | Requires Free |
| **Zygo** (zygomorphism) | Mutual recursion pattern | Derivable |
| **Mutu** (mutual recursion) | Even/odd style | Via product algebras |

**Current focus:** Once prioritizes `Cata`/`Ana`/`Hylo` as the foundation.

**Planned addition:** `Para` (paramorphism) is the key to provably-terminating bounded iteration. It gives the algebra access to both original substructures and recursive results, enabling bounded Hylos like `obs` without trust pragmas. Para is derivable from Cata by returning pairs:

```agda
paraS alg x = proj₂ (cataS alg' x)
  where alg' fx = (⟨ sfmap F proj₁ fx ⟩ , alg fx)
```

The more exotic schemes (`Histo`, `Futu`) require `Free`/`Cofree` which need higher-kinded functor support.

For most practical code, `Cata`/`Ana`/`Para` (for bounded iteration) plus the observation primitives suffice.

---

## Comparison with Haskell's recursion-schemes

| Aspect | Haskell `recursion-schemes` | Once |
|--------|----------------------------|------|
| Fixed point | `Fix f` (unified) | `μ F`, `ν F` (split) |
| Functor | Typeclass `Functor` | Codes (polynomial) |
| Termination | Programmer's responsibility | Type-enforced |
| Productivity | Programmer's responsibility | Follows from totality |
| Fusion | Via rewrite rules (RULES) | Structural (Hylo is primitive) |
| Pattern matching | Via `project`/`embed` | Via `out-μ`/`in-ν` (Lambek) |

### What You Lose

- **General recursion:** No arbitrary `fix`. Must use Cata/Ana/Hylo.
- **Quick prototyping:** Can't write a quick recursive function without thinking about which scheme it is.
- **Some expressiveness:** Polynomial functors exclude some patterns (see limitations above).
- **Ecosystem:** No Hackage equivalent, limited tooling, research-stage maturity.
- **Familiarity:** Different mental model from mainstream languages.

### What You Gain

- **Totality for Cata:** Folds over μ-types are guaranteed to terminate.
- **Productivity for Ana:** Each step of a coalgebra completes (though infinite chains are possible).
- **Structural fusion:** Hylo fusion is definitional, not optimizer-dependent.
- **Explicit boundaries:** μ vs ν forces you to think about finite/infinite at the type level.
- **No accidental infinite loops:** The common case of "oops, forgot the base case" becomes a type error.

### The Tradeoff

Once doesn't eliminate all non-termination (Hylo can diverge). It eliminates the *common* causes: unbounded recursion over infinite data, forgotten base cases, non-productive corecursion. Whether this tradeoff is worth the reduced expressiveness depends on your use case.

---

## Implementation Notes

### Semantics (from Once.Semantics.IR)

```agda
-- Cata: build Set-level algebra, apply sem-cata
eval ps (Cata {F} wf alg) x =
  sem-cata wf (λ fa → eval ps alg (coerce-functor⁻¹ F _ fa)) x

-- Ana: build Set-level coalgebra, apply sem-ana
eval ps (Ana {F} wf {A} coalg) x =
  sem-ana F (λ a → coerce-functor F A (eval ps coalg a)) x

-- Hylo: direct computation, no intermediate structure
eval ps (Hylo {F} wf {A} alg coalg) x =
  sem-hylo F
    (λ fb → eval ps alg (coerce-functor⁻¹ F _ fb))
    (λ a → coerce-functor F A (eval ps coalg a))
    x
```

### Coherence

The `coerce-functor` and `coerce-functor⁻¹` functions bridge between:
- Type-level functor application: `⟦ F ⟧T A` (in IR types)
- Set-level functor application: `⟦ F ⟧F ⟦ A ⟧` (in semantics)

This coherence is proven in `Once.Semantics.Coherence`.

### Proof Status — An Honest Assessment

The Once formal development is a work in progress. Current status:

| Component | Status |
|-----------|--------|
| IR definition | Complete (Agda) |
| Type-level functor semantics | Complete |
| Set-level functor semantics | Complete |
| Coherence between levels | Proven for polynomial functors |
| `sem-cata` termination | **Sound** — structural recursion over μS |
| `sem-ana` productivity | Uses `{-# TERMINATING #-}` pragma |
| `sem-hylo` termination | Uses `{-# TERMINATING #-}` pragma |
| Primitive operations | Postulated (`defaultEvalPrim`) |

**Important:** `sem-cata` is fully verified — it uses structural recursion on well-founded μS types and Agda's termination checker accepts it without pragmas.

`sem-ana` and `sem-hylo` use Agda's `{-# TERMINATING #-}` pragma, which tells Agda to trust termination/productivity without proof. This is a known limitation.

**Path forward:** Para (paramorphism) is derivable from Cata and terminates provably. Bounded Hylos like `obs` can be rewritten using Para, removing reliance on trust pragmas. See `docs/design/para-bounded-hylo.md`.

Primitive operations (arithmetic, etc.) are necessarily opaque. The formal development aims to minimize postulates while remaining practical.

---

## Further Reading

- **Formal development:** `formal/Once/CCC/IR.agda` — IR definition with recursion schemes
- **Semantics:** `formal/Once/Semantics/IR.agda` — Denotational semantics
- **Coinductive types:** `formal/Once/Derived/Coinitial.agda` — Stream, CoList definitions
- **Observation:** `formal/Once/Derived/Observation.agda` — obs implementation
- **Proposal:** `docs/proposals/OCP-0003-total-productive-ir.md` — Design rationale

### References

- Meijer, Fokkinga, Paterson. "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire" (1991)
- Gibbons. "Origami Programming" (2003)
- Abel. "Type-Based Termination" (2004)
- Atkey & McBride. "Productive Coprogramming with Guarded Recursion" (2013)
