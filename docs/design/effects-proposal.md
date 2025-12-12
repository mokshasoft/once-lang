# Effects in Once: IO Monad vs Arrows

## The Problem

Currently, Once has an implicit lifting bug where effectful code can masquerade as pure functions:

```once
println "hello" : Unit
```

Gets implicitly lifted to `Unit -> Unit`, allowing it to be used where a pure function is expected. This breaks equational reasoning - we cannot distinguish pure from effectful code by looking at types.

**Requirement**: Effectful code must be explicitly typed so that:
1. Pure code is guaranteed side-effect free
2. Reasoning about effects is possible
3. Verification can distinguish pure from impure

---

## Option A: IO Monad

### Basic Structure

```once
-- IO as an abstract type constructor
type IO : Type -> Type

-- Primitive operations return IO
println : String -> IO Unit
readLine : Unit -> IO String
readFile : String -> IO (Result String Error)
writeFile : String -> String -> IO (Result Unit Error)

-- Monad operations
pure : A -> IO A
bind : IO A -> (A -> IO B) -> IO B
```

### Sequencing Effects

```once
-- Using bind (verbose)
main : Unit -> IO Unit
main _ = bind (println "What is your name?") (\_ ->
         bind readLine (\name ->
         println ("Hello, " ++ name)))

-- With do-notation sugar (if added)
main : Unit -> IO Unit
main _ = do
  println "What is your name?"
  name <- readLine
  println ("Hello, " ++ name)
```

### Categorical Interpretation

IO Monad corresponds to a **Kleisli category**:
- Objects: Types A
- Morphisms A → B: Functions `A -> IO B`
- Composition: Kleisli composition via `bind`
- Identity: `pure`

The monad laws ensure this forms a category:
```
pure >=> f      = f                    -- left identity
f >=> pure      = f                    -- right identity
(f >=> g) >=> h = f >=> (g >=> h)      -- associativity
```

### Verification Impact

**Pros**:
- Well-understood theory (Moggi's computational lambda calculus)
- Clear separation: `A -> B` is pure, `A -> IO B` is effectful
- Can verify pure code independently
- Monad laws can be verified

**Cons**:
- Kleisli arrows don't compose with regular arrows
- Mixing pure and impure requires lifting: `liftM : (A -> B) -> (IO A -> IO B)`
- Two different composition operators (`.` and `>=>`)
- Verification must track which category we're in

---

## Option B: Arrows

### Why Arrows Are More General

Arrows (Hughes, 2000) generalize monads. Every monad gives rise to an arrow, but not vice versa.

```
Monads ⊂ Arrows ⊂ Categories
```

Key insight: Monads require `A -> M B` (functions returning computations). Arrows abstract over the arrow itself: `arr A B` where `arr` is an abstract type constructor.

### Arrow Operations (Categorical)

Arrows correspond to a **premonoidal category** with:

```once
-- Core arrow operations
arr    : (A -> B) -> Eff A B              -- Lift pure function
(>>>)  : Eff A B -> Eff B C -> Eff A C    -- Sequential composition
first  : Eff A B -> Eff (A * C) (B * C)   -- Parallel composition (product)
```

From these, we derive:
```once
second : Eff A B -> Eff (C * A) (C * B)
second f = arr swap >>> first f >>> arr swap

(***) : Eff A B -> Eff C D -> Eff (A * C) (B * D)
f *** g = first f >>> second g

(&&&) : Eff A B -> Eff A C -> Eff A (B * C)
f &&& g = arr diagonal >>> (f *** g)
```

### How Once Generators Map to Arrows

The 12 Once generators are already arrow-like! Consider:

| Generator | Arrow equivalent |
|-----------|------------------|
| `id`      | `arr id`         |
| `compose` | `(>>>)`          |
| `fst`     | `arr fst`        |
| `snd`     | `arr snd`        |
| `pair`    | `(&&&)`          |
| `inl`     | `arr inl`        |
| `inr`     | `arr inr`        |
| `case`    | `(|||)` (ArrowChoice) |
| `curry`   | ArrowApply       |
| `apply`   | ArrowApply       |

Once's Natural Transformation core is essentially working with arrows!

### Once with Explicit Effect Arrows

```once
-- Pure morphisms (current Once)
type (->)  : Type -> Type -> Type

-- Effectful morphisms
type Eff   : Type -> Type -> Type

-- Lift pure to effectful
arr : (A -> B) -> Eff A B

-- Effectful primitives
println   : Eff String Unit
readLine  : Eff Unit String
readFile  : Eff String (Result String Error)
writeFile : Eff (String * String) (Result Unit Error)

-- Composition
(>>>) : Eff A B -> Eff B C -> Eff A C
```

### Sequencing with Arrows

```once
-- Arrow-style composition
main : Eff Unit Unit
main = arr (const "What is your name?")
   >>> println
   >>> readLine
   >>> arr (\name -> "Hello, " ++ name)
   >>> println

-- Or with product for multiple inputs
greet : Eff (String * String) Unit
greet = arr (\(greeting, name) -> greeting ++ ", " ++ name)
    >>> println
```

### ArrowChoice for Branching

```once
-- Sum types (coproducts) in arrows
left  : Eff A B -> Eff (A + C) (B + C)
right : Eff A B -> Eff (C + A) (C + B)
(|||) : Eff A C -> Eff B C -> Eff (A + B) C

-- Example: conditional IO
processInput : Eff String Unit
processInput = arr parse
           >>> (handleValid ||| handleError)
  where
    parse : String -> Result Data Error
    handleValid : Eff Data Unit
    handleError : Eff Error Unit
```

### Verification Impact

**Pros**:
- Uniform composition: everything uses `(>>>)`
- Pure functions embed via `arr`
- Arrow laws are simpler than monad laws
- Matches Once's categorical foundation exactly
- `first`/`second` preserve parallel structure (useful for verification)
- No need for `liftM` - just use `arr`

**Cons**:
- Less familiar to most programmers
- No direct equivalent of `do`-notation (though proc-notation exists in Haskell)
- Slightly more verbose for simple sequential code

### Arrow Laws (for verification)

```
arr id >>> f              = f                    -- identity
f >>> arr id              = f                    -- identity
(f >>> g) >>> h           = f >>> (g >>> h)      -- associativity
arr (f >>> g)             = arr f >>> arr g      -- arr preserves composition
first (arr f)             = arr (f *** id)       -- first/arr interaction
first (f >>> g)           = first f >>> first g  -- first preserves composition
first f >>> arr (id *** g) = arr (id *** g) >>> first f  -- commutativity
```

---

## Option C: Arrows with Monad Sugar

### Can We Have Both?

Yes! If the compiler uses arrows internally, users can still write monadic code.

**Key insight**: `ArrowApply` (which Once has via `curry`/`apply`) is equivalent to a monad.

```once
-- ArrowApply gives us:
app : Eff (Eff A B * A) B

-- This is equivalent to:
join : Eff A (Eff A B) -> Eff A B
```

### Monadic Interface as Sugar

```once
-- Monad operations derived from ArrowApply
return : A -> Eff Unit A
return x = arr (const x)

(>>=) : Eff Unit A -> (A -> Eff Unit B) -> Eff Unit B
m >>= f = m >>> arr (\a -> (f a, ())) >>> app
```

Users can write:
```once
-- Monadic style
main = println "Name?" >>= \_ ->
       readLine >>= \name ->
       println ("Hello, " ++ name)
```

Compiler desugars to arrow composition internally.

### Recommended Approach

1. **Core**: Arrow-based effect system (`Eff A B`)
2. **Sugar**: Monadic notation for sequential code
3. **Verification**: Reason about arrow laws

---

## Comparison Table

| Aspect | IO Monad | Arrows | Arrows + Monad Sugar |
|--------|----------|--------|---------------------|
| Composition | Two kinds (`.` and `>=>`) | Uniform `(>>>)` | Uniform + sugar |
| Pure/Effect mixing | Requires `liftM` | Natural via `arr` | Natural via `arr` |
| Parallel composition | Awkward | Native (`(***)`, `(&&&)`) | Native |
| Matches Once core | Partial (Kleisli) | Direct | Direct |
| User familiarity | High | Low | Medium |
| Verification | Two categories | One category | One category |
| Expressiveness | Standard | More general | More general |

---

## Verification Considerations

### With IO Monad

Verification must distinguish:
- Pure terms: verified in the standard category
- Effectful terms: verified in Kleisli category
- Mixing requires explicit lifting lemmas

```agda
-- Two different hom-sets
Pure : Type → Type → Set
Pure A B = A → B

Impure : Type → Type → Set
Impure A B = A → IO B

-- Lifting lemma needed
lift-pure : Pure A B → Impure A B
lift-pure f = λ a → pure (f a)
```

### With Arrows

Single unified framework:
- Pure morphisms: `arr f` where `f : A → B`
- Effect morphisms: direct `Eff A B`
- Arrow laws apply uniformly

```agda
-- One hom-set with distinguished pure arrows
Eff : Type → Type → Set

-- Pure embedding
arr : (A → B) → Eff A B

-- Purity predicate
IsPure : Eff A B → Set
IsPure e = ∃ f. e ≡ arr f

-- Can verify: if IsPure e, then e has no effects
```

### Effect Tracking in Types

Both approaches can track effects, but arrows do it more uniformly:

```once
-- Effect-indexed arrows (advanced)
type Eff : Effects -> Type -> Type -> Type

-- Console effect
println : Eff [Console] String Unit

-- File effect
readFile : Eff [FileIO] String (Result String Error)

-- Composition combines effects
(>>>) : Eff e1 A B -> Eff e2 B C -> Eff (e1 ∪ e2) A C
```

This gives fine-grained effect tracking for verification.

---

## Recommendation

**Use Arrows as the foundation with monadic sugar for ergonomics.**

Rationale:
1. Once's NT core is already arrow-like (the 12 generators)
2. Arrows compose uniformly - no category switching
3. `ArrowApply` (which Once has) allows monadic notation
4. Verification is simpler with one unified category
5. More expressive: can represent effects monads cannot

### Implementation Plan

1. **Add `Eff` type constructor** to distinguish effectful morphisms
2. **Primitives return `Eff`**: `println : Eff String Unit`
3. **Add `arr`** to lift pure functions: `arr : (A -> B) -> Eff A B`
4. **Main type**: `main : Eff Unit Unit`
5. **Add sugar** for monadic notation (optional, later)
6. **Update verification** to use arrow laws

### Migration Path

Current code:
```once
main : Unit -> Unit
main _ = println "hello"
```

New code:
```once
main : Eff Unit Unit
main = arr (const "hello") >>> println
```

Or with sugar:
```once
main : Eff Unit Unit
main = do
  println "hello"
```

---

## References

- Hughes, J. (2000). "Generalising Monads to Arrows"
- Paterson, R. (2001). "A New Notation for Arrows"
- Moggi, E. (1991). "Notions of computation and monads"
- Atkey, R. (2011). "What is a Categorical Model of Arrows?"
- Heunen, C. & Jacobs, B. (2006). "Arrows, like Monads, are Monoids"
