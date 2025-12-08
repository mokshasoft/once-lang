# Syntax Exploration for Once

## The Question

What syntax is natural for a language based on natural transformations?

**Key insight**: "Effect declarations" aren't really natural here. In Once, effects are encoded as:
- Which **functor** the computation produces
- **Type structure** itself

There's no separate "effect system" - the types ARE the effects.

---

## LED Blink in 5 Different Syntaxes

### 1. Monadic Do-Notation (NOT natural for Once)

```haskell
-- This is what Haskell does, but it assumes monads
main :: IO ()
main = forever $ do
  digitalWrite led HIGH
  delay 1000
  digitalWrite led LOW
  delay 1000
```

**Why it doesn't fit Once:**
- `do` desugars to `>>=` which is Kleisli composition
- Once uses natural transformations, not Kleisli arrows
- The state threading is hidden, Once makes it explicit

---

### 2. Composition Style (Very Natural)

```
-- Morphisms compose with . or compose
-- Read right-to-left: "delay after low after delay after high"

led = pin 13

cycle : Pin -> Pin
cycle = compose (delay 1000) (compose low (compose (delay 1000) high))

main : Stream Pin
main = ana cycle led
```

**Why it fits:**
- Direct categorical composition
- No hidden state
- Clear data flow
- `ana` (anamorphism) generates the infinite stream

---

### 3. Pipeline Style (Natural, reversed)

```
-- Same as composition, but left-to-right with |>
-- Read: "high, then delay, then low, then delay"

led = pin 13

cycle : Pin -> Pin
cycle = high |> delay 1000 |> low |> delay 1000

main : Stream Pin
main = led |> ana cycle
```

**Why it fits:**
- Still just composition (flipped)
- Reads like English
- Popular in F#, Elixir, newer Haskell

---

### 4. Point-Free Combinator Style (Very Natural)

```
-- No variables at all, pure combinators
-- This is closest to the categorical foundations

high  : Pin -> Pin
low   : Pin -> Pin
delay : Nat -> (A -> A)    -- polymorphic delay

-- Compose morphisms
cycle = compose high (compose (delay 1000) (compose low (delay 1000)))

-- Unfold from initial state into stream
main = ana (pair id cycle) (pin 13)
--         ^^^^^^^^^^^^^^
--         diagonal: produce (current, next)
```

**Why it fits:**
- Directly mirrors categorical diagrams
- `pair id id` is the diagonal (duplicate)
- `ana` is anamorphism
- No variable names cluttering things

---

### 5. Arrow Notation (Somewhat Natural)

```haskell
-- Haskell's arrow notation, designed for non-monadic composition
-- proc/do for arrows, -< for feeding inputs

main : Stream Pin
main = proc () -> do
  rec state <- toggle -< state'
      let state' = state
  returnA -< state

toggle : Pin -> Pin
toggle = proc p -> do
  high -< p
  delay 1000 -< ()
  low -< p
  delay 1000 -< ()
  returnA -< p
```

**Why it partially fits:**
- Arrows are closer to natural transformations than monads
- `proc` notation was designed for dataflow
- But still has some imperative flavor

---

## What About Effects?

In traditional effect systems:
```haskell
effect GPIO where ...   -- declares an effect
```

In Once's categorical model, there's no separate declaration. The **type tells you the effect**:

```
-- The morphism signature declares effects
high : Pin -> External Pin        -- uses external world
high : Pin -> State GPIO Pin      -- uses GPIO state
high : Pin -> Pin                 -- pure (no effect)
```

---

## Once Syntax Decisions

Based on design discussions, Once uses:

```
-- Types declare capabilities implicitly
-- No "effect" keyword needed

-- Pin operations produce External values
high : Pin -> External Pin
low  : Pin -> External Pin

-- Time operations
wait : Nat -> External Unit

-- Composition with standard symbols
cycle : Pin -> External Pin
cycle = compose (wait 1000) (compose low (compose (wait 1000) high))

-- Product uses *
both : Pin * Pin -> External (Pin * Pin)
both = pair high high      -- set both pins high simultaneously

-- Sum uses +
either : Pin + Pin -> External Pin
either = case high low     -- handle left or right case

-- Stream from repeated application
main : External (Stream Unit)
main = ana cycle (pin 13)
```

**Key syntax features:**
- `->` for function types
- `*` for products
- `+` for coproducts (sums)
- `compose` or `.` for composition
- `|>` for pipeline (reverse composition)
- ASCII-friendly throughout

---

## Comparison

| Syntax | Naturalness for Once | Readability | Notes |
|--------|---------------------|-------------|-------|
| Do-notation | ❌ Low | ✓ Familiar | Assumes monads |
| Composition (.) | ✓✓ Very high | ~ Math-like | Right-to-left |
| Pipeline (\|>) | ✓✓ Very high | ✓ Clear | Left-to-right |
| Point-free | ✓✓✓ Highest | ~ Terse | Pure categorical |
| Arrow proc | ✓ Medium | ✓ Clear | Still some sugar |

---

## The Categorical Truth

The most honest syntax is probably just:

```
main = ana (pair snd (compose high (compose (delay 1000) (compose low (delay 1000))))) led
```

Where:
- `ana` = anamorphism (unfold)
- `pair` = diagonal when both args are id (duplicate input)
- `snd` = second projection (take next state)
- `compose` = composition
- `led` = initial state

But that's hard to read. The art is finding syntax that's both **faithful to the math** and **pleasant to write**.

## Balance

Once aims for:
1. **Standard symbols**: `->`, `*`, `+`, `.`, `|>`
2. **Standard names**: `compose`, `pair`, `case`, `fst`, `snd`, etc.
3. **Types as documentation**: Effect visible in return type
4. **Optional type annotations**: Inference handles most cases
5. **ASCII-friendly**: No Unicode required (but allowed)
