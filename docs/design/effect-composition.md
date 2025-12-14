# Design Document: Effect Composition in Once

## Executive Summary

D032 introduced a strict separation between pure functions (`A -> B`) and effectful morphisms (`Eff A B`). This document examines whether there's a real usability gap, and what design choices exist.

**Key Question**: Is `compose puts "hello"` a valid use case, or should Once programs use `puts "hello"` directly?

---

## Background: What D032 Changed

Before D032:
- Effects were implicit or unified with pure functions
- `compose f x` worked regardless of whether `f` was effectful

After D032:
- `Eff A B` is a distinct type from `A -> B`
- The type checker enforces: `TArrow` and `TEff` do NOT unify
- `compose : (B -> C) -> (A -> B) -> (A -> C)` only works with pure arrows

---

## The Failing Pattern

```once
primitive puts : Eff (String Utf8) Unit

main : IO Unit
main = compose puts "Hello"
```

**Why it fails:**
- `compose` expects `(B -> C)` (first argument)
- `puts` is `Eff (String Utf8) Unit`, not `String Utf8 -> Unit`
- Type error: cannot unify `TArrow` with `TEff`

---

## Is This a Real Usability Gap?

### Question: Why use `compose puts "hello"` instead of `puts "hello"`?

Let's examine what these expressions mean categorically:

**Expression 1: `compose puts "hello"`**
```
"hello" : Unit -> String     (constant morphism from terminal)
puts    : Eff String Unit    (effectful morphism)

compose puts "hello" : Unit -> Unit  (if it worked)
```

**Expression 2: Direct application `puts "hello"`**
```
puts "hello" : ???
```

Wait - Once doesn't have traditional function application! In Once:
- Everything is morphism composition
- There's no `f(x)` syntax
- `puts "hello"` would need to be parsed as... what?

### The Real Issue: Once Has No Application

In Haskell: `puts "hello"` applies function to argument
In Once: There is no application - only composition

**Once's categorical model:**
- Values ARE morphisms from the terminal object
- `"hello" : 1 -> String` (morphism from terminal to String)
- `puts : String -> Unit` (morphism from String to Unit, ignoring Eff for now)
- To "apply" puts to hello: `compose puts "hello" : 1 -> Unit`

So `compose f x` IS Once's way of saying `f(x)`.

---

## Example: The Usability Gap

### Example 1: Simple Hello World

**What users want to write:**
```once
main = puts "Hello, World!"
```

**What Once requires (currently broken):**
```once
main = compose puts "Hello, World!"
```

**What actually works:**
```once
-- Nothing! There's no way to print a string with the current system.
-- The only working pattern is using primitives that take Unit:
main = exit0  -- works because exit0 : Eff Unit Unit
```

### Example 2: Sequence of Effects

**What users want:**
```once
main = do
  puts "Step 1"
  puts "Step 2"
  exit0
```

**Categorical equivalent (if we had effCompose):**
```once
main = effCompose exit0 (effCompose (compose puts "Step 2") (compose puts "Step 1"))
```

**Currently:** Impossible - no way to sequence effects.

### Example 3: Conditional Effects

**What users want:**
```once
greet : Bool -> IO Unit
greet b = if b then puts "Hello" else puts "Goodbye"
```

**Categorical equivalent:**
```once
greet : Bool -> IO Unit
greet = case id
  (compose puts "Goodbye")  -- Left branch (false)
  (compose puts "Hello")    -- Right branch (true)
```

**Currently:** Broken because `compose puts "..."` fails.

---

## Design Options

### Option 1: Add `effCompose` Generator

```haskell
effCompose : Eff B C -> Eff A B -> Eff A C
```

**Pros:**
- Explicit - users know they're composing effects
- Mirrors Arrow's `(>>>)` operator
- Preserves type distinction between pure and effectful

**Cons:**
- Two composition operators to learn
- Verbose: `effCompose f (effCompose g h)` vs `f >>> g >>> h`
- Need `arr` to lift constants: `effCompose puts (arr (const "hello"))`

**Example usage:**
```once
main = effCompose puts (arr (const "Hello"))
-- Or with a helper:
main = effCompose puts (pure "Hello")
```

### Option 2: Make `compose` Polymorphic

Allow `compose` to work with both `->` and `Eff`:

```haskell
compose : f B C -> f A B -> f A C
  where f ∈ {(->), Eff}
```

**Pros:**
- Single composition operator
- Existing code "just works"
- More intuitive

**Cons:**
- Implicit effect propagation (less explicit)
- Implementation complexity (type-level polymorphism)
- Blurs the pure/effectful distinction D032 tried to establish

### Option 3: Add Application Syntax Sugar

Add `f x` as sugar for `compose f (const x)`:

```once
main = puts "Hello"  -- desugars to: compose puts (const "Hello")
```

**Pros:**
- Familiar syntax
- Concise
- Hides categorical machinery

**Cons:**
- Still doesn't solve Eff composition
- `puts "Hello"` would still fail because `compose` doesn't accept `Eff`
- Would need to combine with Option 1 or 2

### Option 4: Implicit arr Lifting

Allow pure values to implicitly lift to Eff context:

```once
main = compose puts "Hello"
-- "Hello" : String implicitly becomes arr (const "Hello") : Eff Unit String
-- Then effectful compose is used
```

**Pros:**
- Existing syntax works
- Most concise

**Cons:**
- Magic implicit conversions
- Harder to reason about types
- Goes against D032's explicit effect philosophy

### Option 5: Do Nothing (Status Quo)

Keep the current system. Users must:
- Only use `Eff Unit X` primitives directly
- Cannot compose effectful computations
- Cannot pass arguments to effectful functions

**Pros:**
- No changes needed
- Forces users to think categorically

**Cons:**
- Unusable for practical programs
- Can't print strings
- Can't sequence effects

---

## Expressibility Analysis

| Capability | Option 1 | Option 2 | Option 3 | Option 4 | Option 5 |
|------------|----------|----------|----------|----------|----------|
| Print string | ✅ verbose | ✅ | ❌ | ✅ | ❌ |
| Sequence effects | ✅ | ✅ | ❌ | ✅ | ❌ |
| Pure/Eff distinction | ✅ explicit | ⚠️ implicit | N/A | ⚠️ implicit | ✅ |
| Learning curve | Medium | Low | Low | Low | N/A |
| Categorical purity | ✅ | ⚠️ | ⚠️ | ⚠️ | ✅ |

---

## Recommendation

**Option 1 (effCompose) with helper functions** is the cleanest solution:

1. **Add `effCompose`** - explicit effectful composition
2. **Add `pure`** - sugar for `arr . const`, lifts values to Eff
3. **Keep type distinction** - `Eff` and `->` remain separate

**Example of improved usability:**
```once
-- Helper (could be in standard library)
pure : A -> Eff Unit A
pure = arr const

-- Now users can write:
main = effCompose puts (pure "Hello, World!")

-- Or with infix syntax (if added):
main = pure "Hello, World!" >>> puts
```

This preserves:
- D032's explicit effect tracking
- Categorical foundations (composition-based)
- Usability (can actually write programs)

---

## Implementation Scope

If we proceed with Option 1:

**Files to modify:**
1. `compiler/src/Once/TypeCheck.hs` - add `effCompose` to `generatorType`
2. `compiler/src/Once/IR.hs` - add `EffCompose` constructor (or reuse `Compose`)
3. `compiler/src/Once/CLI.hs` - code generation (same as `Compose`)
4. `compiler/src/Once/Elaborate.hs` - handle `effCompose` in elaboration
5. `compiler/test/Backend/Common.hs` - update test helpers
6. `Strata/Derived/Canonical.once` - add `pure` helper

**Estimated changes:** ~50 lines of code

---

## Open Questions

1. **Should `effCompose` be a keyword or just a generator?**
   - Keyword: `f >>> g` syntax
   - Generator: `effCompose f g`

2. **Should we add `first` for parallel effect composition?**
   - Arrow requires: `first : Eff A B -> Eff (A, C) (B, C)`
   - Useful for: threading state, parallel computation

3. **What about `arr` for non-constants?**
   - Current `arr : (A -> B) -> Eff A B` works
   - Combining with `const` is verbose

4. **Is the pure/Eff distinction worth the complexity?**
   - Alternative: unify them, track effects differently
