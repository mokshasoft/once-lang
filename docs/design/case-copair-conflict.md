# Future Decision: Case Generator vs Case Expression

## Status: Open

## Problem

The `case` generator (categorical copair) conflicts with `case...of` expression syntax:

```once
-- Generator form (currently broken - parser sees "case" as keyword)
handle = case  -- expects "of" after this

-- Expression form (Haskell-style pattern matching)
case x of { Left a -> f a; Right b -> g b }
```

## Mathematical Background

In category theory, given a coproduct A + B with injections:
- `inl : A -> A + B`
- `inr : B -> A + B`

The universal property gives a unique morphism for any `f : A -> C` and `g : B -> C`:
- `[f, g] : A + B -> C`

This is variously called:
- **Copair** or **copairing** (categorical)
- **Case analysis** (type theory)
- **Either** (Haskell)
- Bracket notation `[f, g]` (mathematical)

## Options

### Option 1: Rename generator to `copair`

```once
copair : (A -> C) -> (B -> C) -> A + B -> C

handle = copair okHandler errHandler
```

**Pros:** Clear, no conflict, matches categorical terminology
**Cons:** Less familiar than "case"

### Option 2: Use bracket syntax `[f, g]`

```once
handle = [okHandler, errHandler]
```

**Pros:** Matches mathematical notation exactly
**Cons:** Requires parser changes, brackets overloaded (lists?)

### Option 3: Make `case...of` sugar for copair + lambdas

```once
-- Sugar:
case x of { Left a -> f a; Right b -> g b }

-- Desugars to:
copair (\a -> f a) (\b -> g b) x
```

**Pros:** Familiar syntax preserved, clean desugaring
**Cons:** Lambdas need full support, adds complexity

### Option 4: Remove `case...of` entirely

Point-free style uses composition, not variable binding:

```once
-- Instead of:
case x of { Left a -> f a; Right b -> g b }

-- Write:
copair f g x
```

**Pros:** Simpler language, pure point-free
**Cons:** Less accessible to newcomers, verbose for complex cases

### Option 5: Different keyword for expressions

Use `match` for expressions, keep `case` for generator:

```once
-- Generator:
handle = case f g

-- Expression:
match x of { Left a -> f a; Right b -> g b }
```

**Pros:** No conflict, both forms available
**Cons:** Two similar keywords

## Recommendation

Tentatively: **Option 1 (rename to `copair`)** combined with **Option 3 (case...of as sugar)**.

This gives:
- Mathematical purity with `copair` generator
- Familiar syntax with `case...of` for those who want it
- Clear desugaring semantics

## Action Items

1. [ ] Decide on generator name: `copair`, `either`, or keep `case`
2. [ ] Decide if `case...of` expressions should exist
3. [ ] If yes, define desugaring rules
4. [ ] Update parser accordingly
5. [ ] Document the design decision

## Related

- D024: Initial algebras and data types
- D032: Effect system with `arr` and `effCompose`
- Strata/Derived/Initial.once: Currently cannot use `case` standalone
