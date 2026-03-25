# Guard/Unguard: Surface Language vs IR Design

**Status:** OBSOLETE - GuardedT removed from IR (2026-03-25)
**Related:** OCP-0003 (Total and Productive IR)
**Date:** 2026-03-25

---

## Resolution (2026-03-25)

**This design document is obsolete.** GuardedT, Guard, and Unguard have been
removed from the IR entirely.

**Why:** Productivity follows from IR totality. Since IR morphisms are total
(they terminate), coalgebras `IR A (⟦ F ⟧T A)` automatically produce F-layers
in finite time. This IS "guardedness" — no type-level wrapper needed.

**The simpler design:**
```agda
Ana : WellFormedF F → IR A (⟦ F ⟧T A) → IR A (ν-type F)
-- No GuardedT, no Guard, no Unguard
```

See `Once/CCC/IR/Totality.agda` and `Once/CCC/IR/Productivity.agda` for the proofs.

---

## Original Document (Historical)

---

## Background

OCP-0003 introduces `GuardedT`, `Guard`, and `Unguard` to the IR to enforce productive corecursion at the type level:

```agda
-- Type level
GuardedT : Functor → Type → Type

-- IR constructors
Ana     : WellFormedF F → IR A (GuardedT F A) → IR A (ν-type F)
Guard   : WellFormedF F → IR (⟦ F ⟧T A) (GuardedT F A)
Unguard : WellFormedF F → IR (GuardedT F A) (⟦ F ⟧T A)
```

The key insight is that `Ana` requires `GuardedT` output, making productivity **definitional** — non-productive coalgebras cannot type-check.

---

## The Problem

`Guard` and `Unguard` serve the categorical/semantic layer:

1. **Ana-Out identity law**: `Ana (Guard ∘ Out) ≡ id`
2. **Compositional proofs**: The isomorphism `GuardedT F A ≅ ⟦ F ⟧T A` is explicit
3. **Categorical completeness**: Final coalgebra laws require these morphisms

But from a **user perspective**, they're implementation noise. A user writing:

```
streamFrom : Nat → Stream Nat
streamFrom = ana (λ n → (n, n + 1))
```

Should not need to think about `Guard`/`Unguard`. The compiler should:
1. Recognize that `(n, n + 1)` is syntactically guarded (pair constructor at top)
2. Elaborate to IR with appropriate `Guard` insertions

**Question:** Do we need a separate surface IR, or can we hide these in the existing IR?

---

## Design Options

### Option A: Single IR, Guard/Unguard are Internal-Only

Mark `Guard`/`Unguard` as compiler-internal constructors (like `free-heap`):

```agda
data IR : Type → Type → Set where
  -- ... user-facing constructors ...

  -- Internal: inserted by elaboration, not written by users
  Guard   : WellFormedF F → IR (⟦ F ⟧T A) (GuardedT F A)
  Unguard : WellFormedF F → IR (GuardedT F A) (⟦ F ⟧T A)

  -- Internal: inserted by escape analysis
  free-heap : HeapRef → IR Unit Unit
```

**Surface syntax:**
```
ana coalg    -- where coalg : A → F A (guardedness checked syntactically)
```

**Elaboration:**
```
ana coalg  ~~>  Ana wf (composeIR (Guard wf) (elaborate coalg))
```

**Pros:**
- Single IR to maintain
- Precedent exists (`free-heap` is internal)
- Categorical structure preserved for proofs
- Users never write `Guard`/`Unguard`

**Cons:**
- Must carefully document which constructors are user-facing
- Error messages might leak internal types

### Option B: Two-Level IR (Surface IR → Core IR)

```
┌─────────────────────────────────────────────────────────────┐
│  Surface IR                                                  │
│  - Ana : (A → ⟦ F ⟧T A) → A → ν F  (guardedness as check)   │
│  - No GuardedT, Guard, Unguard                              │
└─────────────────────────────────────────────────────────────┘
                           ↓ translation
┌─────────────────────────────────────────────────────────────┐
│  Core IR (current Once.CCC.IR)                              │
│  - Ana : IR A (GuardedT F A) → IR A (ν-type F)              │
│  - Guard, Unguard for categorical completeness              │
└─────────────────────────────────────────────────────────────┘
```

**Pros:**
- Clean separation of user-facing vs internal concerns
- Surface IR is simpler, easier to document
- Core IR has full categorical structure for proofs

**Cons:**
- Two IRs to maintain and keep in sync
- Translation pass adds complexity
- Which IR do optimizations work on?

### Option C: Hide GuardedT Entirely from Users

The type `GuardedT F A` itself becomes internal:

- Users write coalgebras with type `A → F A`
- Surface-level `ana` has type `(A → F A) → A → ν F`
- Guardedness is checked syntactically at elaboration time
- IR-level `Ana` still uses `GuardedT` internally

**Pros:**
- Cleanest user experience
- `GuardedT` never appears in user type signatures or errors

**Cons:**
- Type errors for non-guarded coalgebras need special handling
- How to express the constraint that the coalgebra must be guarded?

---

## Key Design Questions

### 1. Should `GuardedT` appear in user-visible types?

**If yes:**
- Type signatures are explicit about guardedness
- But users must understand an extra concept
- Error messages might be confusing

**If no:**
- Cleaner user experience
- Must handle guardedness errors specially
- Surface type of `ana` would be `(A → F A) → A → ν F` with implicit constraint

### 2. How should guardedness be checked?

**Option 2a: Syntactic check at surface level**
```
-- Guarded: constructor at top
λ n → (n, n + 1)           ✓  pair at top
λ n → inl (n + 1)          ✓  injection at top
λ xs → (head xs, tail xs)  ✓  pair at top

-- Not guarded: computation at top
λ n → if n > 0 then (n, n-1) else (0, 0)   ✗  conditional at top
λ n → f n                                   ✗  function call at top
```

**Option 2b: Check after elaboration**
- Elaborate the coalgebra to IR
- Check if the result is "obviously guarded"
- This might catch more cases but is less predictable

### 3. What about compositions involving `Out`?

Consider:
```
-- User writes:
foo = ana (λ stream → let (h, t) = out stream in (h + 1, t))
```

Here `out stream` produces `⟦ F ⟧T (ν F)`, then we rebuild a guarded value.

- Should this require explicit `Guard`?
- Or should the compiler auto-insert `Guard` when the result is a constructor?

### 4. Error messages for non-guarded coalgebras

When someone writes:
```
bad = ana (λ n → if n > 0 then (n, n-1) else (0, 0))
```

What should the error say?

**Option 4a: Mention GuardedT**
```
Error: Expected type `GuardedT (K Int ⊗ Id) Int`
       but the expression has type `Int * Int`

Hint: The coalgebra must be guarded (constructor at top level)
```

**Option 4b: Custom guardedness error**
```
Error: Coalgebra is not guarded

The expression:
    if n > 0 then (n, n-1) else (0, 0)

has a conditional at the top level. For productive corecursion,
the coalgebra must produce a constructor (pair, inl, or inr)
before any computation.

Consider restructuring to:
    (if n > 0 then n else 0, if n > 0 then n-1 else 0)
```

---

## Recommendation

**Option A with Option C characteristics:**

1. **Single IR** with `Guard`/`Unguard` as internal constructors
2. **`GuardedT` hidden from users** — surface type signatures use `F A`
3. **Syntactic guardedness check** at elaboration time
4. **Custom error messages** that explain guardedness without mentioning `GuardedT`

The IR remains categorically complete for proofs, while users get a clean experience:

```
-- User writes (surface syntax)
streamFrom : Nat → Stream Nat
streamFrom = ana step
  where step n = (n, n + 1)

-- Compiler checks: step is guarded (pair at top)

-- Elaborates to (internal IR)
streamFrom = Ana wf (Guard wf ∘ step')
  where step' = ... elaborated IR for step ...
```

---

## Implementation Sketch

### Guardedness Predicate (Surface AST)

```agda
-- Check if an expression is syntactically guarded
data IsGuarded : SurfaceExpr → Set where
  guarded-pair : IsGuarded e₁ → IsGuarded e₂ → IsGuarded (Pair e₁ e₂)
  guarded-inl  : IsGuarded e → IsGuarded (Inl e)
  guarded-inr  : IsGuarded e → IsGuarded (Inr e)
  guarded-let  : IsGuarded body → IsGuarded (Let x e body)  -- let is ok if body is guarded
  guarded-any  : IsGuarded e  -- base case: any expr in non-recursive position
```

### Elaboration Rule for Ana

```
Γ ⊢ coalg : A → F A
IsGuarded coalg
────────────────────────────────────
Γ ⊢ ana coalg ~~> Ana wf (Guard wf ∘ ⟦coalg⟧)
```

### Integration with OCP-0003

Add a section to OCP-0003 explaining:
1. `Guard`/`Unguard` are IR-level constructs for categorical completeness
2. They are **not** exposed in surface syntax
3. Elaboration inserts them based on syntactic guardedness checking
4. User-facing error messages explain guardedness without mentioning `GuardedT`

---

## Open Questions

1. Should `Guard`/`Unguard` be marked specially in the IR definition, or just documented?

2. How does this interact with the bootstrap verifier (OCP-0004)? The verifier works on IR, so it will see `Guard`/`Unguard`.

3. What about direct IR manipulation (macros, metaprogramming)? Should power users have access to `Guard`/`Unguard`?

4. How do we handle guardedness for more complex functors? E.g., `ν (K (A → B) ⊗ Id)` where the K contains a function type?

---

## Next Steps

1. Discuss and refine this design
2. Update OCP-0003 with the chosen approach
3. Implement syntactic guardedness checking
4. Add custom error messages for guardedness failures
