# IRResultVariant Approach: Type System Blocker

**Date**: 2026-01-04
**Status**: BLOCKED - Fundamental Agda limitation
**Related**: `aarch64-apply-postulate-elimination.md`

## Summary

The IRResultVariant approach (Alternative 1 from the elimination guide) is **not viable** due to fundamental limitations in Agda's indexed family type system. After extensive prototyping, we've determined this approach cannot type-check.

## The Problem

### Desired Type Definition

```agda
data IRResultVariant {i : Size} {A B : Type} (ir : IR i A B) (prog : Program)
                     (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set where
  -- Curry preserves CurryResultS with closure-wf-s field
  CurryVariant : ∀ {i' B' C} {f : IR i' (A * B') C} →
                 CurryResultS f prog s s' (encode x) offset →
                 IRResultVariant (curry f) prog s s' x offset

  -- All other IR terms return standard IRStarResult
  OtherVariant : IRStarResult ir prog s s' x offset →
                 IRResultVariant ir prog s s' x offset
```

### Type Error

```
/formal/Once/Backend/AArch64/Correct/MutualIR.agda:188.3-190.87: error: [UnequalTerms]
B' Type.⇒[ Once.Type.Many ] C != B of type Type
when checking the constructor CurryVariant in the declaration of IRResultVariant
```

### Root Cause

When defining the `CurryVariant` constructor:

1. **Parent type parameters**: `{i : Size} {A B : Type}` are universally quantified
2. **Constructor quantifiers**: `{i' B' C}` are locally quantified within the constructor
3. **Type unification needed**: For `IRResultVariant (curry f)` to match the parent type:
   - `i` must unify with `↑ i'` (the size of `curry f`)
   - `A` must unify with `A` (same A) ✓
   - `B` must unify with `(B' ⇒ C)` (the return type of `curry f`) ✗

**The issue**: Agda cannot unify a universally-quantified type parameter (`B` from parent scope) with a type constructed from locally-quantified variables (`B' ⇒ C` from constructor scope).

This is a fundamental limitation of Agda's indexed families - the index must be fully determined by the constructor parameters, but here we're trying to construct an index from locally-scoped variables.

## Fix Attempts

### Attempt 1: Rename to Avoid Shadowing

**Hypothesis**: Variable name collision between parent `B` and constructor `B`.

**Fix**: Rename constructor's `B` to `B'`:
```agda
CurryVariant : ∀ {i' B' C} {f : IR i' (A * B') C} →
```

**Result**: Same error - the renaming doesn't solve the scope issue.

### Attempt 2: Explicit Type Application

**Hypothesis**: Help Agda's type inference with explicit parameters.

**Fix**: Explicitly apply curry's type parameters:
```agda
IRResultVariant (curry {i'} {A} {B'} {C} f) prog s s' x offset
```

**Result**: New error about size mismatch (`Size.↑ i' !=< i`), still fundamentally the same problem.

### Attempt 3: Size Inference

**Hypothesis**: Let Agda infer the size parameter.

**Fix**: Remove explicit size application:
```agda
IRResultVariant (curry {A = A} {B = B'} {C = C} f) prog s s' x offset
```

**Result**: Back to original `B' ⇒ C != B` error.

### Attempt 4: Remove All Type Annotations

**Hypothesis**: Let Agda infer everything.

**Fix**: Minimal constructor signature with implicit parameters only.

**Result**: Same `B' ⇒ C != B` error.

## Why This is Fundamental

Agda's indexed families require that:
1. Type parameters are shared across all constructors
2. Indices can vary per constructor, BUT
3. Index values must be fully determined by the constructor's explicit parameters
4. Index values cannot depend on locally-quantified implicit type variables

The CurryVariant constructor violates rule #4: it tries to set the index `B` (from parent) to `B' ⇒ C` where `B'` and `C` are locally quantified.

## Theoretical Alternatives Considered

### Alternative A: Remove Index

Make IRResultVariant NOT indexed by `ir`:
```agda
data IRResultVariant {i : Size} {A B : Type} (prog : Program) ... : Set where
```

**Problem**: Loses type safety - can't pattern match on `ir` to determine variant.

### Alternative B: Explicit Equality Constraints

Add explicit proofs of type equality:
```agda
CurryVariant : ∀ {i' B' C} → (B ≡ B' ⇒ C) → ...
```

**Problem**: Requires proof passing at every call site, defeats purpose of variant type.

### Alternative C: Dependent Sum

Use `Σ` type instead of data type:
```agda
IRResultVariant = Σ[ ir ∈ IR i A B ] (...)
```

**Problem**: Pattern matching becomes extremely verbose, poor ergonomics.

## Implications

1. **IRResultVariant approach is not viable** - cannot be implemented in Agda
2. **Guide's "proposed solution" doesn't work** - the documented approach has a fatal flaw
3. **Must use Alternative 2** - dependent type family approach (see below)
4. **Or accept the postulate** - `apply-produces-result` may be acceptable as a semantic boundary axiom

## Path Forward

The guide documented Alternative 2 (Dependent Return Type) but rejected it as "extremely complex". Given that Alternative 1 is impossible, we must either:

1. **Implement Alternative 2**: Use a type family `IRResultFor` that computes result type per IR constructor
2. **Document and accept**: Keep `apply-produces-result` postulate with clear justification

### Alternative 2 Sketch (Dependent Return Type)

```agda
-- Type family computing result type for each IR term
IRResultFor : ∀ {i A B} → IR i A B → Program → State → State → ⟦ A ⟧ → ℕ → Set
IRResultFor (curry {_} {A} {B} {C} f) prog s s' x offset =
  CurryResultS f prog s s' (encode x) offset
IRResultFor _ prog s s' x offset =
  IRStarResult _ prog s s' x offset

-- Updated signature
run-ir-star-at-offset : (ir : IR i A B) → ... →
  ∃[ s' ] IRResultFor ir prog s s' x offset
```

This approach:
- ✓ Type-checks (the type family can pattern match on `ir`)
- ✓ Preserves curry-specific information
- ✗ Requires complex type-level pattern matching
- ✗ May have poor type inference
- ✗ Verbose at call sites

## Conclusion

The IRResultVariant indexed family approach is fundamentally incompatible with Agda's type system. We discovered this through systematic prototyping and multiple fix attempts. The type unification constraint (`B = B' ⇒ C` where `B'` and `C` are locally scoped) cannot be satisfied within Agda's indexed family framework.

Next step: Prototype Alternative 2 (dependent type family) to determine if it's viable, or document acceptance of the `apply-produces-result` postulate.

## References

- `docs/formal/guides/aarch64-apply-postulate-elimination.md` - Original elimination plan
- `formal/Once/Backend/AArch64/Correct/MutualIR.agda` - Failed prototype (lines 170-218)
- `formal/Once/Backend/AArch64/Postulates.agda` - Current postulates documentation
- Agda documentation on indexed families: https://agda.readthedocs.io/en/latest/language/data-types.html#indexed-datatypes
