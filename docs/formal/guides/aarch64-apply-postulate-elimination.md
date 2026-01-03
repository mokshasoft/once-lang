# AArch64 Apply Postulate Elimination Guide

**Author**: Analysis from Phase 5 investigation (2026-01-03)
**Status**: Proposed solution, ready for prototyping
**Goal**: Eliminate the final `apply-produces-result` postulate from AArch64 verification

## Executive Summary

The AArch64 backend has **2 remaining postulates**:
1. `sp-bound-after-stack-op` - **Acceptable** runtime assumption
2. `apply-produces-result` - **Can be eliminated** with architectural changes

This guide documents the complete path to eliminating postulate #2, achieving full verification modulo justified runtime assumptions.

## The Problem

### Current Architecture

The modular proof system uses a uniform return type for all IR terms:

```agda
run-ir-star-at-offset : (ir : IR i A B) → ... →
  ∃[ s' ] IRStarResult ir prog s s' x offset
```

**Key issue**: When `curry` executes, it produces a `CurryResultS` with a `closure-wf-s` field proving the closure is well-formed. However, `run-curry-star-direct-compat` **discards** this proof when converting to the uniform `IRStarResult` type.

### Where the Proof is Lost

**File**: `Once/Backend/AArch64/Correct/MutualIR.agda`
**Function**: `run-curry-star-direct-compat` (lines 2607-2650)

```agda
run-curry-star-direct-compat f prefix suffix x s ... =
  s-final , ir-result
  where
    -- Line 2626: GET the CurryResultS with closure-wf-s
    curry-res : CurryResultS f prog s s-final (encode x) (length prefix)
    curry-res = proj₂ (run-curry-star-direct f ...)

    -- Lines 2632-2640: DISCARD closure-wf-s, convert to IRStarResult
    ir-result : IRStarResult (curry f) prog s s-final x (length prefix)
    ir-result = record
      { ir-star = CurryResultS.curry-star curry-res
      ; ir-halted = CurryResultS.curry-halted curry-res
      ; ... -- All fields EXCEPT closure-wf-s
      }
```

### Why Apply Needs the Proof

The `apply` combinator calls `apply-produces-result` postulate because it doesn't know where the closure came from. However, `run-apply-with-wf` **already exists** and can prove apply correctness **if** given a `ClosureWellFormed` proof.

**The gap**: When compose executes `compose (curry f) apply`:
1. Curry produces closure → generates `closure-wf-s` proof → **discarded**
2. Apply executes → needs `closure-wf` proof → **missing** → uses postulate

## The Solution: Variant Return Types

### Core Idea

Change `run-ir-star-at-offset` to return a **variant type** that preserves curry-specific information:

```agda
data IRResultVariant {i A B} (ir : IR i A B) (prog : Program)
                     (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set where
  -- Curry returns CurryResultS with closure-wf-s
  CurryVariant : ∀ {i' C} {f : IR i' (A * B) C} →
                 CurryResultS f prog s s' (encode x) offset →
                 IRResultVariant (curry f) prog s s' x offset

  -- All other IR terms return standard IRStarResult
  OtherVariant : IRStarResult ir prog s s' x offset →
                 IRResultVariant ir prog s s' x offset
```

### Key Properties

1. **Type Safety**: Pattern matching on `CurryVariant` gives you the specific `CurryResultS` with `closure-wf-s`
2. **Backward Compatible**: Non-curry terms use `OtherVariant` with standard `IRStarResult`
3. **Composable**: Compose/pair/case can pattern-match and thread proofs

### Threading Through Combinators

#### Compose Example

```agda
run-compose-star-direct f g prefix suffix x s ... =
  case f-variant of
    -- If f is curry, we have closure-wf!
    CurryVariant curry-res →
      case g of
        -- If g is apply, use the proof!
        apply → run-compose-curry-apply f curry-res suffix x s ...
        -- Otherwise, normal compose
        _ → normal-compose f-variant g-result

    -- f is not curry, normal compose
    OtherVariant f-res → normal-compose f-res g-result
```

Where `run-compose-curry-apply` uses `run-apply-with-wf` with the `closure-wf-s` from `curry-res`.

#### Pair Example

```agda
run-pair-star-direct f g prefix suffix x s ... =
  let f-variant = run-ir-star-at-offset f ...
      g-variant = run-ir-star-at-offset g ...
  in case (f-variant , g-variant) of
    -- Either component could be curry
    (CurryVariant f-curry, _) → track-closure-wf-from-f f-curry
    (_, CurryVariant g-curry) → track-closure-wf-from-g g-curry
    _ → normal-pair
```

#### Case Example

Similar to pair - either branch can produce a curry with closure-wf.

## Implementation Plan

### Phase 1: Define Variant Types (StarBase.agda)

Add to `Once/Backend/AArch64/Correct/StarBase.agda`:

```agda
data IRResultVariant {i A B} (ir : IR i A B) (prog : Program)
                     (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set where
  CurryVariant : ∀ {i' C} {f : IR i' (A * B) C} →
                 CurryResultS f prog s s' (encode x) offset →
                 IRResultVariant (curry f) prog s s' x offset

  OtherVariant : IRStarResult ir prog s s' x offset →
                 IRResultVariant ir prog s s' x offset

-- Helper to extract base IRStarResult from any variant
variant-to-ir-result : IRResultVariant ir prog s s' x offset →
                       IRStarResult ir prog s s' x offset
variant-to-ir-result (CurryVariant curry-res) = curry-res-to-ir-result curry-res
variant-to-ir-result (OtherVariant ir-res) = ir-res
```

### Phase 2: Update Mutual Block Signature (MutualIR.agda)

Change return type:

```agda
-- OLD:
run-ir-star-at-offset : (ir : IR i A B) → ... →
  ∃[ s' ] IRStarResult ir prog s s' x offset

-- NEW:
run-ir-star-at-offset : (ir : IR i A B) → ... →
  ∃[ s' ] IRResultVariant ir prog s s' x offset
```

### Phase 3: Update Curry Case

**Delete** `run-curry-star-direct-compat` (which discards closure-wf).

**Modify** curry case to return `CurryVariant`:

```agda
run-ir-star-at-offset (curry {_} {A} {B} {C} f) prefix suffix x s ... =
  s-final , CurryVariant curry-res
  where
    s-final = proj₁ (run-curry-star-direct f ...)
    curry-res = proj₂ (run-curry-star-direct f ...)  -- Keep CurryResultS!
```

### Phase 4: Update Non-Curry Cases

Wrap in `OtherVariant`:

```agda
run-ir-star-at-offset (apply {_} {A} {B}) prefix suffix x s ... =
  s-final , OtherVariant ir-res
  where
    (s-final , ir-res) = run-apply-star-direct prefix suffix x s ...

run-ir-star-at-offset (inl x) prefix suffix x s ... =
  s-final , OtherVariant ir-res
  where
    ...
```

### Phase 5: Update Compose

Add special case for `compose (curry f) apply`:

```agda
run-compose-star-direct f g prefix suffix x s ... =
  let f-variant = run-ir-star-at-offset f ...
  in case f-variant of
    CurryVariant {f = body} curry-res →
      case g of
        apply → run-compose-curry-apply body curry-res prefix suffix x s ...
        _ → run-compose-normal f-variant g ...
    OtherVariant f-res → run-compose-normal f-variant g ...
```

Where `run-compose-curry-apply` uses `run-apply-with-wf` without postulate.

### Phase 6: Update Pair and Case

Similar pattern matching to detect and thread closure-wf from either component/branch.

### Phase 7: Testing and Validation

1. Type-check the entire AArch64 proof module
2. Verify postulate count: should be 1 (`sp-bound-after-stack-op`)
3. Test that all existing proofs still work
4. Document the achievement

## Risks and Mitigations

### Risk 1: Pattern Matching Complexity

**Risk**: Agda may struggle with dependent pattern matching on IR terms in variant.

**Mitigation**: Use `with` clauses and helper functions to break down complex matches.

### Risk 2: Type Inference

**Risk**: Agda may not infer types correctly through variant conversions.

**Mitigation**: Add explicit type annotations at variant boundaries.

### Risk 3: Proof Maintenance

**Risk**: Future changes to IR require updating variant handling.

**Mitigation**: Centralize variant extraction in StarBase.agda helpers.

### Risk 4: Compilation Time

**Risk**: Mutual block is already slow; variants may increase compile time.

**Mitigation**: Keep variant handling in separate helper modules when possible.

## Expected Benefits

1. **Zero unacceptable postulates**: Only runtime assumption remains
2. **Mathematically complete**: Full verification of closure calling convention
3. **Infrastructure reuse**: Leverages existing `run-apply-with-wf` proof
4. **Soundness guarantee**: Proof that curry and apply correctly interact

## Alternative Approaches Considered

### Alternative 1: Whole-Program Proofs Only

Create separate proofs for specific compositions like `compose (curry f) apply` without changing the modular proof.

**Rejected because**: Doesn't eliminate the postulate, just provides alternatives.

### Alternative 2: Dependent Return Type

Make return type depend on the IR term constructor:

```agda
IRResultFor : (ir : IR i A B) → ...
IRResultFor (curry f) = CurryResultS ...
IRResultFor _ = IRStarResult ...
```

**Rejected because**: Extremely complex type-level programming, poor type inference.

### Alternative 3: Proof-Carrying Data

Add optional fields to IRStarResult for curry-specific data.

**Rejected because**: Type parameters of ClosureWellFormed don't match generic IRStarResult.

## Success Criteria

- [ ] Type-check completes successfully
- [ ] Postulate count reduced from 2 to 1
- [ ] `apply-produces-result` postulate eliminated
- [ ] All existing tests pass
- [ ] Documentation updated
- [ ] No new postulates introduced

## Timeline Estimate

- Phase 1 (Types): 1 hour
- Phase 2 (Signature): 0.5 hours
- Phase 3-4 (Cases): 1 hour
- Phase 5 (Compose): 2 hours
- Phase 6 (Pair/Case): 2 hours
- Phase 7 (Testing): 1 hour
- **Total**: 7.5 hours

## References

- `Once/Backend/AArch64/Correct/MutualIR.agda` - Main mutual proof block
- `Once/Backend/AArch64/Correct/ClosureWellFormed.agda` - CurryResultS definition
- `Once/Backend/AArch64/Correct/StarBase.agda` - Result type definitions
- `Once/Backend/AArch64/Postulates.agda` - Current postulate documentation
- `docs/formal/shareable-proof-refactor.md` - RISC-V precedent for major refactoring

## Conclusion

This approach provides a clean, type-safe path to eliminating the final apply postulate. The variant return type preserves curry-specific information without breaking the modular proof architecture. While invasive, the refactoring is well-scoped and builds on existing infrastructure (`run-apply-with-wf`, `CurryResultS`, `ClosureWellFormed`).

The result will be a **fully verified AArch64 backend** with only justified runtime assumptions—a significant achievement in compiler verification!
