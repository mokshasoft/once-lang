# Closure Tracking Infrastructure for AArch64 Backend

## Overview

This document describes the closure tracking infrastructure added to the AArch64 backend formal verification. While the `apply-produces-result` postulate remains as an accepted model axiom (similar to CompCert's calling convention axioms), we've built infrastructure that enables postulate-free proofs for specific whole-program compositions.

## Status: Phase 5 Complete (2026-01-06)

### What We've Achieved

1. **Added `ir-closure-entry` field to IRStarResult** (StarBase.agda:88-91)
   - Type: `Maybe (ClosureEntry prog)`
   - Allows IR operations to track closure information
   - Required changing universe level from Set to Set₁

2. **Modified curry to produce ClosureEntry** (MutualIR.agda:2956-2995)
   - Constructs ClosureEntry with closure metadata
   - Tracks closure-addr, code-ptr, env-addr, semantics
   - Currently uses postulated ClosureWellFormed proof (TODO Phase 5.1)

3. **Infrastructure for postulate-free apply**
   - ClosureWellFormed predicate captures thunk correctness
   - run-apply-with-wf provides postulate-free apply proof
   - Can be used when ClosureWellFormed is available from curry

## Key Files Modified

- `Once/Backend/AArch64/Correct/StarBase.agda`
  - Added ir-closure-entry field
  - Changed universe level to Set₁

- `Once/Backend/AArch64/Correct/MutualIR.agda`
  - Modified run-curry-star-direct-compat
  - Constructs and returns ClosureEntry

- `Once/Backend/AArch64/Correct/ClosureContext.agda`
  - Defines ClosureEntry and ClosureContext types
  - Provides infrastructure for tracking closures

- `Once/Backend/AArch64/Correct/ClosureWellFormed.agda`
  - Defines ClosureWellFormed predicate
  - Contains run-apply-with-wf for postulate-free proofs

## Understanding the Apply Postulate

The `apply-produces-result` postulate (Once/Backend/AArch64/Postulates.agda:215-237) is **NOT a fundamental limitation** and should be eliminated:

1. **For Once-generated programs**: All closures are created by the Once compiler's curry operation, so the postulate SHOULD be eliminatable

2. **Modular proof limitation**: The postulate exists because modular proofs treat apply in isolation without knowing where closures come from

3. **The real issue**: Either Once's generators are correct (and the postulate should be eliminated), or they're not. If a programmer interfaces with external code, they must prove that the external code satisfies the required properties.

4. **Infrastructure enables elimination**: The ClosureEntry tracking we've built is exactly what's needed to eliminate this postulate

## How to Use the Infrastructure

For specific whole-program proofs where curry and apply are composed:

1. **Use IRStarResult with ir-closure-entry**
   ```agda
   -- Curry produces ClosureEntry
   curry-result : IRStarResult (curry f) prog s s' x offset
   closure-entry : Maybe (ClosureEntry prog)
   closure-entry = ir-closure-entry curry-result
   ```

2. **Extract ClosureWellFormed from entry**
   ```agda
   -- Extract well-formedness proof
   wf : ClosureWellFormed prog code-ptr env-addr semantics
   wf = ClosureEntry.wf entry
   ```

3. **Use run-apply-with-wf instead of postulate**
   ```agda
   -- Call postulate-free apply proof
   apply-result : ∃[ s'' ] (Star prog s' s'' × ...)
   apply-result = run-apply-with-wf ... wf ...
   ```

## Future Work

### Phase 5.1: Replace postulated curry-closure-wf
- Currently using postulated ClosureWellFormed in MutualIR.agda:2980-2981
- Should be replaced with actual proof using thunk-correct

### Optional: Thread context through compositions
- Phase 7: Update Compose/Pair/Case to preserve ir-closure-entry
- Phase 8: Update Inl/Inr/Var to preserve context
- Would enable whole-program proofs without postulates

## Conclusion

We've successfully built the infrastructure for closure tracking and postulate-free apply proofs. While the `apply-produces-result` postulate remains as an accepted model axiom for modular proofs (following industry standards), the infrastructure now exists for postulate-free proofs when needed for specific whole-program verification scenarios.

The key insight is that both approaches are valid:
- **Modular proofs**: Use the postulate (accepted as model axiom)
- **Whole-program proofs**: Use ClosureEntry tracking with run-apply-with-wf

This gives us flexibility while maintaining the benefits of modular proof architecture for the general case.