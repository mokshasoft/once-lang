# X86v3 Implementation Status

**Last Updated:** 2026-02-18
**Branch:** x86-arch-clean

## Overview

X86v3 backend with correctness proofs for SlotMachine IR execution.

## Completed Tasks

### Task 6: Add new IR handler modules (COMPLETE)

All sum and recursive type IR handlers are implemented in `IR/SumFixWF.agda`:

| Handler | Status | Description |
|---------|--------|-------------|
| `run-initial` | Done | Absurd elimination (trivial via ⊥ pattern match) |
| `run-unfold` | Done | Dereference fold pointer to extract unfolded value |
| `run-inl` | Done | Inject left into sum type (A ⊕ B) |
| `run-inr` | Done | Inject right into sum type (A ⊕ B) |
| `run-fold` | Done | Wrap value in recursive type (Fix F) |
| `run-case` | Done | Case analysis on sum types with recursive dispatch |

Dispatcher.agda now imports SumFixWF and uses these implementations.

### Already Done: type-slots and ir-stack-requirement

- `type-slots : Type → ℕ` defined in Types.agda (unboxed sizes)
- `ir-stack-requirement` uses `type-slots` for allocation

## Current Issue: Capacity Formula Mismatch

The Dispatcher uses `pair-slots * ir-size` for capacity bounds, but `ir-stack-requirement` uses `type-slots`. This causes the postulates in SumFixWF:

**In SumFixWF.agda:**
- `sum-slots-bound`: type-slots (A ⊕ B) ≤ pair-slots * ir-size inl-ir
- `sucLoc-sum-in-range`: suc n < n + type-slots (A ⊕ B)
- `alloc-slots-eq`: proof irrelevance for allocation state equality
- `fix-slots-bound`: type-slots (Fix F) ≤ pair-slots * ir-size fold-ir

**In ApplyWF.agda:**
- `slot-bounded-apply`: body runs in same frame, requires architecture fix

## Next Step: Fix Capacity Formula

**Option A: Change Dispatcher to use ir-stack-requirement directly**
- Replace `pair-slots * ir-size` with `ir-stack-requirement`
- This matches what the handlers actually allocate
- Eliminates sum-slots-bound and fix-slots-bound postulates

**Option B: Prove the postulates for current (boxed) representation**
- For boxed: type-slots (A ⊕ B) = 2, type-slots (Fix F) = 1
- pair-slots * ir-size = 2 * 1 = 2, so bounds hold
- But this assumes boxed representation

**Recommended: Option A** - Align capacity formula with actual allocation

## File Structure

```
Once/Backend/X86v3/
├── IR.agda                    # IR language definition
├── Types.agda                 # Type definitions with type-slots
├── Validity.agda              # ValidAt predicate
├── ClosureWellFormed.agda     # ValidAtWF with closure body proofs
├── Dispatcher.agda            # Main dispatcher (imports all IR handlers)
├── Allocation.agda            # Stack allocation
├── FrontierLemma.agda         # Frontier invariant lemmas
├── ValidityWriteLemma.agda    # Validity preservation under writes
├── WriteOps.agda              # Write operations
├── IRResult.agda              # IRResultAWF record
├── DispatcherArithmeticLemma.agda  # Capacity arithmetic
└── IR/
    ├── SimpleWF.agda          # id, fst, snd, terminal
    ├── ComposeWF.agda         # compose (g ∘ f)
    ├── PairWF.agda            # pair ⟨ f , g ⟩
    ├── CurryWF.agda           # curry f
    ├── ApplyWF.agda           # apply
    └── SumFixWF.agda          # inl, inr, case, initial, fold, unfold (NEW)
```

## Key Commits

1. `edf8a23` - Add run-inl and run-inr implementations
2. `301127c` - Add run-fold and run-case implementations
3. `c813d7b` - Replace sum/fix postulates with SumFixWF module

## Next Steps (Priority Order)

1. **Fix capacity formula** - Change Dispatcher from `pair-slots * ir-size` to `ir-stack-requirement`
   - This eliminates sum-slots-bound, fix-slots-bound postulates
   - Aligns capacity with actual allocation

2. **Resolve slot-bounded-apply** - Apply body execution issue
   - Body can consume more stack than apply's static requirement
   - Options: new frame for body, or accept reclamation semantics

3. **Migrate to Once.IR** (optional) - Use main IR instead of simplified X86v3 IR

## Build Commands

```bash
# Type-check specific module
make agda MODULE=Once/Backend/X86v3/Dispatcher.agda

# Type-check SumFixWF
make agda MODULE=Once/Backend/X86v3/IR/SumFixWF.agda

# Check for postulates
grep -rn "postulate" formal/Once/Backend/X86v3/
```

## Notes

- All IR handlers now have full validity proofs (ValidAtWF)
- Termination proven via well-founded recursion on ir-size
- RecDispatcherWF pattern enables recursive dispatch within case branches
- Reclamation semantics allow stack reuse after sub-IR execution
