# X86v3 Implementation Status

**Last Updated:** 2026-02-18
**Branch:** x86-arch-clean

## Overview

Implementing "Unboxed Stack / Boxed Heap for SlotMachine + Migrate to Once.IR" plan.

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

Dispatcher.agda now imports SumFixWF and uses these implementations (no more postulates for sum/fix).

## Current Postulates

### Design-Level Postulates (to be resolved with unboxed stack)

**In SumFixWF.agda:**
- `sum-slots-bound`: type-slots (A ⊕ B) ≤ pair-slots * ir-size inl-ir
- `sucLoc-sum-in-range`: suc n < n + type-slots (A ⊕ B)
- `alloc-slots-eq`: proof irrelevance for allocation state equality
- `fix-slots-bound`: type-slots (Fix F) ≤ pair-slots * ir-size fold-ir

These highlight the tension between fixed `pair-slots * ir-size` capacity formula and type-dependent slot allocation.

**In ApplyWF.agda:**
- `slot-bounded-apply`: body runs in same frame, requires architecture fix

## Remaining Plan Steps

### Step 1: Design Document (TODO)
Write `unboxed-stack-design.md` documenting:
- Memory representation changes (boxed → unboxed)
- type-slots function design
- Hybrid approach (stack unboxed, heap boxed)
- ValidAt changes for unboxed pairs

### Step 2: Add type-slots to Once/Type.agda (PARTIAL)
`type-slots` already exists in `X86v3/Types.agda`. Need to:
- Verify it handles all types correctly
- Possibly move to main Once/Type.agda

### Step 3: Migrate X86v3 to Once.IR (TODO)
- X86v3/Types.agda imports from Once.Type
- X86v3/IR.agda imports from Once.IR
- Add missing IR cases (Prim, Eff, etc.)

### Step 4: Update SlotMachine for Unboxed Values (TODO)
- Change memory representation
- Update allocation to use type-slots

### Step 5: Update Dispatcher and IR Handlers (TODO)
- Use type-slots instead of pair-slots
- Handle unboxed value layout

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

1. **Resolve capacity postulates** - Either:
   - Prove them for boxed representation (type-slots ≤ 2)
   - Or wait until unboxed stack implementation

2. **Write design document** - Document unboxed stack approach

3. **Migrate to Once.IR** - Use main IR instead of simplified X86v3 IR

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
