# Compose Generator Conversion Guide: IRStarResult → IRStarResultS

**Status**: Analysis Complete - Ready for Implementation
**Estimated Effort**: 3-5 days
**Files**: `formal/Once/Backend/X86/Correct/MutualIR.agda`, `formal/Once/Backend/X86/Correct/IR/Compose.agda`

---

## Executive Summary

This guide documents the complete conversion of `run-compose-star-direct` from using abstract `IRStarResult` (with encoding postulates) to concrete `IRStarResultS` (with validity predicates). This is Step 1.1 of the X86-64 backend finalization plan.

**Goal**: Eliminate reliance on `encode` postulates by proving actual memory structure.

---

## Type System: Before vs After

### Current (IRStarResult)
```agda
record IRStarResult (ir : IR i A B) (prog : Program) (s s' : State) (x : ⟦ A ⟧) (offset : ℕ)
  field
    ir-rax : readReg (regs s') rax ≡ encode (eval ir x)  -- ❌ Abstract encode!
```

### Target (IRStarResultS)
```agda
record IRStarResultS (ir : IR i A B) (prog : Program) (s s' : State) (addr-out : Word) (offset : ℕ)
  field
    ir-rax-s : readReg (regs s') rax ≡ addr-out  -- ✅ Concrete address!
    -- PLUS validity predicates proving memory structure
```

**Key Difference**: `IRStarResultS` uses actual addresses + validity predicates instead of abstract `encode`.

---

## Validity Predicates (MemoryValid.agda:74-100)

### PairAtS - Proves pair in memory
```agda
record PairAtS (addr-a addr-b addr-pair : Word) (m : Memory) : Set
  field
    fst-valid : readMem m addr-pair ≡ just addr-a
    snd-valid : readMem m (addr-pair +ℕ 8) ≡ just addr-b
```
**Proven from**: Write operations during pair allocation

### InlAtS / InrAtS - Proves sum in memory
```agda
record InlAtS (addr-val addr-sum : Word) (m : Memory) : Set
  field
    tag-valid : readMem m addr-sum ≡ just 0
    val-valid : readMem m (addr-sum +ℕ 8) ≡ just addr-val
```
**Proven from**: Write operations during inl/inr construction

---

## Current Implementation Analysis

### run-compose-star-direct (MutualIR.agda:333-380)

**Structure**:
```agda
run-compose-star-direct f g prefix suffix x s ... →
  -- Step 1: Execute f
  step-f : ∃[ s1 ] IRStarResult f ... x ...
  step-f = run-ir-star-at-offset f ... x ...  -- Line 351

  -- Step 2: Transfer rdi
  tr : TransferResult f g prefix suffix x s s1
  tr = exec-compose-transfer f g ... r1  -- Line 358

  -- Step 3: Execute g
  step-g : ∃[ s3 ] IRStarResult g ... (eval f x) ...
  step-g = run-ir-star-at-offset g ... (eval f x) ...  -- Lines 374-377

  -- Assemble final result
  s3 , assemble-compose-result f g ... r1 tr r3 refl  -- Line 343
```

**Dependencies**:
1. `run-ir-star-at-offset` - Recursive call (mutual)
2. `exec-compose-transfer` - Helper in IR/Compose.agda (line 147)
3. `assemble-compose-result` - Helper in IR/Compose.agda

---

## Conversion Approach

### Phase 1: Update Helper Functions

#### 1.1 exec-compose-transfer → exec-compose-transfer-s
**Location**: `formal/Once/Backend/X86/Correct/IR/Compose.agda:147`

**Current Signature**:
```agda
exec-compose-transfer : ... (r1 : IRStarResult f ...) → TransferResult
```

**Target Signature**:
```agda
exec-compose-transfer-s : ... (r1-s : IRStarResultS f ... addr-f-out) → TransferResultS
  -- NEW: TransferResultS includes validity threading
```

**Changes Needed**:
- Accept `IRStarResultS` instead of `IRStarResult`
- Work with `addr-f-out : Word` instead of `encode (eval f x)`
- Return `TransferResultS` that preserves validity predicates
- Thread validity through register copy (`rdi := rax`)

**Key Insight**: Transfer just copies address - validity predicates transfer unchanged!

#### 1.2 assemble-compose-result → assemble-compose-result-s

**Target Signature**:
```agda
assemble-compose-result-s :
  ∀ f g prefix suffix s s1 s2 s3
  → (r1-s : IRStarResultS f ... addr-f-out)
  → (tr-s : TransferResultS ...)
  → (r3-s : IRStarResultS g ... addr-g-out)
  → IRStarResultS (g ∘ f) ... addr-g-out  -- Compose output = g output!
```

**Changes Needed**:
- Accept all stateful results
- Build final `IRStarResultS (g ∘ f)`
- Final validity comes from `r3-s` (g's output)
- No `encode` in result - just addresses and validity!

---

### Phase 2: Update run-compose-star-direct

**New Signature**:
```agda
run-compose-star-direct-s :
  ∀ {i A B C} (f : IR i A B) (g : IR i B C) (prefix suffix : Program) (s : State)
  → ... (preconditions, no x parameter!) ...
  → ∃[ s' addr-out ] IRStarResultS (g ∘ f) prog s s' addr-out (length prefix)
```

**Key Changes**:
1. **No semantic input `x`** - work with addresses only
2. **Return existential over address** - `∃[ s' addr-out ] ...`
3. **Recursive calls use stateful versions**:
   ```agda
   step-f-s : ∃[ s1 addr-f ] IRStarResultS f ... addr-f ...
   step-f-s = run-ir-star-at-offset-s f ...  -- Stateful!
   ```

**Implementation Pattern**:
```agda
run-compose-star-direct-s f g prefix suffix s ... =
  (s3 , addr-out , result-s)
  where
    -- Step 1: Execute f (stateful)
    (s1 , addr-f , r1-s) = run-ir-star-at-offset-s f ...
    -- r1-s contains: rax = addr-f + validity predicate

    -- Step 2: Transfer (preserve validity)
    tr-s = exec-compose-transfer-s f g ... r1-s
    -- Transfers addr-f to rdi, preserves validity

    -- Step 3: Execute g (stateful, using addr-f as input)
    (s3 , addr-g , r3-s) = run-ir-star-at-offset-s g ...
    -- r3-s contains: rax = addr-g + NEW validity from g

    -- Assemble (stateful)
    addr-out = addr-g  -- Compose output = g output
    result-s = assemble-compose-result-s f g ... r1-s tr-s r3-s
```

---

## Mutual Recursion Challenge

**Problem**: Circular dependency:
- `run-compose-star-direct-s` calls `run-ir-star-at-offset-s`
- `run-ir-star-at-offset-s` calls generators (compose, pair, etc.)

**Solution**: Convert ALL generators simultaneously in mutual block

**Order**:
1. Update helper functions FIRST (exec-compose-transfer-s, assemble-compose-result-s)
2. Create `-s` versions of ALL generators (compose, pair, case, curry, apply)
3. Update `run-ir-star-at-offset-s` to call the `-s` versions
4. Type-check mutual block together

---

## Testing Strategy

### Validation Commands
```bash
cd formal

# Individual helper validation
make -j4 agda MODULE=Once/Backend/X86/Correct/IR/Compose.agda

# Mutual block (critical)
make -j4 agda MODULE=Once/Backend/X86/Correct/MutualIR.agda

# Full x86 backend
make -j4 x86-correct
```

### Success Criteria
1. ✅ `run-compose-star-direct-s` returns `IRStarResultS`
2. ✅ No `encode` in function body
3. ✅ Validity predicates thread correctly
4. ✅ Type-checks in mutual block
5. ✅ `make -j4 x86-correct` passes

---

## Working Example Pattern (from StarBase.agda:1549)

The `test-fst-stateful` E2E test demonstrates the pattern:

```agda
test-fst-stateful : ∀ {A B : Type} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  let (addr-a , st₁) = encode-s {A} a init-heap
      (addr-b , st₂) = encode-s {B} b st₁
      result = initWithInputStateful {A * B} (a , b)
      s0 = state result
      addr-pair = input-addr result
      pair-valid = initWithInputStateful-pair-valid a b  -- ✅ Validity from allocation!
  in ∃[ s' ] (Star (compile-x86 fst) s0 s'
            × halted s' ≡ false
            × readReg (regs s') rax ≡ addr-a)  -- ✅ Just address, no encode!
```

**Key Lesson**: Validity predicates come from allocation/write proofs, NOT postulates!

---

## Implementation Checklist

### Helper Functions
- [ ] Create `TransferResultS` record type
- [ ] Implement `exec-compose-transfer-s` (preserve validity)
- [ ] Implement `assemble-compose-result-s` (build final validity)
- [ ] Validate: `make -j4 agda MODULE=Once/Backend/X86/Correct/IR/Compose.agda`

### Main Generator
- [ ] Update `run-compose-star-direct` signature (remove `x`, add `addr-out`)
- [ ] Replace `run-ir-star-at-offset` with `-s` version (step 1)
- [ ] Replace transfer call with `-s` version (step 2)
- [ ] Replace `run-ir-star-at-offset` with `-s` version (step 3)
- [ ] Replace assembly with `-s` version
- [ ] Validate: `make -j4 agda MODULE=Once/Backend/X86/Correct/MutualIR.agda`

### Integration
- [ ] Update `run-ir-star-at-offset-s` to use `run-compose-star-direct-s` directly
- [ ] Remove `convert-to-stateful` bridge for compose
- [ ] Full validation: `make -j4 x86-correct`

---

## Next Steps

After completing compose conversion:
1. Apply same pattern to `run-pair-star-direct`
2. Then `run-case-star-direct` (3 variants)
3. Then `run-curry-star-direct`
4. Finally `run-apply-star-direct`

**Estimated Total**: 4-6 weeks for all 5 generators

---

## References

- **Type Definitions**: `formal/Once/Backend/X86/Correct/StarBase.agda`
  - IRStarResult: lines 60-80
  - IRStarResultS: lines 1257-1276
  - Working E2E tests: lines 1549-1763

- **Validity Predicates**: `formal/Once/Backend/X86/Correct/MemoryValid.agda`
  - PairAtS: lines 74-78
  - InlAtS: lines 84-88
  - InrAtS: lines 94-98

- **Current Implementation**: `formal/Once/Backend/X86/Correct/MutualIR.agda`
  - run-compose-star-direct: lines 333-380

- **Helpers**: `formal/Once/Backend/X86/Correct/IR/Compose.agda`
  - exec-compose-transfer: line 147
  - assemble-compose-result: (search for it)

---

**Document Version**: 1.0
**Date**: 2026-01-03
**Author**: Analysis Session - X86 Finalization Planning
