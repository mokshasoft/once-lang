# Encoding Postulate Elimination: Implementation Plan

## Current Status

**All 18 mechanical IR correctness postulates eliminated (100%)**

Remaining work: Eliminate 10 encoding postulates using stateful validity predicates.

## Infrastructure (Complete ✅)

All necessary infrastructure exists:

### Stateful Validity Predicates (MemoryValid.agda)
```agda
-- Instead of abstract encode function:
record PairAtS (addr-a addr-b addr-pair : Word) (m : Memory) : Set where
  fst-valid : readMem m addr-pair ≡ just addr-a
  snd-valid : readMem m (addr-pair +ℕ 8) ≡ just addr-b

record InlAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  tag-valid : readMem m addr-sum ≡ just 0
  val-valid : readMem m (addr-sum +ℕ 8) ≡ just addr-val

record InrAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  tag-valid : readMem m addr-sum ≡ just 1
  val-valid : readMem m (addr-sum +ℕ 8) ≡ just addr-val
```

### Stateful Result Type (StarBase.agda:1257-1276)
```agda
record IRStarResultS {i : Size} {A B : Type} (ir : IR i A B) (prog : Program)
                     (s s' : State) (addr-out : Word) (offset : ℕ) : Set where
  field
    ir-star    : Star prog s s'
    ir-halted  : halted s' ≡ false
    ir-pc      : pc s' ≡ offset +ℕ compile-length ir
    ir-rax-s   : readReg (regs s') rax ≡ addr-out  -- ← Address, not encode!
    -- ... (rest identical to IRStarResult)
```

### Working E2E Tests (StarBase.agda:1453-1763)
- `test-fst-stateful` - Pair projection without encode-pair-fst postulate
- `test-snd-stateful` - Pair projection without encode-pair-snd postulate
- `test-inl-stateful` - Left sum creation without inl encoding postulates
- `test-inr-stateful` - Right sum creation without inr encoding postulates

All four tests demonstrate complete E2E execution with ZERO encoding postulates.

## Implementation Plan

### Phase 1: Define Stateful Mutual Runner (Week 1-2)

**Goal**: Create `run-ir-star-at-offset-s` that returns `IRStarResultS`

**Location**: `Once/Backend/X86/Correct/MutualIR.agda`

**Current signature** (line 164-172):
```agda
run-ir-star-at-offset : ∀ {i A B} (ir : IR i A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →  -- ← Uses encode
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)  -- ← Returns IRStarResult
```

**New signature** (proposed):
```agda
run-ir-star-at-offset-s : ∀ {i A B} (ir : IR i A B) (prefix suffix : Program) (addr-in : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →  -- ← Explicit address
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ addr-out ] ∃[ s' ] IRStarResultS ir prog s s' addr-out (length prefix)  -- ← Returns IRStarResultS
```

**Tasks**:
1. Copy `run-ir-star-at-offset` to `run-ir-star-at-offset-s`
2. Change input from `x : ⟦ A ⟧` to `addr-in : Word`
3. Change input precondition from `readReg (regs s) rdi ≡ encode x` to `readReg (regs s) rdi ≡ addr-in`
4. Change return type from `IRStarResult` to `IRStarResultS`
5. Stub out all cases initially (use postulates as placeholders)

### Phase 2: Thread Validity Through Simple Cases (Week 2-3)

**Goal**: Implement stateful versions for base cases

**Cases to implement** (in order of difficulty):
1. `id` - Already works (just passes address through)
2. `terminal` - Already works (returns unit = 0)
3. `fold`/`unfold` - Already work (Fix is identity at runtime)
4. `arr` - Already works (Eff = Closure at runtime)
5. `fst`/`snd` - Use `run-fst-star-s`/`run-snd-star-s` from StarBase.agda
6. `inl`/`inr` - Use `run-inl-star-s`/`run-inr-star-s` from StarBase.agda

**Example for fst**:
```agda
run-ir-star-at-offset-s (fst {A} {B}) prefix suffix addr-in s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  -- Call stateful version
  let (addr-a , s' , res) = run-fst-star-s {A} {B} prefix suffix addr-in s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  in addr-a , s' , res
```

### Phase 3: Implement Stateful Compose (Week 3-4)

**Goal**: Thread validity through composition `f >>> g`

**Current approach** (Compose.agda):
- Runs `f` to get `IRStarResult` with `ir-rax : rax ≡ encode (eval f x)`
- Transfers to setup for `g`
- Runs `g` with input `encode (eval f x)`
- Composes results

**New approach**:
- Run `f` to get `IRStarResultS` with `ir-rax-s : rax ≡ addr-mid`
- Transfer address to setup for `g`
- Run `g` with input `addr-mid` (not encode!)
- Compose results with explicit address threading

**Challenge**: Need to track that `addr-mid` is valid representation of `eval f x`

**Solution**: Add validity witness to `IRStarResultS`:
```agda
record IRStarResultS {i : Size} {A B : Type} (ir : IR i A B) (prog : Program)
                     (s s' : State) (addr-out : Word) (offset : ℕ) : Set₁ where
  field
    -- ... existing fields ...
    ir-validity : ValueAtS {B} (eval ir x-in) addr-out (memory s')  -- ← NEW
```

Where `ValueAtS` is a type family:
```agda
ValueAtS : ∀ {A : Type} → ⟦ A ⟧ → Word → Memory → Set
ValueAtS {Unit} tt addr m = addr ≡ 0
ValueAtS {A * B} (a , b) addr m = ∃[ addr-a ] ∃[ addr-b ] PairAtS addr-a addr-b addr m
ValueAtS {A + B} (inj₁ a) addr m = ∃[ addr-a ] InlAtS {A} {B} addr-a addr m
ValueAtS {A + B} (inj₂ b) addr m = ∃[ addr-b ] InrAtS {A} {B} addr-b addr m
-- ... etc for other types
```

### Phase 4: Implement Stateful Pair (Week 4-5)

**Goal**: Thread validity through `pair f g`

**Current approach** (Pair.agda):
- Setup phase: allocate stack frame
- Run `f` on left component
- Run `g` on right component
- Store both results at rsp-24 and rsp-16
- Uses `encode-pair-construct` to prove result is encoded pair

**New approach**:
- Setup phase: allocate stack frame (unchanged)
- Run `f` to get `addr-a`
- Run `g` to get `addr-b`
- Store `addr-a` and `addr-b` at allocated addresses
- Construct `PairAtS addr-a addr-b new-rsp` from memory writes
- NO POSTULATES NEEDED

**Example**:
```agda
-- After storing both components:
pair-valid : PairAtS addr-a addr-b new-rsp (memory s-final)
pair-valid = pair-at-s
  { fst-valid = mem-write-proof-a  -- From writeMem at rsp-24
  ; snd-valid = mem-write-proof-b  -- From writeMem at rsp-16
  }
```

### Phase 5: Implement Stateful Case (Week 5-6)

**Goal**: Thread validity through `case f g`

**Current approach** (Case.agda):
- Dispatch on tag at `[rdi]`
- Load value from `[rdi+8]`
- Jump to left or right branch
- Run selected branch
- Uses `encode-inl-tag`, `encode-inl-val`, `encode-inr-tag`, `encode-inr-val`

**New approach**:
- Input is `addr-sum` (explicit address)
- Dispatch on tag at `[addr-sum]`
- Load `addr-val` from `[addr-sum+8]`
- Jump to left or right branch
- Run selected branch with `addr-val`
- NO POSTULATES NEEDED (validity predicates constructed from memory reads)

### Phase 6: Update Curry and Apply (Week 6)

**Curry**: Similar to inl/inr, creates closure structure in memory

**Apply**: Already has ClosureWellFormed infrastructure for whole-program proofs

**Tasks**:
1. Create `run-curry-star-s` with `ClosureAtS` validity
2. Thread through apply (may not need changes - uses WF proofs)

### Phase 7: Remove Postulates (Week 6)

Once all cases implemented:
1. Update MutualIR exports to prefer `-s` versions
2. Verify builds pass
3. Remove encoding postulates from Once.Postulates.agda:
   - Lines 232-291 (10 postulates)
4. Update documentation

## Validation Strategy

### Incremental Testing
- After each phase, verify builds pass
- Add unit tests for each new stateful runner
- Compare results with encode-based versions

### Correctness Proof
The stateful approach is correct because:
1. Memory writes create validity predicates directly
2. Validity predicates are stronger than encoding postulates
3. Working E2E tests demonstrate completeness

### Performance Monitoring
- Track proof term size in MutualIR
- If proof terms explode, may need to factor out witnesses

## Success Criteria

1. ✅ All IR generators return `IRStarResultS`
2. ✅ Validity predicates thread through compose/pair/case
3. ✅ Full program builds without encoding postulates
4. ✅ All 10 encoding postulates removed from Once.Postulates

## Estimated Effort

- **Phase 1-2**: 2 weeks (infrastructure + simple cases)
- **Phase 3-4**: 2 weeks (compose + pair)
- **Phase 5-6**: 2 weeks (case + curry/apply)
- **Total**: 6 weeks for experienced Agda developer

## References

- **Validity Predicates**: Once/Backend/X86/Correct/MemoryValid.agda
- **IRStarResultS**: Once/Backend/X86/Correct/StarBase.agda:1257-1276
- **Working Tests**: Once/Backend/X86/Correct/StarBase.agda:1453-1763
- **Mutual Runner**: Once/Backend/X86/Correct/MutualIR.agda:162-
- **Current Encoding Postulates**: Once/Postulates.agda:228-291

## Open Questions

1. **Proof term size**: Will validity witnesses cause proof explosion?
   - Mitigation: Use erased witnesses if available
   
2. **ValueAtS design**: Should it be data family or record family?
   - Recommendation: Record family (easier to construct)

3. **Backward compatibility**: Keep encode-based versions?
   - Recommendation: Yes, via `convert-to-stateful` helper

4. **Apply postulate**: Remains for modular reasoning?
   - Yes - only needed for open programs, not closed programs
