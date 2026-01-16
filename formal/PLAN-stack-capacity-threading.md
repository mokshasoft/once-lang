# Plan: Eliminate Stack Postulates via StackCapacity Threading

## Current Status (2026-01-16)

### Completed:
- [x] Phase 1: Add ir-frame-slots and ir-input-capacity to StackInstantiation.agda
- [x] Phase 2: Update ThunkResult/CurryResult records in ClosureWellFormed.agda
- [x] Phase 3a: Update StarBase.agda base cases to take StackCapacity
- [x] Phase 3b: Update Compose module to use StackCapacity
- [x] Phase 3c: Update Pair and Case parameterized modules to use StackCapacity
- [x] Phase 3d: Update MutualIR.agda base cases to convert rsp-sufficient → StackCapacity
- [x] Refactor Pair.agda: remove function definitions from where clauses (performance fix)
- [x] Add stackBase-in-stack postulate to InitState.agda (specific vs blanket)
- [x] Phase 3e: Change dispatcher signature to take StackCapacity
  - Changed `run-ir-star-at-offset-v` to take `StackCapacity s 2` instead of `rsp-sufficient`
  - Updated `run-curry-star-v`, `run-apply-star-v`, and all dispatcher cases
  - Postulate usage now consolidated at: `run-ir-star` entry point, `curry-thunk-correct-impl`
- [x] Phase 4: Update IR/Inl.agda and IR/Inr.agda to take StackCapacity
  - Changed `run-inl-star-v-auto` and `run-inr-star-v-auto` to take `StackCapacity s 4`
  - Changed `run-inl-star-v` and `run-inr-star-v` to take `StackCapacity s 4`
  - Deleted dead code: `run-inl-star` and `run-inr-star` (~920 lines combined)
  - Internal usages now derive from cap parameter (rsp-bound, rsp-region, cap2)
  - **Both files are now completely postulate-free!**
  - MutualIR derives StackCapacity s 4 from blanket postulate at call sites
- [x] Phase 5: Update IR/Curry.agda to take StackCapacity
  - Changed `run-curry-star` and `run-curry-star-v` to take `StackCapacity s 2`
  - Updated `run-curry-star-with-wf` in MutualIR.agda
  - Internal uses converted from `rsp-sufficient` to `rsp-bound` (extracted from cap)
- [x] Refactor MutualIR.agda: remove function definitions from where clauses (performance fix)
  - Added private block with `m∸n<m-when-positive` and `rsp<rsp+slot` helpers
  - Removed nested function definitions from `thunk-preserves-above-entry-rsp-proof`
  - Simplified nested where clause in `thunk-preserves-frame-proof`

### Remaining:
- [x] Phase 6b: Complete InitState postulate elimination
  - Changed `run-ir-star` to take `StackCapacity s 2` instead of `rsp > slots 2`
  - Updated `run-generator`, `codegen-x86-correct`, `compose-with-star`, etc. in Correct.agda
  - Updated `run-ir-star-whole-program`, `whole-program-correct` in WholeProgram.agda
  - Entry point now uses `initWithInput-stack-capacity` (from specific `stackBase-in-stack` postulate)
  - Blanket `rsp-in-stack-after-stack-op` no longer used at entry points
- [ ] Phase 7: Delete postulates from Postulates.agda
  - NOTE: Blanket postulates still used in 58 places across 9 internal files
  - Entry points now use specific `stackBase-in-stack` postulate instead
  - Full elimination requires threading StackCapacity through all internal operations
  - **Postulate changed**: `rsp-bound-after-stack-op` now returns `> slots 7` (was `> slots 5`) to support pair operations
  - Progress:
    - **Files now postulate-free:**
      - StarBase.agda: deleted ~377 lines of dead code (old non-vv versions)
      - IR/Inl.agda: deleted ~464 lines dead code, refactored to take StackCapacity s 4
      - IR/Inr.agda: deleted ~460 lines dead code, refactored to take StackCapacity s 4
      - IR/Compose.agda: eliminated (use ir-capacity from sub-result directly)
      - IR/Case.agda: eliminated (was unused import)
    - **Remaining files with postulate usages (58 total):**
      - IR/Apply.agda: 11 usages (complex: multiple intermediate states)
      - MutualIR.agda: 9 usages (includes inl/inr consolidated derivation)
      - IR/Curry.agda: 8 usages
      - MutualIR/Case.agda: 7 usages
      - IR/ThunkExec.agda: 7 usages
      - IR/Pair.agda: 7 usages (has mk-capacity-5 helper)
      - MutualIR/Pair.agda: 5 usages
      - Postulates.agda: 3 usages (the definitions)
      - InitState.agda: 1 usage
  - Postulate usage reduced: 85 → 58 (27 eliminated)
  - Current status: Build passes for x86-ccc-whole
- [x] Phase 8: Apply "no functions in where clauses" refactoring to X86 backend files
  - Pattern: Move function definitions from where clauses to private module-level blocks
  - Keep only simple variable bindings (val = expr) in where clauses
  - Completed refactorings:
    - IR/Inl.agda: replaced nested `n<n+8` with `m<m+n` from stdlib (2 occurrences)
    - IR/Inr.agda: replaced nested `n<n+8` with `m<m+n` from stdlib (2 occurrences)
    - StackInstantiation.agda: moved `slots-mono-≤` to private block
    - Arithmetic.agda: moved `suc-∸` to private block
  - See Pair.agda and MutualIR.agda for reference patterns

### Notes:
- Build passes in current hybrid state
- Entry points (Correct.agda, WholeProgram.agda) now use `initWithInput-stack-capacity`
  which uses the specific `stackBase-in-stack` postulate
- Blanket postulates (`rsp-in-stack-after-stack-op`, `rsp-bound-after-stack-op`)
  still used in internal files when constructing StackCapacity after state changes
- See `docs/formal/historical/lessons-learned.md` for "no functions in where clauses" rule
- **Naming convention**: Rename variables with concrete byte values (e.g., `rsp-gt-24`, `rsp-gt-16`)
  to use abstract slot-based names (e.g., `rsp-bound`, `rsp-sufficient`) since `slots n` is abstract
  and the concrete byte representation (n * 8) should not leak into proof names

---

## Goal
Eliminate two stack postulates from `Once/Backend/X86/Postulates.agda`:
- `rsp-bound-after-stack-op : ∀ (s : State) → readReg (regs s) rsp > slots 5`
- `rsp-in-stack-after-stack-op : ∀ (s : State) → region-of (readReg (regs s) rsp) ≡ stack`

## Strategy
Thread `StackCapacity` through proofs instead of using postulates. The key insight is that:
1. Each IR operation has a known stack frame requirement (`ir-frame-slots`)
2. Callers must provide sufficient capacity (`ir-input-capacity = frame-slots + output-capacity`)
3. Operations produce output capacity proof in their result

## Phase 1: Define Stack Slot Functions in StackInstantiation.agda

Add to `Once/Backend/X86/Correct/StackInstantiation.agda`:

```agda
-- Stack slots needed by each IR operation
ir-frame-slots : ∀ {A B} → IR A B → ℕ
ir-frame-slots (prim _) = 0
ir-frame-slots id = 0
ir-frame-slots (compose _ _) = 0  -- Sequence, no extra slots
ir-frame-slots (curry _) = 5     -- alloc-closure: push r15, push rbp, sub 24
ir-frame-slots apply = 3         -- call overhead: push ret addr, thunk frame
ir-frame-slots (pair _ _) = 0    -- No stack allocation
ir-frame-slots fst = 0
ir-frame-slots snd = 0
ir-frame-slots inl = 0
ir-frame-slots inr = 0
ir-frame-slots (case _ _) = 0    -- Branches don't allocate

-- Input capacity needed: frame slots + 2 for output guarantee
ir-input-capacity : ∀ {A B} → IR A B → ℕ
ir-input-capacity ir = ir-frame-slots ir +ℕ 2
```

## Phase 2: Update Record Types

### 2a. Update ThunkResult in ClosureWellFormed.agda

Change:
```agda
thunk-rsp-bound : readReg (regs s') rsp > slots 2
```
To:
```agda
thunk-capacity : StackCapacity s' 2
```

### 2b. Update CurryResult in ClosureWellFormed.agda

Change:
```agda
curry-rsp-bound : readReg (regs s') rsp > slots 2
```
To:
```agda
curry-capacity : StackCapacity s' 2
```

### 2c. Verify IRStarResultV in StarBase.agda

Already has:
```agda
ir-capacity : StackCapacity s' 2
```
No change needed.

## Phase 3: Update MutualIR.agda Dispatcher Signature

Change `run-ir-star` preconditions from:
```agda
readReg (regs s) rsp > slots 2
```
To:
```agda
StackCapacity s (ir-input-capacity ir)
```

The dispatcher will:
1. Receive `cap-in : StackCapacity s (ir-input-capacity ir)`
2. Use `StackCapacity.rsp-sufficient cap-in` where raw bounds needed
3. Use `StackCapacity.rsp-in-stack cap-in` for region proofs
4. Pass appropriate capacity to sub-operations
5. Return `ir-capacity : StackCapacity s' 2` in result

## Phase 4: Update Simple Operations (0 frame slots)

Files: `IR/Id.agda`, `IR/Fst.agda`, `IR/Snd.agda`, `IR/Inl.agda`, `IR/Inr.agda`, `IR/Prim.agda`

These operations don't allocate stack, so:
- Input: `StackCapacity s 2` (since ir-input-capacity = 0 + 2 = 2)
- Output: Same capacity (state unchanged or trivially transformed)
- Replace postulate calls with `cap-in` fields

## Phase 5: Update Stack-Allocating Operations

### 5a. IR/Curry.agda (5 frame slots)

- Input: `StackCapacity s 7` (5 + 2)
- alloc-closure pushes r15, rbp, subs 24 (3 slots)
- After allocation: prove capacity >= 2
- Output: `StackCapacity s' 2`

### 5b. IR/Apply.agda (3 frame slots)

- Input: `StackCapacity s 5` (3 + 2)
- call instruction pushes return address
- Thunk receives capacity, returns capacity
- After ret: prove capacity >= 2
- Output: `StackCapacity s' 2`

## Phase 6: Update Compose, Pair, Case

### 6a. IR/Compose.agda

- Input: capacity for first operation
- First op returns capacity
- Convert/strengthen capacity for second operation
- Second op returns final capacity
- Output: `StackCapacity s' 2`

### 6b. IR/Pair.agda

- Input: capacity for both branches
- Execute both (no stack allocation)
- Output: `StackCapacity s' 2`

### 6c. IR/Case.agda

- Input: capacity for worst-case branch
- Branch on tag
- Each branch receives capacity, returns capacity
- Output: `StackCapacity s' 2`

## Phase 7: Update Entry Point (InitState.agda)

Change:
```agda
initWithInput-rsp-sufficient : ∀ {A} (x : ⟦ A ⟧) → readReg (regs (initWithInput x)) rsp > slots 2
```
To provide initial `StackCapacity` for the main IR operation:
```agda
initWithInput-capacity : ∀ {A B} (x : ⟦ A ⟧) (ir : IR A B) →
  StackCapacity (initWithInput x) (ir-input-capacity ir)
```

The stackBase (0x7FFF0000) provides ample capacity for any reasonable ir-input-capacity.

## Phase 8: Delete Postulates

After all usages are eliminated:

1. Remove from `Once/Backend/X86/Postulates.agda`:
   - `rsp-bound-after-stack-op`
   - `rsp-in-stack-after-stack-op`

2. Remove corresponding imports from all files

## File Edit Order

1. `StackInstantiation.agda` - Add ir-frame-slots, ir-input-capacity
2. `ClosureWellFormed.agda` - Update ThunkResult, CurryResult records
3. `StarBase.agda` - Verify IRStarResultV (likely no changes)
4. `MutualIR.agda` - Update dispatcher signature and implementation
5. `IR/Id.agda`, `IR/Fst.agda`, `IR/Snd.agda`, `IR/Inl.agda`, `IR/Inr.agda`, `IR/Prim.agda` - Simple ops
6. `IR/Curry.agda` - Stack-allocating curry
7. `IR/Apply.agda` - Stack-allocating apply
8. `IR/Compose.agda` - Composition threading
9. `IR/Pair.agda` - Pair threading
10. `IR/Case.agda` - Case threading
11. `InitState.agda` - Entry point capacity
12. `WholeProgram.agda` - Update to use capacity
13. `Postulates.agda` - Delete the postulates

## Verification

After each file change, run `agda` to verify:
```bash
agda Once/Backend/X86/Correct/Correct.agda
```

## Risks and Mitigations

1. **Capacity arithmetic complexity**: May need lemmas like `n ≥ m → StackCapacity s n → StackCapacity s m`
   - Mitigation: Add these to StackInstantiation.agda as needed

2. **Recursive capacity threading**: MutualIR already threads Acc, now also threads capacity
   - Mitigation: Follow existing Acc pattern, add cap-in alongside acc

3. **WholeProgram integration**: Must provide capacity at top level
   - Mitigation: InitState already has stackBase with huge capacity

## Success Criteria

- [ ] `rsp-bound-after-stack-op` removed from Postulates.agda
- [ ] `rsp-in-stack-after-stack-op` removed from Postulates.agda
- [ ] All files compile without warnings
- [ ] No new postulates introduced
