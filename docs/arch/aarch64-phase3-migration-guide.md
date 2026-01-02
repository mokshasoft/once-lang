# AArch64 Phase 3: Fuel-to-Star Migration Guide

**Status**: In Progress
**Created**: 2026-01-02
**Scope**: Convert ~4,779 lines of fuel-based proofs to Star-based proofs

## Executive Summary

Phase 3 involves converting AArch64's IR correctness proofs from fuel-based execution (`exec n`) to Star-based execution (reflexive-transitive closure). This follows RISC-V's successful migration pattern.

**Key Benefit**: Eliminates fuel arithmetic, making composition trivial via `star-trans`.

**Estimated Effort**: 1-2 weeks (based on RISC-V migration timeline)

## Current State Assessment

### Infrastructure (✅ Complete)
- ✅ `Common.Star` imported (Phase 1, commit 2fedb6f)
- ✅ `Common.StackAnalysis` integrated (Phase 2, commit 5aaeb9e)
- ✅ `StarBase.agda` defines `IRStarResult` record type
- ✅ `Star.agda` has bridge lemmas (`exec-to-star`, `star-to-exec`)

### IR Proof Modules (❌ Need Conversion)

| Module | Lines | Status | Priority | Complexity |
|--------|-------|--------|----------|------------|
| StatefulCompose.agda | 170 | ❌ Fuel-based | HIGH | Low |
| Apply.agda | 268 | ❌ Fuel-based | HIGH | Medium |
| Compose.agda | 306 | ❌ Fuel-based | HIGH | Medium |
| Curry.agda | 309 | ❌ Fuel-based | MEDIUM | High |
| Case.agda | 510 | ❌ Fuel-based | HIGH | Medium |
| StatefulProducers.agda | 630 | ❌ Fuel-based | LOW | Low |
| Pair.agda | 913 | ❌ Fuel-based | MEDIUM | High |
| StatefulConsumers.agda | 1673 | ❌ Fuel-based | LOW | Medium |
| **TOTAL** | **4779** | | | |

## Pattern: Fuel-Based vs Star-Based

### Current Fuel-Based Pattern (❌ To Replace)

```agda
-- From Compose.agda (lines 198-219)
record ComposeFResult {i} {A B C : Type} (f : IR i A B) (g : IR i B C)
                      (prefix suffix : Program)
                      (ctx : ComposeContext f g prefix suffix)
                      (s s-after : State) (x : ⟦ A ⟧) : Set where
  field
    -- Execution with FUEL
    f-exec : exec (len-f ctx) (prog ctx) s ≡ just s-after

    -- Not halted
    f-halted : halted s-after ≡ false

    -- PC, registers, etc.
    f-pc : pc s-after ≡ length prefix +ℕ len-f ctx
    f-x0 : readReg (regs s-after) x0 ≡ encode (eval f x)
    ...
```

**Problems:**
- Requires explicit fuel values (`len-f ctx`)
- Composition needs fuel arithmetic: `exec (n +ℕ m)`
- Must prove fuel is sufficient
- Complex chaining via `exec-chain` lemma

### Target Star-Based Pattern (✅ Goal)

```agda
-- From RISC-V Compose.agda (lines 130-151)
assemble-compose-result : ∀ {i A B C} (f : IR i A B) (g : IR i B C)
                          (prefix suffix : Program) (x : ⟦ A ⟧) (s sf sg : State) →
  let ctx = make-compose-context f g prefix suffix in
  let open ComposeContext ctx in
  (r1 : IRStarResult f prog s sf x (length prefix)) →
  (r2 : IRStarResult g prog sf sg (eval f x) (length prefix-g)) →
  IRStarResult (g ∘ f) prog s sg x (length prefix)
assemble-compose-result {_} {A} {B} {C} f g prefix suffix x s sf sg r1 r2 = record
  { ir-star = star-trans (ir-star r1) (ir-star r2)  -- TRIVIAL CHAINING!
  ; ir-halted = ir-halted r2
  ; ir-pc = ... -- arithmetic proof
  ; ir-x0 = ir-x0 r2
  ; ir-x20 = trans (ir-x20 r2) (ir-x20 r1)  -- chain preservation
  ; ...
  }
```

**Benefits:**
- No fuel! Just `Star prog s s'`
- Composition is transitivity: `star-trans`
- Clean compositional structure
- Bridge lemmas handle exec boundaries

## Migration Strategy

### Phase 3A: Foundation Updates (Est: 2-3 days)

1. **Update Foundation.agda**
   - Mark fuel-based lemmas as deprecated (add comments)
   - Keep them for backwards compatibility during migration
   - Add Star-based versions alongside

2. **Create AArch64-specific StarBase runners**
   - Port base cases from RISC-V: `run-id-star`, `run-terminal-star`, etc.
   - Adapt register conventions (x0 vs a0, x20/x21 vs s1/s2)
   - Add StackInvariant and X29Invariant tracking

### Phase 3B: Simple Modules First (Est: 2-3 days)

**Priority Order:**
1. StatefulCompose.agda (170 lines) - Simplest
2. Apply.agda (268 lines) - Well-defined
3. Compose.agda (306 lines) - Core pattern

**For each module:**
1. Replace result records with `IRStarResult`
2. Replace `exec n` with `Star prog s s'`
3. Use `star-trans` for composition
4. Update callers in MutualIR.agda

### Phase 3C: Complex Modules (Est: 3-5 days)

**Order:**
1. Case.agda (510 lines) - Branching
2. Curry.agda (309 lines) - Closures (tricky!)
3. Pair.agda (913 lines) - Large but systematic
4. StatefulProducers.agda (630 lines)
5. StatefulConsumers.agda (1673 lines) - Largest, save for last

### Phase 3D: Integration (Est: 1-2 days)

1. Update MutualIR.agda to use Star-based proofs
2. Remove fuel-based fallbacks from Foundation.agda
3. Type-check entire backend: `make aarch64`
4. Document remaining postulates for Phase 4

## Code Transformation Examples

### Example 1: Simple Record Conversion

**Before (Fuel-based):**
```agda
record ComposeFResult ... where
  field
    f-exec : exec (len-f ctx) (prog ctx) s ≡ just s-after
    f-halted : halted s-after ≡ false
    f-pc : pc s-after ≡ length prefix +ℕ len-f ctx
    f-x0 : readReg (regs s-after) x0 ≡ encode (eval f x)
```

**After (Star-based):**
```agda
-- Use IRStarResult directly! No custom record needed.
-- IRStarResult f prog s s' x offset has all these fields:
--   ir-star   : Star prog s s'
--   ir-halted : halted s' ≡ false
--   ir-pc     : pc s' ≡ offset +ℕ compile-length f
--   ir-x0     : readReg (regs s') x0 ≡ encode (eval f x)
--   ir-x20, ir-x21, ir-x29, ir-x30 : preserved registers
--   ir-sp, ir-mem-x21, ir-mem-x29, etc.
```

### Example 2: Composition

**Before (Fuel arithmetic):**
```agda
-- Must prove: exec (n +ℕ m) prog s ≡ just s''
compose-proof f g s =
  let (s', f-result) = run-f f s
      n = len-f f
      (s'', g-result) = run-g g s'
      m = len-g g
  in exec-chain n m prog s s' s''
       (f-exec f-result)
       (f-halted f-result)
       (g-exec g-result)
```

**After (Transitivity):**
```agda
compose-proof f g s =
  let (s', res-f) = run-f-star f s
      (s'', res-g) = run-g-star g s'
  in record
    { ir-star = star-trans (ir-star res-f) (ir-star res-g)
    ; ...  -- rest is just field projection
    }
```

## Key Differences: AArch64 vs RISC-V

### Register Conventions
| Property | RISC-V | AArch64 |
|----------|--------|---------|
| Input/Output | `a0` | `x0` |
| Callee-saved #1 | `s1` | `x20` |
| Callee-saved #2 | `s2` | `x21` |
| Frame pointer | (implicit) | `x29` |
| Return address | `ra` | `x30` |
| Stack pointer | `sp` | SP (via `readSP`) |

### IRStarResult Fields

**RISC-V has:**
```agda
ir-s1      : readReg (regs s') s1 ≡ readReg (regs s) s1
ir-s2      : readReg (regs s') s2 ≡ readReg (regs s) s2
ir-ra      : readReg (regs s') ra ≡ readReg (regs s) ra
ir-sp-delta : ℕ
ir-mem-preserved : ∀ n → readMem (memory s') (readReg (regs s) sp +ℕ n) ≡ ...
```

**AArch64 has:**
```agda
ir-x20     : readReg (regs s') x20 ≡ readReg (regs s) x20
ir-x21     : readReg (regs s') x21 ≡ readReg (regs s) x21
ir-x29     : readReg (regs s') x29 ≡ readReg (regs s) x29
ir-x30     : readReg (regs s') x30 ≡ readReg (regs s) x30
ir-sp      : readSP (regs s') ≤ readSP (regs s)  -- Stack grows down
ir-mem-x21 : readMem (memory s') (readReg (regs s) x21) ≡ ...
ir-mem-x29 : readMem (memory s') (readReg (regs s) x29) ≡ ...
ir-stack-inv : StackInvariant s'
ir-x29-inv   : X29Invariant s'
ir-sp-bound  : readSP (regs s') > 16
```

**Key Insight**: AArch64 has MORE invariants (StackInvariant, X29Invariant, sp-bound) than RISC-V. These must be threaded through all proof composition.

## Testing Strategy

For each converted module:
1. Type-check in isolation: `make agda MODULE=Once/Backend/AArch64/Correct/IR/Compose.agda`
2. Check dependent modules compile
3. Finally: `make aarch64` for full backend

**Incremental validation prevents cascading errors.**

## Success Criteria

- [ ] All 8 IR proof modules use `IRStarResult`
- [ ] `MutualIR.agda` compiles without fuel-based lemmas
- [ ] `make aarch64` succeeds
- [ ] No new postulates added (only convert existing proofs)
- [ ] Code reduction: expect ~200-300 line reduction (similar to Phase 1's 120-line reduction)

## Lessons from RISC-V Migration

1. **Start with simplest modules** - Build confidence and patterns
2. **Keep fuel-based versions** during transition for reference
3. **Bridge lemmas are essential** - `exec-to-star` and `star-to-exec` at boundaries
4. **Composition is trivial** - The main win is `star-trans` vs fuel arithmetic
5. **Type errors cascade** - Fix from bottom up (simplest → complex)

## Next Steps

When resuming Phase 3:

1. **Start with StatefulCompose.agda** (170 lines)
   - Read RISC-V's IR/Compose.agda as reference
   - Convert `ComposeFResult` → `IRStarResult`
   - Replace `exec (len-f ctx)` → `Star prog s s'`
   - Use `star-trans` for chaining

2. **Then Apply.agda** (268 lines)
   - Similar pattern, slightly more complex

3. **Then Compose.agda** (306 lines)
   - Core compose pattern with nop handling

## References

- **Phase 1 Commit**: 2fedb6f (Common.Star import, 120-line reduction)
- **Phase 2 Commit**: 5aaeb9e (StackAnalysis integration)
- **RISC-V Pattern**: `formal/Once/Backend/RiscV64/Correct/IR/Compose.agda` (lines 130-200)
- **AArch64 StarBase**: `formal/Once/Backend/AArch64/Correct/StarBase.agda` (IRStarResult definition)
- **Prime Directive**: `formal/proof-instructions.md` ("Star is mandatory, fuel-based inevitably fails")

## Conclusion

Phase 3 is the most substantial migration phase, converting ~4,779 lines of proof code. While time-consuming, the pattern is well-established from RISC-V's successful migration. The result will be cleaner, more compositional proofs without fuel arithmetic.

**Recommended approach**: Dedicate 1-2 weeks of focused work, tackle simplest modules first, validate incrementally.
