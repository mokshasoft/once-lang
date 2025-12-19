# X86 Backend Verification Architecture

## Goal: 0 Postulates

Target: **0 postulates** in X86 verification.

**Core Principle**: Proofs should compute. Postulates are symptoms of architecture issues, not proof difficulty.

**When Stuck**: Change the architecture, not the proof. If a statement can't be proven, the statement is likely wrong - change the primitives or architecture to make it provable.

---

## Proven Foundation

The core memory axioms are **PROVEN**, not postulated:

```agda
-- PROVEN in Once.Memory.agda (concrete writeMem definition):
mem-read-write : readMem (writeMem m addr v) addr ≡ just v
mem-read-other : addr₁ ≢ addr₂ → readMem (writeMem m addr₁ v) addr₂ ≡ readMem m addr₂
```

Everything else derives from these proven theorems:
- `encode-is-alloc-addr` - PROVEN (trivially refl in Stateful.agda)
- `alloc-pair-fst/snd`, `alloc-inl-tag/val`, `alloc-inr-tag/val` - DERIVED in Encoding.agda
- HeapValid tracking - available in Encoding.agda

---

## Current Postulate Inventory (~41 total)

| Category | Count | Status |
|----------|-------|--------|
| Encoding axioms (Postulates.agda) | 11 | **DERIVE** from proven infrastructure |
| Star bridges (Star.agda) | 2 | **ELIMINATE** (prove or change architecture) |
| ExecLemmas | 4 | **ELIMINATE** |
| Correct.agda engineering | ~23 | **ELIMINATE** |
| Apply semantic | 1 | **DERIVE** from closure encoding |
| encode-injective | 1 | **DERIVE** from mem-read-write + induction |

---

## Implementation Stages

### Stage 0: Derive Encoding Axioms (HIGHEST IMPACT)

**Target**: 11 encoding axioms in `formal/Once/Postulates.agda` → DERIVED

| Axiom | Approach |
|-------|----------|
| `encode-unit` | Trivial: Unit encodes to 0 by definition |
| `encode-pair-fst` | Use `alloc-pair-fst` + HeapValid |
| `encode-pair-snd` | Use `alloc-pair-snd` + HeapValid |
| `encode-inl-tag` | Use `alloc-inl-tag` + HeapValid |
| `encode-inl-val` | Use `alloc-inl-val` + HeapValid |
| `encode-inr-tag` | Use `alloc-inr-tag` + HeapValid |
| `encode-inr-val` | Use `alloc-inr-val` + HeapValid |
| `encode-pair-construct` | Inverse of reading - use mem theorems |
| `encode-inl-construct` | Inverse of reading |
| `encode-inr-construct` | Inverse of reading |
| `encode-fix-wrap/unwrap` | Trivial by definition |
| `encode-arr-identity` | Trivial: Eff = Closure by definition |
| `encode-closure-construct` | Use Closure record fields |

**Implementation**:
1. Add `HeapValid` precondition to Correct.agda proofs
2. Use derived versions from Encoding.agda instead of axioms
3. Remove axioms from Postulates.agda once no longer used

**Verify**: `make x86-correct`

### Stage 0b: Derive encode-injective

**Target**: `encode-injective` in `formal/Once/Backend/X86/Encoding.agda`

**Approach**: If `encode x = encode y`, they're at the same address. Read memory at that address (using proven `mem-read-write`). Components must be equal, recurse.

**Verify**: `make x86-encoding`

### Stage 1: Eliminate Exec Bridge Postulates

**Target**: 2 postulates in `formal/Once/Backend/X86/Correct/Star.agda`

| Postulate | Line | Approach |
|-----------|------|----------|
| `exec-to-star` | 148 | Prove by induction on fuel |
| `exec-until-pc-to-star` | 154 | Use exec-to-star |

**Proof approach**:
```agda
exec-to-star : exec n prog s ≡ just s' → Star prog s s'
exec-to-star {zero} refl = refl*
exec-to-star {suc n} eq = ... -- induction with step analysis
```

**If blocked**: Change architecture - maybe `exec` should return a step witness instead of just final state.

**Verify**: `make agda MODULE=Once/Backend/X86/Correct/Star.agda`

### Stage 2: Prove ExecLemmas Postulates

**Target**: 3-4 postulates in `formal/Once/Backend/X86/Correct/ExecLemmas.agda`

| Postulate | Approach |
|-----------|----------|
| `runFuel≥` | Concrete: runFuel = 100000, use arithmetic |
| `compile-length>0` | Pattern match on all IR constructors |
| `exec-until-pc-to-exec` | Induction with fuel tracking |

**Verify**: `make x86-correct`

### Stage 3: Compose Bridge Postulates

**Target**: ~4 postulates in `run-ir-at-offset-compose`

Mechanical once Stage 2 complete - derive from exec-until-pc-to-exec.

**Verify**: `make x86-correct`

### Stage 4: Pair Generator Postulates

**Target**: ~6 postulates in `run-ir-at-offset-pair`

| Postulate | Approach |
|-----------|----------|
| `rsp-after-setup>16` | Arithmetic: stackBase = 2147418112 >> 56 |
| `exec-f-raw` | Derive from exec-until-pc |
| `r14-final`, `r15-final` | Track through instructions |
| `mem-final` | Use mem-read-other from Once.Memory |
| `stack-inv-final` | StackInvariant preservation |

**Verify**: `make x86-correct`

### Stage 5: Case Generator Postulates

**Target**: ~10 postulates in `run-ir-at-offset-case-inl/inr`

**Key insight**: Fuel mismatch - use `exec-until-pc` which stops at target PC.

**Verify**: `make x86-correct`

### Stage 6: Curry Generator Postulates

**Target**: ~8 postulates in `run-ir-at-offset-curry`

Track state through 6 setup instructions + thunk + jmp.

**Verify**: `make x86-correct`

### Stage 7: Arithmetic Postulates

**Target**: 2 postulates

| Postulate | File | Approach |
|-----------|------|----------|
| `∸+<-lemma` | StackInvariant.agda:93 | Arithmetic proof |
| `n-steps≤fuel` | Correct.agda:5168 | Use concrete defaultFuel |

**Verify**: `make x86-correct`

### Stage 8: Derive run-apply-seq

**Target**: `run-apply-seq` (Correct.agda:7111)

Once encoding axioms are derived (Stage 0), `run-apply-seq` follows from:
1. `encode-closure-construct` → closure at address has [env, code-ptr]
2. Step through apply instructions using derived memory properties
3. Chain exec proofs for: load pair → load closure → call thunk → return

**Verify**: `make x86-correct`

---

## Verification Commands

```bash
cd /home/whatever/Repo/mokshasoft/once-lang2/formal

# Single file test (fastest iteration)
make agda MODULE=Once/Backend/X86/Correct/Star.agda

# Per-module
make x86-star       # Star.agda only
make x86-encoding   # Encoding.agda
make x86-correct    # Correct.agda and submodules

# Full X86 backend (success criterion)
make x86
```

---

## Files to Modify

| Stage | File | Changes |
|-------|------|---------|
| 0 | `formal/Once/Backend/X86/Correct.agda` | Add HeapValid, use derived encoding proofs |
| 0 | `formal/Once/Backend/X86/Encoding.agda` | Export derived proofs |
| 0 | `formal/Once/Postulates.agda` | Remove encoding axioms |
| 0b | `formal/Once/Backend/X86/Encoding.agda` | Prove encode-injective |
| 1 | `formal/Once/Backend/X86/Correct/Star.agda` | Prove exec-to-star |
| 2 | `formal/Once/Backend/X86/Correct/ExecLemmas.agda` | Prove runFuel≥, compile-length>0 |
| 3-6 | `formal/Once/Backend/X86/Correct.agda` | Replace postulates with proofs |
| 7 | `formal/Once/Backend/X86/Correct/StackInvariant.agda` | Prove ∸+<-lemma |
| 8 | `formal/Once/Backend/X86/Correct.agda` | Derive run-apply-seq |

---

## Risk Mitigation & Philosophy

### Core Principle: Proofs Should Compute

With concrete `writeMem` and `case_of_` definitions, proofs should reduce to `refl`.
If a proof is blocked, the issue is likely the **statement** not the proof technique.

### When Stuck: Change the Architecture, Not the Proof

1. **If a statement can't be proven**: The statement is likely wrong
   - Don't add workarounds or concrete bounds
   - Change the primitives or architecture to make the statement provable
   - Example: If `runFuel≥` is needed, maybe the architecture shouldn't depend on fuel bounds

2. **If case_of_ blocks a proof**: The definition may need restructuring
   - Consider whether the function should return more information
   - Example: If `exec-to-star` is blocked, maybe `exec` should return a witness

3. **Type errors cascade**: Work stage by stage, verify with `make agda MODULE=...`

4. **Document and continue**: If blocked, document exactly why and continue with next stage

### The Goal

Every property should follow from the concrete definitions by computation.
Postulates are a symptom of architecture issues, not proof difficulty.

---

## Success Criteria

- [ ] Stage 0: Encoding axioms DERIVED
- [ ] Stage 0b: `encode-injective` DERIVED
- [ ] Stage 1: Exec bridges ELIMINATED
- [ ] Stage 2: ExecLemmas PROVEN
- [ ] Stage 3-6: Engineering postulates PROVEN
- [ ] Stage 7: Arithmetic postulates PROVEN
- [ ] Stage 8: run-apply-seq DERIVED
- [ ] **`make x86` passes**
- [ ] **0 postulates remain**
