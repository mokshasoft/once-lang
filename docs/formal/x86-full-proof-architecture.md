# X86 Backend Verification Architecture

## Goal: 0 Postulates

Target: **0 postulates** in X86 verification.

**Core Principle**: Proofs should compute. Postulates are symptoms of architecture issues, not proof difficulty.

**When Stuck**: Change the architecture, not the proof. If a statement can't be proven, the statement is likely wrong - change the primitives or architecture to make it provable.

---

## Key Architectural Decision: Star for Composition

**Use Star (reflexive-transitive closure of step) as the primary abstraction for execution proofs.**

```agda
-- Star is the right abstraction for execution proofs
data Star (prog : Program) : State → State → Set where
  refl* : ∀ {s} → Star prog s s
  step* : ∀ {s s' s''} →
          halted s ≡ false →
          step prog s ≡ just s' →
          Star prog s' s'' →
          Star prog s s''

-- Composition is trivial transitivity
star-trans : Star prog s₁ s₂ → Star prog s₂ s₃ → Star prog s₁ s₃
```

**Why Star over fuel-based exec**:
1. **Composition is trivial**: `star-trans` is just structural recursion
2. **No fuel arithmetic**: No need to track step counts or prove fuel bounds
3. **Bridge lemmas are provable**: When `exec` checks `halted s` first, `exec-to-star` is a clean induction

**The pattern**:
1. Build step proofs: `halted s ≡ false`, `step prog s ≡ just s'`
2. Compose using Star: `star-trans`, `step*`, `star-step2`, etc.
3. Convert to `exec` only at final theorem using `star-to-exec`

---

## Proven Foundation

### Memory Axioms (PROVEN)

```agda
-- PROVEN in Once.Memory.agda (concrete writeMem definition):
mem-read-write : readMem (writeMem m addr v) addr ≡ just v
mem-read-other : addr₁ ≢ addr₂ → readMem (writeMem m addr₁ v) addr₂ ≡ readMem m addr₂
```

### Star Bridge Lemmas (PROVEN)

```agda
-- PROVEN in Star.agda (exec checks halted s first):
exec-to-star : exec n prog s ≡ just s' → Star prog s s'
exec-until-pc-to-star : exec-until-pc target fuel prog s ≡ just s' → Star prog s s'
```

These work because `exec` is structured to check `halted s` BEFORE calling `step`:

```agda
exec (suc n) prog s =
  case halted s of λ where
    true → just s  -- Check halted FIRST
    false → case step prog s of λ where
      nothing → nothing
      (just s') → ...
```

### Derived Infrastructure

- `encode-is-alloc-addr` - PROVEN (trivially refl in Stateful.agda)
- `alloc-pair-fst/snd`, `alloc-inl-tag/val`, `alloc-inr-tag/val` - DERIVED in Encoding.agda
- HeapValid tracking - available in Encoding.agda

---

## Current Postulate Inventory

| Category | Count | Status |
|----------|-------|--------|
| Encoding axioms (Postulates.agda) | 11 | **DERIVE** from proven infrastructure |
| Star bridges (Star.agda) | 0 | **DONE** - exec-to-star PROVEN |
| star-to-exec (Star.agda) | 1 | **ADD** - reverse bridge needed |
| Correct.agda engineering | ~23 | **REFACTOR** to use Star |
| Apply semantic | 1 | **DERIVE** from closure encoding |
| encode-injective | 1 | **DERIVE** from mem-read-write + induction |

---

## Implementation Stages

### Stage 1: Add star-to-exec Bridge (IMMEDIATE)

**Target**: Add `star-to-exec` to `formal/Once/Backend/X86/Correct/Star.agda`

```agda
-- Convert Star back to exec for final theorem
star-to-exec : ∀ {prog s s'} →
               Star prog s s' →
               halted s' ≡ true →
               ∃[ n ] exec n prog s ≡ just s'
star-to-exec refl* h-eq = 0 , refl  -- Already at final state
star-to-exec (step* h step-eq rest) h-final =
  let (n , exec-rest) = star-to-exec rest h-final
  in suc n , ...  -- Prepend the step
```

**Why this is provable**: Star is a concrete data structure. We can count the `step*` constructors to get the fuel needed.

**Verify**: `make agda MODULE=Once/Backend/X86/Correct/Star.agda`

### Stage 2: Derive Encoding Axioms (HIGHEST IMPACT)

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

### Stage 3: Derive encode-injective

**Target**: `encode-injective` in `formal/Once/Backend/X86/Encoding.agda`

**Approach**: If `encode x = encode y`, they're at the same address. Read memory at that address (using proven `mem-read-write`). Components must be equal, recurse.

**Verify**: `make x86-encoding`

### Stage 4: Refactor Correct.agda to Use Star

**Target**: Replace fuel-based composition with Star composition

**Before** (blocked by case_of_):
```agda
-- These lemmas are hard to prove when exec uses case_of_
exec-on-halted-step : ... → exec (suc n) prog s ≡ just s'
exec-two-steps-nonhalt : ... → exec 2 prog s ≡ just s2
```

**After** (Star composition is trivial):
```agda
-- Step proofs compose directly via Star
star-f : Star prog s s1
star-g : Star prog s1 s2
star-all : Star prog s s2
star-all = star-trans star-f star-g

-- Convert at final theorem boundary
final-exec : exec n prog s ≡ just s2
final-exec = proj₂ (star-to-exec star-all h-final)
```

**Key insight**: The `run-ir-at-offset` pattern returns Star instead of exec proofs:

```agda
run-ir-at-offset-star : ∀ {A B} (ir : IR A B) ... →
  ∃[ s' ] (Star (prefix ++ compile ir ++ suffix) s s'
         × halted s' ≡ false
         × pc s' ≡ length prefix + compile-length ir
         × readReg (regs s') rax ≡ encode (eval ir x))
```

**Verify**: `make x86-correct`

### Stage 5: Arithmetic Postulates

**Target**: 2 postulates

| Postulate | File | Approach |
|-----------|------|----------|
| `∸+<-lemma` | StackInvariant.agda:93 | Arithmetic proof |
| Fuel bounds | Various | Eliminated by Star (no fuel tracking needed) |

**Verify**: `make x86-correct`

### Stage 6: Derive run-apply-seq

**Target**: `run-apply-seq` (Correct.agda)

Once encoding axioms are derived (Stage 2), `run-apply-seq` follows from:
1. `encode-closure-construct` → closure at address has [env, code-ptr]
2. Build Star proof for apply instructions
3. Convert to exec at theorem boundary

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
| 1 | `formal/Once/Backend/X86/Correct/Star.agda` | Add star-to-exec |
| 2 | `formal/Once/Backend/X86/Correct.agda` | Add HeapValid, use derived encoding proofs |
| 2 | `formal/Once/Backend/X86/Encoding.agda` | Export derived proofs |
| 2 | `formal/Once/Postulates.agda` | Remove encoding axioms |
| 3 | `formal/Once/Backend/X86/Encoding.agda` | Prove encode-injective |
| 4 | `formal/Once/Backend/X86/Correct.agda` | Refactor to use Star |
| 4 | `formal/Once/Backend/X86/Correct/ExecLemmas.agda` | Simplify or remove |
| 5 | `formal/Once/Backend/X86/Correct/StackInvariant.agda` | Prove ∸+<-lemma |
| 6 | `formal/Once/Backend/X86/Correct.agda` | Derive run-apply-seq |

---

## Why Star Eliminates Blocked Proofs

### The Problem with Fuel-Based Composition

When `exec` uses `case_of_`:
```agda
exec (suc n) prog s = case halted s of λ where ...
```

Proving `exec (suc n) prog s ≡ just s'` requires reducing the `case_of_`. But when `halted s` is abstract, `case_of_` doesn't reduce. This blocks lemmas like:
- `exec-on-halted-step`
- `exec-on-non-halted-step`
- `exec-two-steps-nonhalt`

### The Solution: Star as Primary Abstraction

Star composition never touches `case_of_`:
```agda
star-trans refl* p₂ = p₂
star-trans (step* h step-eq p₁) p₂ = step* h step-eq (star-trans p₁ p₂)
```

This is pure structural recursion on the Star witness. No `case_of_`, no abstract scrutinees, no blocked proofs.

### Bridge Lemmas Are Provable

`exec-to-star` and `exec-until-pc-to-star` ARE proven because:
1. `exec` checks `halted s` FIRST
2. Pattern matching on `halted s` causes the goal to reduce
3. Induction proceeds cleanly

`star-to-exec` is conceptually simple but currently blocked:
1. Star is a concrete data structure (we can count `step*` for fuel)
2. BUT: `exec (suc n) prog s` unfolds to `case halted s of ...`
3. `with` abstraction doesn't reduce nested `case_of_` in goal types
4. **Current status**: POSTULATED (plumbing postulate)

**Resolution path**: Change `exec` to return step witnesses, or use a different proof structure where goals don't contain nested `case_of_`.

---

## Encoding Axiom Architecture (Stage 2 Status)

### The Problem

The encoding axioms in `Postulates.agda` claim to hold for ANY memory:
```agda
encode-pair-fst : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (m : Memory) →
  readMem m (encode (a , b)) ≡ just (encode a)
```

This is too strong - it should only hold for memory where `(a, b)` was properly allocated.

### Root Cause

`encode : ∀ {A} → ⟦ A ⟧ → Word` is itself a postulate - an abstract oracle that assigns addresses to values without knowing allocation state.

### Infrastructure Created

`MemoryValid.agda` provides validity predicates that track properly allocated values:
```agda
-- Validity predicate: pair is properly encoded at address
record PairAt {A B : Type} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (addr : Word) (m : Memory) : Set

-- PROVEN: allocation creates validity
alloc-pair-creates-valid : ... → PairAt a b addr m₂

-- Derived: reading with validity proof (replaces axiom)
encode-pair-fst-derived : ... → PairAt a b addr m → readMem m addr ≡ just (encode a)
```

### Resolution Options

**Option A: Thread AllocState through Semantics.eval**
- Replace abstract `encode` with stateful encode
- All encoding axioms become theorems
- **Impact**: Major rewrite of Semantics.agda and all proofs that use `encode`

**Option B: Use validity predicates as preconditions**
- Add `MemoryValid` precondition to `run-ir-at-offset-*` functions
- Prove validity is established by allocation operations
- Prove validity is preserved through execution
- **Impact**: Moderate rewrite similar to `StackInvariant` threading

**Option C: Accept as semantic model axioms**
- The encoding axioms define the intended memory layout
- They're the "contract" between semantics and code generation
- Keep as trusted base, focus on eliminating mechanical postulates
- **Impact**: Minimal code changes, documented trust assumptions

**Current Status**: Infrastructure (MemoryValid.agda) created. Full derivation requires Option A or B - significant architectural work.

---

## Success Criteria

- [x] `exec-to-star` PROVEN
- [x] `exec-until-pc-to-star` PROVEN
- [x] Stage 1: `star-to-exec` ADDED (postulated - blocked by case_of_)
- [ ] Stage 2: Encoding axioms DERIVED
- [ ] Stage 3: `encode-injective` DERIVED
- [ ] Stage 4: Correct.agda REFACTORED to use Star
- [ ] Stage 5: Arithmetic postulates PROVEN
- [ ] Stage 6: `run-apply-seq` DERIVED
- [ ] **`make x86` passes**
- [ ] **0 postulates remain** (currently: star-to-exec postulated)

---

## Philosophy: Compose High, Convert at Boundaries

**The principle**: Work at the highest abstraction level (Star), convert only at system boundaries (final theorem).

This follows the same pattern as:
- Type-level programming: work with types, erase at runtime
- Category theory: work with morphisms, interpret at the end
- CompCert: work with step relations, extract to execution

Star is the "native" abstraction for execution proofs. Fuel-based exec is an implementation detail for extraction. Keep them separate.
