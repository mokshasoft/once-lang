# Plan: Remaining x86 Correctness Proofs

## Current Status

### Proven (base cases)
- `run-case-inl-id` / `run-case-inr-id` - case analysis with f = g = id
- `run-pair-id-id` - pair construction with f = g = id
- `run-compose-id-id` - composition with f = g = id
- `run-curry-seq` - closure creation (with fetch postulates)

### Remaining Postulates

```
                    ┌─────────────────┐
                    │  run-generator  │ ◄── Main theorem
                    └────────┬────────┘
                             │ calls
        ┌────────────────────┼────────────────────┐
        ▼                    ▼                    ▼
┌───────────────┐   ┌────────────────┐   ┌───────────────┐
│ run-case-inl  │   │ run-pair-seq   │   │run-seq-compose│
│ run-case-inr  │   │                │   │               │
└───────┬───────┘   └───────┬────────┘   └───────┬───────┘
        │                   │                    │
        └───────────────────┴────────────────────┘
                            │ call back to
                            ▼
                    ┌─────────────────┐
                    │  run-generator  │  (for sub-IRs f, g)
                    └─────────────────┘

                    MUTUAL RECURSION CLUSTER
```

---

## Phase 1: Independent Postulates

These don't depend on the mutual recursion cluster.

### 1.1 `encodedMemory` (in initWithInput)

**Location**: Line ~89 in Correct.agda

**What it does**: Creates a memory that contains the encoded representation of a value.

**Approach**:
- Define `encodedMemory` as a function that maps `encode x` to `just (encode x)` for the specific addresses needed
- For pairs: map base address to fst, base+8 to snd
- For sums: map base address to tag, base+8 to value
- Use a finite map or nested conditionals

**Difficulty**: Low - just need to construct the right memory function.

### 1.2 `fetch-end-label` (in run-curry-seq)

**Location**: Line ~1317 in Correct.agda

**What it does**: Proves `fetch prog end-label ≡ just (label end-label)` where `end-label = 11 + compile-length f`.

**Approach**:
- The program is `compile-x86 (curry f)` which has structure:
  ```
  [0-4]: setup instructions
  [5]: label 5
  [6-9]: thunk setup
  [10 to 9+|f|]: compile-x86 f
  [10+|f|]: ret
  [11+|f|]: label (11+|f|)  ← this is end-label
  ```
- Need a lemma: `fetch (xs ++ [x]) (length xs) ≡ just x`
- Then show `length (prefix) = end-label`

**Difficulty**: Medium - requires list arithmetic lemmas.

### 1.3 `fetch-past-end` (in run-curry-seq)

**Location**: Line ~1333 in Correct.agda

**What it does**: Proves `fetch prog (end-label + 1) ≡ nothing`.

**Approach**:
- Show `length prog = 12 + compile-length f`
- Show `end-label + 1 = 12 + compile-length f`
- Use lemma: `fetch xs n ≡ nothing` when `n ≥ length xs`

**Difficulty**: Medium - similar to above, list length reasoning.

---

## Phase 2: Mutual Recursion Cluster

These must be proven together using Agda's `mutual` block.

### 2.1 Strategy Overview

The key insight is that all recursive IR constructors (`∘`, `[ , ]`, `⟨ , ⟩`) contain sub-IRs that are structurally smaller. This enables well-founded recursion on IR structure.

```agda
mutual
  run-generator : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) → ...
  run-generator id x s ... = run-single-mov ...
  run-generator fst (a , b) s ... = run-single-mov-mem ...
  run-generator (g ∘ f) x s ... = run-seq-compose-proof f g x s (run-generator f) (run-generator g)
  run-generator [ f , g ] (inj₁ a) s ... = run-case-inl-proof f g a s (run-generator f)
  run-generator [ f , g ] (inj₂ b) s ... = run-case-inr-proof f g b s (run-generator g)
  run-generator ⟨ f , g ⟩ x s ... = run-pair-seq-proof f g x s (run-generator f) (run-generator g)
  -- etc.

  run-seq-compose-proof : ... → (ih-f : ...) → (ih-g : ...) → ...
  run-case-inl-proof : ... → (ih-f : ...) → ...
  run-case-inr-proof : ... → (ih-g : ...) → ...
  run-pair-seq-proof : ... → (ih-f : ...) → (ih-g : ...) → ...
```

### 2.2 `run-seq-compose`

**Dependencies**: run-generator for f and g

**Proof structure**:
1. Run `compile-x86 f` using induction hypothesis, get state s1 with `rax = encode (eval f x)`
2. The `mov rdi, rax` instruction transfers result to input register
3. Run `compile-x86 g` using induction hypothesis with new state
4. Combine using `exec-N-steps` helpers

**Key lemma needed**: Program concatenation execution
```agda
run-concat : run (p1 ++ p2) s ≡ ...
  → run p1 s ≡ just s1
  → run p2 s1' ≡ just s2
  → ...
```

**Difficulty**: High - need to reason about PC offsets after first program.

### 2.3 `run-case-inl` / `run-case-inr`

**Dependencies**: run-generator for f (inl) or g (inr)

**Proof structure** (generalizing run-case-inl-id):
1. Steps 0-2: Load tag, compare, branch (same as base case)
2. Step 3: Load value into rdi
3. Steps 4 to 4+|f|-1: Execute `compile-x86 f` using induction hypothesis
4. Step 4+|f|: jmp to end-label
5. Step at end-label: label (no-op)
6. Halt on fetch past end

**Key challenge**: PC offset tracking through sub-program execution.

**Difficulty**: High - need to track PC through compiled sub-IR.

### 2.4 `run-pair-seq`

**Dependencies**: run-generator for f and g

**Proof structure** (generalizing run-pair-id-id):
1. Steps 0-1: Allocate stack, save input in r14
2. Steps 2 to 2+|f|-1: Execute `compile-x86 f` using induction hypothesis
3. Step 2+|f|: Store result at [rsp]
4. Step 3+|f|: Restore input from r14
5. Steps 4+|f| to 4+|f|+|g|-1: Execute `compile-x86 g` using induction hypothesis
6. Step 4+|f|+|g|: Store result at [rsp+8]
7. Step 5+|f|+|g|: Return rsp as pair pointer

**Key challenges**:
- Register preservation (r14 must survive f execution)
- Memory preservation (stack slot must survive g execution)
- PC offset calculation

**Difficulty**: High - most complex due to interleaved execution.

---

## Phase 3: Closure Operations

### 3.1 `run-apply-seq`

**Dependencies**: None directly, but semantically depends on how closures work.

**What it does**: Given a pair `(closure, arg)` where `closure = [env, code_ptr]`:
1. Load closure from pair.fst
2. Load argument from pair.snd
3. Load env into r12
4. Load code_ptr
5. Move argument to rdi
6. Call code_ptr

**Key challenge**: The `call` instruction changes control flow in a complex way. The called code (thunk from curry) must:
- Execute with env in r12, arg in rdi
- Return with result in rax

**Approach options**:
1. **Postulate call behavior**: Assume call to code_ptr with proper setup produces correct result
2. **Inline thunk execution**: Trace through thunk code (requires knowing thunk structure)
3. **Abstract closure model**: Model closures abstractly without tracing thunk

**Difficulty**: Very High - requires modeling call/ret semantics properly.

---

## Recommended Order

```
Phase 1 (Independent, can parallelize):
  1.1 encodedMemory        [Low]
  1.2 fetch-end-label      [Medium]
  1.3 fetch-past-end       [Medium]

Phase 2 (Mutual recursion, do together):
  2.1 Set up mutual block structure
  2.2 run-generator base cases (id, fst, snd, inl, inr, terminal, fold, unfold, arr)
  2.3 run-seq-compose      [High]
  2.4 run-case-inl/inr     [High]
  2.5 run-pair-seq         [High]

Phase 3 (After Phase 2):
  3.1 run-apply-seq        [Very High]
```

---

## Helper Lemmas Needed

### List/Fetch Lemmas
```agda
fetch-append-left : ∀ xs ys n → n < length xs → fetch (xs ++ ys) n ≡ fetch xs n
fetch-append-right : ∀ xs ys n → fetch (xs ++ ys) (length xs + n) ≡ fetch ys n
fetch-at-length : ∀ xs x → fetch (xs ++ x ∷ []) (length xs) ≡ just x
fetch-past-length : ∀ xs n → n ≥ length xs → fetch xs n ≡ nothing
```

### Compile-length Lemmas
```agda
compile-length-correct : ∀ {A B} (ir : IR A B) → length (compile-x86 ir) ≡ compile-length ir
```

### PC Offset Lemmas
```agda
-- After running program p1, if we continue with p2 at adjusted PC...
run-with-offset : ∀ p1 p2 s s1 offset →
  run p1 s ≡ just s1 →
  pc s1 ≡ length p1 →
  run p2 (record s1 { pc = 0 }) ≡ just s2 →
  run (p1 ++ p2) s ≡ just (record s2 { pc = length p1 + pc s2 })
```

### Register Preservation Lemmas
```agda
-- r14 is callee-saved, preserved across sub-program execution
r14-preserved : ∀ ir x s s' →
  run (compile-x86 ir) s ≡ just s' →
  readReg (regs s') r14 ≡ readReg (regs s) r14
```

---

## Estimated Effort

| Phase | Items | Difficulty | Effort |
|-------|-------|------------|--------|
| 1.1 | encodedMemory | Low | 1-2 hours |
| 1.2-1.3 | fetch lemmas | Medium | 2-4 hours |
| 2.1-2.5 | Mutual cluster | High | 2-3 days |
| 3.1 | run-apply-seq | Very High | 1-2 days |

**Total**: ~1 week of focused work

---

## Alternative: Simplification

If full proofs are too complex, consider:

1. **Keep some postulates**: Document which are "trusted" vs "proven"
2. **Restrict to finite IR**: Prove for IR without recursion (no fold/unfold)
3. **Abstract execution model**: Don't trace individual instructions, use higher-level execution semantics
4. **Property-based testing**: Use QuickCheck-style testing to validate postulates empirically
