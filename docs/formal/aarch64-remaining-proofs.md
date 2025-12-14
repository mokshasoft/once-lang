# Plan: AArch64 Correctness Proofs

## Current Status (Updated 2024-12-14)

### Backend Definition Files

| File | Status | Lines | Notes |
|------|--------|-------|-------|
| `Once/Backend/AArch64/Syntax.agda` | ✓ Created | ~200 | 31 GPRs, AAPCS64 instructions |
| `Once/Backend/AArch64/Semantics.agda` | ✓ Created | ~380 | State model, PSTATE flags |
| `Once/Backend/AArch64/CodeGen.agda` | ✓ Created | ~280 | IR → AArch64 translation |
| `Once/Backend/AArch64/Correct.agda` | Not started | ~4000 est. | Correctness proofs |

### Generator Proofs Status

| Generator | Code Pattern | Status | Notes |
|-----------|--------------|--------|-------|
| `id` | `nop` | ☐ Pending | x0 unchanged |
| `fst` | `ldr x0, [x0]` | ☐ Pending | encode-pair-fst |
| `snd` | `ldr x0, [x0, #8]` | ☐ Pending | encode-pair-snd |
| `pair` | stack alloc + stores | ☐ Pending | encode-pair-construct |
| `inl` | stack + tag=0 | ☐ Pending | encode-inl-construct |
| `inr` | stack + tag=1 | ☐ Pending | encode-inr-construct |
| `case` | ldr + cmp + b.ne | ☐ Pending | Split on sum tag |
| `terminal` | `mov x0, #0` | ☐ Pending | encode-unit |
| `initial` | `brk #0` | ☐ Pending | Absurd pattern |
| `fold` | `nop` | ☐ Pending | Identity encoding |
| `unfold` | `nop` | ☐ Pending | Identity encoding |
| `arr` | `nop` | ☐ Pending | Identity encoding |
| `curry` | Closure alloc | ☐ Pending | encode-closure-construct |
| `apply` | Closure call | ☐ Pending | run-apply-seq |

**Legend**: ☐ Pending, ◐ In Progress, ✓ Proven

---

## Proof Architecture

### Dependency Diagram

```
                    ┌─────────────────────┐
                    │  codegen-correct    │ ◄── Main theorem
                    └─────────┬───────────┘
                              │ calls
        ┌─────────────────────┼─────────────────────┐
        ▼                     ▼                     ▼
┌───────────────┐   ┌────────────────┐   ┌───────────────┐
│ run-case-inl  │   │ run-pair-seq   │   │run-seq-compose│
│ run-case-inr  │   │                │   │               │
└───────┬───────┘   └───────┬────────┘   └───────┬───────┘
        │                   │                    │
        └───────────────────┴────────────────────┘
                            │ call back to
                            ▼
                    ┌─────────────────────┐
                    │  codegen-correct    │  (for sub-IRs f, g)
                    └─────────────────────┘

                    MUTUAL RECURSION CLUSTER
```

### Layered Proof Strategy

Following the x86-64 approach, proofs are organized in layers:

1. **Encoding Axioms (P2)**: Relate semantic values to machine words
2. **Instruction Execution Helpers (P3)**: Single/multi-instruction properties
3. **Per-Generator Proofs**: Compose helpers for each IR constructor
4. **Main Theorem**: Case analysis using all generator proofs

---

## Phase 1: Independent Postulates

These can be proven without the mutual recursion cluster.

### 1.1 `encodedMemory` (in initWithInput)

**Status**: ☐ Pending

**What it does**: Creates a memory that contains the encoded representation of a value.

**Approach**:
- Define `encodedMemory` as a function mapping `encode x` to `just (encode x)`
- For pairs: map base address to fst, base+8 to snd
- For sums: map base address to tag, base+8 to value

**Difficulty**: Low

### 1.2 Encoding Axioms

**Status**: ☐ Pending

These are architecture-independent and match x86:

```agda
postulate
  encode : ∀ {A} → ⟦ A ⟧ → Word
  encode-unit : encode tt ≡ 0
  encode-pair-fst : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
    readMem encodedMemory (encode (a , b)) ≡ just (encode a)
  encode-pair-snd : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
    readMem encodedMemory (encode (a , b) +ℕ 8) ≡ just (encode b)
  encode-inl-tag : ∀ {A B} (a : ⟦ A ⟧) →
    readMem encodedMemory (encode (inl a)) ≡ just 0
  encode-inl-val : ∀ {A B} (a : ⟦ A ⟧) →
    readMem encodedMemory (encode (inl a) +ℕ 8) ≡ just (encode a)
  encode-inr-tag : ∀ {A B} (b : ⟦ B ⟧) →
    readMem encodedMemory (encode (inr b)) ≡ just 1
  encode-inr-val : ∀ {A B} (b : ⟦ B ⟧) →
    readMem encodedMemory (encode (inr b) +ℕ 8) ≡ just (encode b)
```

**Difficulty**: Low (copy from x86, same layout)

### 1.3 Fetch Lemmas

**Status**: ☐ Pending

```agda
fetch-append-left : ∀ xs ys n → n < length xs → fetch (xs ++ ys) n ≡ fetch xs n
fetch-append-right : ∀ xs ys n → fetch (xs ++ ys) (length xs + n) ≡ fetch ys n
fetch-at-length : ∀ xs x → fetch (xs ++ x ∷ []) (length xs) ≡ just x
fetch-past-length : ∀ xs n → n ≥ length xs → fetch xs n ≡ nothing
```

**Difficulty**: Medium

---

## Phase 2: Simple Generator Proofs

Base cases that don't require mutual recursion.

### 2.1 Identity Generators

**Status**: ☐ Pending

```agda
-- id, fold, unfold, arr all compile to nop
run-generator-id : ∀ (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false → pc s ≡ 0 → readReg (regs s) x0 ≡ encode x →
  ∃[ s' ] (exec 1 (compile-aarch64 id) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') x0 ≡ encode x)
```

**Difficulty**: Low

### 2.2 Terminal

**Status**: ☐ Pending

```agda
run-generator-terminal : ∀ (x : ⟦ A ⟧) (s : State) →
  ... → readReg (regs s') x0 ≡ 0
```

**Difficulty**: Low

### 2.3 Projections (fst, snd)

**Status**: ☐ Pending

```agda
run-generator-fst : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  ... → readReg (regs s') x0 ≡ encode a

run-generator-snd : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  ... → readReg (regs s') x0 ≡ encode b
```

**Difficulty**: Low (single ldr instruction)

### 2.4 Injections (inl, inr)

**Status**: ☐ Pending

```agda
run-generator-inl : ∀ {A B} (a : ⟦ A ⟧) (s : State) →
  ... → ∃[ s' ] (exec 4 (compile-aarch64 inl) s ≡ just s'
               × readMem (memory s') (readSP (regs s') + 0) ≡ just 0
               × readMem (memory s') (readSP (regs s') + 8) ≡ just (encode a)
               × readReg (regs s') x0 ≡ readSP (regs s'))
```

**Difficulty**: Medium (4-instruction sequence)

---

## Phase 3: Mutual Recursion Cluster

These must be proven together using Agda's `mutual` block.

### 3.1 `run-seq-compose`

**Status**: ☐ Pending

**Dependencies**: run-generator for f and g

**Proof structure**:
1. Run `compile-aarch64 f` using IH, get state s1 with `x0 = encode (eval f x)`
2. The `nop` instruction advances PC
3. Run `compile-aarch64 g` using IH with new state
4. Combine using `exec-N-steps` helpers

**Difficulty**: High

### 3.2 `run-case-inl` / `run-case-inr`

**Status**: ☐ Pending

**Dependencies**: run-generator for f (inl) or g (inr)

**Proof structure**:
1. Steps 0-2: Load tag, compare, branch
2. Step 3: Load value into x0
3. Steps 4+: Execute sub-IR using IH
4. Handle branch labels and end labels

**Difficulty**: High

### 3.3 `run-pair-seq`

**Status**: ☐ Pending

**Dependencies**: run-generator for f and g

**Proof structure**:
1. Allocate stack, save input in x20
2. Execute f using IH
3. Store result, restore input
4. Execute g using IH
5. Store result, return pair pointer

**Key challenges**:
- Register preservation (x20 must survive f execution)
- Memory preservation (stack slot must survive g execution)

**Difficulty**: High

---

## Phase 4: Closure Operations

### 4.1 `run-curry-seq`

**Status**: ☐ Pending

**Proof structure**:
1. Allocate closure on stack
2. Store environment and code pointer
3. Jump over thunk code
4. Halt on fetch past end

**Difficulty**: Very High (closure creation semantics)

### 4.2 `run-apply-seq`

**Status**: ☐ Pending

**Proof structure**:
1. Load closure and argument from pair
2. Load env into x19, code_ptr into x9
3. Move argument to x0
4. Branch with link to code_ptr

**Difficulty**: Very High (call/ret modeling)

---

## Helper Lemmas Needed

### List/Fetch Lemmas

```agda
fetch-append-left : ∀ xs ys n → n < length xs → fetch (xs ++ ys) n ≡ fetch xs n
fetch-append-right : ∀ xs ys n → fetch (xs ++ ys) (length xs + n) ≡ fetch ys n
```

### Compile-length Lemmas

```agda
compile-length-correct : ∀ {A B} (ir : IR A B) → length (compile-aarch64 ir) ≡ compile-length ir
```

### Register Preservation Lemmas

```agda
-- x20 is callee-saved, preserved across sub-program execution
x20-preserved : ∀ ir x s s' →
  run (compile-aarch64 ir) s ≡ just s' →
  readReg (regs s') x20 ≡ readReg (regs s) x20
```

---

## AArch64-Specific Considerations

### Differences from x86-64

| Aspect | x86-64 | AArch64 | Proof Impact |
|--------|--------|---------|--------------|
| Input/output | rdi/rax | x0/x0 | Simpler (same register) |
| Flags | EFLAGS register | PSTATE (NZCV) | Separate condition flags |
| Zero register | N/A | xzr available | Simplifies tag=0 stores |
| Stack alignment | Optional | Required (16-byte) | Must track alignment |
| Branch semantics | jne checks ZF | b.ne checks Z bit | Similar pattern |

### Advantages for Proofs

1. **Single input/output register (x0)**: No register transfer between operations
2. **Zero register (xzr)**: `str-zr` avoids loading 0 into temp register for inl
3. **Pair load/store (ldp/stp)**: More efficient, fewer instructions to trace

### Challenges

1. **More registers**: 31 vs 16 GPRs means larger readReg/writeReg case splits
2. **SP handling**: Separate from GPRs, requires `mov-from-sp` instruction
3. **PSTATE**: Separate condition flags vs embedded in status register

---

## Estimated Effort

| Phase | Items | Difficulty | Effort |
|-------|-------|------------|--------|
| 1.1-1.3 | Independent postulates | Low-Medium | 1-2 days |
| 2.1-2.4 | Simple generators | Low-Medium | 1-2 days |
| 3.1-3.3 | Mutual cluster | High | 3-4 days |
| 4.1-4.2 | Closure operations | Very High | 2-3 days |

**Total**: ~8-11 days of focused work

---

## Next Steps

1. Create `Correct.agda` with theorem structure and postulates
2. Prove simple generators (id, terminal, fst, snd)
3. Prove injection generators (inl, inr)
4. Set up mutual block for recursive cases
5. Prove compose, case, pair
6. Tackle closure operations (curry, apply)

---

## Verification Checklist

- [ ] Encoding axioms defined (P2)
- [ ] Instruction execution helpers (P3)
- [ ] run-generator-id proven
- [ ] run-generator-terminal proven
- [ ] run-generator-fst proven
- [ ] run-generator-snd proven
- [ ] run-generator-inl proven
- [ ] run-generator-inr proven
- [ ] run-generator-fold proven
- [ ] run-generator-unfold proven
- [ ] run-generator-arr proven
- [ ] run-seq-compose proven
- [ ] run-case-inl/inr proven
- [ ] run-pair-seq proven
- [ ] run-curry-seq proven
- [ ] run-apply-seq proven
- [ ] codegen-aarch64-correct main theorem proven
- [ ] `make aarch64` type-checks successfully
