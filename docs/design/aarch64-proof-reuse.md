# AArch64 Proof Reuse Analysis

This document analyzes what proof machinery from the x86-64 backend can be reused for AArch64 (ARM64).

## Architecture Overview

The proof structure has three layers:

```
┌─────────────────────────────────────────────────────────────┐
│  Layer 1: SHARED (100% reusable)                            │
│  - Once.Type           : Type definitions                   │
│  - Once.IR             : IR morphisms (14 generators)       │
│  - Once.Semantics      : Denotational semantics (⟦_⟧, eval) │
│  - Once.Postulates     : Core axioms (funext, encoding)     │
│  - Once.Category.Laws  : Categorical laws                   │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  Layer 2: BACKEND-PARAMETERIZED (structure reusable)        │
│  - Syntax.agda    : Instruction set definition              │
│  - Semantics.agda : Operational semantics                   │
│  - CodeGen.agda   : IR → Assembly translation               │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  Layer 3: CORRECTNESS PROOFS (pattern reusable)             │
│  - Correct.agda : compile-correct theorem                   │
│  - Instruction helpers, run-* lemmas, etc.                  │
└─────────────────────────────────────────────────────────────┘
```

## What's Fully Reusable (Layer 1)

These modules are **100% shared** between all backends:

| Module | Lines | Description |
|--------|-------|-------------|
| `Once.Type` | ~70 | Type system (Unit, Void, *, +, ⇒, Fix, Eff) |
| `Once.IR` | ~67 | IR morphisms (id, ∘, fst, snd, inl, inr, etc.) |
| `Once.Semantics` | ~115 | Denotational semantics (⟦_⟧, eval) |
| `Once.Postulates` | ~275 | Central axioms (funext, encoding axioms) |

**Total shared: ~527 lines**

The main correctness theorem structure is also shared:

```agda
-- This theorem shape is identical for any backend
codegen-correct : ∀ (ir : IR A B) (x : ⟦A⟧) →
  exec (compile ir) (encode x) ≡ encode (eval ir x)
```

## What Needs New Definitions (Layer 2)

### Syntax.agda - AArch64 Instructions

The x86 version defines:
```agda
data Reg : Set where
  rax rbx rcx rdx rsi rdi rbp rsp r8-r15 : Reg

data Instr : Set where
  mov lea add sub cmp test jmp je jne call ret push pop nop ud2 label
```

AArch64 defines:
```agda
data Reg : Set where
  x0-x30 : Reg  -- 31 GPRs

data Instr : Set where
  mov ldr str ldp stp add sub cmp b b-eq b-ne bl blr ret
  sub-sp add-sp mov-from-sp nop brk str-zr label
```

**Effort**: Medium - Different ISA, but similar structure.

### Semantics.agda - Operational Semantics

The x86 version has:
- `State` record with `regs`, `memory`, `flags`, `pc`, `halted`
- `readReg`/`writeReg` for 16 registers
- `execInstr` for each instruction

AArch64 has the same structure, but:
- 31 registers instead of 16
- PSTATE (NZCV) instead of EFLAGS
- Separate SP handling via `readSP`/`writeSP`
- Different instruction semantics

**Effort**: Medium - Same patterns, different details.

### CodeGen.agda - Translation

Same structure with different instructions:

| IR Generator | x86-64 | AArch64 |
|--------------|--------|---------|
| id | mov rax, rdi | nop |
| fst | mov rax, [rdi] | ldr x0, [x0] |
| snd | mov rax, [rdi+8] | ldr x0, [x0, #8] |
| inl | sub rsp; mov [rsp], 0 | sub-sp; str-zr [sp] |
| inr | sub rsp; mov [rsp], 1 | sub-sp; mov x9, #1; str |
| case | cmp + jne | ldr + cmp + b.ne |
| curry | closure creation | closure creation |
| apply | call [r15] | blr x9 |

**Effort**: Medium - Same IR cases, different instruction sequences.

## AArch64 vs x86-64 Key Differences

| Aspect | x86-64 | AArch64 | Proof Impact |
|--------|--------|---------|--------------|
| Registers | 16 (rax-r15) | 31 (x0-x30) | More case splits |
| Input reg | rdi | x0 | Simpler (same as output) |
| Output reg | rax | x0 | Simpler (same as input) |
| Callee-saved | rbx, r12-r15 | x19-x28 | Same pattern |
| Flags | EFLAGS (in status) | PSTATE (separate) | Cleaner separation |
| Zero reg | N/A | xzr available | Simplifies tag=0 |
| Branches | jz/jne (check ZF) | b.eq/b.ne (check Z) | Similar |
| Memory ops | mov [addr], reg | str/ldr with offset | Same layout |
| Stack align | Optional | Required (16-byte) | Must track |

## Advantages for AArch64 Proofs

1. **Single input/output register (x0)**: No register transfer between compose
2. **Zero register (xzr)**: `str-zr` avoids loading 0 into temp for inl
3. **Pair load/store (ldp/stp)**: More efficient closure handling
4. **Cleaner flags**: PSTATE separate from general status

## What's Pattern-Reusable (Layer 3)

### Correct.agda - Proof Structure

The proof has this structure:

1. **Initial State Setup** (reusable pattern)
   ```agda
   initWithInput : ∀ {A} → ⟦ A ⟧ → State
   initWithInput-x0 : readReg (regs (initWithInput x)) x0 ≡ encode x
   ```

2. **Encoding Axioms** (100% reusable)
   ```agda
   encode-pair-fst, encode-pair-snd, encode-inl-tag, encode-inl-val, ...
   ```
   These are architecture-independent memory layout axioms.

3. **Instruction Execution Helpers** (need rewriting)
   ```agda
   exec-ldr : execInstr s (ldr dst m) ≡ just (...)
   exec-str : execInstr s (str src m) ≡ just (...)
   ```
   Different instruction set, same proof patterns.

4. **Generator Proofs** (structure reusable)
   ```agda
   run-generator-id : exec (compile-aarch64 id) s ≡ just s' ∧ x0 = encode x
   run-generator-fst : ...
   ```
   Same theorem statements, different proofs using AArch64 helpers.

5. **Composition Proofs** (pattern reusable)
   ```agda
   run-seq-compose : exec (compile-aarch64 (g ∘ f)) = ...
   run-case-inl : exec (compile-aarch64 [f,g]) on inl = ...
   run-pair-seq : exec (compile-aarch64 ⟨f,g⟩) = ...
   ```

## Effort Estimate

| Component | x86 Lines | AArch64 Effort | Notes |
|-----------|-----------|----------------|-------|
| Syntax.agda | ~190 | 100% new | Different ISA |
| Semantics.agda | ~315 | 80% new | Same structure, more registers |
| CodeGen.agda | ~260 | 70% new | Same IR, different instructions |
| Correct.agda | ~6400 | 50% new | Proof patterns reusable |
| **Total** | ~7165 | ~60% new | |

**Estimated new code**: ~4300 lines
**Reused patterns**: ~2800 lines worth of structure

## seL4 Alignment

The AArch64 backend aligns with seL4's verified ARM64 target:
- Same ABI (AAPCS64)
- Same calling convention (x0-x7 args, x0 return)
- Same callee-saved registers (x19-x28)
- Same stack alignment (16-byte)

While seL4 uses Isabelle/HOL and Once uses Agda, the same architectural properties apply.

## Implementation Status

| File | Status | Lines |
|------|--------|-------|
| `Once/Backend/AArch64/Syntax.agda` | ✓ Created | ~200 |
| `Once/Backend/AArch64/Semantics.agda` | ✓ Created | ~380 |
| `Once/Backend/AArch64/CodeGen.agda` | ✓ Created | ~280 |
| `Once/Backend/AArch64/Correct.agda` | ✓ Structure | ~350 (postulated) |
| **Total** | | ~1210 |

**Remaining to prove**: ~4000 lines of correctness proofs

## Conclusion

Approximately **40% of the proof effort** can be directly reused:
- Layer 1 (shared modules): 100% reused
- Layer 2 (backend definitions): Structure reused, details new
- Layer 3 (correctness proofs): Theorem statements reused, proofs adapted

The main work is:
1. Proving instruction execution helpers for AArch64
2. Adapting the run-* lemmas for different instruction sequences
3. Handling the mutual recursion cluster (compose, case, pair)
4. Proving closure operations (curry, apply)

The categorical/semantic correctness structure is completely shared.
