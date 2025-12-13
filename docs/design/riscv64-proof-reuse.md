# RISC-V 64 Proof Reuse Analysis

This document analyzes what proof machinery from the x86-64 backend can be reused for RISC-V 64.

## Architecture Overview

The proof structure has three layers:

```
┌─────────────────────────────────────────────────────────────┐
│  Layer 1: SHARED (100% reusable)                            │
│  - Once.Type           : Type definitions                   │
│  - Once.IR             : IR morphisms (12 generators)       │
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

### Syntax.agda - RISC-V Instructions

The x86 version defines:
```agda
data Reg : Set where
  rax rbx rcx rdx rsi rdi rbp rsp r8-r15 : Reg

data Instr : Set where
  mov lea add sub cmp test jmp je jne call ret push pop nop ud2 label
```

RISC-V needs:
```agda
data Reg : Set where
  x0-x31 : Reg  -- or zero, ra, sp, gp, tp, t0-t6, s0-s11, a0-a7

data Instr : Set where
  -- R-type: add, sub, and, or, xor, sll, srl, sra, slt, sltu
  -- I-type: addi, andi, ori, xori, slti, sltiu, lb, lh, lw, ld, jalr
  -- S-type: sb, sh, sw, sd
  -- B-type: beq, bne, blt, bge, bltu, bgeu
  -- U-type: lui, auipc
  -- J-type: jal
  -- Pseudo: li, mv, j, call, ret, la
```

**Effort: Medium** - Different instruction set, but similar structure.

### Semantics.agda - Operational Semantics

The x86 version has:
- `State` record with `regs`, `memory`, `flags`, `pc`, `halted`
- `readReg`/`writeReg` for 16 registers
- `execInstr` for each instruction
- `step`, `exec`, `run`

RISC-V needs the same structure, but:
- 32 registers instead of 16
- Different flag handling (no flags register in RISC-V - conditions computed inline)
- Different instruction semantics

**Effort: Medium** - Same patterns, different details.

### CodeGen.agda - Translation

The x86 version has:
```agda
compile-x86 : ∀ {A B} → IR A B → Program

compile-x86 id = mov (reg rax) (reg rdi) ∷ []
compile-x86 fst = mov (reg rax) (mem (base rdi)) ∷ []
compile-x86 snd = mov (reg rax) (mem (base+disp rdi 8)) ∷ []
-- etc.
```

RISC-V needs same structure with different instructions:
```agda
compile-riscv : ∀ {A B} → IR A B → Program

compile-riscv id = mv a0 a0 ∷ []  -- or: addi a0, a0, 0
compile-riscv fst = ld a0 0(a0) ∷ []
compile-riscv snd = ld a0 8(a0) ∷ []
-- etc.
```

**Effort: Medium** - Same IR cases, different instruction sequences.

## What's Pattern-Reusable (Layer 3)

### Correct.agda - Proof Structure

The proof has this structure:

1. **Initial State Setup** (reusable pattern)
   ```agda
   initWithInput : ∀ {A} → ⟦ A ⟧ → State
   initWithInput-rdi : readReg (regs (initWithInput x)) rdi ≡ encode x
   ```

2. **Instruction Execution Helpers** (need rewriting)
   ```agda
   execMov-reg-reg : execInstr s (mov dst src) ≡ just (...)
   execMov-reg-mem : execInstr s (mov dst [src]) ≡ just (...)
   ```
   These prove what each instruction does - need new versions for RISC-V instructions.

3. **Sequence Execution Helpers** (pattern reusable)
   ```agda
   run-single-mov : exec 1 [mov rax rdi] s ≡ just s'
   run-inl-seq : exec 4 (compile-x86 inl) s ≡ just s'
   ```
   Same proof patterns, different instruction counts and details.

4. **Generator Proofs** (structure reusable)
   ```agda
   run-generator-id : exec (compile-x86 id) s ≡ just s' ∧ rax s' ≡ encode (eval id x)
   run-generator-fst : ...
   run-generator-inl : ...
   ```
   Same theorem statements, different proofs using RISC-V helpers.

5. **Composition Proofs** (pattern reusable)
   ```agda
   run-compose : exec (compile-x86 (g ∘ f)) = exec (compile-x86 g) after exec (compile-x86 f)
   run-case-inl : exec (compile-x86 [f,g]) on inl = exec (compile-x86 f)
   run-pair-seq : exec (compile-x86 ⟨f,g⟩) = pair of (exec f, exec g)
   ```

## Reuse Strategy

### Option A: Copy-and-Modify

```
formal/
├── Once/
│   ├── Type.agda           # shared
│   ├── IR.agda             # shared
│   ├── Semantics.agda      # shared
│   ├── Postulates.agda     # shared (add RISC-V encoding axioms)
│   └── Backend/
│       ├── X86/
│       │   ├── Syntax.agda
│       │   ├── Semantics.agda
│       │   ├── CodeGen.agda
│       │   └── Correct.agda
│       └── RiscV64/           # NEW - copy and modify X86
│           ├── Syntax.agda
│           ├── Semantics.agda
│           ├── CodeGen.agda
│           └── Correct.agda
```

**Pros**: Simple, independent
**Cons**: Duplication, proofs drift apart

### Option B: Abstract Backend Interface (Recommended)

```agda
-- Once/Backend/Interface.agda
record Backend : Set₁ where
  field
    Reg    : Set
    Instr  : Set
    State  : Set

    -- ABI conventions
    input-reg  : Reg      -- x86: rdi, RISC-V: a0
    output-reg : Reg      -- x86: rax, RISC-V: a0

    -- State operations
    readReg  : State → Reg → Word
    writeReg : State → Reg → Word → State

    -- Instruction execution
    execInstr : State → Instr → Maybe State

    -- Code generation
    compile : ∀ {A B} → IR A B → List Instr
```

Then:
```agda
-- Once/Backend/Correct.agda (shared proof structure)
module Once.Backend.Correct (B : Backend) where
  open Backend B

  -- Shared theorem structure parameterized by backend
  run-generator : ∀ (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
    -- ... proof uses backend-specific lemmas ...

-- Once/Backend/X86.agda
X86-Backend : Backend
X86-Backend = record { ... }

-- Once/Backend/RiscV64.agda
RiscV64-Backend : Backend
RiscV64-Backend = record { ... }
```

**Pros**: Shared proof structure, type-checked consistency
**Cons**: More upfront design work

### Option C: Literate Proof Template

Create a "proof script" that generates backend-specific proofs:

```
proof-template/
├── generator-proofs.md    # Proof patterns with placeholders
├── compose-proofs.md
└── case-proofs.md

backends/
├── x86-instantiation.agda
└── riscv-instantiation.agda
```

## Effort Estimate

| Component | X86 Lines | RISC-V Effort | Notes |
|-----------|-----------|---------------|-------|
| Syntax.agda | 62 | 100% new | Different ISA |
| Semantics.agda | 315 | 80% new | Same structure, diff registers |
| CodeGen.agda | 259 | 70% new | Same IR cases, diff instructions |
| Correct.agda | 4500+ | 50% new | Proof patterns reusable |
| **Total** | ~5136 | ~60% new | |

**Estimated new code**: ~3000 lines
**Reused patterns**: ~2100 lines worth of structure

## Specific Reusable Components

### 1. Encoding Axioms (100% reusable)

The `Once.Postulates` axioms are architecture-independent:
- `encode-pair-fst/snd` - pair layout is the same
- `encode-inl-tag/val`, `encode-inr-tag/val` - sum layout is the same
- `encode-closure-construct` - closure layout is the same

### 2. Initial State Pattern (90% reusable)

```agda
-- Same pattern, different register name
initWithInput : ∀ {A} → ⟦ A ⟧ → State
initWithInput x = mkstate
  (writeReg emptyRegFile input-reg (encode x))  -- a0 instead of rdi
  encodedMemory
  0     -- pc
  false -- halted
```

### 3. Run-Generator Theorem Structure (100% reusable)

```agda
-- Identical theorem type for all backends
run-generator : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) input-reg ≡ encode x →
  ∃[ s' ] (exec (compile ir) s ≡ just s' ×
           halted s' ≡ true ×
           readReg (regs s') output-reg ≡ encode (eval ir x))
```

### 4. Proof Patterns for Each IR Case

The proof structure for each IR constructor is the same:

**id**: Show `mov output, input` produces `output = input`
**fst**: Show `load output, [input]` produces `output = encode fst`
**snd**: Show `load output, [input+8]` produces `output = encode snd`
**inl**: Show allocation + tag=0 + store produces correct sum encoding
**etc.**

Only the instruction names and register names change.

## Recommended Approach

1. **Start with Option A** (copy-and-modify) for quick progress
2. **Extract commonality** as patterns emerge
3. **Refactor toward Option B** once both backends work

This gives working proofs quickly while building toward a cleaner architecture.

## RISC-V vs x86 Key Differences

| Aspect | x86-64 | RISC-V 64 |
|--------|--------|-----------|
| Registers | 16 (rax-r15) | 32 (x0-x31) |
| Input reg | rdi | a0 (x10) |
| Output reg | rax | a0 (x10) |
| Stack ptr | rsp | sp (x2) |
| Flags | EFLAGS register | No flags (compare produces result) |
| Branches | jz, jnz (check flags) | beq, bne (compare in instruction) |
| Memory ops | mov [addr], reg | sd/ld with offset |
| Addressing | [base+disp] | offset(base) |

## Conclusion

Approximately **40% of the proof effort** can be directly reused:
- Layer 1 (shared modules): 100% reused
- Layer 2 (backend definitions): Structure reused, details new
- Layer 3 (correctness proofs): Theorem statements reused, proofs adapted

The main work is:
1. Defining RISC-V instruction syntax and semantics
2. Writing the code generator for each IR case
3. Proving instruction execution helpers
4. Adapting the run-* lemmas with new instruction sequences

The categorical/semantic correctness structure is completely shared.
