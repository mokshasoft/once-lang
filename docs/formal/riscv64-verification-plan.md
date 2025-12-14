# RISC-V 64 End-to-End Verification Plan

This document outlines the remaining work for a complete end-to-end verification of the Once compiler targeting RISC-V 64.

## Current Status

### What Exists

**100% Complete and Reusable:**
- Core IR semantics (13 generators including `arr`)
- Categorical laws (18 CCC law proofs)
- Type soundness (progress, preservation, canonical forms)
- Elaboration correctness (Surface → IR)
- Desugar correctness (SurfaceIR → CoreIR)
- Optimization correctness
- Polynomial functors (SPF module for recursive types)
- End-to-end theorem structure (composes all phases)

**Completed for x86-64:**
- `Backend/X86/Syntax.agda` - Instruction set definition (~62 lines)
- `Backend/X86/Semantics.agda` - Operational semantics (~315 lines)
- `Backend/X86/CodeGen.agda` - IR → x86-64 translation (~259 lines)
- `Backend/X86/Correct.agda` - Correctness proofs (~4500+ lines)

**COMPLETED for RISC-V 64:**
- `Backend/RiscV64/Syntax.agda` - Instruction set definition (~371 lines) ✓
- `Backend/RiscV64/Semantics.agda` - Operational semantics (~621 lines) ✓
- `Backend/RiscV64/CodeGen.agda` - IR → RISC-V translation (~297 lines) ✓
- `Backend/RiscV64/Correct.agda` - Correctness proofs (~1530 lines) ✓
- `EndToEnd.agda` - Updated with `compilation-correct-riscv` ✓
- `Makefile` - Added `make riscv` target ✓

**PROVEN in Correct.agda (non-postulated):**
- `exec-one-step`, `exec-two-steps` through `exec-six-steps` - Multi-step execution
- `run-fst-seq`, `run-snd-seq` - Projection instruction sequences
- `run-inl-seq`, `run-inr-seq` - Sum construction with full memory tracking
- `compile-fst-correct`, `compile-snd-correct` - Projection correctness
- `compile-id-correct`, `compile-terminal-correct` - Basic generators
- `compile-fold-correct`, `compile-unfold-correct`, `compile-arr-correct` - Type coercions
- `compile-inl-correct`, `compile-inr-correct` - Sum injection correctness

**REMAINING POSTULATES (9 total):**
1. `readReg-writeReg-same-zero` - Logically unprovable (x0 writes ignored), never instantiated
2. `run-generator` - Main induction theorem, requires mutual block
3. `run-curry-seq` - Closure creation (12+ instructions)
4. `run-apply-seq` - Closure application (7 instructions)
5. `compile-compose-correct` - Requires mutual recursion for sub-IRs
6. `compile-pair-correct` - Requires mutual recursion for sub-IRs
7. `compile-case-correct` - Requires mutual recursion for sub-IRs
8. `compile-curry-correct` - Depends on run-curry-seq
9. `compile-apply-correct` - Depends on run-apply-seq

## Lessons Learned from x86-64 Verification

### Critical Insights

1. **`with` patterns block computation**: The operational semantics use `with` to pattern match on runtime values. Proofs cannot use `refl` directly. Solution: introduce postulates at this boundary layer; everything above can be proven by composition.

2. **Use computed labels**: Placeholder labels (100, 200, 300) cause proof failures because jump targets don't match actual instruction positions. Solution: use `compile-length` function to compute instruction counts and calculate actual jump targets.

3. **Mutual recursion for recursive IR cases**: The recursive IR constructors (`∘`, `[ , ]`, `⟨ , ⟩`) require mutual induction in the main theorem since their proofs need the theorem for sub-IRs.

4. **Encoding axioms bridge semantics and machine state**: Construction axioms are essential for stack-allocated values (pairs, sums) where code builds the encoding rather than receiving it.

5. **Type extensions cause metavariables**: When adding type constructors, provide explicit type annotations at every pattern match to avoid unsolved metavariables.

## Work Plan

### Phase 1: RISC-V Syntax Definition

**Goal:** Define RISC-V 64 instruction set AST

**Create:** `formal/Once/Backend/RiscV64/Syntax.agda`

```agda
module Once.Backend.RiscV64.Syntax where

-- 32 registers (x0-x31) with ABI names
data Reg : Set where
  zero ra sp gp tp          : Reg  -- x0-x4
  t0 t1 t2                  : Reg  -- x5-x7 (temporaries)
  s0 s1                     : Reg  -- x8-x9 (saved, s0=fp)
  a0 a1 a2 a3 a4 a5 a6 a7   : Reg  -- x10-x17 (arguments/return)
  s2 s3 s4 s5 s6 s7 s8 s9   : Reg  -- x18-x25 (saved)
  s10 s11                   : Reg  -- x26-x27 (saved)
  t3 t4 t5 t6               : Reg  -- x28-x31 (temporaries)

-- RISC-V instruction formats
data Instr : Set where
  -- R-type: register-register operations
  add sub and or xor sll srl sra slt sltu : Reg → Reg → Reg → Instr

  -- I-type: immediate operations
  addi andi ori xori slti sltiu : Reg → Reg → ℤ → Instr

  -- Load instructions (I-type)
  ld lw lh lb ldu lwu lhu lbu : Reg → ℤ → Reg → Instr  -- rd ← offset(rs1)

  -- S-type: store instructions
  sd sw sh sb : Reg → ℤ → Reg → Instr  -- rs2 → offset(rs1)

  -- B-type: conditional branches
  beq bne blt bge bltu bgeu : Reg → Reg → ℕ → Instr  -- compare rs1, rs2; branch to label

  -- U-type: upper immediate
  lui auipc : Reg → ℤ → Instr

  -- J-type: unconditional jump
  jal : Reg → ℕ → Instr  -- rd ← pc+4; pc ← label
  jalr : Reg → Reg → ℤ → Instr  -- rd ← pc+4; pc ← (rs1 + imm) & ~1

  -- Pseudo-instructions (for readability)
  li : Reg → ℤ → Instr           -- load immediate
  mv : Reg → Reg → Instr         -- rd ← rs (addi rd, rs, 0)
  j : ℕ → Instr                  -- unconditional jump (jal zero, label)
  call : ℕ → Instr               -- function call (jal ra, label)
  ret : Instr                    -- return (jalr zero, ra, 0)
  nop : Instr                    -- no-op (addi zero, zero, 0)
  label : ℕ → Instr              -- label marker (not a real instruction)
```

**Effort:** 1-2 days
**Key difference from x86:** More registers (32 vs 16), no flags register, load-store architecture

---

### Phase 2: RISC-V Operational Semantics

**Goal:** Define execution semantics for RISC-V instructions

**Create:** `formal/Once/Backend/RiscV64/Semantics.agda`

Key components:
1. **State record**: registers (32), memory, pc, halted
2. **Register file operations**: `readReg`, `writeReg` for 32 registers
3. **Memory operations**: `readMem`, `writeMem` (64-bit words)
4. **Per-instruction execution**: `execInstr` for each instruction type
5. **Stepping functions**: `step`, `exec`, `run`

**Key differences from x86:**
| Aspect | x86-64 | RISC-V 64 |
|--------|--------|-----------|
| Registers | 16 | 32 |
| Input reg (ABI) | rdi | a0 |
| Output reg (ABI) | rax | a0 |
| Stack pointer | rsp | sp |
| Flags | EFLAGS register | No flags (inline comparison) |
| Branches | jz/jnz check EFLAGS | beq/bne compare two registers |
| Memory ops | Complex addressing modes | Simple base+offset only |

**Effort:** 3-5 days
**Lines estimate:** ~400 (vs ~315 for x86 due to more registers)

---

### Phase 3: RISC-V Code Generation

**Goal:** Translate IR to RISC-V 64 instructions

**Create:** `formal/Once/Backend/RiscV64/CodeGen.agda`

Translation for each IR generator:

| Generator | x86-64 | RISC-V 64 |
|-----------|--------|-----------|
| `id` | `mov rax, rdi` | `mv a0, a0` (or `addi a0, a0, 0`) |
| `fst` | `mov rax, [rdi]` | `ld a0, 0(a0)` |
| `snd` | `mov rax, [rdi+8]` | `ld a0, 8(a0)` |
| `inl` | alloc + tag=0 + store | `addi sp, sp, -16; sd zero, 0(sp); sd a0, 8(sp); mv a0, sp` |
| `inr` | alloc + tag=1 + store | `addi sp, sp, -16; li t0, 1; sd t0, 0(sp); sd a0, 8(sp); mv a0, sp` |
| `case` | `cmp [rdi], 0; jne` | `ld t0, 0(a0); bne t0, zero, label` |
| `terminal` | `mov rax, 0` | `li a0, 0` |
| `initial` | (absurd) | (absurd) |
| `fold/unfold` | `mov rax, rdi` | `mv a0, a0` |
| `arr` | `mov rax, rdi` | `mv a0, a0` |
| `curry` | closure creation | closure creation (similar structure) |
| `apply` | indirect call | `jalr ra, t0, 0` |
| `compose` | `f ++ mov rdi, rax ++ g` | `f ++ mv a0, a0 ++ g` |
| `pair` | stack alloc + compute both | stack alloc + compute both |

**Key insight:** RISC-V uses a0 for both input and output (unlike x86's rdi/rax split). This simplifies some cases but requires careful register management in compose.

**Also needed:** `compile-length` function computing exact instruction counts for computed labels.

**Effort:** 3-4 days
**Lines estimate:** ~300 (vs ~259 for x86)

---

### Phase 4: RISC-V Correctness Proofs

**Goal:** Prove code generation preserves semantics

**Create:** `formal/Once/Backend/RiscV64/Correct.agda`

#### 4.1 Encoding Axioms (reuse from x86)

These are architecture-independent:
- `encode-pair-fst/snd` - pair memory layout
- `encode-inl-tag/val`, `encode-inr-tag/val` - sum memory layout
- `encode-closure-construct` - closure memory layout

**Effort:** Can copy from x86, just update register names in comments

#### 4.2 Initial State Setup

```agda
initWithInput : ∀ {A} → ⟦ A ⟧ → State
initWithInput x = mkstate
  (writeReg emptyRegFile a0 (encode x))  -- a0 instead of rdi
  encodedMemory
  0      -- pc
  false  -- halted
```

**Effort:** Low - copy pattern, change register

#### 4.3 Single-Instruction Execution Helpers (postulated)

```agda
postulate
  run-single-mv : ∀ (s : State) (dst src : Reg) →
    halted s ≡ false → pc s ≡ 0 →
    ∃[ s' ] (run (mv dst src ∷ []) s ≡ just s'
           × readReg (regs s') dst ≡ readReg (regs s) src
           × halted s' ≡ true)

  run-single-ld : ∀ (s : State) (dst : Reg) (offset : ℤ) (base : Reg) →
    halted s ≡ false → pc s ≡ 0 →
    ∃[ s' ] (run (ld dst offset base ∷ []) s ≡ just s'
           × readReg (regs s') dst ≡ readMem (mem s) (readReg (regs s) base + offset)
           × halted s' ≡ true)
```

**Key lesson:** These postulates are unavoidable due to `with` patterns in operational semantics. Keep them minimal and layer proofs on top.

**Effort:** 1-2 days for all instruction helpers

#### 4.4 Per-Generator Proofs

For each IR generator, prove:
```agda
run-generator-X : ∀ (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false → pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] (run (compile-riscv X) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode (eval X x))
```

**Base cases (no recursion):**
- `run-generator-id` - trivial (mv preserves input)
- `run-generator-terminal` - li a0, 0
- `run-generator-fold/unfold/arr` - mv preserves input + encoding axiom
- `run-generator-fst` - ld a0, 0(a0) + encoding axiom
- `run-generator-snd` - ld a0, 8(a0) + encoding axiom
- `run-generator-inl` - stack alloc sequence + encoding construction
- `run-generator-inr` - stack alloc sequence + encoding construction

**Recursive cases (mutual recursion cluster):**
- `run-generator-compose` - sequence execution + IH for f and g
- `run-generator-case` - branch + IH for f (inl) or g (inr)
- `run-generator-pair` - interleaved execution + IH for f and g

**Higher-order cases:**
- `run-generator-curry` - closure creation (uses fetch postulates)
- `run-generator-apply` - indirect call (most complex)

**Effort:** 2-3 weeks (largest single phase)
**Lines estimate:** ~4000-5000

#### 4.5 Main Theorem

```agda
codegen-riscv-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-riscv ir) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode (eval ir x))
```

Uses per-generator proofs via case analysis on IR constructor.

---

### Phase 5: End-to-End Integration

**Goal:** Connect RISC-V backend to existing end-to-end theorem

**Modify:** `formal/Once/EndToEnd.agda`

The existing end-to-end structure:
```agda
-- Current (x86 only)
end-to-end : ∀ e →
  run (compile-x86 (optimize (desugar (elaborate e)))) (initWithInput ...) ≡ ...

-- New (backend-parameterized or duplicated)
end-to-end-riscv : ∀ e →
  run (compile-riscv (optimize (desugar (elaborate e)))) (initWithInput ...) ≡ ...
```

**Option A:** Duplicate theorem for RISC-V
**Option B:** Parameterize by backend (requires interface module)

**Effort:** 2-3 days

---

### Phase 6: Build System Updates

**Goal:** Enable `make riscv` and update `make all`

**Modify:** `formal/Makefile`

```makefile
RISCV_SYNTAX := formal/Once/Backend/RiscV64/Syntax.agda
RISCV_SEMANTICS := formal/Once/Backend/RiscV64/Semantics.agda
RISCV_CODEGEN := formal/Once/Backend/RiscV64/CodeGen.agda
RISCV_CORRECT := formal/Once/Backend/RiscV64/Correct.agda

riscv: $(RISCV_SYNTAX) $(RISCV_SEMANTICS) $(RISCV_CODEGEN) $(RISCV_CORRECT)
    $(AGDA) $(RISCV_CORRECT)

all: ... riscv
```

**Effort:** 1 hour

---

## Summary: Work Breakdown

| Phase | Description | Effort | Lines Est. |
|-------|-------------|--------|------------|
| 1 | Syntax.agda (instruction AST) | 1-2 days | ~80 |
| 2 | Semantics.agda (operational semantics) | 3-5 days | ~400 |
| 3 | CodeGen.agda (IR → RISC-V) | 3-4 days | ~300 |
| 4 | Correct.agda (correctness proofs) | 2-3 weeks | ~4500 |
| 5 | EndToEnd integration | 2-3 days | ~50 |
| 6 | Makefile updates | 1 hour | ~10 |
| **Total** | | **4-5 weeks** | **~5300** |

## Reuse Summary

| Component | Reuse % | Notes |
|-----------|---------|-------|
| Layer 1 (Types, IR, Semantics, Laws) | 100% | Completely shared |
| Encoding axioms | 100% | Architecture-independent |
| Proof structure | 100% | Same theorem statements |
| Instruction definitions | 0% | Different ISA |
| Operational semantics | 20% | Same patterns, different details |
| Code generation | 30% | Same IR cases, different instructions |
| Correctness proofs | 50% | Patterns reusable, details new |

**Overall:** ~40% of effort reused from x86-64 work.

## Risk Mitigation

### Risk 1: RISC-V branch semantics complexity
**Mitigation:** RISC-V branches are actually simpler (compare two registers vs check flags). May be easier than x86.

### Risk 2: More registers = more cases
**Mitigation:** Most proofs only care about a0, sp, and temporaries. 32 registers don't mean 2x the work.

### Risk 3: Load-store architecture differences
**Mitigation:** RISC-V's simple addressing (base+offset only) is actually easier to model than x86's complex addressing modes.

### Risk 4: Closure calling convention
**Mitigation:** Start with curry/apply postulated (like x86), fill in proofs later.

## Recommended Execution Order

1. **Start simple:** Syntax.agda (get the ISA right)
2. **Test semantics:** Write Semantics.agda, test with unit proofs
3. **Parallel work:** CodeGen.agda can be started once Syntax.agda is done
4. **Bottom-up proofs:** Prove base cases first (id, fst, snd, terminal)
5. **Mutual recursion:** Tackle compose/case/pair together
6. **Closures last:** curry/apply are the hardest
7. **Integration:** Connect to EndToEnd.agda

## Success Criteria

1. `make riscv` type-checks all RISC-V modules
2. `codegen-riscv-correct` theorem proven for all 14 IR generators
3. `end-to-end-riscv` theorem connects surface syntax to RISC-V
4. All postulates documented in central registry (Postulates.agda or RiscV64/Correct.agda)
