# Once Compiler Verification Architecture

**Status**: Active Design
**Created**: 2026-01-02
**Goal**: Verify the Once compiler for all Once programs (CompCert-level verification)

---

## Executive Summary

This document describes the architecture for **verifying the Once compiler**, not individual Once programs.

### What We're Proving

**Compiler Correctness**: For all Once programs, the compiler preserves semantics:
```
∀ Once program P,
  executing compile(P) produces the same behavior as eval(P)
```

This includes:
- Pure Once programs (using only IR combinators)
- Once programs using Interpretations (File.once, syscalls.once, etc.)
- Programs in the Derived Stratum (Linux.Derived, Windows.Derived, etc.)

### What We're NOT Proving

**Program Verification**: Proving that a specific Once program satisfies some property.

Examples of things we do NOT prove:
- "This Once program correctly computes factorial"
- "This Once program satisfies specification X"
- "This Once program has property P"

**Analogy**: CompCert proves the C compiler is correct, not that your C program is correct.

---

## Table of Contents

1. [Clarification: "Open" vs "Closed" Was Wrong](#clarification-open-vs-closed-was-wrong)
2. [The Correct Architecture](#the-correct-architecture)
3. [Verification Layers](#verification-layers)
4. [The Derived Stratum](#the-derived-stratum)
5. [Implementation Roadmap](#implementation-roadmap)
6. [Comparison with CompCert](#comparison-with-compcert)

---

## Clarification: "Open" vs "Closed" Was Wrong

### The Mistake

Earlier architecture documents split verification into:
- **Closed track**: Prove generators for pure Once programs (zero postulates)
- **Open track**: Prove generators for programs with FFI (with axioms)

**This was conceptually wrong** because it suggested:
- The *generators themselves* differ based on context
- We need to prove generators twice
- FFI/Interpretations are a generator concern

### The Insight

The generators are the same regardless of what programs use them! The distinction should be:

1. **Compiler Verification** (this work): Prove the compiler is correct for ALL Once programs
2. **Program Verification** (separate, future work): Prove a specific program satisfies a property

### Why "Open" Was Misleading

"Open" suggested we're proving generators for programs with unknown external code. But:
- We're not verifying *programs* at all - we're verifying the *compiler*
- Interpretations have *semantic contracts* (axiomatized), not unknown behavior
- The compiler is proven correct once, for all programs

---

## The Correct Architecture

### Verification Scope: The Once Compiler

```
┌─────────────────────────────────────────────────────────────┐
│                  Once Compiler Verification                  │
│                                                              │
│  Proves: ∀ Once program P,                                  │
│          compile(P) preserves semantics of eval(P)          │
│                                                              │
│  Components:                                                 │
│  1. Surface → IR elaboration                                │
│  2. IR → Machine code generation (AArch64, x86-64, RV64)   │
│  3. Interpretation semantic contracts                        │
│                                                              │
│  Result: Compiler is proven correct for ALL Once programs   │
└─────────────────────────────────────────────────────────────┘
                            │
                            │ Enables (but does not prove)
                            ↓
┌─────────────────────────────────────────────────────────────┐
│              Once Program Verification (Future)              │
│                                                              │
│  Given: Compiler is verified                                │
│  Prove: Specific program P satisfies property X             │
│                                                              │
│  User composes:                                             │
│  - Compiler correctness theorem (our work)                  │
│  - Program-specific proof of X                              │
│                                                              │
│  Result: End-to-end verification of program behavior        │
└─────────────────────────────────────────────────────────────┘
```

### Key Principle

**We verify the compiler infrastructure.** Users can build program proofs on top of it.

Like CompCert:
- CompCert verifies the C compiler
- Users can verify their C programs *using* CompCert's compiler correctness theorem
- CompCert doesn't prove your program is correct, but guarantees compilation doesn't break correctness

---

## Verification Layers

The Once compiler has three verification layers, all proven simultaneously:

### Layer 1: IR Code Generation (Backend)

**What**: Prove IR combinators compile to correct machine code

**For each backend** (AArch64, x86-64, RV64):
```agda
∀ (IR term f : IR i A B) (input : ⟦ A ⟧),
  executing compile-backend(f) on encode(input)
  produces encode(eval f input)
```

**IR Combinators Covered**:
- Pure: id, ∘, fst, snd, ⟨_,_⟩, inl, inr, [_,_], terminal, initial
- Higher-order: curry, apply
- Recursive: fold, unfold
- Effectful: arr (lift pure to Eff)

**Current Status**:
- AArch64: Phase 1 (eliminate postulates in IR generators)
- x86-64: Not started
- RV64: Partially done (Star-based proofs exist)

**Postulates**: 1 per backend (sp-bound runtime guarantee)

---

### Layer 2: Surface → IR Elaboration (Frontend)

**What**: Prove Surface syntax elaborates to correct IR

```agda
∀ (Surface program S : Surface A),
  eval-IR(elaborate(S)) ≡ eval-Surface(S)
```

**Elaboration Steps**:
1. **Parsing** (out of scope - parser correctness assumed)
2. **Type checking** (QTT-based, already implemented)
3. **Surface → IR translation** (needs verification)
   - Let bindings → compose
   - Pattern matching → case analysis
   - Lambda → curry
   - Function application → apply

**Current Status**: Not started

**Key Challenge**: Proving elaboration preserves semantics

---

### Layer 3: Interpretation Semantics (FFI/Effects)

**What**: Axiomatize semantic contracts for each Interpretation

Each Interpretation (File.once, syscalls.once, memory.once, etc.) has:
1. **Interface specification**: Types and operations
2. **Semantic contract**: What each operation does (axiomatized)
3. **Implementation verification** (optional): Prove .c implementation satisfies contract

**Example - File.once**:
```agda
-- Semantic contract (axiomatized)
postulate
  file-read-semantics : ∀ (handle : FileHandle) (n : ℕ),
    eval (read handle n) ≡ readFromOS(handle, n)

  file-write-semantics : ∀ (handle : FileHandle) (data : Buffer),
    eval (write handle data) ≡ writeToOS(handle, data)
```

**Current Status**: Not started

**Postulates**: One axiom per Interpretation operation (semantic contract)

---

## The Derived Stratum

### What Is It?

The **Derived Stratum** is the compiled output of Interpretations:
- `Linux.Derived`: Compiled Linux syscalls + File + memory operations
- `Windows.Derived`: Compiled Windows API calls
- `macOS.Derived`: Compiled macOS operations

### Why It's Automatically Verified

**If we prove**:
1. IR code generators are correct (Layer 1) ✓
2. Surface → IR elaboration is correct (Layer 2) ✓
3. Interpretations have semantic contracts (Layer 3) ✓

**Then the Derived Stratum is automatically correct** because it's the result of:
```
Interpretations (verified)
  → elaborate to IR (Layer 2 ✓)
  → compile to machine code (Layer 1 ✓)
  = Derived Stratum (correct by composition)
```

### Concrete Example

**Linux.Derived** is generated from:
1. `syscalls.once` (Interface with semantic contract)
2. `syscalls.c` (Implementation, optionally verified)
3. `File.once` (Built on syscalls, semantic contract)
4. `memory.once` (malloc/free, semantic contract)

**Compiler does**:
```
parse(syscalls.once)
  → type-check
  → elaborate to IR
  → compile to AArch64/x86/RV64
  = Linux.Derived (proven correct!)
```

**No additional verification needed** for Derived Stratum if the three layers are proven.

---

## Implementation Roadmap

### Current Focus: Layer 1 (AArch64 IR Generators)

**Phase 1**: Eliminate postulates in IR code generation
- ✅ Phase 1.0: Document architecture
- ✅ Phase 1.1: Prove preserve-stack-inv lemma
- ⏳ Phase 1.2: Eliminate postulates in MutualIR.agda (1-2 weeks)
  - Make run-curry produce CurryResult with closure-wf
  - Prove thunk execution in mutual block
  - Thread ClosureWellFormed through pair/compose
  - Use run-apply-with-wf (eliminate apply-produces-result)
- ⏳ Phase 1.3: Write example proofs (1-2 days)
- ⏳ Phase 1.4: Validation (1-2 hours)

**Result**: AArch64 IR generators proven correct (1 runtime axiom: sp-bound)

---

### Future: Layer 2 (Surface → IR Elaboration)

**Phase 2**: Prove elaboration correctness
1. Define Surface semantics formally
2. Prove each elaboration rule preserves semantics:
   - Let bindings → compose
   - Pattern matching → case
   - Lambda → curry
   - Application → apply
3. Prove full elaboration theorem

**Estimated Effort**: 2-3 months

---

### Future: Layer 3 (Interpretation Contracts)

**Phase 3**: Axiomatize Interpretation semantics
1. For each Interpretation (File, syscalls, memory):
   - Define semantic contract (axioms)
   - Document expected OS behavior
2. Optionally: Verify .c implementations against contracts

**Estimated Effort**: 1-2 months

---

### Future: End-to-End Theorem

**Phase 4**: Compose all layers into final theorem

```agda
once-compiler-correct : ∀ (P : Surface Program),
  behavior(compile(P)) ≡ behavior(eval-surface(P))
```

This composes:
- Layer 1: IR → Machine code correctness
- Layer 2: Surface → IR elaboration correctness
- Layer 3: Interpretation semantic contracts

**Estimated Effort**: 1 month (mostly composition)

---

## Comparison with CompCert

| Aspect | CompCert | Once (This Work) |
|--------|----------|------------------|
| **What's Verified** | C compiler | Once compiler |
| **Scope** | C → Assembly | Surface → IR → Machine code |
| **Backends** | ARM, x86, PowerPC, RISC-V | AArch64, x86-64, RV64 |
| **FFI/External** | Axiomatized external functions | Axiomatized Interpretations |
| **Frontend** | C parsing + typing | Surface parsing + QTT typing |
| **Middle** | RTL, LTL optimizations | IR combinators (categorical) |
| **Backend** | Register allocation, code gen | IR → Machine code (direct) |
| **Postulates** | ~10 (memory model, external fns) | ~3-5 (runtime, Interpretations) |
| **Program Verification** | Not included (users build on top) | Not included (users build on top) |
| **Derived Code** | N/A | Derived Stratum (auto-verified) |

**Key Similarities**:
- Both verify the *compiler*, not programs
- Both axiomatize external/FFI boundaries
- Both provide infrastructure for program verification

**Key Differences**:
- Once has cleaner categorical IR (easier to prove)
- Once has Derived Stratum (auto-verified compiled Interpretations)
- CompCert has more optimizations (Once is direct compilation)

---

## FAQ

### Q: Why not verify Once programs directly?

**A**: That's application-specific verification, not compiler verification. We provide the infrastructure; users prove their programs using it.

### Q: What about programs using Interpretations?

**A**: Interpretations have semantic contracts (axioms). The compiler preserves these contracts. Users' programs are verified against the contracts, not against OS internals.

### Q: Why axiomatize Interpretations instead of proving them?

**A**: Interpretations call OS syscalls, which are outside our control. We can optionally verify the .c implementations against contracts, but the OS behavior itself is axiomatized (like CompCert's external functions).

### Q: Is the Derived Stratum trusted?

**A**: No! It's automatically verified because it's the compiled output of verified Interpretations through a verified compiler. No additional trust needed.

### Q: How does this help Once users?

**A**: Users can write Once programs and *trust the compilation is correct*. If they prove their Once program satisfies property X, they know the compiled code also satisfies X (modulo Interpretation contracts).

---

## Success Criteria

The Once compiler is **verified** when:

- ✅ Layer 1: All backend IR generators proven correct (1 runtime axiom each)
- ✅ Layer 2: Surface → IR elaboration proven correct
- ✅ Layer 3: All Interpretations have semantic contracts
- ✅ End-to-end theorem: `compile(P)` preserves `eval(P)` for all Once programs
- ✅ Derived Stratum is automatically correct (by composition)
- ✅ Documentation: Complete proof architecture + example usage

**Result**: CompCert-level verification for the Once compiler.

Users can then build program-specific verification on top of this infrastructure.

---

## Next Steps

1. **Complete Layer 1 (AArch64)**: Eliminate IR generator postulates (1-2 weeks)
2. **Port to other backends**: x86-64, RV64 (use AArch64 as template)
3. **Start Layer 2**: Begin Surface → IR elaboration proofs
4. **Document Interpretations**: Write semantic contracts for each Interpretation

**Long-term Goal**: Full stack verification (Surface → Machine code) for all Once programs.

---

## Conclusion

This architecture provides **compiler verification** for Once, similar to CompCert's approach for C.

**Key Insight**: We verify the compiler, not individual programs. The "Open vs Closed" split was wrong - there's only one compiler, and it's correct for ALL Once programs (pure or with Interpretations).

**The Derived Stratum is automatically verified** because it's the result of compiling verified Interpretations through a verified compiler.

Users get a **verified compilation infrastructure** they can build program proofs on top of.
