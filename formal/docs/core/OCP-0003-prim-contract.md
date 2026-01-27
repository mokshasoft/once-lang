# OCP-0003: PrimContract - Unified Interface for Domain Compilers

## Status

Draft

## Summary

Define `PrimContract` as a uniform interface that domain compilers (Arith, future Loop compiler, IO interpretations) must satisfy. This eliminates the `run-prim-star-vv` postulate and provides a clean integration point between the CCC compiler and external/domain-specific code generators.

## Motivation

### Current Problems

1. **ArithIR carried through CCC**: The IR datatype has an `Arith` constructor that carries the entire arithmetic expression tree to the CCC compiler, creating coupling between domains.

2. **Postulated Prim correctness**: The `run-prim-star-vv` postulate in `StarBase.agda` is trusted code that assumes Prim operations are correct without proof.

3. **Postulated evalPrim**: The `evalPrim` postulate in `SemanticBase.agda` defines primitive semantics without proof - we just trust that primitives compute what we expect.

4. **Boundary.agda indirection**: The current design converts ArithIR → IR with string-named `Prim` nodes (e.g., `Prim "arith.add.int"`) via Boundary.agda, then CCC looks up these names. This indirection is unnecessary.

5. **No clear interface**: Domain compilers (Arith) don't have a defined contract specifying what proofs they must provide.

### Intended Architecture

```
Source Code
    │
    ▼
Elaborator (recognizes arithmetic patterns)
    │
    ├──► Arith Compiler ──► (Program, PrimContract proof)
    │                                    │
    ▼                                    ▼
CCC Compiler ◄───────────────────────────┘
    │         receives proven assembly block directly
    ▼
x86/AArch64/RISC-V Code
```

The Arith compiler runs immediately when an arithmetic pattern is recognized, producing:
1. A compiled `Program` (x86 assembly block)
2. A `PrimContract` proof that the assembly is correct

Key points:
- CCC receives the **proven assembly block directly** - no string-named Prim indirection
- The `PrimContract` IS the proof (Agda-verified), not a claim to be trusted
- No postulates: `prim-correct` must be constructed and type-checked by Agda
- Boundary.agda is eliminated - no need to convert ArithIR → IR with Prim nodes

## Design

### PrimContract Definition

```agda
-- | PrimContract: What a domain compiler must provide
--
-- Parameterized by:
--   A, B  : Input and output types
--   sem   : Semantic function (what the operation computes)
--
record PrimContract {A B : Type} (sem : ⟦ A ⟧ → ⟦ B ⟧) : Set₁ where
  field
    -- The compiled program
    prim-program : Program

    -- Main correctness theorem
    prim-correct : ∀ (x : ⟦ A ⟧) (s : State) →
      -- Preconditions
      halted s ≡ false →
      ValidAt x (readReg (regs s) rdi) (memory s) →
      (∀ addr → InStack addr → readReg (regs s) rdi ≢ addr) →
      StackInvariant s →
      StackCapacity s prim-stack-requirement →
      RbpInvariant s →
      -- Postconditions
      ∃[ s' ] (
        -- Execution trace
        Star prim-program s s' ×
        halted s' ≡ false ×

        -- Semantic correctness: result equals sem x
        ValidAt (sem x) (readReg (regs s') rax) (memory s') ×

        -- Register preservation (callee-saved)
        readReg (regs s') r14 ≡ readReg (regs s) r14 ×
        readReg (regs s') r15 ≡ readReg (regs s) r15 ×
        readReg (regs s') rbp ≡ readReg (regs s) rbp ×
        readReg (regs s') rsp ≡ readReg (regs s) rsp ×

        -- Memory preservation (Ownership model)
        -- Addresses ≥ entry-rsp are not modified
        (∀ addr → addr ≥ readReg (regs s) rsp →
           readMem (memory s') addr ≡ readMem (memory s) addr) ×

        -- Invariants preserved
        StackInvariant s' ×
        RbpInvariant s'
      )

    -- Stack requirement for this primitive
    prim-stack-requirement : ℕ
```

### Key Design Decisions

1. **Semantic function as parameter**: The contract is parameterized by `sem : ⟦ A ⟧ → ⟦ B ⟧`, making the expected behavior explicit rather than derived from IR structure.

2. **Memory preservation via Ownership model**: Uses `addr ≥ entry-rsp` bound, consistent with the Ownership model used throughout the CCC proofs.

3. **Explicit stack requirement**: Each primitive declares its stack needs, enabling capacity threading.

### Using PrimContract

```agda
-- Arith provides contracts for arithmetic operations
arith-add-contract : PrimContract {Int × Int} {Int} (λ (a , b) → a + b)
arith-mul-contract : PrimContract {Int × Int} {Int} (λ (a , b) → a * b)

-- IO interpretations provide contracts for system calls
print-contract : PrimContract {String} {Unit} print-sem

-- Eliminate run-prim-star-vv postulate
run-prim-from-contract : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) →
  (contract : PrimContract sem) →
  ... →
  ∃[ s' ] IRStarResultV (Prim name) prog s s' x offset
run-prim-from-contract sem contract =
  -- Extract fields from contract, construct IRStarResultV
```

### IR Changes

```agda
-- Before: ArithIR carried through, string-named Prims
data IR : Type → Type → Set where
  ...
  Arith : NumType → ArithIR → IR A B  -- Carries expression tree
  Prim  : String → IR A B             -- Opaque name (looked up by string)

-- After: Proven assembly blocks directly
data IR : Type → Type → Set where
  ...
  -- Option A: Prim holds the contract directly
  Prim : ∀ {sem} → PrimContract sem → IR A B

  -- Option B: Prim holds reference to externally-provided contract
  -- (simpler for code generation, contract passed separately)
```

The key change: **no string-based lookup**. The assembly and its proof travel together as a `PrimContract`. CCC receives proven code, not a name to look up.

## Integration Path

### Phase 1: Define PrimContract ✓
1. Create `Once/Backend/X86/Correct/PrimContract.agda`
2. Define the `PrimContract` and `PrimResult` records
3. Create helper lemmas for constructing contracts

### Phase 2: Arith Integration
1. Rewrite Arith proofs directly against x86 State (cleaner than ArithState adapter)
2. Create `Once/Arith/Backend/X86/Contract.agda` with PrimContract instances
3. Arith compiler produces `(Program, PrimContract)` pairs

### Phase 3: Eliminate Postulates and Dead Code
1. Replace `run-prim-star-vv` postulate with proof from PrimContract
2. Eliminate `evalPrim` postulate - semantics now explicit in contract's `sem` parameter
3. Remove `Arith` constructor from IR datatype
4. **Eliminate `Once/Arith/Boundary.agda`** - no longer needed:
   - Was: ArithIR → embedArith → IR with `Prim "name"` nodes → CCC
   - Now: ArithIR → Arith compiler → (Program, PrimContract) → CCC directly
5. Remove string-based primitive lookup infrastructure

### Phase 4: IO Interpretations
1. Define contracts for IO operations (print, read, etc.)
2. IO operations provide `(Program, PrimContract)` pairs directly

## Future Work: PrimContract as Foundation for All IRs

The PrimContract design could be extended to prove all CCC operations:

```agda
-- Each CCC generator provides a contract
id-contract    : PrimContract (λ x → x)
fst-contract   : PrimContract proj₁
snd-contract   : PrimContract proj₂
inl-contract   : PrimContract inj₁
inr-contract   : PrimContract inj₂

-- Combinators transform contracts
compose-contract : PrimContract f → PrimContract g → PrimContract (g ∘ f)
pair-contract    : PrimContract f → PrimContract g → PrimContract (λ x → f x , g x)
curry-contract   : PrimContract f → PrimContract (curry f)
```

This would unify the proof structure across:
- CCC categorical generators
- Domain compilers (Arith, Loop)
- IO interpretations

**Benefits**:
- Uniform interface for all proofs
- Easier to add new backends (implement PrimContract for each generator)
- Cleaner separation between semantics and proof obligations

**Trial architecture**: Could prototype this approach on AArch64 or RISC-V backend, which have less existing proof infrastructure.

## Related Work

- **OCP-0001**: Orthogonal Arithmetic Compiler (current Arith design)
- **OCP-0002**: Type conversion support in Arith
- **Ownership model**: Memory preservation via `caller-input-owned`, `owned-caller-preserved`

## References

- `Once/Backend/X86/Correct/StarBase.agda`: Current `run-prim-star-vv` postulate (to be eliminated)
- `Once/Backend/X86/Correct/PrimContract.agda`: New PrimContract interface (Phase 1 complete)
- `Once/Backend/X86/Correct/IRStarDerived.agda`: Ownership integration documentation
- `Once/SemanticBase.agda`: Current `evalPrim` postulate (to be eliminated)
- `Once/Arith/Backend/X86/Correct.agda`: Current Arith proof structure (reference for rewrite)
- `Once/Arith/Boundary.agda`: Current Arith-CCC boundary (to be eliminated)
