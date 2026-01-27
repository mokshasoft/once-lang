# OCP-0003: PrimContract - Unified Interface for Domain Compilers

## Status

Draft

## Summary

Define `PrimContract` as a uniform interface that domain compilers (Arith, future Loop compiler, IO interpretations) must satisfy. This eliminates the `run-prim-star-vv` postulate and provides a clean integration point between the CCC compiler and external/domain-specific code generators.

## Motivation

### Current Problems

1. **ArithIR carried through CCC**: The IR datatype has an `Arith` constructor that carries the entire arithmetic expression tree to the CCC compiler, creating coupling between domains.

2. **Postulated Prim correctness**: The `run-prim-star-vv` postulate in `StarBase.agda` is trusted code that assumes Prim operations are correct without proof.

3. **No clear interface**: Domain compilers (Arith) don't have a defined contract specifying what proofs they must provide.

### Intended Architecture

```
Source Code
    │
    ▼
Elaborator (recognizes arithmetic patterns)
    │
    ├──► Arith Compiler ──► Program + PrimContract proof
    │                              │
    ▼                              ▼
CCC Compiler (sees Prim node) ◄────┘
    │
    ▼
x86/AArch64/RISC-V Code
```

The Arith compiler runs immediately when an arithmetic pattern is recognized, producing:
1. A compiled `Program` (x86 instructions)
2. A `PrimContract` proof that the program is correct

CCC only sees a `Prim` node referencing the compiled block, not the ArithIR tree.

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
-- Before: ArithIR carried through
data IR : Type → Type → Set where
  ...
  Arith : NumType → ArithIR → IR A B  -- Carries expression tree
  Prim  : String → IR A B             -- Opaque name

-- After: Only Prim, with associated contract
data IR : Type → Type → Set where
  ...
  Prim : String → IR A B              -- Opaque primitive

-- Contract lookup (populated by domain compilers)
prim-contracts : String → ∃[ A ] ∃[ B ] ∃[ sem ] PrimContract {A} {B} sem
```

## Integration Path

### Phase 1: Define PrimContract
1. Create `Once/Backend/X86/Correct/PrimContract.agda`
2. Define the `PrimContract` record
3. Create helper lemmas for constructing contracts

### Phase 2: Arith Integration
1. Update Arith compiler to produce `PrimContract` proofs
2. This requires lifting ArithState proofs to x86 State proofs
3. Either rewrite Arith proofs against x86 State, or create embedding/adapter

### Phase 3: Eliminate Postulates
1. Replace `run-prim-star-vv` with `run-prim-from-contract`
2. Remove `Arith` constructor from IR
3. Update elaborator to run Arith compiler immediately

### Phase 4: IO Interpretations
1. Define contracts for IO operations (print, read, etc.)
2. System calls become Prim nodes with contracts

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

- `Once/Backend/X86/Correct/StarBase.agda`: Current `run-prim-star-vv` postulate
- `Once/Backend/X86/Correct/IRStarDerived.agda`: Ownership integration documentation
- `Once/Arith/Backend/X86/Correct.agda`: Current Arith proof structure
- `Once/Arith/Boundary.agda`: Current Arith-CCC boundary
