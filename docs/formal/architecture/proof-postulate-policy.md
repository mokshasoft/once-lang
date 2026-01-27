# Proof Postulate Policy and Target Architecture

This document defines the target architecture for x86 backend verification, specifying which postulates are acceptable and which must be eliminated.

## Core Principles

### 1. Postulate-Free IR Proofs

**IR proofs must be postulate-free.** The only allowed postulates are:

1. **CPU Semantics** - The machine model (x86 instruction semantics)
2. **Allocator Semantics** - Memory allocation guarantees (heap block properties)
3. **Memory Layout** - Runtime-provided region bounds

Everything else - IR correctness proofs, memory preservation, validity threading - must be proven from first principles.

### 2. Portability Through Layering

**Address arithmetic must NOT appear in portable data types.**

Portable types (work across architectures):
- `ValidAt` - value validity predicate
- `AllocMode` - escape analysis result (StackAlloc | HeapAlloc)
- `Owner` - ownership classification (Caller | Current)
- `OwnedBy` - ownership indexed by ValidAt

Architecture-specific (contains address arithmetic):
- Arithmetic lemmas like `addr ≥ rsp ∧ w < rsp → addr ≢ w`
- Concrete slot sizes, frame layouts
- Stack growth direction

This separation means porting to a new architecture only requires:
1. New CPU semantics
2. New memory layout bounds
3. Re-proving arithmetic lemmas

The core proof structure (ValidAt, Ownership, IRStarResultV) remains unchanged.

## Postulate Categories

### Acceptable Postulates (Trusted Foundations)

#### 1. CPU Semantics (`Once.Backend.X86.Semantics`)

These represent the x86 machine model:

```agda
-- Instruction execution semantics
step : Program → State → Maybe State

-- Memory read/write behavior
readMem : Memory → Word → Maybe Word
writeMem : Memory → Word → Word → Memory

-- Register operations
readReg : Registers → RegName → Word
writeReg : Registers → RegName → Word → Registers
```

**Why acceptable:** These define what x86 instructions do. They are the trusted specification against which we verify.

#### 2. Allocator Semantics (`Once.Backend.Common.AllocatorSemantics`)

Two axioms about heap allocation:

```agda
-- P1: Allocated blocks are in heap region
block-in-heap : Allocated addr n → ∀ i → i < n → InHeap (addr + i * slot-size)

-- P2: Distinct allocations are disjoint
blocks-disjoint : Allocated addr₁ n₁ → Allocated addr₂ n₂ →
                  addr₁ ≢ addr₂ → slots don't overlap
```

**Why acceptable:** These are runtime guarantees from the allocator. The allocator implementation (GC, malloc, bump-pointer) must satisfy these properties.

#### 3. Memory Layout (`Once.Backend.X86.Layout`)

Runtime memory region bounds:

```agda
-- Region bounds (provided by runtime/linker)
x86-stack-upper : ℕ
x86-heap-lower  : ℕ
x86-heap-upper  : ℕ
x86-code-upper  : ℕ

-- Region disjointness (runtime guarantee)
x86-intervals-disjoint : Stack ∩ Heap = ∅, etc.
```

**Why acceptable:** These are concrete values provided by the runtime system.

### Unacceptable Postulates (Must Be Eliminated)

#### 1. Encode-Based Postulates

```agda
-- ELIMINATE: encode axioms
encode-pair-construct : encode (a, b) ≡ ...
encode-closure-construct : ...
```

**How to eliminate:** Use `ValidAt` validity predicates. Already done in `Apply.agda`.

#### 2. Caller-Stack-Preserved Postulates

```agda
-- ELIMINATE: per-IR memory preservation postulates
caller-stack-preserved-pair : InStack addr → mem s' addr ≡ mem s addr
caller-stack-preserved-apply : ...
```

**How to eliminate:** Use Ownership model (`caller-input-preserved`). Partially done in `Pair.agda`.

#### 3. Frame Separation Postulates

```agda
-- WRONG: Claims ANY two stack addresses differ (this is false!)
frame-separation : InStack addr → InStack w → w ≢ addr
```

**Why this is wrong:** Two stack addresses CAN be equal. The postulate is too strong.

**Correct approach:** Use Ownership model + architecture-specific arithmetic lemma:

```agda
-- Portable: Ownership establishes addr ≥ entry-rsp for caller values
-- Portable: ir-mem-preserved establishes writes are < entry-rsp

-- Architecture-specific arithmetic lemma (proven, not postulated):
caller-current-disjoint : addr ≥ entry-rsp → w < entry-rsp → addr ≢ w
```

**Key insight:** Keep `ValidAt` and `Ownership` portable (no address arithmetic in types). Put arithmetic in architecture-specific **lemmas** that connect ownership to memory preservation.

## Stack Escape Analysis Architecture

### IR Must Track Allocation Mode

The IR should carry escape analysis results:

```agda
data AllocMode : Set where
  Stack : AllocMode  -- Value doesn't escape, stack-allocate
  Heap  : AllocMode  -- Value may escape, heap-allocate

-- Pair carries allocation mode from escape analysis
data IR (A B : Type) : Set where
  Pair : IR C A → IR C B → AllocMode → IR C (A * B)
  Inl  : AllocMode → IR A (A + B)
  Inr  : AllocMode → IR B (A + B)
  Curry : AllocMode → IR (E * A) B → IR E (A ⇒ B)
```

### Stack-Allocated Values

For `Stack` mode:
- Address is deterministic: `rsp - 16` (for pairs)
- No allocator postulates needed
- Lifetime bounded by stack frame
- Must prove escape analysis is sound

### Heap-Allocated Values

For `Heap` mode:
- Address comes from allocator (uses `AllocatorSemantics` postulates)
- Value may outlive current function
- Subject to GC/memory management

### Region in ValidAt

The current `ValidAt` already tracks region:

```agda
data ValidAt : ∀ {A : Type} → ⟦ A ⟧ → Word → Memory → Set where
  valid-pair : ... → (r : Region) → InRegion r addr → ValidAt (a , b) addr m
```

This enables different preservation strategies:
- **Heap region:** Use stack-heap disjointness (proven)
- **Stack region:** Use ownership model (caller vs current frame)

## Target Postulate Count

### Current State

| Category | Postulates | Status |
|----------|------------|--------|
| CPU Semantics | ~10 | Acceptable |
| Allocator Semantics | 2 | Acceptable |
| Layout | ~5 | Acceptable |
| Ownership | 1 (`caller-input-owned`) | Provable |
| Memory Validity | 2 (`frame-separation`, `stack-offset`) | Provable |
| IR Proofs | ~5 scattered | Must eliminate |
| Prim Semantics | 1 (`run-prim-star-vv`) | Semantic gap |

### Target State

| Category | Postulates | Notes |
|----------|------------|-------|
| CPU Semantics | ~10 | Trusted foundation |
| Allocator Semantics | 2 | Trusted foundation |
| Layout | ~5 | Runtime-provided |
| **IR Proofs** | **0** | All proven |
| Prim Semantics | 1* | Accepted gap (primitives not implemented) |

*The Prim postulate exists because codegen generates `mov rax, rdi` (identity) but `eval Prim` can be arbitrary. This is an implementation gap, not a soundness issue.

## Elimination Strategy

### Phase 1: Complete Ownership Migration (Current)

Files to update:
- `Pair.agda` - Replace remaining `caller-stack-preserved-pair` uses
- `Case.agda` - Apply `caller-input-preserved` pattern
- `Inl.agda`, `Inr.agda` - Apply pattern
- `Compose.agda` - Apply pattern (most complex)

Pattern:
```agda
-- OLD
valid-subst-region-preserved input-valid heap-eq caller-stack-preserved-*

-- NEW
caller-input-preserved input-valid (rsp-in-stack cap) mem-preserved-chain
```

### Phase 2: Prove `caller-input-owned`

Currently postulated in `Ownership.agda:442-448`.

Proof strategy:
1. At program entry, input comes from heap → `OwnedBy Caller` trivially
2. At IR composition, prove ownership transfers through call boundary
3. Key lemma: `entry-rsp` of callee ≤ all stack addresses from caller

### Phase 3: Prove `frame-separation`

Currently postulated in `MemoryValid.agda:209-213`.

Proof strategy:
1. Track `addr-above-rbp` for caller-provided Stack values
2. Track `w-below-rbp` for current frame writes
3. Derive: `addr > rbp ≥ w` → `addr ≢ w`

### Phase 4: Derive `ir-mem-above` and `ir-mem-heap`

These `IRStarResult` fields are derivable from `ir-mem-preserved`:
- `ir-mem-above`: Use `RbpInvariant` (rbp ≥ rsp)
- `ir-mem-heap`: Use `heap-addr-≥-stack-addr`

See `StarBase.agda:232-267` for documentation.

## Reference Implementation

`Apply.agda` is the postulate-free reference:

```agda
-- Line 38: NOTE: IR/Apply.agda is postulate-free!

-- Uses validity-based proofs
ir-result-valid : ValidAt (eval ir x) rax memory

-- Uses ownership for preservation
caller-input-preserved input-valid rsp-in-stack mem-preserved

-- Extracts region from ValidAt for disjointness
valid-in-region : ValidAt v addr m → ∃[ r ] InRegion r addr
```

## Success Criteria

The x86 backend verification is complete when:

1. **All IR proofs are postulate-free** (except Prim semantic gap)
2. **Only CPU/Allocator/Layout postulates remain** (trusted foundations)
3. **Escape analysis is reflected in IR** (`AllocMode` annotations)
4. **Stack allocation uses deterministic addresses** (no allocator for Stack)
5. **Heap allocation uses AllocatorSemantics** (2 axioms)

This architecture achieves maximal verification coverage while keeping trusted foundations minimal and well-documented.
