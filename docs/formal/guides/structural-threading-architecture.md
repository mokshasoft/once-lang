# Structural Threading: Eliminating Apply Postulates Without encode-injective

## Problem Statement

The apply dispatch in `MutualIR.agda` (lines 683-714) has 5 postulates:

```agda
postulate
  cl-eq      : proj₁ x ≡ record { env-addr = encode env ; semantics = sem }
  cl-addr-eq : encode cl ≡ ca
-- plus 3 unreachable cases
```

The previous plan proposed using `encode-injective` to recover value equality
from address equality. This is **wrong** for two reasons:

1. **encode-injective is not an allocator property.** A real allocator provides
   freshness (each allocation returns unused address), not mathematical
   injectivity of a value→address function. The `encode` function is a
   deterministic pure function — it claims the same value always gets the same
   address. Real allocators are stateful; allocating the same value twice gives
   different addresses.

2. **It mixes concerns.** Using address equality to recover value equality
   routes through the allocation scheme, mixing allocator concerns with
   proof-level value threading.

## Key Insight: Values Flow Structurally Through Compose

The identity `proj₁ x ≡ cwf.cl` doesn't need to be recovered from addresses.
It is maintained STRUCTURALLY by the compose threading:

1. **Curry** produces output value `cl` AND `ClosureWFOutput` containing
   the same `cl`. At construction, `cl = eval (curry f) input` — this is
   definitional (refl).

2. **Compose** threads both the output value (as the next IR's input) and
   the `ClosureWFOutput` (as context for apply).

3. **Apply** receives input `x` where `proj₁ x` IS `cl` from step 1, because
   compose preserved the identity.

The equality is a CONSEQUENCE of the compose structure, not something to be
recovered from memory.

## The Compose Address Chain

While values flow structurally, the formal proof needs to connect through
the compose execution trace. The typical path curry→pair→apply:

```
curry:   rax := closure-addr    (stores cl at closure-addr in heap)
transfer: rdi := rax            (rdi = closure-addr for pair)
pair:    writes [rdi, ...] to new pair-addr, rax := pair-addr
transfer: rdi := rax            (rdi = pair-addr for apply)
apply:   reads rdi → pair-addr → first slot → closure-addr
```

The key connection: **the address that apply reads from the pair's first
slot IS closure-addr from the ClosureWFOutput**. This is provable from
the memory write chain, without any value-level injectivity.

## Architecture: Three Orthogonal Layers

```
┌─────────────────────────────────────────────────────────┐
│ Layer 3: Proof Threading (Value Identity)               │
│   Values flow through compose by construction.          │
│   Apply's input contains curry's output.                │
│   No address reasoning needed for value identity.       │
├─────────────────────────────────────────────────────────┤
│ Layer 2: Memory Layout (AtS records)                    │
│   PairAtS, ClosureAtS, InlAtS, InrAtS                 │
│   Describe how values are stored in memory.             │
│   Address relationships (pair-fst = closure-addr).      │
├─────────────────────────────────────────────────────────┤
│ Layer 1: Allocator (2 axioms)                           │
│   P1: block-in-heap (all slots of a block are InHeap)  │
│   P2: blocks-disjoint (distinct blocks don't overlap)  │
│   Parameterized by slot-size from MemoryLayout.         │
│   No value identity, no injectivity.                    │
│   Orthogonal to GC/refcounting/linearity.               │
└─────────────────────────────────────────────────────────┘
```

Each layer is independent. Layer 3 doesn't reason about addresses.
Layer 2 doesn't reason about which values are at addresses. Layer 1
only provides block-level region and separation guarantees.

### Layer 1: Allocator Semantics (2 Axioms)

The allocator is parameterized over `MemoryLayout` (which provides
`slot-size` — 8 for 64-bit, 4 for 32-bit architectures).

An `Allocated addr n` witness records that a block of `n` slots was
allocated at `addr`. This is established by generators at allocation time
(pair → 2 slots, closure → 2 slots, 7-field struct → 7 slots, etc.).

```agda
postulate
  -- P1: All slots of an allocated block are in the heap region.
  block-in-heap : ∀ {addr n} →
    Allocated addr n →
    ∀ (i : ℕ) → i < n → InHeap (addr + i * slot-size)

  -- P2: Distinct allocations have fully disjoint slot ranges.
  blocks-disjoint : ∀ {addr₁ n₁ addr₂ n₂} →
    Allocated addr₁ n₁ →
    Allocated addr₂ n₂ →
    addr₁ ≢ addr₂ →
    ∀ (i j : ℕ) → i < n₁ → j < n₂ →
    (addr₁ + i * slot-size) ≢ (addr₂ + j * slot-size)
```

**Properties of this model:**
- Handles arbitrary block sizes (not hardcoded to 2 slots)
- Architecture-independent (parameterized by slot-size)
- Orthogonal to memory management (GC, refcounting, linear ownership)
  - P1/P2 are about simultaneously-live blocks
  - Liveness management is a separate concern
- No injectivity, no value recovery from addresses
- Non-linear values (shared references) don't affect block properties
  — multiple refs to same block, one `Allocated` witness

## Concrete Proposal

### Step 1: Add `closure-addr-is-pair-fst` to compose threading

When compose calls apply, it knows:
- cwf has `closure-addr` (where the closure was stored by curry)
- The input pair's first slot was written from curry's rax (= closure-addr)

Add a proof that the pair's first memory slot contains closure-addr:

```agda
-- Compose provides this when building cwf for apply:
pair-fst-eq : readMem (memory s) (readReg (regs s) rdi) ≡ just closure-addr
```

This connects Layer 2 (PairAtS) to cwf's closure-addr without any
value-level reasoning.

### Step 2: Derive code-slot and closure-at from address chain

With `pair-fst-eq`, apply can derive:
- `addr-a = closure-addr` (from PairAtS.fst-valid-s + pair-fst-eq)
- `code-slot` from ClosureAtS at closure-addr (already in cwf)
- `closure-at` from cwf.closure-at (same address)

No cl-addr-eq postulate needed.

### Step 3: Derive semantic identity from thunk execution

For `cl-eq` (the value identity), we use the thunk execution semantics:

1. From cwf: `ClosureWellFormed prog cp env sem` means executing the
   thunk at cp with (env, arg) produces `sem arg = eval f (env, arg)`.

2. From memory: at closure-addr, the env-slot contains `encode env`
   (from ClosureAtS). The code-slot contains cp.

3. Apply executes the thunk at cp with the env read from closure-addr.
   The env it reads IS `encode env` (from ClosureAtS). So it passes
   `env` to the thunk. The thunk produces `sem arg`.

4. The SPECIFICATION says: `eval apply (cl, arg) = cl.semantics arg`.
   We need: `sem arg = cl.semantics arg` where `cl = proj₁ x`.

5. From ValidAt decomposition: `ValidAt (proj₁ x) addr-a m`. Since
   addr-a = closure-addr (from step 2), and ClosureAtS at closure-addr
   has env-addr = encode env, the closure at this address has:
   - env-addr = encode env (from ClosureAtS, readable from memory)
   - The thunk at code-ptr produces sem (from ClosureWellFormed)

6. The ONLY closure that is ValidAt closure-addr with this memory layout
   is one with `env-addr = encode env` (determined by memory contents).
   And the semantics is determined by the code at cp (unique thunk).

7. Therefore: `(proj₁ x).env-addr = encode env` and
   `(proj₁ x).semantics = sem`. By Closure record eta:
   `proj₁ x ≡ record { env-addr = encode env ; semantics = sem }`.

### Step 4: Formalize the env-addr connection

The key lemma (replaces encode-injective):

```agda
-- If ValidAt cl addr m, and ClosureAtS records env-addr at addr,
-- then cl.env-addr equals what ClosureAtS says
closure-env-addr-determined-by-memory :
  ∀ {A B} {cl : Closure A B} {env-addr code-ptr addr : Word} {m : Memory} →
  ValidAt cl addr m →
  ClosureAtS env-addr code-ptr addr m →
  Closure.env-addr cl ≡ env-addr
```

This is PROVABLE from the ValidAt constructors:
- `valid-closure` says ClosureAtS uses `Closure.env-addr cl`
- `valid-closure-env` says `Closure.env-addr cl ≡ encode env` and ClosureAtS has `encode env`
- Both cases: the env-addr in ClosureAtS = Closure.env-addr cl

Similarly for semantics, via thunk determinism:

```agda
-- If ClosureWellFormed records semantics sem at code-ptr,
-- and cl is valid at an address whose code-slot points to code-ptr,
-- then cl.semantics ≡ sem
-- (Uses function extensionality: both produce same results for all inputs)
closure-semantics-from-thunk :
  ∀ {A B} {cl : Closure A B} {addr : Word} {m : Memory}
    {E} {env : ⟦ E ⟧} {code-ptr : ℕ} {sem : ⟦ A ⟧ → ⟦ B ⟧} {prog} →
  ValidAt cl addr m →
  ClosureAtS (Closure.env-addr cl) code-ptr addr m →
  ClosureWellFormed prog code-ptr env sem →
  Closure.env-addr cl ≡ encode env →
  cl.semantics ≡ sem
```

This requires function extensionality (already postulated) and the
insight that the code at code-ptr uniquely determines the behavior.
NOTE: This last lemma may require a new postulate about code-ptr
determinism (see "Remaining Axioms" below).

### Step 5: Eliminate unreachable cases

The `yes _ | no _` and `no _ | _` cases in the type equality check
are genuinely unreachable in well-typed programs. Two approaches:

a. **Keep as postulates** — they ARE unreachable and documenting this
   is honest. (1-2 postulates for unreachable branches)

b. **Carry type equality** in ClosureWFOutput — add `A' ≡ A` and
   `B' ≡ B` proofs that compose provides from the IR type structure.

c. **Remove the type check entirely** — if ClosureWFOutput is only
   produced for matching types (guaranteed by the IR structure),
   parameterize it by the same A, B as apply.

Option (c) is cleanest: make ClosureWFOutput's type indices match
apply's types by construction. The compose threading ensures this.

## What About valid-from-encode and valid-addr-is-encode?

These MemoryValid postulates are on a separate elimination path:

- **valid-from-encode** is used at 2 sites (both in apply dispatch).
  With the structural approach, apply gets validity from compose
  threading (input-valid decomposition), not from encode. These
  usages can be eliminated.

- **valid-addr-is-encode** is used at 3 sites:
  1. `MutualIR:323` (curry env) — for ClosureAtS construction. Can be
     replaced by threading env validity directly.
  2. `MutualIR:653` (apply pair addr) — for pair layout. Eliminated by
     structural approach (compose provides pair layout).
  3. `MemoryValid:217` (valid-in-heap) — derives InHeap from ValidAt.
     This can be replaced by threading InHeap directly.

## Remaining Axioms (After This Refactor)

### True Axioms (CPU Instruction Semantics)
How each x86 instruction modifies State. These define the machine model.

### Allocator Axioms (2 — architecture-independent)
- `block-in-heap` : All slots of an allocated block are InHeap
- `blocks-disjoint` : Distinct allocations have non-overlapping slot ranges

These are parameterized over `slot-size` from `MemoryLayout`. They handle
arbitrary block sizes. Orthogonal to GC/refcounting/linearity.

### Semantic Axioms
- `extensionality` : Function extensionality (consistent with Agda)
- `closure-semantics-eq` : Closures equal if semantics equal
- `coerceIRArrow` / `coerceQuantity` : QTT quantity erasure

### Code Determinism (possibly needed for cl-sem derivation)
If the structural approach for semantic identity (Step 4) requires a
postulate about code-ptr uniquely determining behavior:

```agda
-- The code at a given address computes a unique function.
-- Two ClosureWellFormeds at the same code-ptr with same env have same semantics.
thunk-deterministic :
  ClosureWellFormed prog cp env sem1 →
  ClosureWellFormed prog cp env sem2 →
  sem1 ≡ sem2
```

This IS provable if ClosureWellFormed's thunk-correct uniquely determines
the output (which it does — execution is deterministic). The proof would
use determinism of the step function.

### What Is Eliminated
- `encode-injective` : NOT NEEDED (structural threading)
- `valid-from-encode` : NOT NEEDED (compose provides validity)
- `valid-addr-is-encode` : NOT NEEDED (direct heap proofs)
- `encode-in-heap` (old) : REPLACED by block-in-heap (generalized)
- `heap-offset` (old) : REPLACED by block-in-heap with i=1 (bounded)
- `cl-eq` : PROVEN (structural + memory determinism)
- `cl-addr-eq` : PROVEN (compose address chain)
- `cap-for-apply` : ALREADY PROVEN (cwf-cap in ClosureWFOutput)
- 3 unreachable cases : Either kept as honest postulates or eliminated
  by type-indexed ClosureWFOutput

## Net Result

| Before | After |
|--------|-------|
| 2 AllocatorSemantics postulates (unsound) | 2 (sound, generalized) |
| 3 MemoryValid postulates | 0 (all eliminated) |
| 5 apply dispatch postulates | 0-2 (unreachable cases, if kept) |
| **10 postulates** | **2-4 postulates** |

The allocator layer has exactly 2 axioms about block-level properties.
No injectivity. No value recovery from addresses. No hardcoded sizes.
Clean separation of concerns.

## Implementation Order

1. Add `slot-size` to MemoryLayoutSemantics.agda
2. Rewrite AllocatorSemantics.agda with 2-axiom model (block-in-heap, blocks-disjoint)
3. Update usages of old AllocatorSemantics (encode-in-heap, heap-offset)
4. Prove `closure-env-addr-determined-by-memory` (in MemoryValid.agda)
5. Add `pair-fst-eq` or equivalent address threading to compose
6. Derive `cl-addr-eq` from compose's address chain
7. Derive `cl-eq` from memory determinism + Closure eta
8. Eliminate valid-from-encode usages
9. Eliminate valid-addr-is-encode usages
10. Remove the 3 MemoryValid postulates
11. Handle unreachable cases (option a, b, or c)

## Key Principle: Proofs Should Flow With Values, Not Against Them

The old approach (encode-injective) tried to RECOVER values from addresses:
```
value → encode → address → encode-injective → value
```

The new approach carries values FORWARD through execution:
```
value → compose threading → value (same term, by construction)
```

This is more orthogonal because:
- Allocator only provides block-level region/separation (2 axioms)
- Memory layout only describes physical structure (AtS records)
- Value identity is maintained by the proof structure itself
- No axiom connects addresses back to values
- GC/refcounting/linearity are completely orthogonal
- Block sizes are not hardcoded (extensible to custom datatypes)
