# Proof Stack Architecture

This document describes the complete proof architecture for Once's x86 backend verification, including the layered proof stack, postulate policy, and portability strategy.

## Core Principle

**IR proofs must be postulate-free.** The only allowed postulates are:

1. **CPU Semantics** - The machine model (x86 instruction semantics)
2. **Allocator Semantics** - Memory allocation guarantees (2 axioms)
3. **Memory Layout** - Runtime-provided region bounds

Everything else must be proven from first principles.

## Terminology

### AllocMode vs Memory Regions

There are two related but distinct concepts:

| Concept | Module | Description |
|---------|--------|-------------|
| **AllocMode** | `MemoryValid.agda` | Compile-time escape analysis result: `StackAlloc` or `HeapAlloc` |
| **InStack/InHeap** | `Common.Regions` | Runtime address predicates (where an address lives) |
| **InAllocRegion** | `MemoryValid.agda` | Bridge: maps AllocMode to address predicate |

```agda
-- AllocMode: Escape analysis decision (compile-time)
data AllocMode : Set where
  StackAlloc : AllocMode  -- Value doesn't escape, stack-allocate
  HeapAlloc  : AllocMode  -- Value may escape, heap-allocate

-- InAllocRegion: Map allocation mode to runtime predicate
InAllocRegion : AllocMode → Word → Set
InAllocRegion StackAlloc = InStack
InAllocRegion HeapAlloc  = InHeap
```

## The Proof Stack

```
┌─────────────────────────────────────────────────────────────────────┐
│  LAYER 0: TRUSTED FOUNDATIONS (Postulates Allowed)                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  CPU Semantics          Allocator Semantics      Memory Layout     │
│  ───────────────        ──────────────────       ─────────────     │
│  step : Prog→S→S        P1: block-in-heap        stack-bounds      │
│  readMem/writeMem       P2: blocks-disjoint      heap-bounds       │
│  readReg/writeReg       (Only 2 axioms!)         code-bounds       │
│  fetch/execute                                   intervals-disjoint│
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│  LAYER 1: REGION PREDICATES (Proven from Layout)                   │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Common.Regions (parameterized by MemoryLayout)                    │
│  ├─ InStack a = lower ≤ a ≤ upper                                  │
│  ├─ InHeap a  = lower ≤ a ≤ upper                                  │
│  ├─ InCode a  = lower ≤ a ≤ upper                                  │
│  │                                                                  │
│  └─ PROVEN disjointness:                                           │
│      ├─ stack-heap-disjoint : InStack a → InHeap a → ⊥             │
│      ├─ stack-code-disjoint : InStack a → InCode a → ⊥             │
│      └─ heap-code-disjoint  : InHeap a → InCode a → ⊥              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│  LAYER 2: STATELESS VALIDITY (Memory Layout Facts)                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Common.MemoryValid (architecture-independent)                     │
│  ├─ PairAtS    : mem[addr] = fst ∧ mem[addr+8] = snd              │
│  ├─ InlAtS     : mem[addr] = 0 (tag) ∧ mem[addr+8] = val          │
│  ├─ InrAtS     : mem[addr] = 1 (tag) ∧ mem[addr+8] = val          │
│  ├─ ClosureAtS : mem[addr] = env ∧ mem[addr+8] = code-ptr         │
│  │                                                                  │
│  └─ PROVEN allocation lemmas (no postulates):                      │
│      └─ alloc-*-creates-valid-s : writeMem creates valid AtS      │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│  LAYER 3: UNIFIED VALIDITY + ALLOCMODE                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  X86.MemoryValid.ValidAt (THE CORE ABSTRACTION)                    │
│  ├─ Carries value validity AND allocation mode                     │
│  │                                                                  │
│  │  data ValidAt : ⟦A⟧ → Word → Memory → Set where                 │
│  │    valid-unit  : ValidAt tt 0 m                                 │
│  │    valid-pair  : ValidAt a addr-a m → ValidAt b addr-b m →      │
│  │                  PairAtS ... → (mode : AllocMode) →             │
│  │                  InAllocRegion mode addr →                      │
│  │                  ValidAt (a,b) addr m                           │
│  │    ...                                                          │
│  │                                                                  │
│  ├─ valid-in-alloc-region : Extract AllocMode from ValidAt        │
│  │                                                                  │
│  └─ Preservation by AllocMode (PROVEN):                            │
│      ├─ *-preserved-under-heap-eq : HeapAlloc → heap preserved     │
│      ├─ *-preserved-under-stack-eq : StackAlloc → stack preserved  │
│      └─ valid-subst-region-preserved : dispatches on AllocMode     │
│                                                                     │
│  REMAINING POSTULATES (to eliminate):                              │
│  ├─ frame-separation : caller stack ≠ current stack writes        │
│  │   → ELIMINATE: track addr > rbp (caller), w ≤ rbp (current)    │
│  └─ stack-offset : InStack addr → InStack (addr + 8)               │
│      → ELIMINATE: prove from stack region bounds                   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│  LAYER 4: OWNERSHIP MODEL (Caller vs Current Frame)                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Ownership.agda                                                    │
│  ├─ Owner = Caller | Current                                       │
│  │   Caller  = addresses ≥ entry-rsp (preserved by IR)            │
│  │   Current = addresses < entry-rsp (may be written)             │
│  │                                                                  │
│  ├─ OwnedBy : Owner → ValidAt v addr m → Word → Set                │
│  │   Indexed by ValidAt - structural recursion on validity         │
│  │   owned-pair-heap : HeapAlloc → automatically Caller            │
│  │   owned-pair-caller-stack : addr ≥ rsp → Caller                │
│  │                                                                  │
│  ├─ PROVEN:                                                        │
│  │   owned-implies-stack-bound : OwnedBy Caller → addr ≥ rsp      │
│  │   owned-caller-preserved : ownership + mem-preserved → ValidAt │
│  │                                                                  │
│  └─ POSTULATE (to eliminate):                                      │
│      caller-input-owned : At IR entry, input is Caller-owned       │
│      → ELIMINATE: prove from call convention + IR composition      │
│                                                                     │
│  KEY INSIGHT: Ownership replaces ALL caller-stack-preserved-*     │
│  postulates with ONE semantic invariant!                           │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│  LAYER 5: EXECUTION PROOFS (Star-based)                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  StarBase.IRStarResultV (Postulate-free when layers below are)     │
│  ├─ ir-star : Star prog s s'           -- execution trace          │
│  ├─ ir-result-valid : ValidAt (eval ir x) rax (memory s')          │
│  ├─ ir-entry-rsp : ℕ                                               │
│  ├─ ir-mem-preserved : addr ≥ entry-rsp → mem s' = mem s           │
│  ├─ ir-capacity : StackCapacity s' (output-capacity)               │
│  └─ ir-closure-wf : ClosureWFOutput                                │
│                                                                     │
│  DERIVABLE (from ir-mem-preserved):                                │
│  ├─ ir-mem-heap : InHeap addr → preserved                          │
│  └─ ir-mem-above : addr > rbp → preserved                          │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│  LAYER 6: IR PROOFS (Must be postulate-free!)                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  STACK-ALLOCATING IRs (AllocMode = StackAlloc):                    │
│  ├─ Address is DETERMINISTIC (rsp - 16)                            │
│  ├─ No allocator postulates needed!                                │
│  └─ ValidAt carries StackAlloc mode                                │
│                                                                     │
│  HEAP-ALLOCATING IRs (AllocMode = HeapAlloc):                      │
│  ├─ Address from allocator (abstract)                              │
│  ├─ Uses AllocatorSemantics (2 axioms only)                        │
│  └─ ValidAt carries HeapAlloc mode                                 │
│                                                                     │
│  TARGET: ALL IR proofs construct IRStarResultV with:               │
│  ├─ ValidAt-based result (no encode)                               │
│  ├─ Ownership-based preservation (no caller-stack-preserved-*)    │
│  └─ ZERO additional postulates                                     │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## How Concepts Connect

```
ESCAPE ANALYSIS (compile-time)
        │
        ▼
┌───────────────────┐
│ AllocMode         │  StackAlloc = local, HeapAlloc = escapes
└───────────────────┘
        │
        ├─────────────────────────────────┐
        ▼                                 ▼
┌───────────────────┐     ┌───────────────────┐
│ Stack Allocation  │     │ Heap Allocation   │
├───────────────────┤     ├───────────────────┤
│ addr = rsp - n    │     │ addr ← allocate() │
│ (deterministic)   │     │ (2 axioms)        │
│ No postulates!    │     │ block-in-heap     │
└───────────────────┘     └───────────────────┘
        │                         │
        └─────────────┬───────────┘
                      ▼
        ┌─────────────────────────────────┐
        │ ValidAt v addr m                │
        │ ├─ Carries: value, address, mem │
        │ ├─ Carries: AllocMode           │
        │ └─ Carries: InAllocRegion proof │
        └─────────────────────────────────┘
                      │
                      ▼
        ┌─────────────────────────────────┐
        │ OwnedBy owner validAt rsp       │
        │ ├─ Caller: stack addrs ≥ rsp    │
        │ └─ HeapAlloc: automatically ≥   │
        └─────────────────────────────────┘
                      │
                      ▼
        ┌─────────────────────────────────┐
        │ ir-mem-preserved                │
        │ addr ≥ entry-rsp → unchanged    │
        └─────────────────────────────────┘
                      │
                      ▼
        ┌─────────────────────────────────┐
        │ owned-caller-preserved          │
        │ OwnedBy Caller + mem-preserved  │
        │ → ValidAt in new memory         │
        │                                 │
        │ REPLACES: caller-stack-preserved│
        └─────────────────────────────────┘
```

## Postulate Budget

### Target State

| Category | Postulates | Notes |
|----------|------------|-------|
| CPU Semantics | ~10 | Trusted foundation (machine model) |
| Allocator Semantics | 2 | Trusted foundation (block-in-heap, blocks-disjoint) |
| Memory Layout | ~5 | Runtime-provided (region bounds) |
| **IR Proofs** | **0** | Everything proven |
| Prim Semantics | 1* | Accepted gap (primitives not implemented) |

*The Prim postulate exists because codegen generates identity but `eval Prim` can be arbitrary.

### Current Postulates to Eliminate

| Postulate | Location | Elimination Strategy |
|-----------|----------|---------------------|
| `caller-input-owned` | Ownership.agda | Prove from call convention + IR composition |
| `frame-separation` | MemoryValid.agda | Track addr > rbp (caller), w ≤ rbp (current) |
| `stack-offset` | MemoryValid.agda | Prove from stack region bounds |
| `caller-stack-preserved-*` | Various IR/*.agda | Use `caller-input-preserved` from Ownership |

## Stack Escape Analysis Integration

The IR should carry `AllocMode` from escape analysis:

```agda
data IR (A B : Type) : Set where
  Pair : IR C A → IR C B → AllocMode → IR C (A * B)
  Inl  : AllocMode → IR A (A + B)
  Inr  : AllocMode → IR B (A + B)
  Curry : AllocMode → IR (E * A) B → IR E (A ⇒ B)
```

**StackAlloc path:**
- Address is `rsp - 16` (deterministic)
- Write with `writeMem`
- Create `ValidAt` with `StackAlloc` mode
- **No allocator axioms used**

**HeapAlloc path:**
- Call allocator (abstract)
- Get `Allocated` witness
- Use `block-in-heap` for `InHeap` proof
- Create `ValidAt` with `HeapAlloc` mode
- **Uses 2 allocator axioms**

## Portability Strategy

To port to a new architecture (e.g., AArch64, RISC-V):

### Reuse Entirely (Architecture-Independent)
- `Common.Regions` (parameterized by MemoryLayout)
- `Common.MemoryValid` (AtS records)
- `Common.AllocatorSemantics` (2 axioms)

### Adapt for Architecture
- CPU Semantics (instruction set)
- Memory Layout (concrete bounds)
- Stack growth direction (via `StackGrowth`)

### Keep Structure Identical
- `ValidAt` definition (same constructors)
- `Ownership` model (same Owner type)
- `IRStarResultV` fields (same interface)

The portable core is: **ValidAt + Ownership + 2 allocator axioms**.

## Reference Implementation

`Apply.agda` is the postulate-free reference:

```agda
-- Line 38: NOTE: IR/Apply.agda is postulate-free!

-- Uses validity-based proofs
ir-result-valid : ValidAt (eval ir x) rax memory

-- Uses ownership for preservation
caller-input-preserved input-valid rsp-in-stack mem-preserved

-- Extracts AllocMode from ValidAt for disjointness
valid-in-alloc-region : ValidAt v addr m → ∃[ mode ] InAllocRegion mode addr
```

## File Organization

```
formal/Once/Backend/
├── Common/                          # Architecture-independent
│   ├── MemoryLayoutSemantics.agda   # Abstract layout interface
│   ├── Regions.agda                 # InStack/InHeap/InCode predicates
│   ├── AllocatorSemantics.agda      # 2 allocator axioms
│   ├── MemoryValid.agda             # AtS records (PairAtS, etc.)
│   └── StackSlots.agda              # Slot addressing
│
└── X86/
    ├── Semantics.agda               # CPU semantics (trusted)
    ├── Layout.agda                  # X86 memory bounds (trusted)
    │
    └── Correct/
        ├── MemoryValid.agda         # ValidAt + AllocMode
        ├── Ownership.agda           # Caller/Current ownership
        ├── StarBase.agda            # IRStarResult/V
        ├── StackInstantiation.agda  # StackCapacity
        │
        └── IR/                      # Per-IR proofs (must be postulate-free)
            ├── Apply.agda           # Reference: postulate-free
            ├── Pair.agda            # In progress
            ├── Compose.agda
            ├── Case.agda
            └── ...
```
