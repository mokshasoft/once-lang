# Architecture-Independent Stack Abstraction

## Problem Statement

Address arithmetic is leaking into correctness proofs. This manifests as:

1. **Direction-dependent comparisons**: `slot-addr sp k >= rsp` assumes upward stack growth
2. **Architecture-specific register names**: `rsp` is x86-specific
3. **Hard-coded constants**: `word-size = 8`, `slot-addr sp k = addr sp + k * 8`

When proofs contain these details, they cannot be reused across architectures and the abstraction boundary is violated.

## Key Insight

Most proofs don't actually need address arithmetic. They need to know:

- "This frame won't be clobbered by stack writes"
- "These two frames are disjoint"
- "This slot is in the stack region"

These are **abstract properties** that can be expressed without knowing:
- Stack growth direction (up vs down)
- Word size (4, 8, 16 bytes)
- Specific register names (rsp, sp, etc.)

## The Abstract Interface

### Core Concepts

| Abstract Concept | What It Means | X86 Instantiation |
|------------------|---------------|-------------------|
| `FramePreserved frame sp` | Frame won't be clobbered when writing at sp | `addr frame >= sp` |
| `StackGrew old new` | Stack expanded from old to new | `new <= old` (rsp decreased) |
| `grow base k` | Address of slot k from base | `base + k * 8` |

### The StackGrowth Record

```agda
record StackGrowth : Set₁ where
  field
    -- Slot address computation
    grow : Addr → ℕ → Addr
    grow-identity : ∀ a → grow a 0 ≡ a
    grow-injective : ∀ a k₁ k₂ → k₁ ≢ k₂ → grow a k₁ ≢ grow a k₂
    grow-preserves-region : ∀ a k → InStack a → InStack (grow a k)

    -- Frame preservation (abstract ordering)
    FramePreserved : Addr → Addr → Set

    -- Stack growth (direction-independent)
    StackGrew : Addr → Addr → Set

    -- Key property: preserved frames stay preserved
    frame-preserved-under-growth : ∀ frame old-sp new-sp →
      FramePreserved frame old-sp →
      StackGrew old-sp new-sp →
      FramePreserved frame new-sp

    -- Slots in preserved frames are safe
    slot-in-preserved-frame : ∀ frame k sp →
      FramePreserved frame sp →
      FramePreserved (grow frame k) sp
```

### X86 Instantiation

```agda
x86-stack-growth : StackGrowth
x86-stack-growth = record
  { grow = λ base k → base + k * 8
  ; grow-identity = λ a → +-identityʳ a
  ; grow-injective = ...
  ; grow-preserves-region = ...

  ; FramePreserved = _≥_           -- frame addr >= stack ptr
  ; StackGrew = λ old new → new ≤ old  -- rsp decreased
  ; frame-preserved-under-growth = λ _ _ _ fp sg → ≤-trans sg fp
  ; slot-in-preserved-frame = λ frame k sp fp → ≤-trans fp (m≤m+n frame (k * 8))
  }
```

### Hypothetical Upward-Growth Architecture

```agda
upward-stack-growth : StackGrowth
upward-stack-growth = record
  { grow = λ base k → base - k * word-size  -- grows downward from base

  ; FramePreserved = _≤_           -- frame addr <= stack ptr
  ; StackGrew = λ old new → new ≥ old  -- sp increased
  ; frame-preserved-under-growth = ...
  ; ...
  }
```

## Refactoring StackInvariant

### Before (x86-specific)

```agda
data R15Status (s : State) : Set where
  r15-in-heap : InHeap (readReg (regs s) r15) → R15Status s
  r15-in-code : InCode (readReg (regs s) r15) → R15Status s
  r15-in-stack : (frame : StackPointer) (slot : ℕ) →
    readReg (regs s) r15 ≡ slot-addr frame slot →
    addr frame ≥ readReg (regs s) rsp →  -- x86-specific ordering!
    R15Status s
```

### After (architecture-independent)

```agda
-- Parameterized over StackGrowth
module StackInvariant (sg : StackGrowth) where
  open StackGrowth sg

  -- Architecture provides: which register is the stack pointer
  -- Architecture provides: which register tracks frame validity (r15 for x86)

  data FrameRegStatus (s : State) (stack-ptr : Addr) : Set where
    in-heap : InHeap tracked-reg → FrameRegStatus s stack-ptr
    in-code : InCode tracked-reg → FrameRegStatus s stack-ptr
    in-stack : (frame : StackPointer) (slot : ℕ) →
      tracked-reg ≡ slot-addr frame slot →
      FramePreserved (addr frame) stack-ptr →  -- abstract!
      FrameRegStatus s stack-ptr
```

## Migration Strategy

### Phase 1: Add Abstract Predicates to StackGrowth

Add `FramePreserved` and `StackGrew` to the `StackGrowth` record without changing existing code.

### Phase 2: Create Compatibility Layer

```agda
-- In X86.MemoryRegionLemmas
-- Provide old names as aliases during migration

frame-≥-sp : ∀ frame sp → FramePreserved frame sp → frame ≥ sp
frame-≥-sp frame sp fp = fp  -- trivial for x86 where FramePreserved = _≥_
```

### Phase 3: Update StackInvariant

Change `addr frame ≥ rsp` to `FramePreserved (addr frame) stack-ptr`.

### Phase 4: Update Proofs

Replace direct use of `≥` with abstract `FramePreserved` operations.

### Phase 5: Remove Compatibility Layer

Once all proofs use abstract predicates, remove the compatibility aliases.

## Benefits

1. **Architecture Independence**: Proofs work for any stack growth direction
2. **Cleaner Abstraction**: Address arithmetic contained at edges
3. **Explicit Dependencies**: Clear what each proof actually needs
4. **Easier Porting**: New architectures only implement the interface

## What Stays Architecture-Specific

Some things genuinely differ per architecture and belong in arch-specific modules:

- `word-size` constant
- Register names and their roles
- Calling convention details (e.g., `slot-addr-above-thunk-rbp`)
- The actual `grow` formula

## Naming Conventions

| Bad (x86-specific) | Good (abstract) |
|--------------------|-----------------|
| `rsp` | `stack-ptr` |
| `slot-addr-≥-base` | `slot-in-preserved-frame` |
| `frame ≥ rsp` | `FramePreserved frame sp` |
| `rsp' ≤ rsp` | `StackGrew old-sp new-sp` |
| `slot-addr-0-is-base` | `init-slot-at-base` |

## Related Documents

- `arch-proof-instructions.md`: General proof architecture guidelines
- `d041-region-migration.md`: Region-based memory proofs
- `validity-based-correctness.md`: Validity predicates over encode
