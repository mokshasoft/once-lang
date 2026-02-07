# Slot-Based Reasoning for IR Proofs

## Goal

Migrate IR proofs from raw address-based reasoning to slot-based reasoning, eliminating these postulates:
- `x86-frame-disjoint` (unbounded frame disjointness)
- `prim-input-stack-disjoint` (StackAlloc primitive input disjointness)

## Problem: Why Raw Addresses Require Unprovable Postulates

### The Unbounded Disjointness Postulate

The current `x86-frame-disjoint` postulate:

```agda
postulate
  x86-frame-disjoint : ∀ f₁ f₂ k₁ k₂ →
    f₁ x86-≺ f₂ →
    x86-slot-addr f₁ k₁ ≢ x86-slot-addr f₂ k₂
```

This says: "any slot in frame f₁ is disjoint from any slot in frame f₂."

**Why it's unprovable**: The slot index `k₁` is unbounded. If `k₁` is large enough,
`slot-addr f₁ k₁` could overlap with `slot-addr f₂ k₂`. The frames are only
guaranteed disjoint within their allocated capacity.

### The Stack-Allocating Primitive Postulate

The current `prim-input-stack-disjoint` postulate:

```agda
postulate
  prim-input-stack-disjoint : ValidAt x (readReg (regs s) rdi) (memory s) →
    InStack (readReg (regs s) rdi) →
    InStack addr →
    readReg (regs s) rdi ≢ addr
```

This says: "input in stack doesn't overlap with any stack address."

**Why it's unprovable**: Without knowing WHERE in the stack the input lives
(which slot, which frame), we can't prove it's disjoint from writes.

## Solution: Frame + Slot Pairs

### Key Insight

A Frame has N slots (from `sub rsp, N*8`). Every write is to slot `k` where
`k < capacity`. The proven `x86-frame-disjoint-bounded` lemma applies when
we track slot indices.

```agda
-- PROVEN: slot within bounds → disjoint
x86-frame-disjoint-bounded : ∀ f₁ f₂ k₁ k₂ →
  f₁ x86-≺ f₂ →
  x86-slot-addr f₁ k₁ < sp-addr f₂ →  -- Slot is within frame bounds
  x86-slot-addr f₁ k₁ ≢ x86-slot-addr f₂ k₂
```

### The Bounded Lemma

The `x86-frame-disjoint-bounded` lemma is **proven**, not postulated:

1. `slot-addr f₂ k₂ ≥ sp-addr f₂` (slots grow upward from frame base)
2. `slot-addr f₁ k₁ < sp-addr f₂` (slot is below f₂'s base)
3. Therefore: `slot-addr f₁ k₁ < slot-addr f₂ k₂`
4. Therefore: they're not equal

### When The Bounded Lemma Applies

The bounded lemma applies when we can prove:
```
slot-addr current-frame write-slot < sp-addr caller-frame
```

This follows from:
1. `StackCapacity` tracks that writes are within frame capacity
2. Frame capacity determines maximum slot index
3. Each IR knows its capacity (from `ir-stack-requirement`)

## Ownership Propagation Through Compose

### Input Ownership

At function entry, inputs are owned by the caller. For StackAlloc inputs:
- Input is at `slot-addr caller-frame k` for some `k`
- We know `k` from the slot evidence in `OwnedBy`

### Through Compose (f ; g)

1. **f executes**: May allocate slots in current frame
2. **Transfer (rdi := rax)**: Result of f becomes input to g
3. **g executes**: May allocate more slots

Key property: Caller-owned inputs remain disjoint from current-frame writes
because `current-frame ≺ caller-frame` (callee's frame is "further" in growth direction).

### The Disjointness Chain

```
caller-owned input at slot-addr caller-frame k
  ⟹ k extracted from OwnedBy evidence (owned-implies-at-slot)
  ⟹ caller-frame ordering: current-frame ≺ caller-frame
  ⟹ slot bound: slot-addr current-frame write-slot < sp-addr caller-frame
  ⟹ x86-frame-disjoint-bounded: addresses differ
  ⟹ input preserved
```

## Implementation Phases

### Phase 1: Add Frame Tracking to IRStarResultV

Add to IRStarResultV record:
```agda
ir-current-frame : StackPointer
ir-current-frame-eq : sp-addr ir-current-frame ≡ readReg (regs s') rsp
```

This tracks which frame the IR executed in, enabling slot-bound proofs.

### Phase 2: Thread Input Ownership

Add to `run-ir-star-at-offset-v`:
```agda
(input-owned : OwnedBy Caller input-valid caller-sp) →
```

Update RecDispatcher to pass ownership. At top-level, use `init-input-owned`.

### Phase 3: Track Write Slots

For stack-allocating IRs (Curry, Pair, Inl, Inr):
- Derive slot bound from `StackCapacity`
- Provide frame evidence in output
- Track which slots were written

### Phase 4: Switch to Bounded Lemma

Update `owned-disjoint-from-current-slot` to require slot bound:
```agda
slot-addr current-frame write-slot < sp-addr caller-frame →
```

Replace `x86-frame-disjoint` with `x86-frame-disjoint-bounded`.

### Phase 5: Eliminate prim-input-stack-disjoint

In Prim case, use ownership-based reasoning:
- Input is `OwnedBy Caller` from dispatcher
- Frame ordering from `RbpInvariant`
- Slot bound from `StackCapacity`
- Apply `owned-disjoint-from-current-slot`

### Phase 6: Delete Postulates

Once all call sites migrated, delete:
1. `x86-frame-disjoint` from `FrameInstantiation.agda`
2. `prim-input-stack-disjoint` from `MutualIR.agda`

## Critical Files

| File | Role |
|------|------|
| `StarBase.agda` | IRStarResultV definition - add frame tracking |
| `MutualIR.agda` | Main dispatcher - thread ownership, DELETE prim postulate |
| `Ownership.agda` | owned-disjoint-from-current-slot - switch to bounded lemma |
| `FrameInstantiation.agda` | DELETE unbounded postulate after migration |
| `IR/CurryInstr.agda` | Pattern for stack-allocating IR with slot evidence |

## Verification

1. Build passes: `make -j4 x86-compiler`
2. No uses of eliminated postulates (grep returns empty)
3. No new postulates introduced
4. Architecture-independent interfaces (FrameSemantics, OwnershipSemantics) used

## Success Criteria

- `x86-frame-disjoint` postulate has zero uses
- `prim-input-stack-disjoint` postulate has zero uses
- All tests pass
- Slot indices are tracked, enabling bounded lemma
