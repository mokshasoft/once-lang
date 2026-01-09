# D041 Region Migration Guide

## Summary

This guide documents the D041 abstract region approach for memory preservation proofs in the x86 backend. The key insight is to model memory as three disjoint regions (Stack, Heap, Code) rather than using concrete addresses and arithmetic bounds.

## THE FUNDAMENTAL ARCHITECTURE

**Proofs and instantiation are ORTHOGONAL.**

```
┌─────────────────────────────────────────────────────────┐
│            ABSTRACT PROOF LAYER                         │
│                                                         │
│  - 100% region-based                                    │
│  - NO arithmetic (not even in helper lemmas)            │
│  - NO concrete addresses (rsp, rbp, rsp-8, etc.)        │
│  - Works against abstract interfaces only               │
│  - Uses: StackPointer, slot-addr, frameSlot, region-of  │
│                                                         │
│  This is where IR correctness proofs live.              │
└─────────────────────────────────────────────────────────┘
                         │
                         │  (orthogonal - completely separate)
                         ▼
┌─────────────────────────────────────────────────────────┐
│            X86 INSTANTIATION LAYER                      │
│                                                         │
│  - Arithmetic lives HERE and ONLY here                  │
│  - Concrete addresses (rsp - 8, etc.)                   │
│  - Proves: "X86 satisfies the abstract interface"       │
│  - ISOLATED from main correctness proofs                │
│                                                         │
│  This is trusted base / refinement proof.               │
└─────────────────────────────────────────────────────────┘
```

**The main correctness proofs NEVER touch arithmetic.**
**Arithmetic is not "local dirt" - it belongs in a completely separate layer.**

## HARD RULE: No Arithmetic in Proofs

This is not a guideline. This is an architectural invariant.

**In the abstract proof layer, you may NOT use:**
- `<`, `>`, `≤`, `≥` on addresses
- `rsp`, `rbp` as concrete values
- `addr - 8`, `addr + 16`, or any address arithmetic
- `region-of (rsp ∸ 8)` - this is arithmetic in disguise!
- Any helper lemma that internally uses arithmetic

**If you find yourself reaching for arithmetic, STOP.**
You are in the wrong layer. Either:
1. You need to add an abstract operation to the interface, or
2. This proof belongs in the instantiation layer, not the proof layer

## STOP RULE: Before Adding ANY Postulate

**If you cannot express something using the existing abstractions below, STOP and ASK.**

The likelihood of needing a new postulate is close to zero. If you think you need one, you are probably on the wrong path.

## Abstract Interface (MemoryRegions.agda)

### Region Membership and Disjointness

```agda
region-of : Addr → Region                    -- Each address has a region
regions-disjoint : r₁ ≢ r₂ → ...→ a₁ ≢ a₂   -- Different regions → different addresses
stack-code-disjoint : ...                    -- Stack ≢ Code
stack-heap-disjoint : ...                    -- Stack ≢ Heap
zero-not-in-stack : region-of 0 ≢ stack      -- Null page protection
```

### Abstract Stack Operations

```agda
StackPointer : Set                           -- Abstract stack pointer (addr + in-stack proof)
slot-addr : StackPointer → ℕ → Addr          -- Slot at index k from SP
frameSlot : Memory → StackPointer → ℕ → Maybe Word  -- Read slot k
frameWriteSlot : Memory → StackPointer → ℕ → Word → Memory  -- Write slot k

-- Disjointness via identity, not arithmetic
sp-distinct : sp₁ ≢ sp₂ → slot-addr sp₁ k ≢ slot-addr sp₂ k
offset-distinct : k₁ ≢ k₂ → slot-addr sp k₁ ≢ slot-addr sp k₂
```

### Abstract Memory Preservation Properties

```agda
-- Stack writes preserve non-stack memory
stackWrite-preserves-heap : ∀ mem sp k val addr →
  region-of addr ≡ heap →
  readMem (frameWriteSlot mem sp k val) addr ≡ readMem mem addr

-- Stack writes preserve other frames
stackWrite-preserves-other-frame : ∀ mem sp₁ sp₂ k₁ k₂ val →
  addr sp₁ ≢ addr sp₂ →
  frameSlot (frameWriteSlot mem sp₁ k₁ val) sp₂ k₂ ≡ frameSlot mem sp₂ k₂

-- Stack writes preserve address 0
stackWrite-preserves-zero : ∀ mem sp k val →
  readMem (frameWriteSlot mem sp k val) 0 ≡ readMem mem 0
```

**Note:** These properties are stated WITHOUT arithmetic. The proofs of these properties (in the instantiation layer) may use arithmetic, but consumers never see it.

## How to Write Abstract Proofs

### Memory Preservation for Non-Stack Addresses

**WRONG (uses arithmetic):**
```agda
mem-at-0-proof : readMem mem' 0 ≡ readMem mem 0
mem-at-0-proof = ... (rsp > 24) ... (0 < rsp - 24) ...
```

**RIGHT (uses abstract property):**
```agda
mem-at-0-proof : readMem mem' 0 ≡ readMem mem 0
mem-at-0-proof = stackWrite-preserves-zero mem sp k val
```

### Memory Preservation for Caller's Frame

**WRONG (uses arithmetic):**
```agda
mem-caller : ∀ addr → addr > rbp → readMem mem' addr ≡ readMem mem addr
```

**RIGHT (uses StackPointer identity):**
```agda
mem-caller : ∀ k → frameSlot mem' caller-sp k ≡ frameSlot mem caller-sp k
mem-caller k = stackWrite-preserves-other-frame mem current-sp caller-sp _ k _ sp-neq
```

### Connecting to Concrete Addresses (ONLY in Instantiation Layer)

The `FrameSlotInternal` module provides glue for the instantiation layer:

```agda
module FrameSlotInternal where
  -- ONLY use these in instantiation proofs, never in abstract proofs
  frameSlot-is-readMem : frameSlot mem sp k ≡ readMem mem (slot-addr sp k)
```

## Proof Structure

### What Goes Where

| Layer | Contains | May Use |
|-------|----------|---------|
| Abstract Proofs | IR correctness, memory preservation | StackPointer, frameSlot, region-of, sp-distinct |
| Instantiation | "X86 satisfies interface" | Arithmetic, rsp, rbp, concrete addresses |

### Example: Proving mem-at-0

**Abstract layer (what you write):**
```agda
mem-at-0 : readMem (memory s') 0 ≡ readMem (memory s) 0
mem-at-0 = stackOp-preserves-zero s sp operation
```

**Instantiation layer (already proven, you just use it):**
```agda
-- In StackInvariant2.agda or similar
stackOp-preserves-zero : ∀ s sp op →
  readMem (memory (exec-op s sp op)) 0 ≡ readMem (memory s) 0
stackOp-preserves-zero s sp op = ... -- arithmetic proof here, isolated
```

## Migration Order: Top-Down

**CRITICAL: Always migrate TOP-DOWN, never middle-out.**

```
1. WholeProgram.agda      -- Entry point: receives/creates initial StackPointer
2. MutualIR.agda          -- Recursive dispatcher: threads StackPointer
3. IR/*.agda              -- Individual IR proofs: receive StackPointer from MutualIR
4. StarBase.agda          -- Base runners: receive StackPointer from IR/*
```

StackPointer flows from caller to callee. Start at the top.

## Pre-Commit Checklist

**MANDATORY - No exceptions:**

- [ ] **Zero arithmetic in proof layer**: No `<`, `>`, `≤`, `≥`, `rsp`, `rbp`, `addr ∸ k`
- [ ] **Zero arithmetic in types**: Function signatures mention only abstract types
- [ ] **Zero arithmetic in comments**: Don't explain what arithmetic you avoided
- [ ] Memory preservation uses abstract properties (stackWrite-preserves-*)
- [ ] Caller memory uses `sp-distinct` or `offset-distinct`
- [ ] No new postulates without asking first
- [ ] All proofs type-check: `make -j8 x86-ccc`

**If ANY arithmetic appears in the diff, the commit is REJECTED.**

## When You're Stuck

If you can't express something without arithmetic:

1. **STOP** - Don't add a "temporary" arithmetic proof
2. **ASK** - The abstraction may need extending
3. **Check** - Is this proof in the wrong layer?

The abstract interface should be sufficient. If it's not, we extend the interface (after discussion), not bypass it.

## Verification

```bash
cd formal
make -j8 x86-ccc  # Full x86 backend type-check
```

## Summary

- **Proofs are 100% abstract** - region-based, no arithmetic, ever
- **X86 is orthogonal** - arithmetic lives only in instantiation layer
- **The layers don't mix** - this is architecture, not convention
- **When stuck, ask** - don't reach for arithmetic
