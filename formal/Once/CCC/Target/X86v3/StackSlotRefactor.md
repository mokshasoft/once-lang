# Stack Slot Refactor: Adding stackSlot to Registers

## Problem Statement

The current SlotMachine design has a fundamental issue with trace correctness proofs:

### Current Design
```agda
record AllocState : Set where
  field
    current-frame : Frame
    next-slot : ℕ
    frame-capacity : ℕ
    slots-available : next-slot ≤ frame-capacity  -- PROOF
    next-heap-ref : ℕ
```

### The Issue
When `exec-abstract` executes an allocation instruction:
```agda
exec-abstract (instr-alloc-stack n) s alloc = s , ???
```

It needs to produce a new `AllocState` with:
- `next-slot = next-slot alloc + n`
- `slots-available : next-slot alloc + n ≤ frame-capacity alloc`

But we don't have this proof at trace execution time! The capacity was verified by the Dispatcher when constructing the trace, not during trace execution.

This leads to:
1. Incomplete `exec-abstract` (currently returns `s, alloc` unchanged)
2. Unsound postulates for `trace-correct`
3. No path to actual proofs

## Solution: Move stackSlot to Registers

### Key Insight
Capacity verification is a **compile-time** concern (Dispatcher), not a **runtime** concern (trace execution). The trace should model what happens at runtime.

At runtime (x86):
- `sub rsp, n*8` just decrements rsp (no capacity check)
- Capacity was verified when generating the code

### New Design

**Registers with stackSlot:**
```agda
record Registers (FS : FrameSemantics) : Set where
  field
    input output : ValueLocation FS  -- rdi, rax
    stackSlot : ℕ                    -- current stack slot index (like rsp)
```

**Simplified AllocState:**
```agda
record AllocState : Set where
  field
    current-frame : Frame
    frame-capacity : ℕ    -- for Dispatcher's compile-time checks
    next-heap-ref : ℕ
    -- REMOVED: next-slot (now in Registers.stackSlot)
    -- REMOVED: slots-available proof (stays in Dispatcher)
```

**Clean exec-abstract:**
```agda
exec-abstract (instr-alloc-stack n) s alloc =
  record s { regs = record (regs s) { stackSlot = stackSlot (regs s) + n } } , alloc

exec-abstract (instr-dealloc-stack n) s alloc =
  record s { regs = record (regs s) { stackSlot = stackSlot (regs s) - n } } , alloc
```

No proofs needed - just arithmetic on ℕ!

## Dynamic Capacity and Gap-Free Stack

### Reclamation Pattern
The Dispatcher uses slot reclamation to avoid gaps:

```
f runs:     stackSlot: s₀ → s₁ (f allocates temporary space)
f reclaims: stackSlot: s₁ → reclaim-f (f's temps freed, only result persists)
g runs:     stackSlot: reclaim-f → s₂
g reclaims: stackSlot: s₂ → reclaim-g
allocate:   stackSlot: reclaim-g → reclaim-g + result-size
```

### Trace with Alloc/Dealloc
The trace directly models this:
```agda
pair-trace =
  instr-alloc-stack 1 ∷              -- backup slot
  mov-to-output ∷ store-at-slot s₀ ∷ -- save input
  f-trace ++
  instr-dealloc-stack (s₁ - reclaim-f) ∷  -- reclaim f's temps
  store-at-slot reclaim-f ∷          -- fst
  restore-input s₀ ∷
  g-trace ++
  instr-dealloc-stack (s₂ - reclaim-g) ∷  -- reclaim g's temps
  store-at-slot (reclaim-f + 1) ∷    -- snd
  lea-slot reclaim-f ∷ []
```

### Dynamic Capacity for Apply
Each closure carries its body's exact capacity requirement:
```agda
record BodyCorrect : Set where
  field
    body-capacity : ℕ  -- exact stack requirement for this closure's body
    ...
```

Apply creates a child frame with exactly `body-capacity` slots - no worst-case global allocation.

## Correspondence to x86

| SlotMachine | x86 |
|-------------|-----|
| `stackSlot` | `(rbp - rsp) / 8` |
| `instr-alloc-stack n` | `sub rsp, n*8` |
| `instr-dealloc-stack n` | `add rsp, n*8` |
| `store-at-slot k` | `mov [rbp + k*8], rax` |
| `lea-slot k` | `lea rax, [rbp + k*8]` |

The abstract model directly corresponds to x86 stack operations.

## Proof Strategy

### What the Dispatcher Proves (Compile-time)
1. Before emitting `instr-alloc-stack n`: `stackSlot + n ≤ frame-capacity`
2. Reclamation bounds: `reclaim-f ≤ stackSlot after f`
3. Result locations are valid: `BeforeFrontier` properties

### What exec-trace Computes (Runtime simulation)
1. State transformations (memory writes, register updates)
2. stackSlot updates (just arithmetic)
3. No capacity proofs needed

### trace-correct Becomes Provable
```agda
trace-correct : exec-trace trace s alloc ≡ (s-final , alloc-final)
```

Since exec-abstract is now fully defined (no TODOs), we can prove this by:
1. Induction on the trace
2. Each instruction has a clear semantics
3. The Dispatcher's construction ensures the trace produces the expected state

## Refactoring Plan

### Phase 1: Update SlotMachine
1. Add `stackSlot : ℕ` to `Registers`
2. Simplify `AllocState` (remove `next-slot` and `slots-available`)
3. Update `exec-abstract` for alloc/dealloc instructions
4. Update `readReg`/`writeReg` for new register structure

### Phase 2: Update Dispatcher (Top-down)
1. Fix imports and type errors
2. Thread `stackSlot` through state transformations
3. Use `regs.stackSlot` instead of `alloc.next-slot`
4. Keep capacity proofs in Dispatcher's local reasoning

### Phase 3: Update IR Modules
1. ComposeWF, PairWF, CurryWF, ApplyWF, SumFixWF
2. Construct traces with proper alloc/dealloc instructions
3. Prove trace-correct for each IR

### Phase 4: Prove AbstractSimulation
1. Per-instruction simulation proofs
2. Trace composition via Star transitivity
3. Full program correctness

## Benefits

1. **No postulates** - Everything is provable
2. **Clean separation** - Compile-time capacity checks vs runtime execution
3. **Direct x86 correspondence** - Traces map directly to x86
4. **Dynamic capacity** - Each closure gets exactly what it needs
5. **Gap-free stack** - Reclamation is explicit in traces
