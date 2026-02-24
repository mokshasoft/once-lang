# Stack Management: X86 vs X86v3 Comparison

## Overview

This document compares the stack management approaches in X86 (real calling convention) and X86v3 (SlotMachine abstraction), analyzing stack space efficiency and the remaining `slot-bounded-apply` postulate.

## IR Coverage

| IR Constructor | X86 | X86v3 |
|----------------|-----|-------|
| id, fst, snd, terminal | ✓ | ✓ |
| compose (∘) | ✓ | ✓ |
| pair ⟨,⟩ | ✓ | ✓ |
| case [,] | ✓ | ✗ |
| curry | ✓ | ✓ |
| apply | ✓ | ✓ |
| inl, inr | ✓ | ✗ |
| fold, unfold | ✓ | ✗ |
| arr | ✓ | ✗ |
| **Prim** | ✓ (parameterized) | ✗ |

**X86v3** is a proof-of-concept for the SlotMachine abstraction with a minimal IR subset.

**X86 Prim**: Fully proven via `PrimProofProvider` parameterization. Domain compilers (Arith, etc.) provide proofs for their primitives. No postulates.

## Stack Frame Models

### X86: Real x86-64 Calling Convention

```
┌─────────────────────────────────────┐
│ Caller's Frame                       │
│   [local vars] [saved regs] [...]    │
├─────────────────────────────────────┤ ← RSP before call
│ Return Address (8 bytes)             │  pushed by CALL
├─────────────────────────────────────┤
│ Callee's Frame                       │
│   [saved r15] [local vars] [...]     │
├─────────────────────────────────────┤ ← RSP during callee
│ Nested call frames...                │
└─────────────────────────────────────┘
```

**Key properties:**
- Each `call` instruction pushes 8-byte return address
- Each `ret` pops return address, restoring RSP
- Caller's frame is fully isolated from callee
- `ir-rsp-delta apply = 0` (push/pop + call/ret balance)

### X86v3: SlotMachine Flat Allocation

```
┌─────────────────────────────────────────────────────┐
│ Single Frame (pre-sized)                             │
│                                                      │
│ [slot 0] [slot 1] [slot 2] ... [slot N] ... [cap]   │
│  ^                             ^                     │
│  frame-base                    next-slot (frontier)  │
│                                                      │
│ Slots 0..next-slot are allocated                     │
│ Slots next-slot..cap are available                   │
└─────────────────────────────────────────────────────┘
```

**Key properties:**
- No call/ret instructions for IR dispatch (Agda recursion)
- Slots allocated monotonically (frontier advances)
- `reclaimable-slot` allows reclaiming intermediate allocations
- No per-call overhead (no return addresses)

## Codegen Comparison

### Compose `g ∘ f`

**X86:**
```asm
; Inlined, no function call
<code for f>        ; result in rax
mov rdi, rax        ; pass to g
<code for g>        ; result in rax
```
- `ir-rsp-delta (g ∘ f) = delta_f + delta_g`
- No frame overhead

**X86v3:**
```
execute f → result at slot S₁
execute g → result at slot S₂
; Can reclaim f's intermediate allocations before g
```
- `ir-stack-requirement (g ∘ f) = max(req_f, delta_f + req_g)`
- Same efficiency as X86

### Apply `(closure, arg)`

**X86:**
```asm
push r15              ; 8 bytes
mov r15, [rdi]        ; load closure
mov rsi, [rdi+8]      ; load arg
mov r12, [r15]        ; load env
mov r15, [r15+8]      ; load code-ptr
mov rdi, rsi          ; arg to rdi
call r15              ; 8 bytes (return addr)
  ; body executes in separate frame
  ret
pop r15
```
- **16 bytes overhead** per apply (saved r15 + return address)
- Body's stack usage is in separate frame
- `ir-rsp-delta apply = 0` (all balanced)

**X86v3 (current):**
```
allocate pair at slots [S, S+1]
execute body in SAME frame
  → body uses slots S+2 ... S+N
result at slot S+K
```
- **No call/ret overhead** (saves 16 bytes per apply)
- BUT: body's slots count against same frame capacity
- `slot-bounded` postulate because body can exceed `pair-slots`

## Stack Space Analysis

### Nested Applies: `apply (apply (apply (curry f, x), y), z)`

**X86:**
```
Frame 0: [caller locals]
  ├─ push r15 + call (16 bytes)
  Frame 1: [apply 1 locals]
    ├─ push r15 + call (16 bytes)
    Frame 2: [apply 2 locals]
      ├─ push r15 + call (16 bytes)
      Frame 3: [f executes]
      ret
    ret
  ret
```
- Stack: O(depth × 16) bytes overhead
- Each frame independent

**X86v3 (current flat model):**
```
Frame: [slot 0: closure₁] [slot 1: arg₁] [slot 2: closure₂] [slot 3: arg₂] ...
        ^                                                                    ^
        start                                                            high water
```
- Stack: O(depth × pair-slots) for results (unavoidable)
- **No return address overhead** (saves 8 bytes per level)
- But cannot reclaim until outermost apply completes

**X86v3 (with frame push/pop for apply):**
```
Frame 0: [pair for apply 1]
  push frame
  Frame 1: [pair for apply 2]
    push frame
    Frame 2: [pair for apply 3]
      push frame
      Frame 3: [f's allocations]
      pop frame → reclaim
    pop frame → reclaim
  pop frame → reclaim
```
- Same isolation as X86
- Loses the "no call/ret" advantage

## Current Reclamation Infrastructure (X86v3)

X86v3 already has reclamation support in `IRResultAWF`:

```agda
record IRResultAWF ... where
  field
    ...
    -- Reclamation fields
    reclaimable-slot : ℕ
    reclaim-monotone : next-slot alloc ≤ reclaimable-slot
    reclaim-bounded : reclaimable-slot ≤ next-slot final-alloc
    reclaim-preserves-result : ∀ (fits : reclaimable-slot ≤ frame-capacity alloc) →
      BeforeFrontier (record alloc { next-slot = reclaimable-slot ; ... }) result-loc
```

**How it works:**
- `reclaimable-slot`: minimum slot that preserves the result
- After IR completes, caller can reset `next-slot` to `reclaimable-slot`
- All slots between `reclaimable-slot` and `next-slot final` are reclaimed

**Current usage in ComposeWF:**
```agda
-- For g ∘ f:
-- After f: result at reclaimable-slot of f
-- Run g: can start from f's reclaimable-slot (not f's next-slot)
-- Compose's reclaimable-slot = g's reclaimable-slot
```

**Why this doesn't solve `slot-bounded-apply`:**

`slot-bounded` requires: `next-slot final ≤ next-slot initial + ir-stack-requirement ir`

For apply:
- `ir-stack-requirement apply = pair-slots` (static)
- Body executes and may use slots >> pair-slots
- Even with reclamation, the PEAK usage (during body) exceeds the bound
- `slot-bounded` is about the final position, not peak, but...
- The body's `final-alloc.next-slot` becomes apply's `final-alloc.next-slot`

The issue: body's slot usage flows through to apply's result.

## Escape Analysis vs Slot Reclamation

**These are different optimizations**, not the same thing:

| | Escape Analysis | Slot Reclamation |
|---|---|---|
| **Question** | WHERE to allocate? | WHEN to free stack slots? |
| **Decision** | Stack vs Heap | Reuse slot now vs later |
| **Scope** | Value lifetime vs call stack | Value lifetime vs expression |
| **Applied** | IR transformation (before codegen) | During/after IR execution |
| **Goal** | Minimize heap allocations | Minimize peak stack usage |

### Example

```
let closure = curry f    -- allocate closure
let pair = (closure, x)  -- allocate pair
let result = apply pair  -- execute, get result
return result
```

**Escape analysis asks:** Does each value escape its creating context?
- `closure` consumed by `apply` → doesn't escape → **stack-allocate**
- `pair` consumed by `apply` → doesn't escape → **stack-allocate**
- `result` is returned → **escapes** → heap-allocate (or caller's frame)

**Slot reclamation asks:** When can we reuse slots for dead values?
- After `apply` consumes `pair`, slots for `pair` can be reclaimed
- After `apply` consumes `closure`, slots for `closure` can be reclaimed
- `result` must persist until return

### The Relationship

```
                    ┌─────────────────┐
                    │ All values      │
                    └────────┬────────┘
                             │
              ┌──────────────┴──────────────┐
              │ Escape Analysis             │
              │ (IR → IR transformation)    │
              └──────────────┬──────────────┘
                             │
         ┌───────────────────┴───────────────────┐
         │                                       │
    ┌────▼────┐                            ┌─────▼─────┐
    │ Escapes │                            │ No Escape │
    │ → Heap  │                            │ → Stack   │
    └─────────┘                            └─────┬─────┘
                                                 │
                                    ┌────────────┴────────────┐
                                    │ Slot Reclamation        │
                                    │ (within stack values)   │
                                    └────────────┬────────────┘
                                                 │
                              ┌──────────────────┴──────────────────┐
                              │                                     │
                        ┌─────▼─────┐                        ┌──────▼──────┐
                        │ Dead early│                        │ Live longer │
                        │ → Reclaim │                        │ → Keep slot │
                        └───────────┘                        └─────────────┘
```

**Slot reclamation is a second-level optimization applied to stack-allocated values.**
It's not escape analysis - it's what you do AFTER escape analysis decides something goes on the stack.

### Optimality

- **Optimal escape analysis:** Maximize stack allocation (every non-escaping value on stack)
- **Optimal slot reclamation:** Minimize peak stack usage (reuse slots as soon as values are dead)

Both are needed for efficient stack usage. X86v3 currently has slot reclamation infrastructure (`reclaimable-slot`) but doesn't have an explicit escape analysis pass - that would be an IR-to-IR transformation before the proofs.

## Escape Analysis in proof-architecture.md

From `proof-architecture.md`:

```
IR (all heap)  →  escape analysis  →  IR (stack where safe)
```

**Key insight:** Escape analysis is an **IR-to-IR transformation**, not part of the correctness proofs.

1. Initial IR: Conservative, all allocations on heap
2. Escape analysis: Identifies non-escaping values
3. Transformed IR: Non-escaping values use `StackAlloc`

The proofs work with EITHER allocation mode. The transformed IR specifies `StackAlloc` or `HeapAlloc` per allocation.

**X86v3's current state:**
- Has slot reclamation infrastructure (`reclaimable-slot` in `IRResultAWF`)
- Does NOT have explicit escape analysis in IR (would be a separate pass)
- Reclamation tracks when intermediate results can be freed
- Escape analysis would decide stack vs heap placement

## Slot Reclaim vs Stack Frame for Apply

### The Core Issue with Current Reclamation

With slot reclamation as currently defined:
- `reclaimable-slot` = minimum slot that preserves the result
- The result IS at `reclaimable-slot` (or above)
- We can reclaim slots ABOVE the result, not below

For apply:
```
initial: next-slot = S
allocate pair: slots S, S+1
execute body: uses slots S+2 ... S+N
body result: at slot R (somewhere in S+2..S+N)
reclaimable-slot = R (can't go below result!)
```

**Problem:** The result stays at slot R (high position). We can reclaim S+N down to R, but not below R.

So `slot-bounded` still fails: `R > S + pair-slots`

### Making Reclaim Work: Move the Result

To satisfy `slot-bounded` with reclamation, we'd need to **MOVE the result** to a lower slot:

```
1. Body result at slot R (high)
2. COPY result to slot S (reuse pair's slots)
3. Set next-slot = S + result-size
4. Now: next-slot ≤ S + pair-slots ✓
```

But this "copy result down" is essentially what frame pop does:

| Stack Frame | Slot Reclaim + Move |
|-------------|---------------------|
| Push frame (save next-slot) | (nothing) |
| Body executes | Body executes |
| Pop frame (restore next-slot) | Reclaim (set next-slot = S) |
| Copy result to caller | Copy result to slot S |

They're nearly equivalent operations.

### Stack Usage Comparison

**Nested applies: `apply (apply (apply ...))`** depth D, body uses B slots

**Stack Frame:**
```
Frame 0: [pair₀]
  Frame 1: [pair₁]
    Frame 2: [pair₂]
      Body: [B slots]
```
- Peak: D × (frame-overhead + pair-slots) + B
- After all pops: pair-slots (just outermost result)

**Slot Reclaim + Move:**
```
Slots: [pair₀][result₀][pair₁][result₁]...[body slots]
        ^-- after reclaim, only results remain
```
- Peak: D × pair-slots + B (no frame overhead)
- After all reclaims: pair-slots (same)

**Winner: Slot reclaim saves ~D × frame-overhead bytes at peak**

Where frame-overhead ≈ 1-2 slots (8-16 bytes) for saved state.

### Performance Comparison

| Operation | Stack Frame | Slot Reclaim + Move |
|-----------|-------------|---------------------|
| Frame push | Save next-slot, frame-ptr | None |
| Frame pop | Restore next-slot, frame-ptr | Set next-slot = S |
| Copy result | Yes | Yes |
| **Total ops** | 3 | 2 |

**Winner: Slot reclaim is slightly faster** (no push, simpler restore)

### Aggressive Reclaim: The Optimal Approach

**Observation:** The (closure, arg) pair is consumed by apply. After reading it, slots S, S+1 are dead!

**Aggressive reclaim:**
```
1. Read pair at S, S+1 (closure, arg extracted)
2. Pair is dead → reclaim: next-slot = S
3. Body executes starting from slot S (reuses pair's space!)
4. Body result at slot S + body-delta
5. reclaimable-slot = S + result-size
```

Now `slot-bounded` works without copying:
- Body result is at low slot (reused pair space)
- No frame overhead
- No result copy needed

**This is the optimal approach** - but requires proving:
1. Pair is dead after extraction (no references remain)
2. Body can start allocating at the reclaimed slot

This is essentially a mini liveness/escape analysis within apply.

### Comparison Summary

| Approach | Peak Stack | Performance | Provability |
|----------|------------|-------------|-------------|
| Stack Frame | D × (overhead + pair) + B | Good | Easy (isolated) |
| Reclaim + Move | D × pair + B | Better | Moderate |
| Aggressive Reclaim | D × max(pair, result) + B | Best | Harder (liveness) |

### Conclusion

Slot reclaim CAN be better than stack frames:
- **Stack usage:** ~8-16 bytes less per nesting level
- **Performance:** fewer operations (no frame push)

**BUT** the current reclaim infrastructure doesn't solve `slot-bounded` because results stay at high slots. To fix this, we need either:
1. **Move result down** - similar cost to frame pop, but no frame push
2. **Aggressive reclaim** - reuse pair slots, best performance, but needs liveness proof

The aggressive approach would be optimal but requires proving the pair is dead after extraction.

## Options for `slot-bounded-apply`

### Option A: Frame Push/Pop for Apply Only

```
apply:
  1. Push new frame (save next-slot, reset to 0)
  2. Execute body in new frame
  3. Pop frame (restore next-slot)
  4. Copy result to caller's frame (uses pair-slots)
```

**Pros:**
- Clean isolation
- `slot-bounded` trivially satisfied (apply uses exactly pair-slots in caller's frame)
- Matches X86's semantics

**Cons:**
- Loses "no call/ret overhead" advantage
- Frame push/pop has its own overhead
- More complex proof

### Option B: Reclamation-Based (Current Infrastructure)

```
apply:
  1. Allocate pair at slots S, S+1
  2. Execute body, uses slots S+2..S+N
  3. Body's result has reclaimable-slot = S+2 (or less)
  4. Apply's reclaimable-slot = S (pair location)
  5. After apply, caller can reclaim S+2..S+N
```

**The problem:** `slot-bounded` checks `next-slot final`, not `reclaimable-slot`.

**Fix:** Change `slot-bounded` to track `reclaimable-slot` instead:
```agda
-- Current (problematic for apply):
slot-bounded : next-slot final-alloc ≤ next-slot alloc + ir-stack-requirement ir

-- Alternative:
slot-reclaimed : reclaimable-slot ≤ next-slot alloc + ir-stack-requirement ir
```

This says: "after reclamation, we're within budget" rather than "peak usage is within budget."

### Option C: Dynamic Stack Requirement

```agda
-- Current (static):
ir-stack-requirement apply = pair-slots

-- Alternative (dynamic):
ir-stack-requirement apply closure = pair-slots + body-capacity closure
```

**Problem:** This makes `ir-stack-requirement` depend on runtime data (the closure), breaking the static analysis.

### Option D: Accept and Document

Accept that `slot-bounded` for apply is a postulate with the following justification:

1. Frame capacity is sized at entry: `cap ≥ 2 × pair-slots × program-bound`
2. This guarantees enough space for any body execution
3. The postulate is "morally true" given the capacity constraint
4. The postulate is eliminated when transitioning to frame-based apply

## Hybrid Approach: Mixing Reclamation + Frame Push/Pop

**Proposed architecture:**

```
┌────────────────────────────────────────────────────────────────┐
│ Most IRs: Flat allocation with reclamation                     │
│   - compose, pair, curry, simple ops                           │
│   - Use reclaimable-slot to reuse space                        │
│   - No frame overhead                                          │
├────────────────────────────────────────────────────────────────┤
│ Apply only: Frame push/pop                                     │
│   - Body executes in isolated frame                            │
│   - Frame popped after body returns                            │
│   - Result copied to caller's frame                            │
└────────────────────────────────────────────────────────────────┘
```

**Why this makes sense:**
- Most IR operations don't need frame isolation
- Only `apply` executes "foreign" code (the closure body)
- The closure body could be anything (size unknown statically)
- Frame isolation for apply matches real calling conventions

**Stack space comparison:**

| Scenario | X86 | X86v3 (flat) | X86v3 (hybrid) |
|----------|-----|--------------|----------------|
| `f ∘ g ∘ h` (no apply) | 0 overhead | 0 overhead | 0 overhead |
| `apply (curry f, x)` | 16 bytes | 0 (but slot-bounded issue) | ~16 bytes |
| Nested applies (depth d) | 16d bytes | 0 (postulate) | 16d bytes |

**Conclusion:** The hybrid approach loses stack space advantage for apply chains, but preserves it for non-apply composition, which may be the common case.

## Summary

| Aspect | X86 | X86v3 (current) | X86v3 (hybrid) |
|--------|-----|-----------------|----------------|
| Compose/Pair overhead | None | None | None |
| Apply overhead | 16 bytes/call | None (postulate) | 16 bytes/call |
| Frame isolation | Full (call/ret) | None (flat) | Apply only |
| `slot-bounded` | N/A (uses ir-rsp-delta) | Postulate for apply | Provable |
| Reclamation | Via ret | Via reclaimable-slot | Both |
| Prim IR | Proven (parameterized) | Not in IR | N/A |

## Recommendation

**Short term:** Keep the `slot-bounded-apply` postulate with documentation. The postulate is sound given the frame capacity constraint.

**Medium term:** Implement frame push/pop for apply only (hybrid approach). This:
1. Eliminates the postulate
2. Preserves stack efficiency for non-apply operations
3. Matches real execution semantics
4. Simplifies reasoning about closure execution
