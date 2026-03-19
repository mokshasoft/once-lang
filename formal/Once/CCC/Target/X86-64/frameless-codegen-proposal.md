# Frameless Codegen Proposal for X86v3

## Problem Statement

There is an architectural mismatch between the Dispatcher (slot machine) layer and the Runner (x86) layer regarding frame management.

### Current Dispatcher Model (PairWF.agda)

The Dispatcher uses **slot reclamation within a single frame**:

```agda
-- Everything stays in caller's frame
pair-loc = OnStack (current-frame alloc) reclaim-g
alloc₃ = record alloc { next-slot = reclaim-g +ℕ ps ; ... }
```

Key characteristics:
- No frame push/pop modeled
- `current-frame alloc` stays constant (caller's frame)
- Slots are allocated and reclaimed via `next-slot` index
- `BeforeFrontier` tracks validity within this single frame

### Current Runner/Codegen Model (PairRunner.agda)

The x86 codegen **creates new frames** via prologue/epilogue:

```asm
; pair-setup (prologue)
push rbp              ; save caller's frame pointer
mov rbp, rsp          ; establish new frame
sub rsp, 24           ; allocate local space
mov [rsp+16], rdi     ; backup input

; pair-cleanup (epilogue)
mov rax, rsp          ; pair address
mov [rsp], fst        ; store fst
mov [rsp+8], snd      ; store snd
add rsp, 24           ; deallocate locals
pop rbp               ; restore caller's frame
```

This creates `pair-frame` at a different address than `caller-frame`.

### The Mismatch

```
Dispatcher view:     [caller-frame: slot 0, 1, 2, ...]
                     └─ pair-loc = OnStack caller-frame reclaim-g

Runner view:         [caller-frame]  (rbp points here after pop)
                          │
                          ▼ prologue creates new frame
                     [pair-frame]    (rbp points here during pair)
                          │
                     └─ pair-loc = OnStack pair-frame 0
```

These are **different locations** with different addresses:
- Dispatcher: `caller-frame-base + reclaim-g * 8`
- Runner: `pair-frame-base + 0 * 8` (which equals `pair-rsp`)

### Symptom: Unprovable Postulate

This mismatch surfaces as an unprovable postulate in PairRunner.agda:

```agda
postulate
  restored-frame-scope-at-cleanup :
    ∀ f k loc' → readLoc (pair-cleanup-slot-state σ4 pair-loc) (OnStack f k) ≡ just loc' →
                 orig-rbp-value ≤ x86-frame-base f
```

The `frame-scope` invariant requires all tracked frames to have base ≥ current frame base. After pair cleanup, we need this relative to caller's frame, but σ4 may contain entries at pair-frame (which has lower base address).

---

## Two Architectural Solutions

### Path 1: Frame-Aware Dispatcher

**Change the Dispatcher to model frame push/pop.**

The infrastructure exists in `Allocation.agda`:

```agda
push-frame : (parent : AllocState) → (child-frame : Frame) → (child-capacity : ℕ) → AllocState
pop-frame : (child : AllocState) → (parent : AllocState) → (result-slot : ℕ) → ... → AllocState

parent-before-child : ... → BeforeFrontier parent loc → BeforeFrontier (push-frame ...) loc
```

**Changes required:**
1. Modify PairWF to use `push-frame` when entering pair, `pop-frame` when exiting
2. `pair-loc` would be `OnStack child-frame slot` (matching x86)
3. `BeforeFrontier` transfer handles frame transitions via `parent-before-child`
4. `restored-frame-scope-at-cleanup` becomes derivable

**Pros:**
- Dispatcher model matches x86 reality
- Existing push/pop infrastructure handles complexity
- No codegen changes needed

**Cons:**
- More complex Dispatcher proofs
- Frame management overhead remains in generated code

### Path 2: Frameless Codegen (RECOMMENDED)

**Change the codegen to not create frames, matching the Dispatcher's model.**

New codegen for pair:

```asm
; pair-setup (frameless)
sub rsp, 24           ; allocate space only
mov [rsp+16], rdi     ; backup input
; NO push rbp, NO mov rbp, rsp

; pair-cleanup (frameless)
mov rax, rsp          ; pair address
mov [rsp], fst        ; store fst
mov [rsp+8], snd      ; store snd
add rsp, 24           ; deallocate
; NO pop rbp
```

**Changes required:**
1. Remove prologue/epilogue from pair codegen
2. Use rsp-relative addressing throughout (already mostly done)
3. Runner's `StateCorresponds.current-frame` stays as caller's frame
4. `pair-loc = OnStack caller-frame slot` matches Dispatcher

**Pros:**
- Dispatcher's reclamation model is already correct
- Saves ~5 cycles per combinator level (no push/pop rbp, no frame setup)
- Simpler proof structure - no frame transitions to reason about
- `restored-frame-scope-at-cleanup` becomes trivial (no frame change occurred)

**Cons:**
- Non-standard stack layout (harder to debug with traditional tools)
- Stack traces won't show combinator boundaries
- Need to track stack depth for correct rsp-relative offsets

---

## Detailed Analysis of Path 2 (Frameless)

### Stack Layout Comparison

**With frames (current):**
```
High addresses
    │
    ├─ caller's locals
    ├─ caller's rbp backup  ← caller-frame (rbp after pair returns)
    ├─ pair's rbp backup    ← pair-frame (rbp during pair)
    ├─ pair's locals [+16]: input backup
    ├─ pair's locals [+8]:  snd
    ├─ pair's locals [+0]:  fst  ← rsp during pair
    │
Low addresses
```

**Frameless (proposed):**
```
High addresses
    │
    ├─ caller's locals
    ├─ caller's frame       ← rbp (unchanged throughout)
    ├─ pair's locals [+16]: input backup
    ├─ pair's locals [+8]:  snd
    ├─ pair's locals [+0]:  fst  ← rsp during pair
    │
Low addresses
```

The difference: no `push rbp` / `pop rbp`, rbp stays pointing to caller's frame.

### Addressing Changes

**Current (rbp-relative after mov rbp, rsp):**
```asm
mov [rbp-8], rdi      ; input backup (negative offset from rbp)
mov [rbp-24], fst     ; pair.fst
mov [rbp-16], snd     ; pair.snd
```

**Frameless (rsp-relative):**
```asm
mov [rsp+16], rdi     ; input backup (positive offset from rsp)
mov [rsp+0], fst      ; pair.fst
mov [rsp+8], snd      ; pair.snd
```

The current codegen already uses rsp-relative addressing, so minimal changes needed.

### Impact on Nested Combinators

For `⟨ ⟨ f , g ⟩ , h ⟩`:

**With frames:** 3 frame push/pop pairs (~15 cycles overhead)
**Frameless:** 0 frame overhead, just `sub rsp` / `add rsp`

Stack management:
```
outer-pair: sub rsp, 24
  inner-pair: sub rsp, 24
    f executes
    g executes
  inner-pair: add rsp, 24
  h executes
outer-pair: add rsp, 24
```

### Slot Machine Correspondence

With frameless codegen, the Dispatcher's model directly corresponds:

| Dispatcher | x86 (Frameless) |
|------------|-----------------|
| `OnStack caller-frame 0` | `[rbp + 0]` |
| `OnStack caller-frame 1` | `[rbp + 8]` |
| Pair allocates at `next-slot` | `[rsp + offset]` where `rsp = rbp - total_allocated` |

The key insight: `caller-frame-base = rbp`, and all allocations are at addresses below rbp (stack grows down). The slot index maps directly to rsp-relative offset.

### StateCorresponds Simplification

With frameless codegen:
- `current-frame sc` stays constant (caller's frame)
- `frame-scope` trivially holds (no frame changes)
- `rbp-is-frame-base` stays valid (rbp unchanged)
- `rsp-at-or-below-rbp` managed via sub/add rsp

The `restored-frame-scope-at-cleanup` postulate becomes:
```agda
-- Trivially true: no new frames created, all entries in caller-frame or above
restored-frame-scope-at-cleanup f k loc' read-eq = frame-scope sc f k loc' read-eq
```

---

## Proof Architecture Simplification

A major benefit of frameless codegen is dramatically simpler refinement proofs.

### Current Proof Layers (Complex)

```
IR Semantics (eval)
    ↓
Dispatcher (slot machine, BeforeFrontier, ValidAtWF, reclamation)
    ↓
StateCorresponds (MemCorresponds, RegsCorrespond, frame-scope,
                  current-frame, rbp-is-frame-base, rsp-at-or-below-rbp,
                  rsp-in-stack, heap-in-heap, ...)
    ↓
Runner (per-combinator x86 proofs with frame transitions)
    ↓
x86 Semantics (fetch-decode-execute)
```

### What Becomes Trivial With Frameless

| Current Complexity | With Frameless |
|-------------------|----------------|
| `current-frame` field | Constant (caller's frame) - no field needed |
| `frame-scope` invariant | Trivially `refl` (one frame) - delete it |
| `rbp-is-frame-base` | rbp never changes - trivial or delete |
| `restored-frame-scope-at-cleanup` | No frame change occurred - delete postulate |
| Frame transition proofs in Runner | Don't exist |
| `parent-before-child` reasoning | Not needed |

### Simplified Proof Layers

```
IR Semantics (eval)
    ↓
Dispatcher (slot machine, BeforeFrontier, ValidAtWF, reclamation)
    ↓
Address Mapping (simple arithmetic: slot k → frame-base - k*8)
    ↓
Instruction Correspondence (generic lemmas, composed per-combinator)
    ↓
x86 Semantics
```

### Simplified StateCorresponds

**Delete these fields:**
```agda
-- DELETE: no longer needed
current-frame : X86Frame
rbp-is-frame-base : x86-readReg regs rbp ≡ x86-frame-base current-frame
frame-scope : ∀ f k loc' → readLoc σ (OnStack f k) ≡ just loc' →
              x86-frame-base current-frame ≤ x86-frame-base f
```

**Keep these fields (simplified):**
```agda
record StateCorresponds (σ : LocState) (s : x86State) : Set where
  field
    frame-base : Addr                    -- constant throughout execution
    regs-correspond : RegsCorrespond σ s
    mem-corresponds : MemCorresponds frame-base σ s
    rsp-in-bounds : InStack (x86-readReg regs rsp)
    rsp-below-frame : x86-readReg regs rsp ≤ frame-base
```

### Generic Instruction Lemmas (Replace Complex Runners)

Instead of per-combinator proofs reasoning about frame transitions, have generic reusable lemmas:

```agda
-- Stack allocation
sub-rsp-preserves : ∀ n →
  rsp-in-bounds s →
  n ≤ available-capacity →
  rsp-in-bounds (exec (sub rsp n) s)

-- Memory write at valid address
mov-mem-preserves : ∀ addr v →
  InStack addr →
  addr < frame-base →  -- below tracked slots
  mem-corresponds σ m →
  mem-corresponds σ (write m addr v)

-- Stack deallocation
add-rsp-preserves : ∀ n →
  rsp-in-bounds s →
  rsp + n ≤ frame-base →
  rsp-in-bounds (exec (add rsp n) s)
```

### Simplified Combinator Proofs

With generic lemmas, combinator proofs become composition:

```agda
-- Current PairRunner: ~600 lines with frame reasoning
-- Simplified: ~100 lines composing lemmas

pair-correspondence : ...
pair-correspondence =
  sub-rsp-preserves 24 rsp-ok capacity-ok        -- allocate
  ∷ mov-mem-preserves backup-addr input-ok       -- backup input
  ∷ f-correspondence                              -- run f
  ∷ g-correspondence                              -- run g
  ∷ mov-mem-preserves fst-addr fst-ok            -- store fst
  ∷ mov-mem-preserves snd-addr snd-ok            -- store snd
  ∷ add-rsp-preserves 24 rsp-ok                  -- deallocate
  ∷ []
```

### Why This Works

The key insight: **frame transitions were the source of complexity**.

With frames:
- Each combinator creates a new frame
- Must prove `frame-scope` transfers across frame boundaries
- Must track `current-frame` changes
- Must prove `restored-frame-scope` when returning

Without frames:
- One frame throughout (caller's)
- `frame-scope` is reflexivity
- No transitions to reason about
- Proofs compose directly

### Estimated Complexity Reduction

| Component | Current | Simplified |
|-----------|---------|------------|
| StateCorresponds fields | ~12 | ~5 |
| PairRunner lines | ~600 | ~100 |
| Frame-related postulates | ~5 | 0 |
| Generic instruction lemmas | 0 | ~10 (reusable) |
| Per-combinator frame proofs | Many | 0 |

### Architectural Principle

**Dispatcher computes WHAT should happen** (slot allocation, reclamation, values)

**Address mapping shows WHERE** (slot → address, simple arithmetic)

**Instruction lemmas verify HOW** (x86 instructions preserve correspondence)

This separation means:
- Dispatcher proofs don't mention x86
- x86 proofs don't reason about allocation strategy
- The connection is thin and mechanical

---

## Implementation Plan for Path 2

### Why Fresh Start on Runner Layer

The current `pair-setup-result` proof is **tightly coupled** to the 4-instruction sequence:
- Step 0: push rbp effects
- Step 1: mov rbp, rsp effects
- Step 2: sub rsp effects
- Step 3: mov [rsp+16], rdi effects

Changing to 2 instructions breaks nearly all of this - it's not "fix a few things",
it's "rewrite the whole proof." The current PairRunner is ~1800 lines; the new one
should be ~300 lines.

### What to Keep vs Fresh Start

```
KEEP:           Dispatcher (PairWF, Allocation, BeforeFrontier, ValidAtWF)
KEEP:           IR, Types, Semantics
SMALL CHANGE:   CodeGen/Compile.agda (pair-setup, pair-cleanup)
FRESH START:    StateCorresponds → SimpleCorresponds (fewer fields)
FRESH START:    PairRunner.agda → SimplePairRunner.agda (much smaller)
```

### Phase 1: Codegen Changes

**Current pair-setup (4 instructions):**
```agda
pair-setup =
  push (reg rbp) ∷                              -- REMOVE
  mov (reg rbp) (reg rsp) ∷                     -- REMOVE
  sub (reg rsp) (imm (slots 3)) ∷               -- KEEP
  mov (mem (base+disp rsp (slots 2))) (reg rdi) ∷ []  -- KEEP
```

**New pair-setup (2 instructions):**
```agda
pair-setup =
  sub (reg rsp) (imm (slots 3)) ∷
  mov (mem (base+disp rsp (slots 2))) (reg rdi) ∷ []
```

**Current pair-cleanup (4 instructions):**
```agda
pair-cleanup =
  mov (mem (base+disp rsp slot-size)) (reg rax) ∷  -- KEEP
  mov (reg rax) (reg rsp) ∷                        -- KEEP
  mov (reg rsp) (reg rbp) ∷                        -- REMOVE
  pop rbp ∷ []                                     -- REMOVE
```

**New pair-cleanup (3 instructions):**
```agda
pair-cleanup =
  mov (mem (base+disp rsp slot-size)) (reg rax) ∷
  mov (reg rax) (reg rsp) ∷
  add (reg rsp) (imm (slots 3)) ∷ []
```

### Phase 2: Create SimpleCorresponds

New minimal StateCorresponds with only essential fields:

```agda
record SimpleCorresponds (σ : LocState) (s : x86State) : Set where
  field
    frame-base : Addr                    -- constant throughout execution
    regs-correspond : RegsCorrespond σ s
    mem-corresponds : MemCorresponds frame-base σ s
    rsp-in-bounds : InStack (x86-readReg regs rsp)
    rsp-below-frame : x86-readReg regs rsp ≤ frame-base
    halted-corresponds : halted σ ≡ halted s
```

**Deleted fields** (no longer needed):
- `current-frame` - constant, use `frame-base` directly
- `rbp-is-frame-base` - rbp never changes
- `frame-scope` - trivially true with one frame
- `heap-in-heap` - can derive from mem-corresponds if needed

### Phase 3: Create SimplePairRunner

Build new runner using generic instruction lemmas:

```agda
-- Generic lemmas (reusable across all combinators)
sub-rsp-valid : ...
add-rsp-valid : ...
mov-mem-valid : ...
mov-reg-valid : ...

-- Simplified pair runner (~300 lines instead of ~1800)
simple-pair-runner : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) →
  SimpleRunner f → SimpleRunner g → SimpleRunner (⟨ f , g ⟩ m)
simple-pair-runner f g m f-run g-run = ...
```

### Phase 4: Migration and Cleanup

1. Once SimplePairRunner works, migrate other combinators
2. Delete old StateCorresponds frame-related fields
3. Delete old PairRunner.agda
4. Rename SimpleCorresponds → StateCorresponds

---

## Trade-off Summary

| Aspect | Path 1 (Frame-Aware Dispatcher) | Path 2 (Frameless Codegen) |
|--------|--------------------------------|---------------------------|
| Runtime cost | ~5 cycles/combinator | 0 extra cycles |
| Proof complexity | Higher (frame transitions) | Lower (no transitions) |
| Debugging | Standard stack traces | Non-standard |
| ABI compliance | Standard | Non-standard (internal only) |
| Code changes | Dispatcher (PairWF, etc.) | Codegen + Runner |
| Dispatcher model | Changes to match x86 | Stays as-is |

---

## ABI Compliance: Detailed Analysis

### Standard x86-64 ABI (System V AMD64)

The ABI specifies that functions should set up frames:

```asm
; Standard prologue
push rbp          ; save caller's frame pointer
mov rbp, rsp      ; establish new frame

; ... function body ...

; Standard epilogue
pop rbp           ; restore caller's frame pointer
ret
```

This creates a **linked list of frames** via rbp:

```
┌─────────────────┐
│ caller's rbp ───────┐
│ caller's locals │    │
├─────────────────┤    │
│ saved rbp ──────│────┘  (points to caller's frame)
│ pair's locals   │
├─────────────────┤
│ saved rbp ──────│────►  (points to pair's frame)
│ f's locals      │
└─────────────────┘
       ▲
      rbp (current)
```

### What Uses This Frame Chain

1. **Debuggers (gdb, lldb)**: Walk the chain to show stack traces
2. **Profilers (perf, valgrind)**: Sample the chain for call graphs
3. **Exception handlers**: Unwind the stack to find catch blocks
4. **Crash reporters**: Generate backtraces for crash logs

### Frameless Impact on Stack Walking

With frameless codegen, **internal CCC combinators** don't create frames:

```
┌─────────────────┐
│ caller's rbp ───────┐
│ caller's locals │    │
├─────────────────┤    │
│ pair's locals   │    │  ← no saved rbp here!
├─────────────────┤    │
│ f's locals      │    │  ← no saved rbp here!
└─────────────────┘    │
       ▲               │
      rsp              │
       ▲               │
      rbp ─────────────┘  (still points to caller's frame)
```

**Consequence**: Tools see one big frame instead of the combinator structure.

### When ABI Compliance Matters vs Doesn't

**Doesn't matter (internal CCC code):**
- CCC combinators calling each other
- Pure functional code without external calls
- Performance-critical inner loops

**Matters (external boundaries):**
- Calling libc functions (printf, malloc, etc.)
- FFI to C/Rust libraries
- Signal handlers
- Anything that might throw exceptions

### The Hybrid Solution

At **external call boundaries**, we still create proper frames:

```
  ┌─ CCC combinators (frameless, fast) ─┐
  │   pair                               │
  │     ├─ f                             │
  │     └─ g ────────────────────────────┼──► malloc()  ← FRAME HERE
  │   compose                            │
  │     └─ ...                           │
  └──────────────────────────────────────┘
```

```asm
; Before FFI/external call
push rbp
mov rbp, rsp
call external_function
pop rbp
; Continue frameless internally
```

### ABI Compliance Summary

| Scenario | Frame needed? | Why |
|----------|---------------|-----|
| `pair` calling `f` | No | Internal, same compilation unit |
| `f` calling `g` via compose | No | Internal CCC combinator |
| Any combinator calling `malloc` | Yes | External, ABI compliance |
| Any combinator calling FFI | Yes | External, ABI compliance |
| Signal handler during execution | Partial | Only sees external boundaries |
| Debugger stack trace | Partial | Only sees external boundaries |

### Debug Build Option

For development, a "debug build" flag could enable frames for all combinators:

```agda
-- Debug mode: full frames (slower, better traces)
pair-setup-debug = [ push rbp, mov rbp rsp, sub rsp N, ... ]

-- Release mode: frameless (faster, minimal traces)
pair-setup-release = [ sub rsp N, ... ]
```

This gives developers the choice between debuggability and performance.

---

## Recommendation

**Path 2 (Frameless Codegen) is recommended** for the following reasons:

1. **Performance**: Eliminates unnecessary frame overhead for CCC combinators
2. **Proof simplicity**: Dispatcher's existing reclamation model is correct
3. **Architectural clarity**: One frame model, not two different models
4. **The combinators are not function calls**: Traditional frames exist for function call/return semantics, which CCC combinators don't use

The non-standard stack layout is acceptable because:
- This is internal to the compiled CCC code
- External function calls (FFI) would still use proper frames
- Debug tooling can be adapted if needed

---

## Refined Architecture: Layers and Their Responsibilities

### Overview: What We're Connecting

```
┌─────────────────────────────────────────────────────────────────┐
│  IR Semantics                                                    │
│  eval : IR A B → ⟦A⟧ → ⟦B⟧                                      │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│  Dispatcher (PairWF, etc.)                                       │
│  - LocState: slot machine state (regs, stackMem, heapMem)       │
│  - AllocState: allocation tracking (next-slot, capacity)        │
│  - BeforeFrontier: which locations are allocated                │
│  - ValidAtWF: value representation validity                     │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│  Correspondence Layer (NEW: SimpleCorresponds)                   │
│  - Maps slot machine state to x86 state                         │
│  - Minimal fields, no frame tracking                            │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│  Instruction Lemmas (NEW: generic, reusable)                     │
│  - One lemma per instruction type                               │
│  - Shows how each instruction affects correspondence            │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│  x86 Semantics                                                   │
│  State: regs, memory, pc, halted                                │
│  step/Star: instruction execution                               │
└─────────────────────────────────────────────────────────────────┘
```

### Layer 1: Dispatcher (EXISTING - NO CHANGES)

**Purpose**: Compute slot machine state transitions for IR execution.

**Structures**:
- `LocState`: Abstract machine state
  - `regs`: Register file (RDI, RAX, etc. hold ValueLocations)
  - `stackMem`: Frame → Slot → Maybe ValueLocation
  - `heapMem`: HeapLocation → Maybe HeapLocation
  - `halted`: Execution status

- `AllocState`: Allocation bookkeeping
  - `current-frame`: The frame we're allocating in
  - `next-slot`: Next available slot index
  - `frame-capacity`: How many slots available
  - `slots-available`: Proof that next-slot ≤ capacity

- `BeforeFrontier alloc loc`: Proof that `loc` is a valid allocated location
  - `stack-before`: loc is in current frame, slot < next-slot
  - `stack-ancestor`: loc is in a parent frame
  - `heap-before`: loc is on heap with valid ref-id

- `ValidAtWF mode alloc value loc state`: Value is correctly represented at loc

**What Dispatcher handles**:
- Which slots to allocate for pair (reclamation)
- Value validity tracking
- Memory write sequencing
- Capacity management

**What Dispatcher does NOT handle**:
- x86 instruction execution
- Actual memory addresses
- Register values (just locations)

### Layer 2: Address Mapping (NEW - simple functions)

**Purpose**: Convert slot machine locations to x86 addresses.

```agda
-- Convert ValueLocation to x86 address
loc-to-addr : (frame-base : Addr) → (heap-base : HeapRef → Addr) →
              ValueLocation → Addr
loc-to-addr fb hb (OnStack frame k) = frame-base frame + k * 8
loc-to-addr fb hb (OnHeap hl) = heap-base (heap-ref hl) + offset hl * 8
```

With frameless codegen:
- `frame-base` = initial rbp value (CONSTANT throughout execution)
- Stack slots are at addresses relative to this fixed base
- `rsp` moves but `frame-base` doesn't

**Key insight**: Since rbp never changes, we don't need to track "current frame" -
there's only one frame for the entire combinator execution.

### Layer 3: SimpleCorresponds (NEW - minimal correspondence)

**Purpose**: Prove slot machine state corresponds to x86 state.

```agda
record SimpleCorresponds (σ : LocState) (s : x86State) : Set where
  field
    -- Address mapping parameters (constant throughout execution)
    frame-base : Addr
    heap-base : HeapRef → Addr

    -- Register correspondence
    regs-correspond : RegsCorrespond frame-base heap-base σ s

    -- Memory correspondence
    mem-corresponds : MemCorresponds frame-base heap-base σ s

    -- Stack pointer validity
    rsp-in-bounds : InStack (x86-readReg s.regs rsp)
    rsp-at-or-below-frame : x86-readReg s.regs rsp ≤ frame-base

    -- Halted flag
    halted-corresponds : σ.halted ≡ s.halted
```

**Field explanations**:

| Field | Purpose | Why needed |
|-------|---------|------------|
| `frame-base` | Fixed frame base address | Address calculations, constant |
| `heap-base` | Heap address mapping | Convert HeapRef to address |
| `regs-correspond` | x86 regs hold addr of slot machine locs | Verify register values |
| `mem-corresponds` | x86 memory matches slot machine memory | Verify memory contents |
| `rsp-in-bounds` | Stack pointer in valid region | Memory safety |
| `rsp-at-or-below-frame` | Haven't overflowed stack | Memory safety |
| `halted-corresponds` | Halted flags match | Termination |

**What's NOT in SimpleCorresponds** (compared to old StateCorresponds):

| Removed Field | Why removed |
|---------------|-------------|
| `current-frame` | Constant - just use `frame-base` |
| `rbp-is-frame-base` | rbp never changes - trivial |
| `frame-scope` | Only one frame - trivially true |
| `heap-in-heap` | Derivable from mem-corresponds |

### Layer 4: RegsCorrespond (SIMPLIFIED)

**Purpose**: Each slot machine register corresponds to x86 register value.

```agda
record RegsCorrespond (fb : Addr) (hb : HeapRef → Addr)
                      (σ : LocState) (s : x86State) : Set where
  field
    rdi-corresponds : x86-readReg s.regs rdi ≡ loc-to-addr fb hb (readReg σ.regs RDI)
    rax-corresponds : x86-readReg s.regs rax ≡ loc-to-addr fb hb (readReg σ.regs RAX)
    -- ... other registers as needed
```

**Insight**: The x86 register holds the ADDRESS of the slot machine location,
not the value itself. To get the value, read memory at that address.

### Layer 5: MemCorresponds (SIMPLIFIED)

**Purpose**: Slot machine memory entries exist in x86 memory.

```agda
record MemCorresponds (fb : Addr) (hb : HeapRef → Addr)
                      (σ : LocState) (mem : x86Memory) : Set where
  field
    stack-corresponds : ∀ f k loc →
      σ.stackMem f k ≡ just loc →
      x86-readMem mem (stack-loc-to-addr fb f k) ≡ just (loc-to-addr fb hb loc)

    heap-corresponds : ∀ hl hl' →
      σ.heapMem hl ≡ just hl' →
      x86-readMem mem (heap-loc-to-addr hb hl) ≡ just (heap-loc-to-addr hb hl')
```

### Layer 6: Instruction Lemmas (NEW - generic, reusable)

**Purpose**: Prove how each x86 instruction affects correspondence.

```agda
-- Allocate stack space
sub-rsp-lemma : ∀ n →
  SimpleCorresponds σ s →
  n ≤ available-capacity →
  SimpleCorresponds σ (exec (sub rsp n) s)

-- Deallocate stack space
add-rsp-lemma : ∀ n →
  SimpleCorresponds σ s →
  rsp + n ≤ frame-base →
  SimpleCorresponds σ (exec (add rsp n) s)

-- Write to stack memory
mov-to-mem-lemma : ∀ offset val →
  SimpleCorresponds σ s →
  InStack (rsp + offset) →
  (rsp + offset) < frame-base →  -- below tracked slots
  SimpleCorresponds σ (exec (mov [rsp+offset] val) s)

-- Write to register
mov-to-reg-lemma : ∀ dst src →
  SimpleCorresponds σ s →
  SimpleCorresponds (updateReg σ dst (addrToLoc src)) (exec (mov dst src) s)
```

**Key principle**: Each lemma handles ONE instruction. Combinator proofs compose these.

### Layer 7: Combinator Runners (NEW - compositional)

**Purpose**: Compose instruction lemmas for each combinator.

```agda
simple-pair-runner : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) →
  SimpleRunner f → SimpleRunner g → SimpleRunner (⟨ f , g ⟩ m)
simple-pair-runner f g m f-run g-run prefix suffix σ s sc =
  let
    -- Phase 1: Setup (2 instructions)
    (s1, sc1) = sub-rsp-lemma (slots 3) sc capacity-ok
    (s2, sc2) = mov-to-mem-lemma (slots 2) rdi sc1 in-bounds-ok

    -- Phase 2: Run f
    (s3, σ3, sc3) = f-run ... sc2

    -- Phase 3: Middle (2 instructions)
    (s4, sc4) = mov-to-mem-lemma 0 rax sc3 ...
    (s5, sc5) = mov-from-mem-lemma rdi (slots 2) sc4 ...

    -- Phase 4: Run g
    (s6, σ6, sc6) = g-run ... sc5

    -- Phase 5: Cleanup (3 instructions)
    (s7, sc7) = mov-to-mem-lemma slot-size rax sc6 ...
    (s8, sc8) = mov-to-reg-lemma rax rsp sc7
    (s9, sc9) = add-rsp-lemma (slots 3) sc8 ...
  in
    (s9, σ-final, sc9, ...)
```

**Estimated size**: ~100-150 lines (vs ~1800 in old PairRunner)

### Summary: Division of Responsibilities

| Layer | Handles | Doesn't Handle |
|-------|---------|----------------|
| Dispatcher | Allocation, validity, slot indices | x86 addresses, execution |
| Address Mapping | Location → Address conversion | State tracking |
| SimpleCorresponds | State correspondence | Allocation policy |
| Instruction Lemmas | Single instruction effects | Combinator logic |
| Combinator Runners | Composing instructions | Instruction semantics |
| x86 Semantics | Instruction execution | Abstract locations |

### File Organization

```
formal/Once/CCC/Target/X86v3/
├── Dispatcher/           # UNCHANGED
│   ├── Allocation.agda
│   ├── IR/PairWF.agda
│   └── ...
├── CodeGen/
│   └── Compile.agda      # UPDATED (frameless)
├── Refinement/
│   ├── SlotToX86.agda    # OLD - keep for reference during migration
│   ├── SimpleCorresponds.agda   # NEW - minimal correspondence
│   └── InstructionLemmas.agda   # NEW - generic lemmas
├── SimplePairRunner.agda  # NEW - compositional runner
└── PairRunner.agda        # OLD - delete after migration
```

---

## Open Questions

1. **Apply combinator**: Does apply need frames for closure calls? May need hybrid approach.
2. **Stack alignment**: Does removing push rbp affect 16-byte alignment requirements?
3. **Exception handling**: If exceptions are added later, will frameless cause issues?
4. **Debugging story**: What tooling is needed for frameless stack traces?

---

## References

- `formal/Once/CCC/Target/X86v3/Dispatcher/Allocation.agda` - BeforeFrontier, push-frame/pop-frame
- `formal/Once/CCC/Target/X86v3/Dispatcher/IR/PairWF.agda` - Current Dispatcher pair implementation
- `formal/Once/CCC/Target/X86v3/PairRunner.agda` - Current Runner with frame creation
- `formal/Once/CCC/Target/X86v3/Refinement/SlotToX86.agda` - StateCorresponds, frame-scope
