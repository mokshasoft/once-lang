# Comprehensive Analysis of Once Language Backend Formal Proofs

## Executive Summary

This analysis examines the formal verification status across AArch64, x86-64, and RISC-V backends for the categorical generators. The core finding is that **apply is universally unprovable** with the current execution model, and **compose/pair/case** have difficulties due to program concatenation reasoning.

**Key Strategic Insight:** We can maintain **multiple generator implementations** - some optimized for proof simplicity, others for performance. This allows us to first prove correctness with simpler implementations, then optionally prove equivalence to faster versions.

---

## Table 1: Generator Verification Status

Generators grouped by category. Status: ✅ Proven | ⚠️ Partially Proven | ❌ Postulated

| Category | Generator | AArch64 | x86-64 | RISC-V | Difficulty |
|----------|-----------|---------|--------|--------|------------|
| **Identity** | id | ✅ | ✅ | ✅ | Trivial |
| **Composition** | compose | ❌ | ✅ | ❌ | Medium |
| **Product** | fst | ⚠️ | ✅ | ✅ | Low |
| **Product** | snd | ⚠️ | ✅ | ✅ | Low |
| **Product** | pair | ❌ | ✅ | ❌ | Medium-High |
| **Coproduct** | inl | ⚠️ | ✅ | ✅ | Low |
| **Coproduct** | inr | ⚠️ | ✅ | ✅ | Low |
| **Coproduct** | case | ❌ | ✅ | ❌ | Medium-High |
| **Terminal** | terminal | ✅ | ✅ | ✅ | Trivial |
| **Initial** | initial | ✅ | ✅ | ✅ | Trivial |
| **Exponential** | curry | ❌ | ✅ | ✅ | High |
| **Exponential** | apply | ❌ | ❌ | ❌ | **FUNDAMENTAL** |
| **Recursive** | fold | ✅ | ✅ | ✅ | Trivial |
| **Recursive** | unfold | ✅ | ✅ | ✅ | Trivial |
| **Effect** | arr | ✅ | ✅ | ✅ | Trivial |

**Summary by backend:**
- **x86-64**: 14/15 proven (apply intentionally postulated)
- **RISC-V**: 11/15 proven
- **AArch64**: 8/15 proven (active development)

---

## Table 2: Key Unproven Lemmas Per Generator

| Generator | Most Difficult Lemma #1 | Most Difficult Lemma #2 | Core Difficulty |
|-----------|------------------------|------------------------|-----------------|
| **apply** | `run-apply-seq` | N/A | Code pointer points to curry's program, not apply's. **FUNDAMENTAL MODEL LIMITATION** |
| **compose** | `exec-concat-left` | `run-concat-seq` | Proving execution continues correctly when programs are joined |
| **pair** | `rsp-eq-r15-after-g` (x86) | Memory separation (`addr-diff`) | Stack frame preservation across nested IR |
| **case** | `run-case-inl` | `run-case-inr` | Branch reasoning + IH on sub-IRs |
| **curry** | `fetch-at-thunk-fails` | Jump target calculation | Proving jump skips thunk; mostly solved in RISC-V/x86 |
| **fst/snd** | Agda pattern match limitation | N/A | Cannot pattern match on `⟦ B ⟧` when B is abstract |
| **inl/inr** | `encode-inl/inr-construct` | Memory layout axiom | Infrastructure proven; semantic link remaining |

---

## Table 3: Cycle Count Estimates Per Generator

Estimates for modern out-of-order CPUs (Cortex-A76, Zen 4, SiFive U74). Cycles shown are approximate latency, not throughput.

| Generator | AArch64 | x86-64 | RISC-V | Notes |
|-----------|---------|--------|--------|-------|
| id | 0-1 | 1 | 0-1 | nop or mov (zero-latency on some CPUs) |
| compose | |f|+|g| | |f|+1+|g| | |f|+|g| | x86 needs mov rdi,rax |
| fst | 3-4 | 3-4 | 3-4 | Single load, L1 hit |
| snd | 3-4 | 3-4 | 3-4 | Single load, L1 hit |
| pair | 10+ + |f| + |g| | 15+ + |f| + |g| | 10+ + |f| + |g| | Stack ops + 2 stores |
| inl | 5-6 | 6-7 | 5-6 | Stack alloc + 2 stores |
| inr | 6-7 | 6-7 | 6-7 | Stack alloc + 3 stores |
| case | 8-10 + |branch| | 10-12 + |branch| | 7-9 + |branch| | Branch + loads |
| terminal | 1 | 1 | 1 | Immediate load |
| initial | - | - | - | Trap, doesn't return |
| curry | 15-20 + skip | 18-22 + skip | 15-20 + skip | Closure alloc + jump over thunk |
| apply | 20-30 | 25-35 | 20-30 | Load chain + indirect call |
| fold | 0-1 | 1 | 0-1 | nop/mov |
| unfold | 0-1 | 1 | 0-1 | nop/mov |
| arr | 0-1 | 1 | 0-1 | nop/mov |

---

## Table 4: Key Instructions and Their Costs

| Instruction | AArch64 | x86-64 | RISC-V | Cycles | Notes |
|-------------|---------|--------|--------|--------|-------|
| nop | nop | nop | nop | 0-1 | Often eliminated |
| mov reg,reg | mov xD,xS | mov %rs,%rd | mv rd,rs | 0-1 | Register rename |
| mov reg,imm | mov xD,#imm | mov $imm,%rd | li rd,imm | 1 | Immediate |
| load | ldr xD,[xS] | mov (rs),rd | ld rd,0(rs) | 3-4 | L1 cache hit |
| store | str xD,[xS] | mov rd,(rs) | sd rs,0(rd) | 1 | Store buffer |
| sub sp | sub sp,sp,#N | sub $N,%rsp | addi sp,sp,-N | 1 | Stack allocation |
| add sp | add sp,sp,#N | add $N,%rsp | addi sp,sp,N | 1 | Stack deallocation |
| push | - | push %r | - | 1 | x86 only |
| pop | - | pop %r | - | 1 | x86 only |
| cmp | cmp xN,#imm | cmp $imm,%r | - | 1 | Sets flags (x86/ARM) |
| bne/jne | b.ne label | jne label | bne r,zero,L | 1-3 | Branch, 1 if predicted |
| b/jmp | b label | jmp label | j label | 1 | Unconditional |
| bl/call | bl label | call label | jal ra,label | 1-3 | Direct call |
| blr/call* | blr xN | call *%r | jalr ra,rs,0 | 5-10 | **Indirect call** |
| ret | ret | ret | ret | 1-3 | Return prediction |
| trap | brk #0 | ud2 | ebreak | - | Exception |

**Critical observation:** Indirect calls (blr/call*/jalr) are the most expensive operations and are used only by **apply**.

---

## Table 4b: Detailed Cycle Analysis by Microarchitecture

### AArch64 - Apple M1/M2 (Firestorm cores)

| Generator | Instructions | Issue Slots | Latency | Throughput | Notes |
|-----------|-------------|-------------|---------|------------|-------|
| id | 1 nop | 0 | 0 | - | Eliminated in decode |
| fst | 1 ldr | 2 load | 4 | 2/cycle | L1 hit assumed |
| snd | 1 ldr | 2 load | 4 | 2/cycle | L1 hit assumed |
| inl | 4 | 1+1+1+1 | 5 | 1/cycle | Stack ops pipeline |
| inr | 5 | 1+1+1+1+1 | 6 | 1/cycle | Extra mov for tag |
| terminal | 1 mov | 1 | 1 | 4/cycle | Fast immediate |
| curry | 8+|f| | 6+|f| | 10+|f| | - | Jump over thunk |
| apply | 6 | 4ld+1+1 | **18-25** | - | **blr has 12-18 cycle penalty** |

### x86-64 - AMD Zen 4

| Generator | Instructions | µops | Latency | Notes |
|-----------|-------------|------|---------|-------|
| id | 1 mov | 0 | 0 | Register rename, eliminated |
| fst | 1 mov | 1 | 4 | Load from memory |
| snd | 1 mov | 1 | 4 | Load from memory |
| pair | 11+|f|+|g| | 13+|f|+|g| | 15+|f|+|g| | Push/pop are expensive |
| inl | 4 | 5 | 6 | sub+movq+mov+mov |
| inr | 4 | 5 | 6 | Same as inl |
| case | 8+branch | 10+branch | 3-15 | Depends on prediction |
| curry | 12+|f| | 15+|f| | 12+|f| | |
| apply | 6 | 8 | **20-35** | **call * has ~15 cycle penalty** |

### RISC-V - SiFive U74 (in-order)

| Generator | Instructions | Cycles | Notes |
|-----------|-------------|--------|-------|
| id | 1 nop | 1 | In-order, no elimination |
| fst | 1 ld | 2-3 | Cache dependent |
| snd | 1 ld | 2-3 | Cache dependent |
| compose | |f|+|g| | |f|+|g| | No mov overhead! |
| inl | 4 | 5 | Sequential execution |
| inr | 5 | 6 | Sequential execution |
| curry | 12+|f| | 14+|f| | |
| apply | 7 | **25-40** | **jalr very expensive on in-order** |

### Key Microarchitectural Observations

1. **Apple M1/M2 advantages:**
   - Massive reorder buffer (630+ entries) hides latency
   - 8-wide decode can process most generators in 1-2 cycles
   - Zero-cycle register moves for id/fold/unfold

2. **AMD Zen 4 advantages:**
   - Excellent branch prediction (97%+) makes case fast when predictable
   - push/pop are single µop, but still create dependencies
   - Indirect call prediction helps apply

3. **RISC-V U74 (in-order) challenges:**
   - Every instruction serializes
   - No speculative execution to hide apply latency
   - Branch mispredictions stall completely (5+ cycles)

4. **The a0 = input AND output optimization:**
   - RISC-V and AArch64 use same register for input/output
   - Saves 1 instruction per compose vs x86-64
   - Cumulative savings significant in deeply nested IR

---

## Table 5: Cache Hotness Analysis

| Generator | Code Locality | Data Locality | Cache Behavior |
|-----------|---------------|---------------|----------------|
| id, fold, unfold, arr | Excellent | N/A | Single instruction, always hot |
| fst, snd | Excellent | Single access | One load from likely-hot pair |
| terminal, initial | Excellent | N/A | Single instruction |
| compose | Good | N/A | Sequential, f then g |
| inl, inr | Good | Stack writes | Sequential, stack likely in L1 |
| pair | Fair | Multiple stack ops | f and g sequential, stack access |
| case | Fair | Branch dependent | One branch cold after prediction |
| curry | Fair | Closure on stack | Jump over thunk creates gap |
| **apply** | **Poor** | Closure + indirect | **Indirect jump = potential I-cache miss** |

**Key insight:** `apply` is the only generator with potential instruction cache misses due to indirect jumps to thunk code.

---

## The Fundamental Problem: Why apply Cannot Be Proven

### The Isolated Program Execution Model

The current formal model executes each IR morphism as an **isolated program**:

```
compile(curry f) → [alloc closure; store env; store code_ptr=6; jump over thunk; THUNK CODE; end]
compile(apply)   → [load closure; load arg; load env; load code_ptr; jalr code_ptr]
```

When `curry` stores `code_ptr = 6`, it points to instruction 6 **within curry's program**.

When `apply` executes `jalr code_ptr`, it jumps to instruction 6 **within apply's program**, but the thunk code only exists in curry's program!

### Why This Is Fundamental

1. **curry** and **apply** are compiled separately
2. Thunk code is embedded in curry's output
3. apply's indirect jump targets curry's code space
4. Our semantics has no linking phase

**This is documented as intentionally postulated** in `docs/formal/lessons-learned.md` (line 163).

---

## Deep Dive: Stack-Based Generator Implementations

### The Core Proof Difficulty with Registers

The current difficulties stem from **callee-saved register preservation**:

1. **pair** uses x20/r14 to save input across f execution
2. **case** uses x9/r15 for tag across branch execution
3. When f or g contain nested pair/case, they may use the same registers
4. Proof must show callee-saved semantics hold through arbitrary nesting

**The fundamental issue:** Proving that nested IR executions don't corrupt outer registers requires tracking register usage through the entire sub-IR, which creates mutual recursion in the proof.

### Stack-Based Alternative: "Easy-to-Prove" Implementations

By using the stack exclusively for temporaries, we can make proofs **purely local** - each generator's proof doesn't need to reason about what sub-IRs do to registers.

#### Implementation 1: Stack-Only Pair

```asm
; AArch64 Stack-Only Pair
; Input: x0 = value
; Output: x0 = pointer to (f(value), g(value))

    sub     sp, sp, #32         ; allocate: [input][f_result][pair_fst][pair_snd]
    str     x0, [sp, #24]       ; save input at sp+24
    ; --- compile f ---
    str     x0, [sp, #16]       ; save f_result at sp+16
    ldr     x0, [sp, #24]       ; reload input
    ; --- compile g ---
    str     x0, [sp, #8]        ; save g_result at sp+8 (pair.snd)
    ldr     x1, [sp, #16]       ; load f_result
    str     x1, [sp]            ; store as pair.fst
    mov     x0, sp              ; return pointer to pair
    ; Note: stack not restored - pair lives on stack
```

**Instruction count:** 8 + |f| + |g| (vs 6 + |f| + |g| for register version)

**Proof advantage:**
- No callee-saved register reasoning
- Stack slots at fixed offsets are trivially non-overlapping
- Each load/store has explicit address

#### Implementation 2: Stack-Only Case

```asm
; AArch64 Stack-Only Case
; Input: x0 = pointer to sum [tag, value]

    sub     sp, sp, #8          ; allocate: [saved_value]
    ldr     x9, [x0]            ; load tag (scratch reg OK)
    ldr     x0, [x0, #8]        ; load value into x0
    str     x0, [sp]            ; save value on stack
    cbnz    x9, .right
.left:
    ldr     x0, [sp]            ; reload value (in case f clobbered)
    ; --- compile f ---
    b       .end
.right:
    ldr     x0, [sp]            ; reload value
    ; --- compile g ---
.end:
    add     sp, sp, #8          ; restore stack
```

**Instruction count:** 10 + |f| + |g| (vs 8 + |f| + |g| for register version)

**Proof advantage:**
- No need to prove x9 preserved through f or g
- Value always reloaded from known stack location

#### Implementation 3: Stack-Only Compose

```asm
; AArch64 Stack-Only Compose
; Already simple, but with explicit frame:

    ; --- compile f --- (x0 -> x0)
    nop                         ; separator for proof clarity
    ; --- compile g --- (x0 -> x0)
```

**Current compose is already easy!** The difficulty is in exec-concat, not the generated code.

### Stack Machine: The Most Proof-Friendly Architecture

Instead of a register machine with stack, consider a **pure stack machine**:

```
Stack Machine State:
  - Stack: List Word
  - Memory: Word → Word
  - PC: ℕ
  - Halted: Bool

No registers!
```

#### Stack Machine Generators

| Generator | Stack Effect | Instructions |
|-----------|-------------|--------------|
| id | (a -- a) | (no-op) |
| compose f g | (a -- c) | f; g |
| fst | (ptr -- a) | DUP; LOAD 0 |
| snd | (ptr -- b) | DUP; LOAD 8 |
| pair f g | (a -- ptr) | DUP; f; SWAP; g; ALLOC 2; STORE_PAIR |
| inl | (a -- ptr) | PUSH 0; SWAP; ALLOC 2; STORE_PAIR |
| inr | (a -- ptr) | PUSH 1; SWAP; ALLOC 2; STORE_PAIR |
| case f g | (ptr -- c) | DUP; LOAD 0; JMPNZ right; DROP; LOAD 8; f; JMP end; right: DROP; LOAD 8; g; end: |
| terminal | (a -- unit) | DROP; PUSH 0 |
| curry f | (a -- closure) | MAKE_CLOSURE(f) |
| apply | (closure_arg_pair -- result) | CALL_CLOSURE |

**Proof advantages:**
1. **No register interference** - stack is the only state
2. **Explicit data flow** - every value's location is on the stack
3. **Simple composition** - f; g just concatenates
4. **Local reasoning** - each instruction's effect is immediate

**Performance cost:**
- ~2-3x slower than register machine
- More memory traffic (stack push/pop vs register move)
- But still linear in IR size

### Comparison: Proof Complexity vs Performance

| Implementation | pair proof | case proof | compose proof | Cycles (relative) |
|----------------|------------|------------|---------------|-------------------|
| Register-based | **Hard** (mutual IH) | **Hard** (branch + IH) | Medium | 1.0x |
| Stack-only regs | Medium | Medium | Easy | 1.3x |
| Pure stack machine | **Easy** | **Easy** | **Trivial** | 2.5x |

### Recommended Strategy: Multiple Implementations

```
Level 1: Stack Machine (easiest proofs)
  └─ Prove correctness for all generators
  └─ Serves as specification

Level 2: Stack-Only Registers (medium proofs)
  └─ Prove equivalent to Level 1
  └─ Still uses real registers for result

Level 3: Register-Optimized (hard proofs)
  └─ Prove equivalent to Level 2
  └─ Maximum performance
```

**Benefit:** Once Level 1 is proven, Level 2 and 3 only need to prove equivalence, not full semantic correctness.

---

## Deep Dive: Stack-Based Solutions for apply

### Why apply Is Different

The apply problem is **not about data threading**, it's about **code addressing**:

```
curry f a:
  1. Allocate closure [env=a, code_ptr=THUNK_ADDR]
  2. THUNK_ADDR points to: pair(env, arg); f; ret
  3. Return closure

apply (closure, arg):
  1. Load env from closure
  2. Load code_ptr from closure
  3. Jump to code_ptr  ← WHERE IS THIS CODE?
```

The thunk code only exists in curry's program space!

### Alternative 1: Defunctionalization

Transform closures into tagged data:

```
curry f a → (Tag_f, a)     ; no code pointer!
apply (tag, env, arg) → case tag of
                           Tag_f → f (env, arg)
                           Tag_g → g (env, arg)
                           ...
```

**Proof advantage:** No indirect jumps, just case analysis on tags

**Drawback:**
- Must know all possible curry'd functions at compile time
- Code duplication (each tag has its own f copy)
- Breaks separate compilation

### Alternative 2: Interpreter-Based apply

Instead of generating code that calls apply, generate code that **returns a request**:

```
curry f a → Closure(f_id, a)

apply (closure, arg) →
  return ApplyRequest(closure, arg)
  ; Interpreter handles the actual call
```

**Proof advantage:** apply becomes a simple data constructor, no control flow

**Drawback:** Requires trampolining, much slower

### Alternative 3: Whole-Program Compilation (Best for Proofs)

Compile the entire IR as one unit:

```agda
compile-whole : IR A B → Program
compile-whole (apply ∘ ⟨ curry f , id ⟩) =
  ; Inline the curry+apply into one sequence:
  <curry-alloc>; <apply-inline-f>
```

**Proof approach:**
- Never generate standalone curry/apply
- Always inline curry+apply pairs
- Thunk code is part of the same program

**Drawback:** Requires whole-program knowledge

### Alternative 4: Self-Modifying/Relocatable Code

Store thunk code in the closure itself:

```
curry f a:
  1. Allocate closure [env, THUNK_CODE_BYTES...]
  2. THUNK_CODE = assembled instructions for: pair(env,arg); f; ret
  3. Return closure

apply (closure, arg):
  1. Load env from closure+0
  2. Jump to closure+8  ; thunk code is IN the closure!
```

**Proof approach:**
- Thunk code is data stored in memory
- apply's jump target is deterministic: closure base + 8
- Need memory-as-code semantics

**Drawback:**
- Security (W^X violation)
- Complex memory model for proofs
- Architecture-specific code bytes in formal model

---

## Deep Dive: exec-concat Proof Techniques

### The Problem Statement

The key lemma `exec-concat-left` states:

```agda
exec-concat-left : ∀ (prog1 prog2 : Program) (s : State) (n : ℕ) →
  -- If running prog1 for n steps terminates at s₁...
  exec n prog1 s ≡ just s₁ → halted s₁ ≡ true →
  -- Then running prog1++prog2 for n steps also terminates at s₁
  exec n (prog1 ++ prog2) s ≡ just s₁
```

**Why this is hard:**
1. `exec` uses `with` abstraction, blocking computation
2. Must prove PC stays within prog1 bounds during execution
3. Must handle the interaction between `fetch` and list concatenation

### Current Proof Structure in AArch64 (lines 600-665)

```agda
exec-concat-left prog1 prog2 s n run-eq halted-eq = goal
  where
    -- Helper: fetch from concatenated program equals fetch from prog1
    -- when pc < length prog1
    fetch-concat-left : ∀ (pc : ℕ) → pc < length prog1 →
      fetch (prog1 ++ prog2) pc ≡ fetch prog1 pc

    -- POSTULATED: pc-in-bounds
    pc-in-bounds : ∀ (k : ℕ) (s' : State) →
      exec k prog1 s ≡ just s' → halted s' ≡ false →
      pc s' < length prog1

    -- POSTULATED: s'-is-s₁ (extract state equality)
    -- POSTULATED: exec-n'-eq (extract recursive equation)
```

### Strategy 1: Prove pc-in-bounds via Instruction Semantics

**Approach:** Show that every instruction either:
- Increments PC by 1 (within bounds)
- Sets PC via jump (to computed label within bounds)
- Halts execution

```agda
pc-progress : ∀ (prog : Program) (s s' : State) →
  step prog s ≡ just s' → halted s' ≡ false →
  pc s' < length prog

pc-progress prog s s' step-eq not-halted with halted s
... | true = ⊥-elim (step returns s unchanged, contradiction)
... | false with fetch prog (pc s)
...   | nothing = ⊥-elim (would halt)
...   | just instr = instr-pc-lemma prog s s' instr step-eq not-halted

instr-pc-lemma : For each instruction type, prove PC stays valid
```

**Key insight:** Only `jmp` and `b.ne/jne` can change PC non-incrementally. These use computed labels that are within program bounds by construction.

### Strategy 2: Use Well-Founded Recursion

Instead of fighting `with`, structure the proof using well-founded recursion on step count:

```agda
exec-concat-left : ∀ prog1 prog2 s n → ...
exec-concat-left prog1 prog2 s zero = ...  -- base case: n=0
exec-concat-left prog1 prog2 s (suc n) with halted s
... | true = refl  -- already halted
... | false with fetch prog1 (pc s) | fetch (prog1 ++ prog2) (pc s)
...   | nothing | _ = ...  -- halt due to fetch fail
...   | just i | just i' with i ≟Instr i'
...     | yes refl = exec-concat-left prog1 prog2 s' n (IH ...)
...     | no neq = ⊥-elim (fetch-concat-left contradiction)
```

### Strategy 3: Separate PC Tracking from Execution

Define a PC-tracking predicate separately:

```agda
-- PC never exceeds prog length during non-halted execution
PCBounded : Program → State → ℕ → Set
PCBounded prog s n =
  ∀ k → k < n → ∀ s' → exec k prog s ≡ just s' → halted s' ≡ false → pc s' < length prog

-- Prove PC is bounded for any program (via instruction analysis)
pc-bounded : ∀ prog s n → PCBounded prog s n

-- Use PC boundedness in exec-concat
exec-concat-left prog1 prog2 s n run-eq halted-eq =
  let pc-ok = pc-bounded prog1 s n
  in concat-with-bounded-pc prog1 prog2 s n pc-ok run-eq halted-eq
```

### Strategy 4: Specialized Lemmas per Generator

Instead of general exec-concat, prove specialized versions:

```agda
-- For compose: exec (prog-f ++ nop ++ prog-g)
exec-compose-chain : ∀ f g s →
  exec (length-f) (compile f) s ≡ just s₁ →
  exec (length-g) (compile g) s₂ ≡ just s₃ →
  exec (length-f + 1 + length-g) (compile (g ∘ f)) s ≡ just s₃

-- For case: exec (setup ++ branch-f ++ branch-g)
exec-case-left-branch : ∀ f g s →
  tag s ≡ 0 →  -- inl case
  exec (5 + length-f) (compile [f,g]) s ≡ just s'

exec-case-right-branch : ∀ f g s →
  tag s ≡ 1 →  -- inr case
  exec (5 + length-g) (compile [f,g]) s ≡ just s'
```

**Advantage:** Each specialized lemma only reasons about the specific instruction patterns of that generator.

### The fetch-append Lemmas (Already Proven)

These are the building blocks (lines 391-452 in RISC-V Correct.agda):

```agda
-- Fetching before append point
fetch-append-left : ∀ prog1 prog2 (i : ℕ) → i < length prog1 →
  fetch (prog1 ++ prog2) i ≡ fetch prog1 i

-- Fetching at append point
fetch-at-length : ∀ prog1 prog2 →
  fetch (prog1 ++ prog2) (length prog1) ≡ fetch prog2 0

-- Fetching after append point
fetch-append-right : ∀ prog1 prog2 (i : ℕ) →
  fetch (prog1 ++ prog2) (length prog1 + i) ≡ fetch prog2 i

-- Fetching past end fails
fetch-past-end : ∀ prog (i : ℕ) → i ≥ length prog →
  fetch prog i ≡ nothing
```

### Recommended Approach: Indexed Execution

The cleanest approach is to define **indexed execution** that tracks PC bounds:

```agda
-- Execution indexed by PC bound
exec-bounded : (n : ℕ) (prog : Program) (s : State) (bound : ℕ) →
               pc s < bound → bound ≤ length prog →
               Maybe State

-- Property: bounded execution preserves bound
exec-bounded-preserves : ∀ n prog s bound pc<bound bound≤len →
  case exec-bounded n prog s bound pc<bound bound≤len of λ where
    nothing → ⊤
    (just s') → halted s' ≡ true ∨ pc s' < bound

-- Main theorem follows easily
exec-concat-left-via-bounded : ...
```

### Estimated Proof Sizes

| Approach | Lines of Agda | Complexity | Reusability |
|----------|---------------|------------|-------------|
| Direct (current) | 200-300 | High (with fighting) | Low |
| Well-founded | 150-200 | Medium | Medium |
| Specialized | 100-150 per generator | Low | Low |
| Indexed execution | 250-350 | Medium | **High** |

### Helper Lemmas to Prove First

1. **fetch-concat-left** (already available)
2. **step-preserves-pc-bound** - Single step keeps PC in bounds
3. **execInstr-pc-increment** - Each instruction increments PC predictably
4. **jmp-target-in-bounds** - Jump targets are within program
5. **exec-step-concat** - One step in concat = one step in original

---

## Multiple Implementations Strategy

### The Key Insight

We don't need ONE implementation per generator. We can have:

```
Generator → List Implementation
  where
    Implementation = { code : Program, proof : Correctness, perf : CycleCount }
```

### Implementation Tiers

**Tier 1: Specification (Stack Machine)**
- Pure stack semantics
- Trivial proofs
- Defines "what" the generator should do
- May be too slow for production

**Tier 2: Easy-to-Prove (Stack-Only Registers)**
- Uses registers for result only
- All temporaries on stack
- Medium performance
- Independent proofs per generator

**Tier 3: Optimized (Current Register-Based)**
- Maximum performance
- Complex proofs with mutual recursion
- Can be proven equivalent to Tier 2

### Proof Strategy

```
                    ┌───────────────┐
                    │ Tier 1: Spec  │
                    │ (stack machine)│
                    └───────┬───────┘
                            │ equiv-1-2
                    ┌───────▼───────┐
                    │ Tier 2: Easy  │
                    │ (stack-only)  │
                    └───────┬───────┘
                            │ equiv-2-3
                    ┌───────▼───────┐
                    │ Tier 3: Fast  │
                    │ (optimized)   │
                    └───────────────┘
```

**Proving equiv-1-2:**
- Both produce same observable state
- Stack machine operations correspond to register+stack ops
- Straightforward simulation argument

**Proving equiv-2-3:**
- Only difference is register vs stack for temporaries
- Show that observable state (x0/rax/a0 and memory) is identical
- Callee-saved registers are restored, so final state matches

### Which Generators Need Multiple Implementations?

| Generator | Tier 1 Needed? | Tier 2 Useful? | Tier 3 Worth It? |
|-----------|---------------|----------------|------------------|
| id | No (trivial) | No | No |
| compose | Yes | Yes | Maybe |
| fst, snd | No (1 instr) | No | No |
| pair | **Yes** | **Yes** | Yes |
| inl, inr | No (proven) | No | No |
| case | **Yes** | **Yes** | Yes |
| terminal, initial | No | No | No |
| curry | Maybe | Maybe | Yes |
| apply | **Yes** | **Yes** | **Complex** |
| fold, unfold, arr | No (trivial) | No | No |

### Recommended Implementation Priority

1. **pair-stack-only**: Easiest win, unblocks many programs
2. **case-stack-only**: Required for any sum type handling
3. **compose**: Benefits from exec-concat, but stack version is backup
4. **curry-defunctionalized**: If defunctionalization is acceptable
5. **apply-defunctionalized**: Paired with curry-defunctionalized

---

## Proposed Solutions

### Solution 1: Combined Program Model (Recommended)

Instead of compiling each IR separately, compile the **entire program** as one unit:

```agda
compile-whole : IR A B → Program
compile-whole-correct : ∀ ir x → run (compile-whole ir) (init x) ≡ encode (eval ir x)
```

For curry+apply, the thunk code would be at a known offset in the combined program.

**Pros:** Solves apply fundamentally
**Cons:** Major refactor of codegen and proofs

### Solution 2: Linking Phase

Add an explicit linking phase that resolves code pointers:

```agda
link : List Program → Program
link-correct : ...
```

**Pros:** Matches real compilation
**Cons:** Complex new proof obligation

### Solution 3: Continuation-Passing Style (CPS)

Transform closures to CPS to avoid indirect jumps:

```
curry f a = (λk. k (λb. f (a, b)))
apply (closure, arg) = closure (λresult. result) arg
```

**Pros:** No indirect jumps, more linear code
**Cons:** Code size explosion, closure allocation still needed

### Solution 4: Stack Machine

Replace register machine with stack machine (like JVM):

```
curry f: PUSH_ENV; MAKE_CLOSURE(thunk_offset)
apply:   LOAD_CLOSURE; LOAD_ARG; CALL_CLOSURE
```

**Pros:** Simpler proofs, explicit stack semantics
**Cons:** Less efficient code, major architecture change

### Solution 5: Accept apply as Axiomatic (Current Approach)

Keep apply postulated as a trusted semantic axiom.

**Pros:** Already working, practical
**Cons:** Incomplete verification

---

## Recommended Plan to Tackle Proof Difficulties

### Phase 1: Complete AArch64 exec-concat Infrastructure (Priority: HIGH)

**Target files:**
- `formal/Once/Backend/AArch64/Correct.agda` (lines 600-665)

**Tasks:**
1. Prove `pc-in-bounds` helper (pc stays within prog1 during execution)
2. Prove `exec-n'-eq` (extract recursive execution equation from with-abstraction)
3. Complete `exec-concat-left` proof
4. Derive `run-concat-seq` from exec-concat-left

**Why first:** This unblocks compose, pair, case for AArch64.

### Phase 2: Abstract Pattern Match Workaround (Priority: MEDIUM)

**Target:** fst, snd, inl, inr semantic linking

**Approach:**
1. Add explicit type witnesses to encoding axioms
2. Use parametricity/free theorem style reasoning
3. Consider switching to Cubical Agda for better handling of abstract types

### Phase 3: Evaluate Alternative Architectures (Priority: RESEARCH)

**Goal:** Determine if stack machine or CPS could yield simpler proofs

**Tasks:**
1. Prototype stack machine semantics in Agda
2. Measure proof complexity vs register machine
3. Benchmark generated code performance
4. Make go/no-go decision on architecture change

### Phase 4: Document apply as Trusted (Priority: LOW)

**Goal:** Formalize what apply's postulate means for the trusted computing base

**Tasks:**
1. Specify exactly what semantic property apply satisfies
2. Document test coverage that validates apply's behavior
3. Add runtime assertions that catch apply violations

---

## Files to Modify/Create

| File | Action | Purpose |
|------|--------|---------|
| `formal/Once/Backend/AArch64/Correct.agda` | Modify | Complete exec-concat proofs |
| `formal/Once/Backend/RiscV64/Correct.agda` | Modify | Add exec-concat infrastructure |
| `formal/Once/Backend/Common/ExecConcat.agda` | Create | Shared concat proof infrastructure |
| `docs/formal/apply-tcb.md` | Create | Document apply's trusted status |
| `formal/Once/Backend/Stack/` | Create (optional) | Stack machine prototype |

---

## Making apply Provable: Execution Model Changes

### The Core Problem

The isolated-program execution model compiles each IR morphism separately:
- `curry f` embeds thunk code at instruction 6 **within curry's program**
- `apply` executes `jalr code_ptr` expecting the thunk **within apply's program**
- The thunk doesn't exist in apply's address space

### Option A: Whole-Program Compilation

Compile entire IR as one unit so curry and apply share code space:

```agda
compile-whole : IR A B → Program
compile-whole (apply ∘ ⟨ curry f , g ⟩) =
  <compile g>           -- compute argument
  <allocate closure>    -- curry part (thunk is HERE)
  <load closure, call>  -- apply jumps to known offset
  <thunk code: f>       -- thunk at predictable position
```

**Changes needed:**
1. Refactor `compile` to take full IR context
2. Compute thunk offsets based on whole-program layout
3. Proofs become about whole programs, not composable pieces

**Proof complexity:** Medium - thunk at known offset, no indirect jump uncertainty

### Option B: Defunctionalization (Best for proofs)

Eliminate closures by tagging:

```agda
defunc : IR A B → IR' A B  -- IR' has no curry/apply

defunc (curry f) = inl ∘ ⟨ id , const f_tag ⟩  -- (env, tag) instead of closure
defunc apply = case [ f₁ , f₂ , f₃ , ... ]     -- dispatch on tag
```

**Changes needed:**
1. Whole-program analysis to collect all curry'd functions
2. Generate dispatch table for apply
3. Transform IR before codegen

**Proof complexity:** Easy - apply becomes a case, no indirect jumps

### Option C: Memory-as-Code (Store thunk in closure)

```
Closure layout: [env: 8 bytes][thunk_code: N bytes...]

apply (closure, arg):
  load env from closure+0
  jump to closure+8  -- deterministic offset!
```

**Changes needed:**
1. Encode instruction bytes as data in formal model
2. Memory model must support executable data
3. Architecture-specific machine code representation

**Proof complexity:** Hard - need to model instruction encoding

---

## Branchless Execution: Eliminating All Branches

### Current Branch Usage

| Generator | Branch Type | Purpose | Cache Impact |
|-----------|-------------|---------|--------------|
| case | Conditional (bne/jne) | Select left or right | One branch cold |
| curry | Unconditional (b/jmp) | Skip over thunk | Small gap |
| apply | Indirect (blr/jalr) | Call thunk | **I-cache miss** |

**Key insight:** `apply` is the only non-cache-hot generator due to indirect jumps.

### Branchless case via Speculation + Select

```asm
; Branchless case [f, g] on AArch64
; Input: x0 = pointer to sum [tag, value]

    ldr     x9, [x0]            ; tag
    ldr     x0, [x0, #8]        ; value

    ; Save value, compute BOTH branches
    mov     x20, x0             ; save value
    ; --- compile f ---
    mov     x21, x0             ; save f result

    mov     x0, x20             ; restore value
    ; --- compile g ---
    ; x0 now has g result

    ; Select based on tag (branchless!)
    cmp     x9, #0
    csel    x0, x21, x0, eq     ; x0 = (tag==0) ? f_result : g_result
```

**Cost:** Executes both branches (2x work)
**Benefit:** No branch misprediction, fully predictable, constant-time

### Branchless curry (Defunctionalized)

```asm
; Branchless curry (defunctionalized)
; Input: x0 = env
; Output: x0 = (env, tag) pair

    sub     sp, sp, #16
    str     x0, [sp]            ; store env
    mov     x9, #TAG_F          ; compile-time constant
    str     x9, [sp, #8]        ; store tag
    mov     x0, sp
    ; No branch needed!
```

### Branchless apply (Defunctionalization + Speculation)

```asm
; Branchless apply - speculate over all possible functions
; Input: x0 = (closure, arg) where closure = (env, tag)

    ldr     x9, [x0]            ; closure ptr
    ldr     x10, [x0, #8]       ; arg
    ldr     x11, [x9]           ; env
    ldr     x12, [x9, #8]       ; tag

    ; Build (env, arg) pair
    sub     sp, sp, #16
    str     x11, [sp]           ; env
    str     x10, [sp, #8]       ; arg
    mov     x0, sp

    ; Execute ALL possible functions (speculation)
    mov     x20, x0
    ; --- compile f1 ---
    mov     x21, x0             ; f1 result

    mov     x0, x20
    ; --- compile f2 ---
    mov     x22, x0             ; f2 result

    ; ... more functions ...

    ; Select based on tag (cascade of csel)
    cmp     x12, #1
    csel    x0, x21, x0, eq
    cmp     x12, #2
    csel    x0, x22, x0, eq
```

**This is defunctionalization + branchless case!**

### Cycle Comparison: Branching vs Branchless

| Approach | case cycles | apply cycles | Predictable? | Constant-time? |
|----------|-------------|--------------|--------------|----------------|
| Branching | 8 + \|one branch\| | 25-40 (indirect) | No | No |
| Branchless | 8 + \|both branches\| + 3 | 10 + \|all funcs\| + 3n | **Yes** | **Yes** |

For small functions (\|f\|, \|g\| < 10 instructions), branchless often wins due to avoiding misprediction penalties (15-20 cycles on modern CPUs).

---

## Decision Log: Generator Implementation Selection

Different implementations serve different purposes. Select based on your program's requirements:

### Implementation Profiles

| Profile | Primary Goal | Trade-offs | Use Case |
|---------|--------------|------------|----------|
| **Crypto** | Constant-time execution | Slower (2x+ for case) | Cryptographic operations, side-channel resistance |
| **Verified** | Provable correctness | May be slower | Safety-critical systems, formal methods |
| **Fast** | Maximum performance | Complex proofs, may have branches | General-purpose, performance-critical |
| **Small** | Minimal code size | May be slower | Embedded systems, constrained memory |
| **Debug** | Observable execution | Slowest, most overhead | Development, testing |

### Per-Generator Implementation Matrix

| Generator | Crypto | Verified | Fast | Small |
|-----------|--------|----------|------|-------|
| id | nop | nop | nop | nop |
| compose | f;g | f;nop;g | f;g | f;g |
| fst | load | load | load | load |
| snd | load | load | load | load |
| pair | stack-only | stack-only | register | stack-only |
| inl | standard | standard | standard | standard |
| inr | standard | standard | standard | standard |
| case | **branchless** | stack-only | branching | branching |
| terminal | mov | mov | mov | mov |
| initial | trap | trap | trap | trap |
| curry | **defunc** | defunc | thunk+jump | defunc |
| apply | **branchless-defunc** | defunc-case | indirect-call | defunc-case |
| fold | nop | nop | nop | nop |
| unfold | nop | nop | nop | nop |
| arr | nop | nop | nop | nop |

### Profile Details

#### Crypto Profile (Constant-Time)

**Goal:** No timing side channels - execution time independent of secret data.

**Requirements:**
- No data-dependent branches
- No data-dependent memory access patterns
- Constant instruction count

**Implementation choices:**
- case: Branchless speculation (execute both, select with cmov/csel)
- apply: Defunctionalization + branchless case dispatch
- All memory accesses at fixed offsets

**Overhead:** ~2x for case (both branches), ~Nx for apply (N = number of curry'd functions)

**When to use:**
- Cryptographic key operations
- Password comparison
- Any code handling secrets

#### Verified Profile (Formally Proven)

**Goal:** Complete formal verification with minimal trusted computing base.

**Requirements:**
- All generators must be provable
- Prefer simpler proofs over performance
- Minimize postulates

**Implementation choices:**
- pair/case: Stack-only (no callee-saved register reasoning)
- curry/apply: Defunctionalization (no indirect jumps)
- compose: With explicit nop separator

**Overhead:** ~1.3x for pair/case (extra stack ops), apply depends on function count

**When to use:**
- Safety-critical systems (aerospace, medical, automotive)
- High-assurance software
- Formal certification requirements

#### Fast Profile (Maximum Performance)

**Goal:** Minimize cycle count, maximize throughput.

**Requirements:**
- Use all available registers
- Minimize memory traffic
- Accept complex proofs or postulates

**Implementation choices:**
- pair: Register-based (callee-saved x20/r14)
- case: Branching with computed labels
- apply: Indirect call (blr/call*/jalr)

**Overhead:** Baseline (1.0x)

**When to use:**
- Performance-critical inner loops
- General-purpose applications
- When verification is not required

#### Small Profile (Minimal Code Size)

**Goal:** Smallest generated code.

**Requirements:**
- Minimize instruction count
- Share code where possible
- Accept slower execution

**Implementation choices:**
- pair/case: Stack-only (smaller than register save/restore)
- curry/apply: Defunctionalization (smaller than thunk duplication)
- Prefer shorter instruction encodings

**Overhead:** Variable, often similar to Verified

**When to use:**
- Embedded systems
- ROM/flash constrained environments
- Bootloaders

### Selection Algorithm

```
select_profile(program):
  if program.handles_secrets:
    return Crypto
  elif program.requires_certification:
    return Verified
  elif program.memory_constrained:
    return Small
  else:
    return Fast
```

### Mixing Profiles

Profiles can be mixed within a program:

```
-- Use Crypto for key handling, Fast elsewhere
program = compose (encrypt_fast key) (derive_key_crypto password)
```

The compiler could annotate IR nodes with required profiles:

```agda
data IR : Type → Type → Profile → Set where
  id     : IR A A p
  crypto : IR A B Fast → IR A B Crypto  -- promote to constant-time
  ...
```

### Proof Strategy by Profile

| Profile | Proof Approach |
|---------|----------------|
| Crypto | Prove constant-time property separately, then correctness |
| Verified | Full correctness proof, stack-machine equivalence |
| Fast | Equivalence to Verified, or accept postulates |
| Small | Equivalence to Verified |

---

## Summary: All Approaches for apply

| Approach | Proof Complexity | Performance | Separate Compilation | Status |
|----------|-----------------|-------------|---------------------|--------|
| Accept as axiomatic | N/A (postulated) | **Best** | Yes | Current |
| Defunctionalization | **Easy** | Good (case dispatch) | **No** | Promising |
| Whole-program compilation | Medium | Best | **No** | Promising |
| Interpreter/trampolining | Easy | **Poor** | Yes | Backup |
| Self-modifying code | Hard (memory-as-code) | Good | Yes | Complex |
| Stack machine | **Easiest** | Poor | Yes | Specification |

**Recommendation for apply:** Start with **defunctionalization** for programs where all curry'd functions are known at compile time. This gives easy proofs with good performance. Keep axiomatic apply as fallback for dynamic closures.

---

## Conclusion

This is a **research analysis** of the formal verification status across all three backends.

### Key Findings

1. **x86-64 is most complete** (14/15 proven), followed by RISC-V (11/15), then AArch64 (8/15)

2. **apply cannot be proven** with the current isolated-program model - but can be made provable via:
   - Defunctionalization (recommended for Verified/Crypto profiles)
   - Whole-program compilation
   - Memory-as-code model

3. **apply is the only non-cache-hot generator** - indirect jumps cause I-cache misses, making it both the hardest to prove AND the slowest

4. **Branchless execution** enables:
   - Constant-time code for cryptographic applications
   - Simpler proofs (no control flow reasoning)
   - Better performance on in-order CPUs and when branch prediction fails

5. **Multiple implementation profiles** allow optimizing for different goals:
   - **Crypto**: Constant-time, branchless, side-channel resistant
   - **Verified**: Fully proven, stack-only, defunctionalized
   - **Fast**: Maximum performance, may use postulates
   - **Small**: Minimal code size for embedded systems

6. **compose/pair/case difficulties** are technical (exec-concat) and can be addressed via:
   - Completing the pc-in-bounds lemmas
   - Using stack-only implementations
   - Using branchless implementations (for Crypto profile)

### Cycle Count Summary

| Profile | case | apply | Notes |
|---------|------|-------|-------|
| Fast | 8 + \|one branch\| | 25-40 | Branch misprediction risk |
| Crypto | 8 + \|both branches\| + 3 | 10 + \|all funcs\| + 3n | Constant-time |
| Verified | 10 + \|one branch\| | depends on defunc | Provable |

Simple generators (id, fst, snd, terminal, fold, unfold, arr): **0-4 cycles** across all profiles.

### Architecture Comparison for Proofs

| Architecture | Proof Friendliness | Performance | Best For |
|--------------|-------------------|-------------|----------|
| RISC-V | **Best** | Good | Verified profile, in-order CPUs |
| AArch64 | Good | **Best** | Fast profile, branchless (csel) |
| x86-64 | Medium | Good | Mature ecosystem, cmov support |

### Research Questions for Future Work

1. **Defunctionalization trade-off:** How much code size increase is acceptable for provability?
2. **Branchless threshold:** At what function size does branchless beat branching?
3. **Profile mixing:** How to efficiently mix Crypto and Fast within one program?
4. **Constant-time verification:** Can we prove the Crypto profile is actually constant-time?
5. **Stack machine performance:** What's the actual slowdown vs register machine?
6. **Cubical Agda:** Would function extensionality issues go away?

---

## Files Referenced

| File | Purpose |
|------|---------|
| `formal/Once/Backend/AArch64/Correct.agda` | AArch64 proofs (2,454 lines) |
| `formal/Once/Backend/X86/Correct.agda` | x86-64 proofs (7,612 lines) |
| `formal/Once/Backend/RiscV64/Correct.agda` | RISC-V proofs (2,072 lines) |
| `Strata/Generators/Generators.arm64` | AArch64 reference assembly |
| `Strata/Generators/Generators.x86_64` | x86-64 reference assembly |
| `Strata/Generators/Generators.riscv64` | RISC-V reference assembly |
| `docs/formal/lessons-learned.md` | Proof techniques documentation |
