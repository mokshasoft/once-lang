# Allocation Strategies and Escape Analysis

This document explains Once's current memory allocation strategy, why heap allocation is used, and how to implement stack allocation with escape analysis while maintaining formal verification.

## Table of Contents

1. [Current Architecture](#current-architecture)
2. [Why Heap Allocation?](#why-heap-allocation)
3. [The Abstraction Gap](#the-abstraction-gap)
4. [Stack vs Heap Tradeoffs](#stack-vs-heap-tradeoffs)
5. [Escape Analysis Levels](#escape-analysis-levels)
6. [Implementation Roadmap](#implementation-roadmap)
7. [Verification Implications](#verification-implications)

## Current Architecture

### Memory Representation in Once

Once uses a **uniform 64-bit Word representation** for all values:

```agda
-- From Once/Semantics.agda

-- Simple types have concrete encodings
encode : ∀ {A} → ⟦ A ⟧ → Word
encode {Unit} tt = 0                           -- Concrete value
encode {Fix F} (wrap x) = encode {F} x         -- Identity (concrete)

-- Compound types return ALLOCATION ADDRESSES
encode {A * B} (a , b) = encode-pair-addr a b      -- Heap address
encode {A + B} (inj₁ a) = encode-inl-addr a        -- Heap address
encode {A ⇒[ q ] B} cl = encode-closure-addr cl    -- Heap address
```

### Why Addresses for Compound Types?

**The fundamental constraint:** x86-64 registers are 64 bits, but compound values don't fit:

```
┌─────────────────────────────────────┐
│ Unit value: fits in 64 bits ✓      │
│   encode tt = 0x0000000000000000    │
└─────────────────────────────────────┘

┌─────────────────────────────────────┐
│ Pair (x, y): needs 128 bits ✗       │
│   Component x: 64 bits              │
│   Component y: 64 bits              │
│   Total: doesn't fit in register!   │
└─────────────────────────────────────┘

Solution: Return ADDRESS of pair in memory
```

## Why Heap Allocation?

### Current Status: ALL Compound Values → Heap

The current code generator allocates all pairs, sums, and closures on the heap via allocation primitives:

```agda
postulate
  encode-pair-addr : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → Word
  encode-inl-addr  : ∀ {A B} → ⟦ A ⟧ → Word
  encode-inr-addr  : ∀ {A B} → ⟦ B ⟧ → Word
  encode-closure-addr : ∀ {A B} → Closure A B → Word
```

### Why Not Stack by Default?

**The Escaping Problem:**

```ocaml
-- SAFE for stack allocation:
let f x y =
  let p = (x, y) in   -- p only used locally
  fst p               -- Returns x, not p itself

-- UNSAFE for stack allocation:
let f x = λy. (x, y)  -- Closure outlives f's stack frame!
```

If we stack-allocate the closure in the second example, it gets **clobbered** when `f` returns and its stack frame is reused.

### Design Choice: Uniform Heap Allocation

Once currently uses heap allocation for ALL compound values because:

1. **Correctness:** Always safe, no escape analysis needed
2. **Simplicity:** Uniform representation, no special cases
3. **GC-friendly:** Uniform layout enables precise garbage collection
4. **Verification:** Simpler to verify (no stack/heap distinction)

## The Abstraction Gap

### Semantic Level (IR)

At the IR level, values are **abstract mathematical objects**:

```agda
-- Pair is a mathematical product
⟦ A * B ⟧ = ⟦ A ⟧ × ⟦ B ⟧

-- Evaluation produces semantic values
eval (Pair f g) x = (eval f x , eval g x)
```

### Machine Level (x86-64)

At the machine level, values are **bits in registers and memory**:

```assembly
; Pair compilation (current implementation)
call compile_f        ; Result in rax
push rax              ; Save first component
call compile_g        ; Result in rax
pop rbx               ; Retrieve first component
call allocate_pair    ; Allocate heap memory
mov [rax], rbx        ; Write first component
mov [rax+8], rax      ; Write second component
; rax now contains ADDRESS of pair
```

### The Bridge: encode Function

The `encode` function bridges semantic and machine representations:

```
Semantic World          encode          Machine World
┌──────────────┐       ─────────>      ┌──────────────┐
│ (x, y) : A×B │                        │ 0x7fff1000   │
│   x : A      │                        │   (address)  │
│   y : B      │                        └──────────────┘
└──────────────┘                               │
                                               v
                                        ┌──────────────┐
                                        │ [0x7fff1000] │
                                        │  = encode x  │
                                        │ [0x7fff1008] │
                                        │  = encode y  │
                                        └──────────────┘
```

## Stack vs Heap Tradeoffs

### Heap Allocation (Current)

**Advantages:**
- Always correct (no escape issues)
- Uniform representation
- Simple to verify
- GC-friendly

**Disadvantages:**
- Allocation overhead (even with GC bump-pointer)
- Cache pressure (heap is cold)
- GC pause time increases

### Stack Allocation (Future)

**Advantages:**
- **70-90% fewer allocations** (empirical data from Java, Go, MLton)
- **Near-zero allocation cost** (just adjust `rsp`)
- **Better cache locality** (stack is hot)
- **Deterministic lifetime** (freed on return)

**Disadvantages:**
- Requires escape analysis
- Dual representations (stack vs heap)
- More complex verification
- Must prove analysis is sound

## Escape Analysis Levels

### Level 0: All Heap (Current)

```
Allocation Strategy:
  ALL compound values → heap

Verification Complexity: Low
Performance: Baseline
Implementation: Complete ✓
```

### Level 1: Simple Escape Analysis (Recommended)

**Conservative analysis with high impact:**

```haskell
-- Escape analysis rules (conservative):
escapes : IR A B → Bool
escapes (Pair f g) =
  if usedInReturn then Heap else Stack

escapes (Closure ...) =
  Heap  -- Closures always escape (conservative)

escapes (Apply f x) =
  -- Returned value from apply escapes
  Heap
```

**Expected impact:** 70-80% of allocations → stack

**Implementation effort:** Moderate

**Verification effort:** Moderate (prove soundness of analysis)

### Level 2: Region Inference

**Sophisticated analysis using region types:**

```
Allocation Strategy:
  - Infer region lifetimes
  - Stack regions for local scopes
  - Heap regions for long-lived data
  - Region polymorphism for libraries

Verification Complexity: High
Performance: 90-95% stack-allocated
Implementation: Significant
```

### Level 3: Manual Annotations

**User-specified allocation via surface syntax:**

```ocaml
-- Hypothetical surface syntax
let f x y =
  let p = @stack (x, y) in  -- Explicit stack allocation
  fst p

let g x =
  let c = @heap λy. (x, y) in  -- Explicit heap allocation
  c
```

**Verification requirement:** Prove annotations are safe (no stack-allocated values escape)

## Implementation Roadmap

### Phase 1: Extend IR with Allocation Mode

Add allocation annotations to IR types:

```agda
-- Once/IR.agda

data AllocMode : Set where
  Stack : AllocMode  -- Safe to allocate on stack
  Heap  : AllocMode  -- Must allocate on heap

-- Add allocation mode to constructors
data IR (A B : Type) : Set where
  -- Existing constructors...
  Pair : ∀ {X Y Z} →
    IR X Y → IR X Z → AllocMode → IR X (Y * Z)
  Inl  : ∀ {Y Z} → AllocMode → IR Y (Y + Z)
  Inr  : ∀ {Y Z} → AllocMode → IR Z (Y + Z)
```

**Initially:** Set all modes to `Heap` (no behavior change)

### Phase 2: Extend Code Generator

Add stack allocation support:

```agda
-- Once/Backend/X86/CodeGen.agda

compile-pair : ∀ {A B C} → IR A B → IR A C → AllocMode → List Instruction
compile-pair f g Stack =
  compile f ++                   -- Result in rax
  [ push rax ] ++                -- Save on stack
  compile g ++                   -- Result in rax
  [ pop rbx ] ++                 -- Retrieve first component
  [ sub rsp (imm 16) ] ++        -- Allocate 16 bytes on stack
  [ mov [rsp] rbx ] ++           -- Write first component
  [ mov [rsp + 8] rax ] ++       -- Write second component
  [ mov rax rsp ]                -- Return stack address

compile-pair f g Heap =
  -- Original heap allocation code
  compile f ++
  compile g ++
  [ call allocate-pair ] ++
  [ mov [rax] rbx ] ++
  [ mov [rax + 8] rcx ]
```

### Phase 3: Extend Verification

Prove correctness for both allocation strategies:

```agda
-- Once/Backend/X86/Correct/IR/Pair.agda

-- Stack-allocated pairs have deterministic addresses
encode-stack-pair : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → Word → Word
encode-stack-pair a b stack-addr = stack-addr

-- Heap-allocated pairs use abstract allocation
encode-heap-pair : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → Word
encode-heap-pair = encode-pair-addr

-- Correctness depends on allocation mode
pair-correct : ∀ {A B C} (f : IR A B) (g : IR A C) (mode : AllocMode) →
  IRStarResultS (Pair f g mode) prog s s' addr-out offset →
  encode x ≡ addr-in →
  (mode ≡ Stack →
    -- Stack case: deterministic address
    addr-out ≡ readReg (regs s') rsp ∧
    readMem (memory s') addr-out ≡ encode (fst (eval f x , eval g x)) ∧
    readMem (memory s') (addr-out + 8) ≡ encode (snd (eval f x , eval g x))) ∧
  (mode ≡ Heap →
    -- Heap case: abstract allocation address
    addr-out ≡ encode-pair-addr (eval f x) (eval g x))
```

### Phase 4: Implement Escape Analysis

Conservative analysis in compiler implementation:

```haskell
-- compiler/src/Once/Compiler/EscapeAnalysis.hs

data EscapeInfo = Escapes | Local

analyzeIR :: IR a b -> IR a b  -- Annotate with allocation modes
analyzeIR ir = runEscapeAnalysis (buildEscapeGraph ir)

-- Conservative rules:
--  1. Returned directly from function → Escapes → Heap
--  2. Stored in closure → Escapes → Heap
--  3. Only used locally → Local → Stack
--  4. If uncertain → Escapes → Heap (always safe)
```

### Phase 5: Prove Analysis Soundness

Formalize escape analysis and prove soundness:

```agda
-- Formalize "value escapes" predicate
data ValueEscapes {A B} (ir : IR A B) : Set where
  returns-value : returnsValue ir → ValueEscapes ir
  stored-closure : storedInClosure ir → ValueEscapes ir

-- Soundness theorem
escape-analysis-sound : ∀ {A B} (ir : IR A B) →
  allocMode ir ≡ Stack →
  ¬ (ValueEscapes ir)
```

**This is the hardest part** but can be done incrementally by expanding the set of cases proven safe for stack allocation.

## Verification Implications

### Stack Allocation is EASIER to Verify

Surprisingly, stack allocation is **simpler** to verify than heap allocation:

**Why?**

1. **Deterministic addresses:** Stack addresses are concrete (`rsp - 16`), not abstract postulates
2. **Bounded lifetime:** Stack frames have clear entry/exit points
3. **No aliasing:** Stack slots don't alias with each other or heap
4. **Simpler invariants:** Just maintain `rsp ≤ rbp` (already proven!)

**Example:**

```agda
-- Stack allocation: concrete address
pair-addr-stack : Word
pair-addr-stack = readReg (regs s) rsp ∸ 16  -- Deterministic!

-- Heap allocation: abstract address
postulate
  pair-addr-heap : Word  -- Abstract, requires postulate
```

### The Challenge: Proving Escape Analysis is Sound

The **hard part** is proving that the escape analysis correctly identifies which values can be safely stack-allocated:

```agda
-- Must prove: stack-allocated values don't escape
∀ (ir : IR A B) → allocMode ir ≡ Stack →
  lifespan ir ⊆ stackFrame
```

**Approach:** Start conservative, gradually expand:

1. **Phase 1:** Only stack-allocate obviously local values (high confidence)
2. **Phase 2:** Prove these cases sound in Agda
3. **Phase 3:** Expand to more cases as confidence grows
4. **Phase 4:** Eventually reach 70-80% stack allocation

## Expected Performance Gains

### Empirical Data from Other Languages

**Java Escape Analysis:**
- 85% of allocations identified as non-escaping
- 2-5x speedup in allocation-heavy benchmarks

**Go Escape Analysis:**
- 70-80% of allocations stack-allocated
- Reduced GC pause times by 40-60%

**MLton Whole-Program Compiler:**
- >90% of allocations stack or region-allocated
- Competitive with C in allocation-heavy code

### Expected Impact for Once

**Level 1 Escape Analysis (Conservative):**
- 70-80% fewer heap allocations
- 2-5x speedup in allocation-heavy code
- Better cache locality
- Lower GC pressure

**This is a HUGE win** for relatively modest implementation and verification effort.

## Relationship to Haskell Implementation

### Critical Understanding: Haskell is Just the Meta-Language

```
┌─────────────────────────────────────────┐
│ Once source code (user writes this)    │
└─────────────────┬───────────────────────┘
                  │
                  v
┌─────────────────────────────────────────┐
│ Once Compiler (implemented in Haskell)  │ ← Haskell GC only affects
│  - Parser                               │   COMPILATION time,
│  - Elaborator                           │   NOT generated code!
│  - Code generator                       │
│  - Escape analysis                      │
└─────────────────┬───────────────────────┘
                  │
                  v
┌─────────────────────────────────────────┐
│ Generated x86-64 assembly               │ ← THIS is what we verify
│  - Native code                          │   in Agda!
│  - No Haskell runtime                   │
│  - Allocation strategy is OUR choice    │
└─────────────────────────────────────────┘
```

**Key point:** Haskell's GC has **ZERO** impact on Once's generated code. The allocation strategy (heap vs stack) is entirely controlled by the code generator specification that we verify in Agda.

## Relationship to GC vs malloc

### Current Abstraction: Allocation Primitives

The current Agda verification uses **abstract allocation primitives**:

```agda
postulate
  encode-pair-addr : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → Word
```

This doesn't specify **how** allocation happens, only **that** it returns an address.

### Possible Implementation Strategies

The actual implementation could use:

1. **GC with bump-pointer allocation** (fast, simple):
   ```c
   void* allocate(size_t bytes) {
     void* result = heap_pointer;
     heap_pointer += bytes;
     return result;  // No malloc call!
   }
   ```

2. **Manual malloc/free**:
   ```c
   void* allocate(size_t bytes) {
     return malloc(bytes);  // Slow, but no GC needed
   }
   ```

3. **Region-based allocation**:
   ```c
   void* allocate_in_region(Region* r, size_t bytes) {
     void* result = r->current;
     r->current += bytes;
     return result;
   }
   ```

**The verification doesn't care which!** It proves correctness assuming allocation returns a valid, fresh address.

### GC Bump-Pointer is MUCH Faster than malloc

If you use a proper GC with bump-pointer allocation:

```
Allocation cost:
  malloc():           ~50-100ns (system call, free list traversal)
  GC bump-pointer:    ~1-2ns   (just increment a pointer!)
  Stack allocation:   ~0.5-1ns (just adjust rsp)
```

GC bump-pointer allocation is **50x faster** than malloc, nearly as fast as stack allocation!

## Conclusion

### Current Status

Once uses **uniform heap allocation** for all compound values. This is:
- ✓ Correct (always safe)
- ✓ Simple to verify
- ✓ GC-friendly
- ✗ Slower than necessary

### Recommended Next Steps

1. **Extend IR** with allocation mode annotations (set all to Heap initially)
2. **Extend code generator** to support stack allocation
3. **Extend verification** to prove both strategies correct
4. **Implement conservative escape analysis** in Haskell compiler
5. **Prove escape analysis sound** in Agda incrementally

### Expected Outcome

With Level 1 escape analysis:
- **70-80% fewer heap allocations**
- **2-5x speedup** in allocation-heavy code
- **Easier verification** (stack is deterministic!)
- **Maintained correctness** (escape analysis proven sound)

This is a **high-impact optimization** that actually makes verification simpler in many ways.

## References

### Relevant Files

- `Once/Semantics.agda` - Encoding function and semantic interpretation
- `Once/IR.agda` - IR definition (where to add AllocMode)
- `Once/Backend/X86/CodeGen.agda` - Code generator (where to add stack allocation)
- `Once/Backend/X86/Correct/IR/Pair.agda` - Pair correctness proofs
- `Once/Postulates.agda` - Current allocation postulates

### External References

- "Escape Analysis in the Context of Dynamic Compilation" (Choi et al.)
- "Region-Based Memory Management" (Tofte & Talpin)
- "MLton: An Optimizing Compiler for Standard ML" (Weeks)
- "A Principled Approach to Memory Safety in Imperative Languages" (Morrisett et al.)
