# Inlining and Generator Fusion for CCC Native Code Generation

This document analyzes how inlining can work with Once's verified CCC (Cartesian Closed Category) generators, covering strategies for eliminating function call overhead while preserving correctness.

## 1. Introduction & Motivation

### Current State

When generating native code for primitives, the compiler currently emits function calls:

```asm
call once_add       # call interpretation function
```

Each call has overhead:
- `call` instruction: ~1-2 cycles (push return address, jump)
- `ret` instruction: ~1-2 cycles (pop return address, jump)
- **Total overhead: ~2-4 cycles per primitive**

### The Problem

For arithmetic-heavy code, this overhead dominates execution time:

```
add ∘ mul ∘ sub     # 3 primitives
```

Generates:
```asm
call once_sub       # ~4 cycles overhead
mov %rax, %rdi      # 1 cycle
call once_mul       # ~4 cycles overhead
mov %rax, %rdi      # 1 cycle
call once_add       # ~4 cycles overhead
# Total: ~14 cycles overhead + actual work (~3 cycles)
```

The overhead is **~5x the actual computation**.

### Goal

Inline primitives to eliminate call overhead on performance-critical paths while maintaining:
1. Correctness (via categorical laws)
2. Modularity (swappable interpretations where needed)
3. Reasonable code size

---

## 2. IR Tree Structure

Once's IR forms a tree structure based on Cartesian Closed Category morphisms.

### Node Types

**Leaf Nodes** (no IR children - terminals):
| Node | Type | Description |
|------|------|-------------|
| `Id` | `A → A` | Identity morphism |
| `Fst` | `A × B → A` | First projection |
| `Snd` | `A × B → B` | Second projection |
| `Inl` | `A → A + B` | Left injection |
| `Inr` | `B → A + B` | Right injection |
| `Terminal` | `A → Unit` | Terminal morphism |
| `Initial` | `Void → A` | Initial morphism |
| `Apply` | `(A ⇒ B) × A → B` | Function application |
| `Fold` | `F(Fix F) → Fix F` | Fold into fixed point |
| `Unfold` | `Fix F → F(Fix F)` | Unfold from fixed point |
| `Prim` | varies | Primitive operation |
| `Var` | varies | Variable/function reference |
| `StringLit` | `Unit → String` | String literal |

**Internal Nodes** (contain IR children - combinators):
| Node | Children | Description |
|------|----------|-------------|
| `Compose g f` | 2 | Sequential composition: `g ∘ f` |
| `Pair f g` | 2 | Pairing: `⟨f, g⟩` |
| `Case f g` | 2 | Case analysis: `[f, g]` |
| `Curry f` | 1 | Currying: `curry f` |
| `Let x e1 e2` | 2 | Let binding (surface syntax) |

### Tree Example

The expression `(a + b) * c` represented as IR:

```
        Compose
        /      \
      mul      Pair
              /    \
           add     snd
           /
         Pair
         /   \
       fst   fst∘snd
```

Where input is `((a, b), c)`.

---

## 3. Inlining Levels

### Level 0: No Inlining (Current)

Every primitive generates a function call:

```asm
call once_<primitive>
```

**Characteristics:**
- Maximum modularity - interpretations are swappable at link time
- Minimum code size
- Maximum overhead (~2-4 cycles per call)

**Use case:** Development, debugging, interpretation experimentation

### Level 1: Leaf Inlining

Inline individual primitives at their call sites:

```
Prim "add" ...  →  add %rsi, %rdi; mov %rdi, %rax
```

**Before (Level 0):**
```asm
call once_add
```

**After (Level 1):**
```asm
add %rsi, %rdi
mov %rdi, %rax
```

**Savings:** 1 `call` + 1 `ret` = ~4 cycles per primitive

**Requirements:**
- Primitive instruction sequences known at compile time
- Lookup table: primitive name → instruction sequence

**Characteristics:**
- Code size: +10-20%
- Performance: +20-50% (eliminates call overhead)
- Modularity: Medium (primitives fixed at compile time)

### Level 2: Block Fusion

Fuse consecutive primitives in composition chains, eliminating intermediate register transfers:

```
mul ∘ add  →  fused block (no intermediate mov)
```

**Before (Level 1):**
```asm
# add
add %rsi, %rdi
mov %rdi, %rax
# transfer
mov %rax, %rdi
# mul (with second operand already in %rsi)
imul %rsi, %rdi
mov %rdi, %rax
```

**After (Level 2):**
```asm
# fused add-mul
add %rsi, %rdi      # result in %rdi
imul %rcx, %rdi     # multiply by third operand
mov %rdi, %rax
```

**Savings:** Eliminates intermediate `mov` instructions between operations

**Requirements:**
- Register allocation across fused blocks
- Uses associativity: `(f ∘ g) ∘ h = f ∘ (g ∘ h)`

**Characteristics:**
- Code size: +30-50%
- Performance: +50-100%
- Modularity: Low

### Level 3: Subtree Inlining

Inline entire subtrees up to depth N:

```
(a + b) * (c - d)  →  one fused expression
```

**Before (Level 1):**
```asm
# Compute a + b
mov (%rdi), %rax
add 8(%rdi), %rax
push %rax
# Compute c - d
mov 16(%rdi), %rax
sub 24(%rdi), %rax
mov %rax, %rsi
pop %rdi
# Multiply
imul %rsi, %rdi
mov %rdi, %rax
```

**After (Level 3):**
```asm
# Fully fused
mov (%rdi), %r8
add 8(%rdi), %r8      # a + b in r8
mov 16(%rdi), %r9
sub 24(%rdi), %r9     # c - d in r9
imul %r9, %r8
mov %r8, %rax
```

**Characteristics:**
- Code size: +100%+
- Performance: +100-200%
- Modularity: None (fully specialized)

---

## 4. Generator Unrolling

Analogous to loop unrolling in traditional compilers.

### Composition Chain Unrolling

For a chain of N compositions:

```
f₁ ∘ f₂ ∘ f₃ ∘ ... ∘ fₙ
```

**Unroll factor k:** Inline k consecutive primitives as a block.

**Example (k=3):**
```
f₁ ∘ f₂ ∘ f₃ ∘ f₄ ∘ f₅
    └──────┘     └──────┘
     block1       block2 (f₄ ∘ f₅ + call f₁)
```

### Fold Unrolling

For recursive structures using `fold`:

```agda
fold f : F(Fix F) → Fix F
```

**Unroll N iterations:**
```
fold f (Cons x (Cons y (Cons z rest)))
  → f x (f y (f z (fold f rest)))
```

With inlining:
```asm
# Unrolled 3 iterations
<inline f for x>
<inline f for y>
<inline f for z>
call once_fold_rest    # Continue recursively
```

### Linear Fold Unrolling

For **linear types**, fold unrolling becomes particularly clean and efficient.

**Why linear types simplify fold unrolling:**

1. **No aliasing** - the structure is consumed exactly once, no reference counting during traversal
2. **Predictable memory layout** - linear cons cells can be laid out contiguously
3. **No sharing checks** - don't need to worry about multiple references to the tail
4. **Guaranteed termination** - linear consumption means finite traversal

**Example: Summing a linear list**

```once
sum : List! Int -> Int   -- List! is linear
sum = fold add 0
```

Each fold iteration applies the algebra `f : F(B) → B`, which is itself a CCC morphism. Unrolling N iterations is simply composing `f` with itself N times through the functor structure.

**Unrolled 4 iterations:**
```asm
# sum [a, b, c, d, ...rest]
# Linear layout: elements contiguous in memory
add (%rdi), %rax        # a
add 8(%rdi), %rax       # b
add 16(%rdi), %rax      # c
add 24(%rdi), %rax      # d
add $32, %rdi           # advance pointer
# check for end, loop or return
```

**Categorical foundation:**

The catamorphism fusion law enables pre-optimization:
```
fold f ∘ map g = fold (f ∘ g)
```

This allows fusing a map into the fold before unrolling, eliminating intermediate allocations entirely.

**Performance characteristics for linear folds:**

| Unroll Factor | Loop Overhead | Memory Access | Pipeline |
|---------------|---------------|---------------|----------|
| 1 | High (branch/iter) | Sequential | Poor |
| 4 | Low (branch/4 iter) | Sequential | Good |
| 8 | Minimal | Sequential | Excellent |

Linear types guarantee sequential memory access patterns, which modern CPUs handle extremely efficiently with prefetching.

### Unrolling Tradeoffs

| Unroll Factor | Code Size | Performance | Branch Prediction |
|---------------|-----------|-------------|-------------------|
| 1 (none) | Baseline | Baseline | Good |
| 2 | +50% | +30% | Good |
| 4 | +150% | +50% | Moderate |
| 8 | +400% | +60% | Poor |

Diminishing returns beyond k=4 for most workloads.

### Automatic Arithmetic Expression Inlining

A key insight: **arithmetic expressions can be fully inlined automatically** because they form a closed set of combinators.

**The Arithmetic Closure Property:**

If an IR subtree contains only these node types:
- `Compose` - sequential composition
- `Pair` - parallel computation
- `Fst`, `Snd` - projections (become addressing, no code)
- `Id` - identity (no code)
- Arithmetic `Prim` - `add`, `sub`, `mul`, `div`, `mod`

Then the **entire subtree can be inlined into a single basic block** with no function calls.

**Why this works:**

1. **Arithmetic primitives** have simple, known instruction sequences
2. **Projections** become register/memory selection—zero runtime cost
3. **Pair** becomes parallel register allocation—just bookkeeping
4. **Compose** becomes instruction concatenation
5. **No control flow** in pure arithmetic—no branches needed

**Simple Detection Heuristic:**

```haskell
canFullyInline :: IR -> Bool
canFullyInline (Compose g f)  = canFullyInline g && canFullyInline f
canFullyInline (Pair f g)     = canFullyInline f && canFullyInline g
canFullyInline Fst            = True
canFullyInline Snd            = True
canFullyInline Id             = True
canFullyInline (Prim name _)  = name `elem` ["add","sub","mul","div","mod"]
canFullyInline _              = False  -- Fold, Case, Apply, Var, etc.
```

**Example: Full arithmetic inlining**

Expression: `(a + b) * (c - d)`

IR tree:
```
mul ∘ ⟨add ∘ ⟨π₁, π₂⟩, sub ∘ ⟨π₃, π₄⟩⟩
```

All nodes pass `canFullyInline`, so emit a single fused block:

```asm
# Input: ((a,b),(c,d)) in memory at %rdi
mov (%rdi), %r8           # a
add 8(%rdi), %r8          # a + b
mov 16(%rdi), %r9         # c
sub 24(%rdi), %r9         # c - d
imul %r9, %r8             # (a+b) * (c-d)
mov %r8, %rax             # result
# Zero function calls. ~6 cycles total.
```

**Correctness guarantee:**

The inlined block implements the same CCC morphism as the original tree. The categorical laws don't constrain the assembly representation—only that it computes the same function. Since each primitive's semantics is preserved and composition is associative, the fused block is semantically equivalent.

**What breaks full inlining:**

| Node | Why it breaks inlining |
|------|------------------------|
| `Fold`/`Unfold` | Recursion requires loop or call |
| `Case` | Needs conditional branch (but still inlinable with branches) |
| `Apply` | Calls unknown function |
| `Var` | Calls user-defined function |
| Non-arithmetic `Prim` | May have complex semantics (syscalls, I/O) |

**Recommendation:** Implement `canFullyInline` check and automatically apply Level 3 inlining to all qualifying subtrees. This eliminates most arithmetic overhead with zero programmer annotation.

---

## 5. Categorical Foundation for Correctness

Inlining is semantics-preserving when it follows proven categorical laws.

### Relevant Laws (Proven in formal/Once/Category/Laws.agda)

**Identity Laws:**
```
id ∘ f = f
f ∘ id = f
```
Enables: Removing identity nodes during inlining.

**Associativity:**
```
(f ∘ g) ∘ h = f ∘ (g ∘ h)
```
Enables: Reordering composition for better fusion opportunities.

**Pairing Fusion:**
```
⟨f, g⟩ ∘ h = ⟨f ∘ h, g ∘ h⟩
```
Enables: Distributing computation into pair branches for independent optimization.

**Case Fusion:**
```
h ∘ [f, g] = [h ∘ f, h ∘ g]
```
Enables: Fusing through case analysis branches.

**Product Beta:**
```
fst ∘ ⟨f, g⟩ = f
snd ∘ ⟨f, g⟩ = g
```
Enables: Dead code elimination when only one branch is used.

### Natural Transformation Preservation

The mapping from IR to assembly is a functor:
- **Objects:** Types → machine representations
- **Morphisms:** IR expressions → instruction sequences

For inlining to be correct:
```
compile(f ∘ g) ≡ compile(f) ; transfer ; compile(g)
```

When we inline, we must preserve this equivalence:
```
compile_inlined(f ∘ g) ≡ compile(f ∘ g)  (semantically)
```

The categorical laws guarantee that reordering and fusion preserve semantics at the IR level. The code generator preserves semantics from IR to assembly (proven in formal/Once/Backend/*/Correct.agda).

---

## 6. Implementation Approaches

### Approach A: Compile-time Inlining (Pragmatic)

**Strategy:**
1. Parse interpretation assembly files (`.x86_64`, `.arm64`, `.riscv64`)
2. Build lookup table: `primitive name → instruction sequence`
3. During code generation, emit instructions directly instead of `call`

**Pros:**
- Works with existing interpretation files
- No changes to formal proofs
- Immediate performance benefit

**Cons:**
- Not formally verified
- Instruction sequences must be carefully extracted
- Register allocation becomes complex for Level 2+

**Implementation sketch:**
```haskell
data InlineInfo = InlineInfo
  { iiInstructions :: [Instruction]
  , iiClobbersRegs :: [Register]
  , iiInputReg     :: Register
  , iiOutputReg    :: Register
  }

inlinePrimitive :: Text -> Maybe InlineInfo
inlinePrimitive "add" = Just $ InlineInfo
  [ Add (Reg RSI) (Reg RDI)
  , Mov (Reg RDI) (Reg RAX)
  ]
  [RDI, RAX]
  RDI
  RAX
```

### Approach B: Verified Inlining (Principled)

**Strategy:**
1. Add primitive semantics to Agda model
2. Prove inlining transformations correct
3. Generate verified inlined code via MAlonzo

**Pros:**
- Formally verified end-to-end
- Guaranteed correct

**Cons:**
- Requires extending formal proofs significantly
- Each primitive needs semantics specification
- Longer development time

**Required additions to formal model:**
```agda
-- Primitive semantics
⟦_⟧prim : PrimName → ⟦ A ⟧ → ⟦ B ⟧

-- Inlining correctness
inline-correct : ∀ (p : Prim name A B) (x : ⟦ A ⟧)
               → run (compile-inline p) x ≡ run (compile p) x
```

### Approach C: Hybrid (Recommended)

**Strategy:**
1. Use verified categorical fusion (already exists in optimizer)
2. Add unverified primitive inlining with extensive testing
3. Gradually extend proofs for critical primitives (arithmetic)

**Implementation phases:**

**Phase 1:** Level 1 inlining for arithmetic primitives only
- `add`, `sub`, `mul`, `div`, `mod`
- Comprehensive test suite

**Phase 2:** Level 2 block fusion for arithmetic chains
- Extend register allocator
- Prove fusion correctness at IR level (use existing laws)

**Phase 3:** Verified arithmetic inlining
- Add arithmetic semantics to Agda
- Prove inline-correct for each arithmetic primitive

**Phase 4:** Extend to other primitives
- Comparisons, bitwise operations
- Syscall primitives (remain as calls - can't inline kernel transitions)

---

## 7. Hot Path Detection

### Pragma-based Annotation

```once
{-# INLINE depth=2 #-}
hotFunction : Int -> Int -> Int
hotFunction x y = (x + y) * (x - y)
```

**Pragma options:**
- `INLINE` - inline all primitives in this function
- `INLINE depth=N` - inline up to depth N
- `NOINLINE` - never inline (for debugging)
- `INLINE prim=add,mul` - inline only specified primitives

### Automatic Detection (Future)

Profile-guided optimization:
1. Compile with profiling
2. Run benchmarks
3. Identify hot functions by execution count
4. Recompile with targeted inlining

### Heuristics

**Always inline:**
- Arithmetic in tight loops
- Functions marked `{-# INLINE #-}`

**Never inline:**
- Syscalls (can't inline kernel transitions)
- Large primitives (e.g., string operations)
- Cold paths (error handling)

---

## 8. Code Size vs Performance Analysis

### Quantitative Tradeoffs

| Level | Code Size | Cycles Saved | Net Speedup |
|-------|-----------|--------------|-------------|
| 0 (baseline) | 1.0x | 0 | 1.0x |
| 1 (leaf) | 1.1-1.2x | ~4/call | 1.2-1.5x |
| 2 (fusion) | 1.3-1.5x | ~6/chain | 1.5-2.0x |
| 3 (subtree) | 2.0-3.0x | ~10/tree | 2.0-3.0x |

### When to Use Each Level

**Level 0:**
- Development/debugging
- Code size critical (embedded)
- Need to swap interpretations at runtime

**Level 1:**
- Production builds
- General-purpose optimization
- Good balance of size/speed

**Level 2:**
- Performance-critical inner loops
- Numeric computation
- Known hot paths

**Level 3:**
- Maximum performance required
- Specific hot functions only
- Benchmarking/profiling driven

---

## 9. Examples with Cycle Counts

### Example 1: Simple Arithmetic

**Once code:**
```once
f x y = x + y
```

**IR:**
```
add ∘ pair(fst, snd)
```

| Level | Assembly | Cycles |
|-------|----------|--------|
| 0 | `call once_add` | ~6 |
| 1 | `add %rsi, %rdi; mov %rdi, %rax` | ~2 |

**Speedup: 3x**

### Example 2: Compound Expression

**Once code:**
```once
f x y z = (x + y) * z
```

**IR:**
```
mul ∘ pair(add ∘ pair(fst, fst∘snd), snd∘snd)
```

| Level | Cycles (overhead) | Cycles (work) | Total |
|-------|-------------------|---------------|-------|
| 0 | ~12 | ~3 | ~15 |
| 1 | ~4 | ~3 | ~7 |
| 2 | ~2 | ~3 | ~5 |

**Speedup: 2-3x**

### Example 3: Numeric Loop (Conceptual)

**Once code:**
```once
sumList : List Int -> Int
sumList = fold add 0
```

With unrolling factor 4:

| Unroll | Iterations | Overhead/iter | Total for 100 items |
|--------|------------|---------------|---------------------|
| 1 | 100 | ~6 | ~600 |
| 4 | 25 | ~4 | ~100 |

**Speedup: 6x** (for overhead; actual computation unchanged)

---

## 10. Future Work

### Verified Primitive Inlining

Extend the Agda model:
1. Define primitive semantics for arithmetic
2. Prove inline transformations correct
3. Generate verified inline code via MAlonzo

### Catamorphism Fusion

Prove fusion laws for recursive structures:
```
fold f ∘ map g = fold (f ∘ g)
```

Enable aggressive optimization of recursive computations.

### Supercompilation

Apply partial evaluation and deforestation:
- Eliminate intermediate data structures
- Specialize polymorphic code
- Unroll bounded recursion completely

### SIMD Vectorization

For Level 3 inlining of numeric code:
- Detect parallel arithmetic patterns
- Generate SIMD instructions (SSE, AVX, NEON)
- Requires extending IR with vector types

### Profile-Guided Optimization

Implement feedback-directed inlining:
1. Instrument builds to collect execution profiles
2. Identify hot paths automatically
3. Apply targeted Level 2-3 inlining

---

## Summary

Inlining in Once's CCC-based code generation is both feasible and beneficial:

1. **Levels 0-3** provide a spectrum from maximum modularity to maximum performance
2. **Categorical laws** provide the foundation for correctness
3. **Hybrid approach** recommended: verified fusion + tested primitive inlining
4. **Expected speedups**: 2-6x for arithmetic-heavy code
5. **Future work**: verified primitives, catamorphism fusion, SIMD

The key insight is that the compositional structure of CCC generators naturally supports inlining - composition becomes concatenation, and fusion becomes instruction merging - all while preserving the semantic guarantees provided by the categorical laws.
