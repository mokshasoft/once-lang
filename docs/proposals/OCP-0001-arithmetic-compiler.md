# OCP-0001: Orthogonal Arithmetic Compiler

**Author:** [TBD]
**Status:** Implemented
**Created:** 2025-12-25
**Accepted:** 2025-12-26
**Implemented:** 2025-12-27
**Decision:** D040

---

## Summary

Introduce a separate compilation path for arithmetic expressions that bypasses the categorical generator machinery. The IR would recognize arithmetic subexpressions and compile them directly to efficient register-based assembly, while control flow continues through generators.

---

## Implementation Status

### Completed ✓

| Component | Status | Location |
|-----------|--------|----------|
| ArithIR data type | ✓ | `compiler/src/Once/Arith/IR.hs` |
| NumType (I8-I64, F32, F64) | ✓ | `compiler/src/Once/Arith/IR.hs` |
| `Arith` constructor in IR | ✓ | `compiler/src/Once/IR.hs` |
| Sugar-level recognition | ✓ | `compiler/src/Once/Elaborate.hs` |
| Recognition from main IR | ✓ | `compiler/src/Once/Arith/Recognize.hs` |
| C backend (`--arith`) | ✓ | `compiler/src/Once/Arith/CodeGen/C.hs` |
| x86-64 native backend | ✓ | `compiler/src/Once/Arith/Backend/X86/` |
| AArch64 native backend | ✓ | `compiler/src/Once/Arith/Backend/AArch64/` |
| RISC-V native backend | ✓ | `compiler/src/Once/Arith/Backend/RiscV/` |
| Verified MAlonzo codegen | ✓ | `compiler/src/MAlonzo/Code/Once/Backend/` |
| Agda type proofs | ✓ | `formal/Once/Arith/Type.agda` |
| Agda semantics proofs | ✓ | `formal/Once/Arith/Semantics.agda` |
| Agda correctness proofs | ✓ | `formal/Once/Arith/Backend/X86/Correct.agda` |
| Boundary proofs | ✓ | `formal/Once/Arith/Boundary.agda` |
| Float type in proofs | ✓ | `formal/Once/Type.agda` |
| Test coverage | ✓ | `compiler/test/Arith/Spec.hs` (308 tests) |

### Known Limitations

- XMM/FP register spill not yet implemented (GPR spill works)

### Recent Updates (2025-12-28)

- Removed legacy `CmpIR` type in favor of unified `ACmp` in `ArithIR`
- Added native comparison codegen to all backends:
  - X86: `cmp`/`setcc`/`movzx` pattern
  - AArch64: `cmp`/`cset` pattern
  - RISC-V: `slt`/`slti` pattern
- Fixed float negation in X86 backend with proper sign mask XOR
- Added `movqToXMM` instruction for GPR to XMM constant loading

---

## Motivation

The 12 categorical generators handle control flow elegantly:
- `case` for branching
- `pair`/`fst`/`snd` for data flow
- `compose` for sequencing
- `curry`/`apply` for higher-order

But arithmetic like `2*2+3/4` has no inherent branching or products. Compiling through generators means:
- Unnecessary stack manipulation for intermediate values
- Can't use register allocation effectively
- Each primitive op becomes a function call or thunk

A dedicated arithmetic compiler could emit:
```asm
mov  eax, 2
imul eax, 2      ; 4
mov  ebx, 3
xor  edx, edx
mov  ecx, 4
div  ecx         ; 0 (integer)
add  eax, ebx    ; 4
```

Instead of threading through `compose`, `pair`, etc.

---

## Architecture

### Two Orthogonal Compilers

Arithmetic expressions are recognized at elaboration time and embedded directly
in the IR using the `Arith ArithIR` constructor:

```
Source → Parse → Elaborate → IR (with embedded ArithIR)
                                      ↓
                    ┌─────────────────┴─────────────────┐
                    ↓                                   ↓
            Arith nodes                          Other IR nodes
            (ArithIR tree)                       (12 generators)
                    ↓                                   ↓
            Direct C expr /                     Current codegen
            Register alloc                      (stack-based)
                    ↓                                   ↓
                    └─────────────────┬─────────────────┘
                                      ↓
                                  Assembly
```

The elaborator recognizes calls to arithmetic primitives like `add_i64 (x, y)`
and generates `Arith (AAdd ...)` instead of `Compose (Var "add_i64") (Pair ...)`.

### File Structure

```
compiler/src/Once/Arith/
├── IR.hs              # ArithIR data type, NumType
├── Recognize.hs       # Pattern matching: IR → Maybe ArithIR (fallback)
├── CodeGen/
│   └── C.hs           # ArithIR → C expressions
└── Backend/
    ├── X86/           # x86-64 native codegen
    │   ├── Syntax.hs
    │   ├── CodeGen.hs
    │   └── Emit.hs
    ├── AArch64/       # ARM64 native codegen
    │   ├── Syntax.hs
    │   ├── CodeGen.hs
    │   └── Emit.hs
    └── RiscV/         # RISC-V native codegen
        ├── Syntax.hs
        ├── CodeGen.hs
        └── Emit.hs

formal/Once/Arith/
├── Type.agda          # NumType definition
├── IR.agda            # ArithIR indexed by context and type
├── Semantics.agda     # Denotational semantics
├── Boundary.agda      # Natural transformation to main IR
└── Backend/X86/
    ├── Syntax.agda    # x86 instruction syntax
    ├── CodeGen.agda   # Verified code generation
    └── Correct.agda   # Correctness proofs
```

### Arithmetic IR

```haskell
data ArithIR
  = ALitInt NumType Integer
  | ALitFloat NumType Double
  | AVar Text NumType
  | AAdd ArithIR ArithIR
  | ASub ArithIR ArithIR
  | AMul ArithIR ArithIR
  | ADiv ArithIR ArithIR
  | AMod ArithIR ArithIR
  | ANeg ArithIR
  | ACmp CmpOp ArithIR ArithIR

data NumType = I8 | I16 | I32 | I64 | F32 | F64
```

### Recognition

The `recognizeArith` function pattern-matches on categorical IR:

```haskell
-- Identity on numeric type → input variable
Id TInt → AVar "_input" I64

-- Literal primitive → literal
Prim "__int_42" _ TInt → ALitInt I64 42

-- Binary op: op ∘ ⟨left, right⟩
Compose (Prim "__add_i64" (TProduct TInt TInt) TInt) (Pair left right)
  → AAdd (recognize left) (recognize right)

-- Unary op: op ∘ expr
Compose (Prim "__neg_i64" TInt TInt) expr
  → ANeg (recognize expr)

-- Projections
Fst TInt _ → AVar "_input.fst" I64
Snd _ TInt → AVar "_input.snd" I64
```

### Primitives

82 primitives across 6 numeric types:

| Operation | Integer Types | Float Types |
|-----------|--------------|-------------|
| Add | `__add_{i8,i16,i32,i64}` | `__add_{f32,f64}` |
| Sub | `__sub_{i8,i16,i32,i64}` | `__sub_{f32,f64}` |
| Mul | `__mul_{i8,i16,i32,i64}` | `__mul_{f32,f64}` |
| Div | `__div_{i8,i16,i32,i64}` | `__div_{f32,f64}` |
| Mod | `__mod_{i8,i16,i32,i64}` | — |
| Neg | `__neg_{i8,i16,i32,i64}` | `__neg_{f32,f64}` |
| Lt | `__lt_{i8,i16,i32,i64}` | `__lt_{f32,f64}` |
| Le | `__le_{i8,i16,i32,i64}` | `__le_{f32,f64}` |
| Gt | `__gt_{i8,i16,i32,i64}` | `__gt_{f32,f64}` |
| Ge | `__ge_{i8,i16,i32,i64}` | `__ge_{f32,f64}` |
| Eq | `__eq_{i8,i16,i32,i64}` | `__eq_{f32,f64}` |
| Ne | `__ne_{i8,i16,i32,i64}` | `__ne_{f32,f64}` |

---

## Usage

### C Backend with Arithmetic Inlining

```bash
once build --arith --exe program.once -o output
```

The `--arith` flag inlines arithmetic primitives as C expressions instead of function calls.

### Verified Native Backends

Pure categorical IR (no primitives) can be compiled to verified native assembly:

```haskell
import Once.Backend.Native (compileToX86, compileToAArch64, compileToRiscV64)

-- Returns Just assembly if IR is pure categorical
compileToX86 :: IR -> Maybe Text
```

---

## Formal Verification

### Proof Structure

1. **Type preservation**: ArithIR is well-typed
2. **Semantic correctness**: `eval ∘ compile = eval-arith`
3. **Boundary preservation**: `eval ∘ embed = numToSem ∘ eval-arith`

### Key Theorems (Agda)

```agda
-- Literal correctness
lit-int-correct : ∀ n → final-rax (run (compile-arith (Lit n))) ≡ n

-- Semantic preservation at boundary
embed-preserves-semantics :
  ∀ e env → eval (embedArith e) (envToSem env) ≡ numToSem τ (eval-arith e env)
```

---

## Impact

### Performance

| Aspect | Impact |
|--------|--------|
| Arithmetic-heavy code | Significant speedup (fewer stack ops, register allocation) |
| Control-flow-heavy code | Unchanged |
| Compile time | Slight increase (two passes) |

### Expressivity

| | Before | After |
|---|--------|-------|
| **Least** | Same | Same (syntax unchanged) |
| **Most** | Same | Same (no new constructs) |

This is purely an optimization - no surface syntax changes.

---

## Open Questions (Resolved)

1. **Where exactly is the boundary?** `if (x > 0) then ...` - is `x > 0` arithmetic or control flow?
   - **Answer:** Comparisons are arithmetic, returning Bool. The `if` is control flow that uses the Bool result.

2. **How do floating point operations fit?**
   - **Answer:** F32/F64 are first-class NumTypes with full support.

3. **Should the arithmetic IR support SIMD?**
   - **Deferred:** Not in initial implementation.

4. **How does this interact with QTT linearity tracking?**
   - **Answer:** Linearity is tracked during recognition; ArithIR uses simple free variables.

---

## Discussion

Implementation completed 2025-12-27 with:
- Full recognition from categorical IR
- C backend with `--arith` flag
- Three verified native backends (x86-64, AArch64, RISC-V)
- Agda proofs for types, semantics, and correctness
- 308 tests passing
