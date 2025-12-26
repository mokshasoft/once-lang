# OCP-0001: Orthogonal Arithmetic Compiler

**Author:** [TBD]
**Status:** Accepted
**Created:** 2025-12-25
**Accepted:** 2025-12-26
**Decision:** D040

---

## Summary

Introduce a separate compilation path for arithmetic expressions that bypasses the categorical generator machinery. The IR would recognize arithmetic subexpressions and compile them directly to efficient register-based assembly, while control flow continues through generators.

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

## Proposal

### Two Orthogonal Compilers

```
Source → Parse → Elaborate → IR
                              ↓
                    ┌─────────┴─────────┐
                    ↓                   ↓
            Arithmetic IR         Control Flow IR
            (expressions)         (generators)
                    ↓                   ↓
            Register alloc        Current codegen
                    ↓                   ↓
                    └─────────┬─────────┘
                              ↓
                          Assembly
```

### Arithmetic IR

A simple expression language:
```
data ArithIR
  = Lit Int
  | Var Name
  | Add ArithIR ArithIR
  | Sub ArithIR ArithIR
  | Mul ArithIR ArithIR
  | Div ArithIR ArithIR
  | Mod ArithIR ArithIR
  | Neg ArithIR
  | ...
```

### Recognition

The elaborator or a post-pass identifies "arithmetic regions" - subexpressions that:
1. Involve only numeric types
2. Use only arithmetic primitives
3. Have no internal branching (no `case`)
4. Have no effects

These regions get compiled by the arithmetic compiler; their result feeds back into the generator-based control flow.

### Interface

At the boundary:
- Control flow passes inputs via registers/stack (as now)
- Arithmetic compiler receives values, computes, returns result
- Control flow continues with the result

```
-- Generator IR calls into arithmetic
compose (arith "x*2 + y") (pair (prim "getX") (prim "getY"))
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

### Formal Verification

Two separate correctness proofs:
1. **Arithmetic compiler**: Standard expression compilation (well-understood)
2. **Generator compiler**: Existing proofs unchanged
3. **Interface**: Prove composition preserves semantics

The arithmetic compiler is simpler to verify than the full generator machinery (no closures, no branching).

---

## Trade-offs

**Gained:**
- Faster arithmetic-heavy code
- Opportunity for register allocation within expressions
- Cleaner separation of concerns
- Arithmetic proofs are simpler

**Lost:**
- Two compilers to maintain
- Boundary between them adds complexity
- Must decide what counts as "arithmetic"

---

## Alternatives

### A: Optimize within generators
Keep single compiler but add peephole optimizations to recognize arithmetic patterns.

**Rejected because:** Doesn't address fundamental issue of stack-based evaluation for expressions.

### B: Hybrid IR
Single IR with both generator and arithmetic nodes.

**Considered:** This might be the right implementation, but conceptually they remain orthogonal.

### C: Full expression language
Replace generators with traditional expression-based IR.

**Rejected because:** Loses categorical foundation and verification benefits.

---

## Open Questions

- Where exactly is the boundary? `if (x > 0) then ...` - is `x > 0` arithmetic or control flow?
- How do floating point operations fit?
- Should the arithmetic IR support SIMD?
- How does this interact with QTT linearity tracking?

---

## Discussion

[To be filled during review]
