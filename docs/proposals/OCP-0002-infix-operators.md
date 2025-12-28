# OCP-0002: Infix Arithmetic Operators

**Author:** [TBD]
**Status:** Draft
**Created:** 2025-12-28

---

## Summary

Add infix operator syntax for arithmetic expressions as syntactic sugar.

---

## Motivation

Currently arithmetic must be written as explicit primitive calls:

```once
add_i64 (mul_i64 (x, x), mul_i64 (2, x))
```

With infix operators:

```once
x * x + 2 * x
```

This improves readability significantly for arithmetic-heavy code.

---

## Design

### Operators

| Operator | Desugars to | Precedence | Associativity |
|----------|-------------|------------|---------------|
| `+` | `add_i64` | 6 | Left |
| `-` | `sub_i64` | 6 | Left |
| `*` | `mul_i64` | 7 | Left |
| `/` | `div_i64` | 7 | Left |
| `%` | `mod_i64` | 7 | Left |
| `<` | `lt_i64` | 4 | None |
| `<=` | `le_i64` | 4 | None |
| `>` | `gt_i64` | 4 | None |
| `>=` | `ge_i64` | 4 | None |
| `==` | `eq_i64` | 4 | None |
| `!=` | `ne_i64` | 4 | None |

Unary `-` (negation) desugars to `neg_i64`.

### Type Suffixes (optional)

For non-default types, use suffix notation:

```once
x +f64 y      -- add_f64
a *i32 b      -- mul_i32
```

Or rely on type inference to select the right primitive.

### Implementation

Parser changes only:
1. Add operator tokens to lexer
2. Add precedence climbing or Pratt parsing for expressions
3. Desugar to `EApp (EVar "add_i64") (EPair a b)` in parser

The elaborator's existing arithmetic detection then generates `Arith` nodes.

---

## Integration with OCP-0001

This is pure syntax sugar. The desugared form feeds directly into the
arithmetic compiler pipeline from OCP-0001:

```
Source: x + y
  ↓ Parser (desugar)
Sugar: EApp (EVar "add_i64") (EPair (EVar "x") (EVar "y"))
  ↓ Elaborator (arithmetic detection)
IR: Arith (AAdd (AVar "x" I64) (AVar "y" I64))
  ↓ Codegen
C: (x + y)
```

---

## Open Questions

1. Should operators be overloaded by type, or require explicit suffixes?
2. Should we support user-defined operators?
3. Precedence of comparison operators vs logical operators (if added)?

---

## References

- OCP-0001: Orthogonal Arithmetic Compiler
