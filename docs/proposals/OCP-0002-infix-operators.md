# OCP-0002: Infix Arithmetic Operators

**Author:** [TBD]
**Status:** Implemented
**Created:** 2025-12-28
**Implemented:** 2025-12-28

---

## Summary

Add infix operator syntax for arithmetic expressions as syntactic sugar, with automatic type promotion within the same numeric domain.

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

| Operator | Meaning | Precedence | Associativity |
|----------|---------|------------|---------------|
| `*` | Multiplication | 7 (highest) | Left |
| `/` | Division | 7 | Left |
| `%` | Modulo | 7 | Left |
| `+` | Addition | 6 | Left |
| `-` | Subtraction | 6 | Left |
| `<` | Less than | 4 (lowest) | Non-associative |
| `<=` | Less or equal | 4 | Non-associative |
| `>` | Greater than | 4 | Non-associative |
| `>=` | Greater or equal | 4 | Non-associative |
| `==` | Equal | 4 | Non-associative |
| `!=` | Not equal | 4 | Non-associative |

Unary `-` (negation) has higher precedence than all binary operators.

### Examples

```once
-- Precedence: mul binds tighter than add
2 + 3 * 4        -- = 14 (not 20)

-- Left associativity
1 + 2 + 3        -- = (1 + 2) + 3

-- Parentheses override
(2 + 3) * 4      -- = 20

-- Unary negation
-x               -- negation of x
-5               -- negative literal

-- Comparisons
x < 10           -- less than
a >= b           -- greater or equal
x == y           -- equality
```

### Type Promotion

When operands have different numeric types within the same domain, the smaller type is implicitly widened to the larger:

```once
-- int8 + int16 -> int16
-- int32 + int64 -> int64
-- float32 + float64 -> float64
```

**Domain separation:** Mixing integers and floats is a type error:

```once
x_int + y_float  -- Error: Cannot mix integer and float types
```

This prevents subtle precision loss from implicit conversions.

---

## Implementation

### AST Changes (`Once/Syntax.hs`)

```haskell
-- Binary operators
data BinOp
  = OpAdd | OpSub | OpMul | OpDiv | OpMod
  | OpLt | OpLe | OpGt | OpGe | OpEq | OpNe
  deriving (Eq, Show)

-- Unary operators
data UnaryOp = OpNeg
  deriving (Eq, Show)

-- Added to Expr
| EBinOp BinOp Expr Expr
| EUnaryOp UnaryOp Expr
```

### Parser (`Once/Parser.hs`)

Precedence-climbing parser with layers:
1. `compareExpr` - non-associative comparisons
2. `addExpr` - left-associative `+` and `-`
3. `mulExpr` - left-associative `*`, `/`, `%`
4. `unaryExpr` - unary `-`

### Elaboration (`Once/Elaborate.hs`)

1. Convert operands to `ArithIR`
2. Determine promoted type via `promoteNumTypes`
3. Insert `AConv` nodes for type widening
4. Build appropriate `ArithIR` node

### ArithIR (`Once/Arith/IR.hs`)

```haskell
| AConv NumType ArithIR  -- Type conversion/promotion
```

### Backend Support

**C Backend:** Emits explicit casts `(int64_t)x`

**X86 Backend:**
- Integer widening handled implicitly by 64-bit registers
- Float widening uses `cvtss2sd` instruction

---

## Integration with OCP-0001

Infix syntax elaborates directly to ArithIR:

```
Source: x + y
  ↓ Parser
AST: EBinOp OpAdd (EVar "x") (EVar "y")
  ↓ Elaborator
IR: Arith (AAdd (AVar "x" I64) (AVar "y" I64))
  ↓ Codegen
C: (x + y)
```

---

## Testing

16 new parser tests added in `compiler/test/ParserSpec.hs`:
- Basic operators (+, -, *, /, %)
- Precedence (mul binds tighter than add)
- Associativity (left-associative)
- Parentheses override
- Unary negation
- All comparison operators

---

## Files Modified

| File | Changes |
|------|---------|
| `compiler/src/Once/Syntax.hs` | Added `BinOp`, `UnaryOp`, `EBinOp`, `EUnaryOp` |
| `compiler/src/Once/Parser.hs` | Precedence-climbing parser |
| `compiler/src/Once/Elaborate.hs` | `EBinOp`/`EUnaryOp` handling, type promotion |
| `compiler/src/Once/Arith/IR.hs` | Added `AConv` constructor |
| `compiler/src/Once/Arith/CodeGen/C.hs` | `AConv` emission |
| `compiler/src/Once/Arith/Backend/X86/CodeGen.hs` | `AConv` handling |
| `compiler/src/Once/Arith/Backend/X86/Syntax.hs` | Added `Cvtss2sd` |
| `compiler/src/Once/Arith/Backend/X86/Emit.hs` | `Cvtss2sd` emission |
| `compiler/test/ParserSpec.hs` | 16 new infix operator tests |

---

## References

- OCP-0001: Orthogonal Arithmetic Compiler
