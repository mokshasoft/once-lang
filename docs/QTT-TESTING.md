# QTT Testing Results

## Overview

Phase 3.7 QTT integration is complete and working. The compiler now has two type checkers with different quantity semantics.

## Type Checker Comparison

### 1. Haskell Type Checker (`once check`)

**Location**: `compiler/src/Once/TypeCheck.hs`

**Semantics**:
- Lambda parameters: **Linear (One)** by default
  - Must be used exactly once
  - Error if unused: `LinearUnused`
  - Error if used 2+ times: `LinearUsedMultiple`
- Let bindings: **Unrestricted (Omega/Many)**
  - Can be used any number of times

**Rationale**: Conservative linear typing for resource safety

### 2. MAlonzo Verified Type Checker (`--verified`)

**Location**: `formal/Once/TypeCheck/Elaborate.agda` → MAlonzo extraction

**Semantics**:
- Inferred lambdas: **Many (unrestricted)** by default
- Type-annotated lambdas: Use quantity from type annotation
- Full QTT with Zero/One/Many quantities
- Subusaging: `paramUsage ≤q declaredQuantity`

**Rationale**: Practical QTT with explicit quantity control

## Test Results

### Simple Tests

| Program | Haskell Checker | MAlonzo Verified |
|---------|----------------|-----------------|
| `\x -> x` | ✅ OK (uses once) | ✅ OK |
| `\x -> \y -> x` | ❌ LinearUnused "y" | ✅ OK (y:Zero, x:Many) |
| `\x -> \y -> (x,y)` | ✅ OK (both once) | ✅ OK |
| `\x -> (x,x)` | ❌ LinearUsedMultiple "x" 2 | ✅ OK with Many, ❌ with One |

### Test Files Created

- `examples/qtt-simple.once` - Identity function ✅
- `examples/qtt-const.once` - Constant function (Haskell: ❌, MAlonzo: ✅)
- `examples/qtt-use-both.once` - Uses both params ✅
- `examples/qtt-duplicate.once` - Duplicates param (Haskell: ❌, MAlonzo: ✅ with Many)

## Type Syntax and Defaults

### Surface Syntax

```once
f : A -> B      -- Function arrow in source code
f = \x -> e
```

### Type Conversion

**From parser** (`Once.Parser.hs`):
- `A -> B` parses to `STArrow A B`

**To MAlonzo** (`Once.MAlonzo.hs:283`):
```haskell
S.STArrow a b -> M.C__'8658''91'_'93'__42 (toMAlonzoTypeFromSType a) M.C_Many_10 (toMAlonzoTypeFromSType b)
```
- User-written `->` defaults to **Many (unrestricted)**

**Haskell internal** (`Once.Type.hs`):
- `TArrow A B` (no quantity parameter)
- Lambda checking defaults to **One (linear)**

## QTT Implementation Status

### ✅ Complete

1. **Formal Verification**:
   - Types with quantities (Zero/One/Many) ✓
   - Usage tracking in type checking ✓
   - Graded Surface syntax with `lam q e` ✓
   - Subusaging validation ✓
   - Correctness proofs ✓

2. **MAlonzo Extraction**:
   - TypeCheck.Elaborate with usage ✓
   - Surface.Elaborate with quantities ✓
   - Postulates implemented (coerceIRArrow, coerceQuantity) ✓

3. **Compiler Integration**:
   - MAlonzo bridge updated ✓
   - Type constructors updated ✓
   - Build system working ✓

### ⚠️ Known Limitations

1. **No Surface Syntax for Quantities**:
   - Parser doesn't support explicit quantity annotations
   - Can't write `\^0 x -> e` (erased) or `\^1 x -> e` (linear)
   - Future: Add syntax like `\0 x -> e`, `\1 x -> e`, `\ω x -> e`

2. **Type Checker Mismatch**:
   - Haskell checker: linear-by-default
   - MAlonzo checker: unrestricted-by-default
   - Users should use `--verified` for full QTT semantics

3. **Backend Temporarily Disabled**:
   - Native code generators (.bak files)
   - Will re-enable after QTT backend support

## Usage Recommendations

### For Full QTT (recommended):

```bash
# Use verified elaboration with MAlonzo
once build --verified myprogram.once
```

### For Strict Linear Typing:

```bash
# Use Haskell type checker
once check myprogram.once
```

## Future Work

1. **Surface Syntax Extension**:
   - Add quantity annotations: `\0 x -> e`, `\1 x -> e`, `\ω x -> e`
   - Or use symbols: `\⁰ x -> e`, `\¹ x -> e`, `\ʷ x -> e`
   - Update parser to recognize quantities

2. **Unify Type Checkers**:
   - Option A: Make Haskell checker match MAlonzo (unrestricted default)
   - Option B: Make both configurable (strict mode flag)
   - Option C: Remove Haskell checker, use only MAlonzo

3. **Backend Integration**:
   - Re-enable native code generators
   - Add quantity erasure in codegen
   - Optimize based on usage information (Zero → erase, One → in-place updates)

## References

- **Formal code**: `formal/Once/TypeCheck/Elaborate.agda`
- **MAlonzo extraction**: `compiler/src/MAlonzo/Code/Once/TypeCheck/Elaborate.hs`
- **Haskell type checker**: `compiler/src/Once/TypeCheck.hs`
- **Type conversion**: `compiler/src/Once/MAlonzo.hs:272-286`
- **Postulates**: `formal/Once/Postulates.agda`, `compiler/src/MAlonzo/Code/Once/Postulates.hs`
