# Phase 3.7 Step 3: QTT Implementation TODOs

**Status**: In Progress
**Date**: 2025-12-31

## Summary

Step 3 extends the bidirectional type checker to compute and track **usage vectors** for QTT. The infrastructure is in place (result types extended), but actual usage computation needs to be implemented.

## Current State

✅ **Complete**:
- Extended `InferElabResult` to include `usage : Surface.Usage n`
- Extended `CheckElabResult` to include `usage : Surface.Usage n`
- Added usage helper imports (`zeroUsage`, `singleUse`, `_+ᵘ_`, `_*ᵘ_`)

🚧 **In Progress**:
- Threading usage through all type checking rules
- Currently using `zeroUsage` as placeholder (no actual tracking)

## Implementation Tasks

### 1. Update All Pattern Matches on Results

Every place that pattern matches on `success` needs to include the `usage` parameter:

**Before**:
```agda
... | success bodyExpr depth fresh' = ...
```

**After**:
```agda
... | success bodyExpr depth fresh' usage' = ...
```

**Files**: `formal/Once/TypeCheck/Elaborate.agda` (all mutual rules)

### 2. Update All Success Constructor Calls

Every place that constructs a `success` result needs to include usage:

**Before**:
```agda
success expr depth fresh
```

**After**:
```agda
success expr depth fresh usage
```

### 3. Implement QTT Usage Computation Rules

Replace `zeroUsage` placeholders with actual usage tracking:

#### Variable Reference
```agda
-- Current (placeholder):
inferElabImpl ctx (Raw.RVar x) = ... success A se 0 fresh' zeroUsage

-- Should be:
inferElabImpl ctx (Raw.RVar x) with lookupVar ctx x
... | just (A , se , fresh') =
    let i = varIndex x ctx
        q = lookupQuantity (NamedCtx.debruijn ctx) i
    in success A se 0 fresh' (singleUse i q)  -- Mark variable i used with quantity q
```

#### Lambda
```agda
-- Current:
checkElabImpl ctx (Raw.RLam x body) (A ⇒[ q ] B) with checkElabImpl (extendCtx ctx x A) body B
... | success bodyExpr depth fresh' usage' =
    success (Surface.lam bodyExpr) (suc depth) fresh' zeroUsage  -- TODO

-- Should be:
... | success bodyExpr depth fresh' usage' =
    let paramUsage = lookup usage' zero  -- How was parameter used?
    in if paramUsage ≤q q  -- Check usage respects declared quantity
       then success (Surface.lam bodyExpr) (suc depth) fresh' (tail usage')  -- Drop parameter from usage
       else failure ("Parameter used with quantity " ++ show paramUsage ++ " but declared " ++ show q)
```

#### Application
```agda
-- Should compute: usageFun +ᵘ usageArg
checkElabImpl ctx (Raw.RApp fun arg) with inferElabImpl ctx fun
... | success (A ⇒[ q ] B) funExpr funDepth funFresh usageFun =
    checkElabImpl ctx arg A with ...
    ... | success argExpr argDepth argFresh usageArg =
        success (Surface.app funExpr argExpr)
                (funDepth ⊔ argDepth)
                argFresh
                (usageFun +ᵘ usageArg)  -- Combine usage from both sides
```

#### Pair
```agda
-- Both components contribute to usage
inferElabImpl ctx (Raw.RPair e1 e2) with inferElabImpl ctx e1
... | success A1 expr1 d1 f1 usage1 with inferElabImpl ctx e2
... | success A2 expr2 d2 f2 usage2 =
    success (A1 * A2)
            (Surface.pair expr1 expr2)
            (d1 ⊔ d2)
            f2
            (usage1 +ᵘ usage2)  -- Add usage from both components
```

#### Case Expression
```agda
-- Both branches must have compatible usage
inferElabImpl ctx (Raw.RCase scrut leftBranch rightBranch) with inferElabImpl ctx scrut
... | success (A + B) scrutExpr dScr fScr usageScr with
        checkElabImpl (extendCtx ctx "x" A) leftBranch C,
        checkElabImpl (extendCtx ctx "y" B) rightBranch C
... | success leftExpr dL fL usageL, success rightExpr dR fR usageR =
    success C
            (Surface.case' scrutExpr leftExpr rightExpr)
            (dScr ⊔ dL ⊔ dR)
            fR
            (usageScr +ᵘ tail usageL +ᵘ tail usageR)  -- Combine all three usage vectors
```

### 4. Helper Functions Needed

```agda
-- Get variable index in context
varIndex : String → NamedCtx → Fin n

-- Lookup usage at specific index
lookup : Usage n → Fin n → Quantity

-- Drop first element (for removing bound variable usage)
tail : Usage (suc n) → Usage n

-- Check subusaging
_≤q?_ : Quantity → Quantity → Bool
```

### 5. Top-Level Entry Points

Update `checkElab` and `inferElab` to handle usage:

```agda
checkElab : (ctx : NamedCtx) → RawExpr → (A : Type) → CheckElabResult (NamedCtx.debruijn ctx) A
checkElab ctx expr ty with checkElabImpl ctx expr ty
... | failure err = failure err
... | success expr' depth fresh usage with depth ≤? 7
...   | yes _ with checkUsageValid ctx usage  -- NEW: verify usage is valid
...     | true  = success expr' depth fresh usage
...     | false = failure "Usage constraint violation"
...   | no _  = failure "Expression nesting depth exceeds verified limit"

-- Check all usage respects declared quantities in context
checkUsageValid : NamedCtx → Usage n → Bool
checkUsageValid ctx usage = usage ≤ᵘ NamedCtx.debruijn ctx
```

## Testing Strategy

1. **Start with simple cases**: Variable references, lambdas
2. **Add complex cases**: Applications, pairs, case expressions
3. **Test with examples**:
   ```once
   // Should infer: x used Once
   id : A -> A
   id = \x -> x

   // Should infer: x used Many times
   dup : A -> (A * A)
   dup = \x -> (x, x)

   // Should accept: usage matches declared quantity
   close : File^1 -> Unit
   close = \f -> closeImpl f  // f used exactly once

   // Should reject: usage violation
   bad : File^1 -> Unit
   bad = \f -> let _ = close f in close f  // ERROR: f used twice
   ```

## Dependencies

**Requires**:
- `Surface.Usage` operations (✅ already implemented in Step 2)
- `Quantity` algebra (`_+q_`, `_*q_`, `_≤q_`) (✅ already in `Once.Type`)

**Blocks**:
- Step 4 (Subusaging) - needs usage tracking working
- Step 6 (MAlonzo extraction) - needs all rules implemented

## Estimated Effort

- **Threading usage through rules**: 2-3 hours (mechanical)
- **Implementing actual QTT rules**: 4-6 hours (requires careful thought)
- **Testing and debugging**: 2-3 hours
- **Total**: ~8-12 hours

## Notes

- The infrastructure (extended result types) is done
- Current code uses `zeroUsage` placeholder to compile
- Need to systematically replace placeholders with actual usage computation
- Take incremental approach: one expression form at a time
