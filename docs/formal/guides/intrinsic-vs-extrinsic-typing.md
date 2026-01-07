# Intrinsic vs Extrinsic Typing for Soundness Proofs

## Overview

When formalizing a type system, there are two fundamental approaches:

1. **Extrinsic typing**: Expressions are untyped, and a separate typing relation proves they have types
2. **Intrinsic typing**: Types are part of the expression structure (GADT-style)

This guide explains why intrinsic typing makes soundness proofs trivial, and how the Once codebase uses both approaches.

## The Two Approaches

### Extrinsic Typing (Separate Relation)

```agda
-- Expressions are untyped
data RawExpr : Set where
  RVar : String → RawExpr
  RApp : RawExpr → RawExpr → RawExpr
  RLam : String → RawExpr → RawExpr
  -- etc.

-- Typing is a separate relation
data WellTyped : Ctx → RawExpr → Type → Set where
  T-Var : lookup x Γ ≡ A → WellTyped Γ (RVar x) A
  T-App : WellTyped Γ e₁ (A ⇒ B) → WellTyped Γ e₂ A → WellTyped Γ (RApp e₁ e₂) B
  T-Lam : WellTyped (Γ , x ∷ A) e B → WellTyped Γ (RLam x e) (A ⇒ B)

-- Type inference returns type + substitution
infer : Ctx → RawExpr → Fresh → InferResult

-- Soundness must be PROVEN
Soundness : infer Γ e f ≡ success A σ f' → WellTyped Γ e (applySubst σ A)
```

### Intrinsic Typing (Types in Structure)

```agda
-- Types are indices of the expression datatype
data Expr : ∀ {n} → Ctx n → Type → Set where
  var : (i : Fin n) → Expr Γ (lookup Γ i)
  app : Expr Γ (A ⇒ B) → Expr Γ A → Expr Γ B
  lam : Expr (Γ , A) B → Expr Γ (A ⇒ B)

-- Type inference produces intrinsically-typed expressions
inferElab : Ctx → RawExpr → Maybe (∃[ A ] Expr Γ A)

-- Soundness is TRIVIAL: if you have Expr Γ A, it IS well-typed!
```

## Why Intrinsic Typing Makes Soundness Trivial

With extrinsic typing, soundness requires proving that the inferred type matches the typing relation. This involves:

1. **Substitution transport**: If IH gives `WellTyped Γ e (applySubst σ₁ T)`, and we need `WellTyped Γ e (applySubst σ₂ T')`, we must show the types are equal and transport the evidence.

2. **Freshness tracking**: Proving that substitutions from different inference stages don't interfere requires tracking which type variables are "fresh" at each point.

3. **Unification soundness**: When unification produces a substitution, we must show it correctly relates the WellTyped derivations.

With intrinsic typing, **none of this is needed**. The expression `Expr Γ A` is a proof that the expression has type `A` in context `Γ`. If `inferElab` returns `success A expr`, then `expr : Expr Γ A` is the soundness proof itself.

## The Fundamental Challenge with Extrinsic Typing

The core problem is a **structural mismatch**:

- Type inference works with **polymorphic types and substitutions**
- The WellTyped relation expects **concrete types**

Example: For binary operators, the typing rule requires:
```agda
T-BinArith : WellTyped Γ e₁ Int → WellTyped Γ e₂ Int → WellTyped Γ (RBinOp op e₁ e₂) Int
```

But inference returns:
- IH: `WellTyped Γ e₁ (applySubst σ₁ tyA)` where `tyA` might be `TVar "t0"`
- Unification: `applySubst σ₃ tyA = Int`

The gap: `applySubst σ₁ tyA ≠ Int` in general. We'd need to rebuild the entire derivation tree to get `WellTyped Γ e₁ Int`.

With intrinsic typing, this problem doesn't exist. Inference directly produces `Expr Γ Int` for both operands, or fails.

## Current State in Once Codebase

The Once codebase has **both approaches**:

### Extrinsic Path (older)
- **Module**: `Once.TypeCheck.Infer`
- **Returns**: `InferResult` with type and substitution
- **Soundness**: `Once.TypeCheck.Sound` (complex, has postulates)

### Intrinsic Path (newer, recommended)
- **Module**: `Once.TypeCheck.Elaborate`
- **Returns**: `InferElabResult` with intrinsically-typed `SExpr Δ A`
- **Soundness**: Trivial by construction

```agda
-- From Elaborate.agda
data InferElabResult {n : ℕ} (Δ : SCtx n) : Set where
  success : (A : Type) → SExpr Δ A → ... → InferElabResult Δ
  failure : String → InferElabResult Δ
```

The intrinsically-typed surface expressions are in `Once.Surface.Syntax`:
```agda
data Expr : ∀ {n} → Ctx n → Type → Set where
  var   : (i : Fin n) → Expr Γ (lookup Γ i)
  lam   : Expr (Γ , A) B → Expr Γ (A ⇒[ q ] B)
  app   : Expr Γ (A ⇒[ q ] B) → Expr Γ A → Expr Γ B
  pair  : Expr Γ A → Expr Γ B → Expr Γ (A * B)
  -- etc.
```

## Recommendations

### For New Development

1. **Use `inferElab`** as the primary type checking entry point
2. **Extend `Surface.Syntax.Expr`** if new expression forms are needed
3. **Soundness is automatic** - no separate proof needed

### For the Extrinsic Soundness Proof

The extrinsic `WellTyped` relation and its soundness proof in `Sound.agda` can be:

1. **Deprecated** in favor of the intrinsic approach
2. **Kept for documentation** as an explicit typing relation
3. **Completed with postulates** for the hard cases (unification-involving cases)

The freshness infrastructure in `Sound.agda` handles the "easy" cases (Pair, Let) where inference is sequential without unification in the current step. The "hard" cases (App, Case, BinOp, UnaryOp, Annot) require transporting WellTyped evidence through unification, which is structurally difficult.

### Migration Path

If migrating from extrinsic to intrinsic:

1. Ensure `inferElab` handles all expression forms
2. Update downstream code to use `SExpr` instead of `RawExpr + WellTyped`
3. The elaborate-to-IR step (`Surface.Elaborate.elaborate`) already works with intrinsic types

## Gap Analysis: Intrinsic Path is Now Complete

As of commit `9399104`, the intrinsic `Surface.Syntax.Expr` supports **all** `RawExpr` forms:

### Full Coverage

| RawExpr | Surface.Syntax.Expr | Notes |
|---------|---------------------|-------|
| `RVar` | `var` | de Bruijn indexed |
| `RApp` | `app` | ✓ |
| `RLam` | `lam` | With quantity annotation |
| `RLet` | `let'` | ✓ |
| `RPair` | `pair` | ✓ |
| `RCase` | `case'` | ✓ |
| `RUnit` | `unit` | ✓ |
| `RAnnot` | N/A | Handled by checking mode |
| `RInt` | `int` | ✓ (newly added) |
| `RStringLit` | `str` | ✓ (newly added) |
| `RBinOp` | `add`, `sub`, `mul`, `div`, `mod'`, `lt`, `le`, `gt`, `ge`, `eq`, `ne` | ✓ (newly added) |
| `RUnaryOp` | `neg` | ✓ (newly added) |

### Extra in Intrinsic Path

The intrinsic path has expression forms that are builtins in the extrinsic path:

- `fst'`, `snd'` - Pair projections (builtins "fst", "snd" in extrinsic)
- `inl'`, `inr'` - Sum injections (builtins "inl", "inr" in extrinsic)
- `absurd` - Void elimination

### Implementation Notes

The arithmetic and comparison operations use postulated IR primitives (`intLit`, `addIR`, etc.) whose correctness is assumed. This is consistent with the existing `ArithIR` boundary architecture where `embedArith` is also postulated. The key benefit remains: **soundness is trivial by construction** for the type checking step

## Summary

| Aspect | Extrinsic | Intrinsic |
|--------|-----------|-----------|
| Expression type | `RawExpr` | `Expr Γ A` |
| Typing proof | Separate `WellTyped` relation | Built into expression type |
| Soundness | Complex proof needed | Trivial by construction |
| Substitution handling | Must transport evidence | Transforms expression directly |
| Implementation | `Infer.agda` | `Elaborate.agda` |

**Bottom line**: Intrinsic typing eliminates the structural mismatch between polymorphic inference and concrete typing rules, making soundness proofs trivial. The Once codebase already has the intrinsic infrastructure in place.
