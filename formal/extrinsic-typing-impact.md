# Extrinsic Typing: Concrete Impact on Once

## Overview

This document shows **exactly** what would change if Once switched from intrinsic to extrinsic typing, with concrete code examples.

## Current State: Intrinsic Typing

### Surface Syntax (Current)

**File**: `formal/Once/Surface/Syntax.agda`

```agda
-- Context with size in the type
data Ctx : ℕ → Set where
  ∅   : Ctx 0
  _,_ : Ctx n → Type → Ctx (suc n)

-- Intrinsically-typed expressions
data Expr (Γ : Ctx n) : Type → Set where
  var  : (i : Fin n) → Expr Γ (lookup Γ i)
  lam  : ∀ {A B} → Expr (Γ , A) B → Expr Γ (A ⇒ B)
  app  : ∀ {A B} → Expr Γ (A ⇒ B) → Expr Γ A → Expr Γ B
  pair : ∀ {A B} → Expr Γ A → Expr Γ B → Expr Γ (A * B)
  fst' : ∀ {A B} → Expr Γ (A * B) → Expr Γ A
  snd' : ∀ {A B} → Expr Γ (A * B) → Expr Γ B
  -- ... etc
```

**Key properties**:
- ✅ Type is embedded in the expression: `Expr Γ A`
- ✅ Impossible to construct ill-typed terms
- ✅ Variables are `Fin n` - bounded by context size
- ✅ Lookup is in the type: `lookup Γ i`
- ❌ Context manipulation requires expression transformation

### TypeCheck.Elaborate (Current)

**File**: `formal/Once/TypeCheck/Elaborate.agda`

```agda
-- Type inference produces intrinsically-typed expression
inferElab : Ctx → RawExpr → Maybe (∃[ A ] SExpr Γ A)

-- Weakening transforms expressions
weaken : ∀ {n} {Γ : SCtx n} {A B : Type}
       → SExpr Γ B → SExpr (Γ S, A) B
weaken (Surface.var i) =
  subst (SExpr _) (lookup-suc i) (Surface.var (suc i))
weaken (Surface.lam e) = Surface.lam (exchange e)
-- Must transform every constructor!

-- Exchange transforms for nested binders
exchange : ∀ {n} {Γ : SCtx n} {A B C : Type}
         → SExpr (Γ S, B) C → SExpr ((Γ S, A) S, B) C
-- THIS IS THE PROBLEM - needs exchange₂, exchange₃, ... exchange₇, exchange₈
```

### Surface.Elaborate (Current)

**File**: `formal/Once/Surface/Elaborate.agda`

```agda
-- Takes intrinsically-typed expression
elaborate : ∀ {n} {Γ : Ctx n} {A} → Expr Γ A → IR ∞ ⟦ Γ ⟧ᶜ A
elaborate (var i) = proj i
elaborate (lam e) = curry (elaborate e)
elaborate (app f x) = apply ∘ ⟨ elaborate f , elaborate x ⟩
-- Pattern matching on typed constructors
```

**Correctness theorem**:
```agda
elaborate-correct : ∀ {n} {Γ : Ctx n} {A} (ρ : Env Γ) (e : Expr Γ A) →
                    evalSurface ρ e ≡ eval (elaborate e) (interpEnv ρ)
```

## Proposed State: Extrinsic Typing

### Surface Syntax (Extrinsic)

**New file**: `formal/Once/Surface/Expr.agda`

```agda
-- Simple context - just a list of types
Ctx : Set
Ctx = List Type

-- Untyped expressions (or "simply-typed" - no type parameter)
data Expr : Set where
  var  : ℕ → Expr
  lam  : Expr → Expr
  app  : Expr → Expr → Expr
  pair : Expr → Expr → Expr
  fst' : Expr → Expr
  snd' : Expr → Expr
  inl' : Expr → Expr
  inr' : Expr → Expr
  case' : Expr → Expr → Expr → Expr
  unit : Expr
  absurd : Expr → Expr
  let' : Expr → Expr → Expr
```

**Key differences**:
- ❌ No type parameter: `Expr` not `Expr Γ A`
- ✅ Variables are `ℕ` - simple natural numbers
- ✅ No context in type - just a plain datatype
- ✅ Easier to construct and manipulate

### Typing Judgment (New)

**New file**: `formal/Once/Surface/Typing.agda`

```agda
-- Variable lookup in context (separate function)
lookup : Ctx → ℕ → Maybe Type
lookup [] _ = nothing
lookup (A ∷ Γ) zero = just A
lookup (A ∷ Γ) (suc i) = lookup Γ i

-- Typing judgment as inductive relation
data _⊢_∶_ : Ctx → Expr → Type → Set where

  T-Var : ∀ {Γ i A}
        → lookup Γ i ≡ just A
        → Γ ⊢ var i ∶ A

  T-Lam : ∀ {Γ e A B}
        → (A ∷ Γ) ⊢ e ∶ B      -- Just cons! No transformation!
        → Γ ⊢ lam e ∶ (A ⇒ B)

  T-App : ∀ {Γ f x A B}
        → Γ ⊢ f ∶ (A ⇒ B)
        → Γ ⊢ x ∶ A
        → Γ ⊢ app f x ∶ B

  T-Pair : ∀ {Γ a b A B}
         → Γ ⊢ a ∶ A
         → Γ ⊢ b ∶ B
         → Γ ⊢ pair a b ∶ (A * B)

  T-Fst : ∀ {Γ p A B}
        → Γ ⊢ p ∶ (A * B)
        → Γ ⊢ fst' p ∶ A

  T-Snd : ∀ {Γ p A B}
        → Γ ⊢ p ∶ (A * B)
        → Γ ⊢ snd' p ∶ B

  T-Case : ∀ {Γ s l r A B C}
         → Γ ⊢ s ∶ (A + B)
         → (A ∷ Γ) ⊢ l ∶ C     -- Just cons!
         → (B ∷ Γ) ⊢ r ∶ C     -- Just cons!
         → Γ ⊢ case' s l r ∶ C

  T-Let : ∀ {Γ e₁ e₂ A B}
        → Γ ⊢ e₁ ∶ A
        → (A ∷ Γ) ⊢ e₂ ∶ B    -- Just cons!
        → Γ ⊢ let' e₁ e₂ ∶ B

  -- ... etc
```

**Crucial observation**: Going under binders is just **list cons**:
- Lambda: `(A ∷ Γ)`
- Case: `(A ∷ Γ)` for left, `(B ∷ Γ)` for right
- Let: `(A ∷ Γ)` for body

**No transformation, no exchange, no problem!**

### Weakening as Lemma (New)

**File**: `formal/Once/Surface/Weakening.agda`

```agda
-- Context inclusion (subcontext)
data _⊆_ : Ctx → Ctx → Set where
  ⊆-refl : ∀ {Γ} → Γ ⊆ Γ
  ⊆-ext  : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊆ (A ∷ Γ')

-- Variable lookup respects inclusion
lookup-⊆ : ∀ {Γ Γ' i A}
         → Γ ⊆ Γ'
         → lookup Γ i ≡ just A
         → lookup Γ' i ≡ just A
lookup-⊆ ⊆-refl prf = prf
lookup-⊆ (⊆-ext inc) prf = {! shift and recurse !}

-- Weakening theorem: expressions still type in larger contexts
weakening : ∀ {Γ Γ' e A}
          → Γ ⊢ e ∶ A
          → Γ ⊆ Γ'
          → Γ' ⊢ e ∶ A
weakening (T-Var prf) inc = T-Var (lookup-⊆ inc prf)
weakening (T-Lam body) inc = T-Lam (weakening body (⊆-ext inc))
weakening (T-App f x) inc = T-App (weakening f inc) (weakening x inc)
weakening (T-Pair a b) inc = T-Pair (weakening a inc) (weakening b inc)
-- ... etc - straightforward induction!
```

**Key point**: This is a **lemma** (proof), not a **transformation** (function on expressions).

We prove "the same expression still types" - we don't transform it!

### TypeCheck.Elaborate (Extrinsic)

**File**: `formal/Once/TypeCheck/Elaborate.agda`

```agda
-- Type inference returns expression + type + typing derivation
inferElab : Ctx → RawExpr → Maybe (∃[ A ] ∃[ e ] (Γ ⊢ e ∶ A))

-- Or simpler version if we trust the implementation:
inferElab : Ctx → RawExpr → Maybe (∃[ A ] Expr)
-- Returns untyped Expr, caller must trust it's well-typed

-- Implementation becomes simpler - no weaken/exchange transformations!
inferElab Γ (RLam x body) = do
  (B , e) ← inferElab (A ∷ Γ) body  -- Just cons! No weaken!
  return (A ⇒ B , lam e)

inferElab Γ (RCase scrut left right) = do
  (A + B , s) ← inferElab Γ scrut
  (C , l) ← inferElab (A ∷ Γ) left   -- Just cons!
  (C' , r) ← inferElab (B ∷ Γ) right -- Just cons!
  guard (C ≟ C')
  return (C , case' s l r)

-- NO WEAKEN, NO EXCHANGE, NO PROBLEM!
```

### Surface.Elaborate (Updated for Extrinsic)

**File**: `formal/Once/Surface/Elaborate.agda`

**Option 1: Require typing derivation**
```agda
-- Takes expression + proof it's well-typed
elaborate : ∀ {Γ e A} → Γ ⊢ e ∶ A → IR ∞ ⟦ Γ ⟧ᶜ A
elaborate (T-Var {i = i} prf) = proj i
elaborate (T-Lam body) = curry (elaborate body)
elaborate (T-App f x) = apply ∘ ⟨ elaborate f , elaborate x ⟩
-- Pattern match on typing derivation
```

**Option 2: Trust that expression is well-typed**
```agda
-- Takes expression, assumes it's well-typed for given context/type
elaborate : Ctx → Expr → Type → IR ∞ ⟦ Γ ⟧ᶜ A
elaborate Γ (var i) A = proj i
elaborate Γ (lam e) (A ⇒ B) = curry (elaborate (A ∷ Γ) e B)
elaborate Γ (app f x) B =
  -- Need to figure out A from f's type
  let A ⇒ B = inferType Γ f in
  apply ∘ ⟨ elaborate Γ f (A ⇒ B) , elaborate Γ x A ⟩
```

**Option 3: Erasure - extract Expr from intrinsic**
```agda
-- Keep intrinsic for some parts, erase to extrinsic for others
erase : ∀ {Γ A} → IntrinsicExpr Γ A → Expr
erase (var i) = var (toℕ i)
erase (lam e) = lam (erase e)
-- ...

-- Then elaborate the erased version
elaborate : Expr → IR ...
```

**Correctness theorem (Option 1)**:
```agda
elaborate-correct : ∀ {Γ e A} (typing : Γ ⊢ e ∶ A) (ρ : Env Γ) →
                    evalExpr ρ e ≡ eval (elaborate typing) (interpEnv ρ)
```

## Side-by-Side Comparison

### Lambda Expression

**Intrinsic** (current):
```agda
-- Type: Expr (Γ , A) B
-- Can only construct if body types correctly
lam-expr : Expr (∅ , Int) Int
lam-expr = lam (var zero)  -- zero : Fin 1

-- Going under binder requires weaken
process-under-binder : Expr Γ A → Expr (Γ , B) A
process-under-binder e = weaken e
  -- Must transform entire expression!
```

**Extrinsic**:
```agda
-- Type: Expr (just a datatype)
-- Can construct anything, typing is separate
lam-expr : Expr
lam-expr = lam (var 0)  -- 0 : ℕ

-- Typing judgment
lam-typing : (Int ∷ ∅) ⊢ lam-expr ∶ (Int ⇒ Int)
lam-typing = T-Lam (T-Var refl)

-- Going under binder - expression unchanged!
process-under-binder : Expr → Expr
process-under-binder e = e  -- No transformation!

-- Typing is updated by adding to context
typing-under-binder : ∀ {Γ e A B}
                    → Γ ⊢ e ∶ A
                    → (B ∷ Γ) ⊢ e ∶ A  -- Weakening lemma
typing-under-binder = weakening (⊆-ext ⊆-refl)
```

### Type Inference for Case

**Intrinsic** (current - simplified):
```agda
inferCase : RawExpr → RawExpr → RawExpr
          → Maybe (∃[ C ] SExpr Γ C)
inferCase scrut left right = do
  (A + B , s) ← infer Γ scrut
  (C , l) ← infer (Γ S, A) left    -- Creates SExpr (Γ S, A) C
  (C' , r) ← infer (Γ S, B) right  -- Creates SExpr (Γ S, B) C'

  -- Problem: l has type SExpr (Γ S, A) C
  --          r has type SExpr (Γ S, B) C'
  -- But Surface.case' needs both to have same context!
  -- Must transform expressions!
  guard (C ≟ C')
  return (C , Surface.case' s l r)  -- Type mismatch!
```

**Extrinsic**:
```agda
inferCase : RawExpr → RawExpr → RawExpr
          → Maybe (∃[ C ] Expr)
inferCase Γ scrut left right = do
  (A + B , s) ← infer Γ scrut
  (C , l) ← infer (A ∷ Γ) left     -- Returns Expr (plain)
  (C' , r) ← infer (B ∷ Γ) right   -- Returns Expr (plain)

  -- No problem! l and r are just Expr, no context in type
  guard (C ≟ C')
  return (C , case' s l r)  -- Works!
```

## What Actually Changes

### Files That Need Major Changes

1. **Once/Surface/Syntax.agda** → Split into:
   - `Once/Surface/Expr.agda` - Untyped expressions
   - `Once/Surface/Typing.agda` - Typing judgment

2. **Once/TypeCheck/Elaborate.agda**:
   - Remove `weaken`, `exchange`, `exchange₂-₇`
   - Simplify inference - no expression transformation
   - Return `Expr` (untyped) instead of `SExpr Γ A`

3. **Once/Surface/Elaborate.agda**:
   - Update to accept either:
     - Typing derivation: `Γ ⊢ e ∶ A → IR`
     - Or trusted expr: `Ctx → Expr → Type → IR`
   - Update correctness theorem

4. **Once/Surface/Correct.agda**:
   - Update correctness statement
   - Proof structure may need adjustment

### Files That Don't Change

1. **Once/IR.agda** - IR unchanged
2. **Once/Optimize/*.agda** - Optimization unchanged
3. **Once/Backend/X86/*.agda** - Code generation unchanged
4. **Once/Type.agda** - Type definitions unchanged

### New Files Needed

1. **Once/Surface/Typing.agda** - Typing judgment
2. **Once/Surface/Weakening.agda** - Weakening lemma
3. **Once/Surface/Substitution.agda** - (If needed) Substitution lemma

### Estimated Effort

| Task | Effort | Risk |
|------|--------|------|
| Define extrinsic Expr | 1 day | Low |
| Define typing judgment | 2-3 days | Low |
| Prove weakening lemma | 3-4 days | Medium |
| Update TypeCheck.Elaborate | 1 week | Medium |
| Update Surface.Elaborate | 1 week | Medium |
| Update correctness proofs | 1-2 weeks | High |
| Testing and integration | 1 week | Medium |
| **Total** | **4-6 weeks** | **Medium-High** |

## Advantages of Extrinsic Typing

1. ✅ **No exchange problem** - expressions don't change
2. ✅ **Simpler context operations** - just list operations
3. ✅ **Standard approach** - used by Cogent, CakeML, CompCert
4. ✅ **Easier to extend** - adding new constructors is simpler
5. ✅ **Weakening is trivial** - just a lemma, not transformation

## Disadvantages of Extrinsic Typing

1. ❌ **Can construct ill-typed terms** - `lam (var 999)` compiles
2. ❌ **Need typing judgment** - extra proof burden
3. ❌ **Lost type-safety guarantee** - must prove separately
4. ❌ **Refactoring effort** - 4-6 weeks of work
5. ❌ **Learning curve** - team must learn new approach

## Migration Strategy (If Chosen)

### Phase 1: Parallel Implementation (2 weeks)
- Create new `Once/Surface/Expr.agda` (extrinsic)
- Create `Once/Surface/Typing.agda`
- Keep old intrinsic version running
- Prove key lemmas (weakening, substitution)

### Phase 2: Update TypeCheck (1 week)
- Modify `TypeCheck.Elaborate` to produce extrinsic expressions
- Remove weaken/exchange transformations
- Test type inference still works

### Phase 3: Update Surface.Elaborate (1 week)
- Modify to accept extrinsic + typing derivation
- Or modify to accept extrinsic + trust well-typed
- Update correctness theorem

### Phase 4: Prove Correctness (2 weeks)
- Prove updated elaborate-correct theorem
- Ensure no gaps in reasoning
- Verify end-to-end still composes

### Phase 5: Integration & Cleanup (1 week)
- Remove old intrinsic definitions
- Update MAlonzo extraction
- Test all 221 compiler tests
- Update documentation

## Recommendation

Given the investigation of Cogent and the **proven track record** of extrinsic typing in verified compilers, **if we must verify the type checker**, extrinsic typing is the recommended approach.

**However**, consider first whether type checker verification is necessary given:
- Once's philosophy (types as assertions, generators as truth)
- Existing verified parts (Surface→IR→x86 all proven)
- Cogent's scope (they verify Cogent→C, not type checking)

**Two paths**:
1. **Pragmatic**: Accept type checker in TCB, proceed with current intrinsic for verified parts
2. **Complete**: Switch to extrinsic typing, verify entire pipeline including type checker

The choice depends on project goals and timeline.
