# Analysis: Achieving Normal Form Uniqueness in Once

## Executive Summary

The `normal-unique` property (semantically equivalent normal forms are syntactically equal) is currently false due to degenerate types. However, **this is fixable** with a clean architectural change: **type-directed normalization**.

The key insight is that:
- Any `f : A → Unit` is semantically equal to `terminal`
- Any `f : Void → B` is semantically equal to `initial`

By adding these as **primary normalization rules** (checked before structural rules), we eliminate all counterexamples and make `normal-unique` provable.

## The Problem

### Current Counterexamples

For type `(Unit * Unit) → Unit`, three distinct normal forms are semantically equivalent:

```agda
fst      : (Unit * Unit) → Unit   -- eval fst (tt, tt) = tt
snd      : (Unit * Unit) → Unit   -- eval snd (tt, tt) = tt
terminal : (Unit * Unit) → Unit   -- eval terminal (tt, tt) = tt
```

The fundamental issue: `Unit` has exactly one inhabitant (`tt`), so any function `A → Unit` is the constant function returning `tt`.

### Root Cause

The current optimizer uses **structural normalization**: it pattern-matches on IR constructors and applies rewrite rules. It doesn't consider the **types** when deciding normal forms.

For Unit/Void types, multiple syntactically distinct terms collapse to the same semantic function.

## The Solution: Type-Directed Normalization

### Core Principle

Add two **meta-rules** that take priority over all structural rules:

1. **Unit Target Rule**: Any `f : A → Unit` normalizes to `terminal`
2. **Void Source Rule**: Any `f : Void → B` normalizes to `initial`

These rules are semantically justified:
- `eval f x : Unit` can only be `tt`, same as `eval terminal x`
- `eval f x` for `x : Void` is vacuously equal to `eval initial x` (no inputs exist)

### Implementation

Modify `optimize-once` to check types first:

```agda
optimize-once : ∀ {A B} → IR A B → IR A B
optimize-once {A} {B} ir with B ≟Type Unit
... | yes refl = terminal                    -- Target is Unit → terminal
... | no _ with A ≟Type Void
...   | yes refl = initial                   -- Source is Void → initial
...   | no _ = optimize-once-structural ir   -- Otherwise → structural rules

optimize-once-structural : ∀ {A B} → IR A B → IR A B
optimize-once-structural id = id
optimize-once-structural (g ∘ f) = optimize-compose (optimize-once g) (optimize-once f)
... (current structural rules)
```

### Why This Works

After this change:

| Type | Normal Form | Count |
|------|-------------|-------|
| `A → Unit` | `terminal` | 1 (unique!) |
| `Void → B` | `initial` | 1 (unique!) |
| `Void → Unit` | `terminal` (Unit rule wins) | 1 (unique!) |
| Other types | Structural normal forms | Need to prove uniqueness |

For the "other types" category (neither Void source nor Unit target), we need to prove that structurally distinct normal forms have distinct semantics.

## Proof of Correctness

### 1. Semantic Preservation

**Theorem**: The type-directed rules preserve semantics.

**Proof for Unit target**:
```
Goal: eval terminal x ≡ eval f x  for any f : A → Unit

eval terminal x = tt        (definition)
eval f x : Unit             (by typing)
∴ eval f x = tt             (Unit has one inhabitant)
∴ eval terminal x ≡ eval f x
```

**Proof for Void source**:
```
Goal: eval initial x ≡ eval f x  for any f : Void → B

x : ⟦ Void ⟧ = ⊥            (by typing)
⊥-elim x                    (no such x exists)
∴ vacuously true
```

### 2. Normality Preservation

**Theorem**: The type-directed rules produce normal forms.

- `terminal` is normal: `normal-terminal`
- `initial` is normal: `normal-initial`

### 3. Cost Non-Increase

**Theorem**: The type-directed rules don't increase cost.

- `cost terminal = 0`
- `cost initial = 0`
- `0 ≤ cost f` for any f

### 4. Normal Uniqueness

**Theorem**: After type-directed normalization, `normal-unique` holds.

**Case 1: A → Unit**
The only normal form is `terminal`. Any two normal forms are both `terminal`, hence equal.

**Case 2: Void → B**
The only normal form is `initial`. Any two normal forms are both `initial`, hence equal.

**Case 3: A → B where A ≠ Void and B ≠ Unit**
Here we need structural uniqueness. The claim is that for non-degenerate types, different normal IR constructors produce different functions.

**Proof sketch**:
- `id` vs others: identity function is unique
- `fst` vs `snd`: on input `(a, b)` with `a ≠ b`, they differ
- `inl` vs `inr`: produce different tags
- Compositions: by induction on structure
- Pairs/Cases: by component distinctness

The key insight is that for types with multiple inhabitants, we can always find a **distinguishing input** that separates different normal forms.

## Detailed Implementation Plan

### Step 1: Modify Optimize.agda

```agda
-- Add type-directed wrapper
optimize-once : ∀ {A B} → IR A B → IR A B
optimize-once {A} {B} ir with B ≟Type Unit
... | yes refl = terminal
... | no ¬unit with A ≟Type Void
...   | yes refl = initial
...   | no ¬void = optimize-once-core ir

-- Rename current optimize-once to optimize-once-core
optimize-once-core : ∀ {A B} → IR A B → IR A B
optimize-once-core id = id
-- ... rest unchanged
```

### Step 2: Update Optimize/Correct.agda

```agda
optimize-once-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
  eval (optimize-once ir) x ≡ eval ir x

optimize-once-correct {A} {B} ir x with B ≟Type Unit
... | yes refl = refl  -- eval terminal x = tt = eval ir x
... | no ¬unit with A ≟Type Void
...   | yes refl = ⊥-elim x  -- x : ⟦ Void ⟧ = ⊥
...   | no ¬void = optimize-once-core-correct ir x
```

### Step 3: Update Optimizer/Normal.agda

```agda
optimize-once-normal : ∀ {A B} (ir : IR A B) → IsNormal (optimize-once ir)
optimize-once-normal {A} {B} ir with B ≟Type Unit
... | yes refl = normal-terminal
... | no ¬unit with A ≟Type Void
...   | yes refl = normal-initial
...   | no ¬void = optimize-once-core-normal ir

optimize-once-cost-le : ∀ {A B} (ir : IR A B) → cost (optimize-once ir) ≤ cost ir
optimize-once-cost-le {A} {B} ir with B ≟Type Unit
... | yes refl = z≤n  -- cost terminal = 0 ≤ cost ir
... | no ¬unit with A ≟Type Void
...   | yes refl = z≤n  -- cost initial = 0 ≤ cost ir
...   | no ¬void = optimize-once-core-cost-le ir
```

### Step 4: Prove normal-unique

```agda
normal-unique : ∀ {A B} (t t' : IR A B) →
  IsNormal t → IsNormal t' →
  (∀ x → eval t x ≡ eval t' x) →
  t ≡ t'

-- Case 1: Target is Unit
normal-unique {A} {Unit} t t' nt nt' eq =
  terminal-unique t t' nt nt'
  where
    -- Both must be terminal (only normal form of type A → Unit)
    terminal-unique : ...

-- Case 2: Source is Void
normal-unique {Void} {B} t t' nt nt' eq =
  initial-unique t t' nt nt'
  where
    -- Both must be initial (only normal form of type Void → B)
    initial-unique : ...

-- Case 3: Neither Void nor Unit
normal-unique {A} {B} t t' nt nt' eq with B ≟Type Unit | A ≟Type Void
... | no ¬unit | no ¬void = structural-unique t t' nt nt' eq ¬void ¬unit
  where
    -- Prove by structural induction
    structural-unique : ...
```

### Step 5: The Structural Uniqueness Lemma

For Case 3, we need:

```agda
structural-unique : ∀ {A B} (t t' : IR A B) →
  A ≢ Void → B ≢ Unit →
  IsNormal t → IsNormal t' →
  (∀ x → eval t x ≡ eval t' x) →
  t ≡ t'
```

**Proof approach**:

1. **Base cases**: For each pair of distinct constructors (id vs fst, fst vs snd, etc.), show they have different semantics on some input.

2. **Recursive cases**: For compositions, pairs, cases, use induction:
   - If `g ∘ f ≡ g' ∘ f'` semantically, then by choosing appropriate inputs, we can show `g ≡ g'` and `f ≡ f'` (or derive contradiction).

3. **The key lemma**: For non-degenerate types, there exist "discriminating" inputs:
   ```agda
   -- For products: there exist distinct elements
   prod-has-distinct : ∀ {A B} → A ≢ Void → B ≢ Unit →
     ∃[ a ] ∃[ a' ] ∃[ b ] (a ≢ a') × ((a, b) : ⟦ A * B ⟧)

   -- For sums: we can inject into either side
   sum-has-both : ∀ {A B} → A ≢ Void → B ≢ Void →
     (∃[ a ] inj₁ a : ⟦ A + B ⟧) × (∃[ b ] inj₂ b : ⟦ A + B ⟧)
   ```

## Edge Cases and Considerations

### 1. Nested Unit/Void

Types like `(Unit * A) → B` or `A → (B + Unit)` are NOT affected by the type-directed rules. The rules only apply to:
- **Direct** Unit as target type
- **Direct** Void as source type

Nested occurrences are handled by structural rules as usual.

### 2. Function Types

For `(A → Unit) → B`, the argument type contains Unit but the source type is `A → Unit`, not `Void`. These cases work normally.

### 3. Fix Types

`Fix F` types are handled structurally. If `Fix F ≅ Unit` or `Fix F ≅ Void`, the isomorphism would need to be used explicitly. In practice, most Fix types are non-degenerate.

### 4. Effects and IO

**Critical**: The Unit optimization relies on Once's effect type discipline.

**Type structure**:
```
Unit        : pure unit type (single inhabitant: tt)
Eff A B     : effectful computation from A to B
IO A        : Eff Unit A (effectful computation producing A)
```

**The invariant**: Effectful operations use `Eff`/`IO` types, not plain types.

| Term | Type | Safe to optimize? |
|------|------|-------------------|
| `terminal` | `A → Unit` | ✅ Already terminal |
| `f ∘ g` | `A → Unit` | ✅ Pure, can become terminal |
| `Prim "add"` | `(Int * Int) → Int` | N/A (not Unit target) |
| `Prim "print"` | `String → IO Unit` | ❌ Not `Unit`, it's `IO Unit` |
| `Prim "print"` | `String → Unit` | ⚠️ TYPE ERROR - violates discipline |

**Why it's safe**: The Unit rule checks `B ≟Type Unit`. Since `IO Unit = Eff Unit Unit ≠ Unit`, effectful computations don't match.

**The discipline requirement**: Primitives with effects MUST use `Eff`/`IO` types:
```agda
-- CORRECT: effectful primitive with effect type
Prim "print" : IR String (IO Unit)

-- WRONG: effectful primitive with pure type (violates discipline)
Prim "print" : IR String Unit  -- Would be incorrectly optimized!
```

**Enforcement**: The type discipline should be enforced at:
1. Primitive definition time (library authors)
2. FFI boundary (runtime integration)
3. Potentially by the type checker for known primitives

**Conclusion**: The Unit optimization is sound IF the effect type discipline is maintained. Effectful operations returning Unit use `IO Unit`, not `Unit`, so they're not affected.

### 5. Void → Unit

When both rules apply, Unit rule wins (checked first). The canonical form is `terminal : Void → Unit`.

## Benefits

1. **Coherence**: Equivalent terms optimize to identical normal forms
2. **Dead code elimination**: `f ∘ g` where target is Unit becomes `terminal`, eliminating g's computation
3. **Simpler proofs**: Many edge cases disappear
4. **Principled design**: Based on categorical semantics of terminal/initial objects

## Cost-Benefit Analysis

**Costs**:
- Refactoring `optimize-once` to add type-directed layer
- Updating all dependent proofs
- Proving structural uniqueness for non-degenerate types

**Benefits**:
- `normal-unique` becomes provable
- `coherence` theorem is fully justified
- Cleaner optimizer architecture
- Additional dead code elimination

## Estimated Effort

| Task | Effort | Notes |
|------|--------|-------|
| Modify optimize-once | Low | ~20 lines |
| Update optimize-once-correct | Low | ~10 lines |
| Update optimize-once-normal | Low | ~10 lines |
| Update optimize-once-cost-le | Low | ~10 lines |
| Prove terminal/initial uniqueness | Low | Straightforward |
| Prove structural uniqueness | Medium | ~200-300 lines of case analysis |
| Update dependent code | Medium | Downstream proofs may need adjustment |

**Total**: Medium effort, achievable in a focused session.

## Conclusion

The `normal-unique` property IS achievable in Once through type-directed normalization. The approach is:

1. **Simple core idea**: `A → Unit = terminal`, `Void → B = initial`
2. **Clean implementation**: Type checks before structural matching
3. **Sound justification**: Based on categorical semantics
4. **Provable correctness**: All components have straightforward proofs

The main work is in proving structural uniqueness for non-degenerate types, which requires careful but mechanical case analysis.

**Recommendation**: Implement this change. It strengthens the formal guarantees and aligns the optimizer with categorical semantics.
