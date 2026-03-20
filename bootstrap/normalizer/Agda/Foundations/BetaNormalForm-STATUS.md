# BetaNormalForm Proof - Work in Progress

## Task
Proving `encode-is-betanf` in `Foundations/BetaNormalForm.agda` - showing that all encoded terms are in beta-normal form (have no beta-redexes).

## What's Working
- The `BetaNormalForm.agda` module structure is in place
- `_⟶β_` relation defining beta-reductions is complete
- `IsBetaNormalForm` predicate is defined
- Mathematical argument is clear and correct

## The Fundamental Problem: Agda Type Inference

The encoding uses deeply nested binary sums. For example, `TermF` has 14 alternatives encoded as:
```
TermF = (K TyFuncCode)                    -- 0: id
      ⊕ (Id ⊗ Id)                         -- 1: compose
      ⊕ ...                               -- positions 2-12
      ⊕ (K TyFuncCode ⊗ K TyFuncCode)    -- 13: apply
```

To inject into position 13 (apply), the encoding is:
```agda
encode (apply {A} {B}) = In ∘ inr ∘ inr ∘ ... (13 times) ... ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩
```

When proving `IsSafe (encode apply)` using a predicate like:
```agda
data IsSafe : ∀ {A B} → Term A B → Set where
  safe-inr : ∀ {A B C} {f : Term C B} → IsSafe f → IsSafe (inr {A} {B} ∘ f)
  ...
```

Agda cannot infer the implicit type parameters `{A B C}` through 13 levels of `safe-inr` applications. The type constraints become "blocked" and unification fails.

## Approaches Tried

### 1. Original IsEncoding Structure
```agda
data IsEncoding : ∀ {A B} → Term A B → Set where
  enc-inr : ∀ {A B C} {f} → IsEncoding f → IsEncoding (inr {A} {B} ∘ f)
  ...
```
**Result**: Type inference fails on `encode-enc (apply ...)` - Agda can't determine `TermF` through 13 nested `enc-inr` calls.

### 2. Type-Specific Predicates (IsTyFuncBody, IsTermBody)
Split the predicate by target type to give Agda more information.
**Result**: Still fails - the nested `tb-inr` calls have the same inference problem.

### 3. Helper Functions with Explicit Return Types
```agda
apply-body : (A B : Ty) → IsTermBody (inr ∘ inr ∘ ... ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)
```
**Result**: Still fails - the body still uses `safe-inr` which has implicit parameters.

### 4. Polymorphic IsSafe Predicate
```agda
data IsSafe : ∀ {A B} → Term A B → Set where
  safe-inr : ∀ {A B C} {f} → IsSafe f → IsSafe (inr ∘ f)
```
**Result**: Same inference failure - polymorphism doesn't help.

## The Mathematical Argument (What We're Trying to Prove)

The proof is actually simple mathematically:

> **Theorem**: All encoded terms are in β-normal form.
>
> **Proof**: By structural induction. Every encoding has the form `In ∘ body` where `body` is built from `{inl, inr, terminal, ⟨_,_⟩}` and nested encodings. The head constructor `In` doesn't match any β-redex pattern—it's not `id`, `fst`, `snd`, `[_,_]`, `apply`, `cata`, or `Out`. The body contains no redex patterns since it's pure data injection. Recursively, all subterms are also encodings. ∎

This argument doesn't care about how many `inr`s there are—it's uniform. **Agda is fighting us because of its type inference limitations, not because the math is hard.**

## Potential Solutions

### Option A: Extend Polynomial Functor Grammar with Σⁿ
Add n-ary indexed sums to the functor grammar:
```agda
data Func : Set where
  ...
  Σⁿ : (n : ℕ) → (Fin n → Func) → Func
```
Then `TermF = Σⁿ 14 (λ i → ...)` and injection is single-step.

**Pros**: Clean, mathematically natural, fixes inference
**Cons**: Requires extending the functor grammar and all related proofs

### Option B: Use the Fixpoint Property Instead
Per OCP-0004, the **fixpoint property** is the primary verification mechanism:
```
If N(⌜N⌝) ⟶* ⌜N⌝  then ⌜N⌝ is in normal form
```
The `encode-is-betanf` proof is explaining *why* the fixpoint works, but the fixpoint test itself is the real verification.

**Pros**: Aligns with the minimal-trust philosophy
**Cons**: Less formal documentation of the "why"

### Option C: Wait for Once + Dependent Types
With dependent types in Once, the proof becomes a Once program verified by normalization. The Agda bureaucracy disappears.

**Pros**: The end goal anyway
**Cons**: Requires dependent types (future work)

### Option D: Add Explicit Type Annotations Everywhere
Manually provide all 13 type arguments at each `safe-inr` call.

**Pros**: Should work
**Cons**: Extremely verbose, error-prone, hard to maintain

## Recommended Path Forward

1. **Short-term**: Keep the postulate with detailed comments explaining the proof structure. The mathematical argument is correct; it's just Agda that's being difficult.

2. **Medium-term**: Consider Option A (Σⁿ) if more proofs hit this pattern. The extension is mathematically sound and would simplify many things.

3. **Long-term**: Option C - Once + dependent types makes this natural.

## Key Insight

This is an instance of a broader observation: **Agda is not the proof language we want**. Per OCP-0004, the vision is that Once itself becomes the proof language, with verification via normalization. The current Agda work is bootstrapping—we're using an external system to verify the foundation until Once can self-verify.

The "13 nested inr" problem is an Agda problem, not a mathematical one. A mathematician's proof doesn't count `inr`s—it reasons about the *structure*.

## Files
- `normalizer/Foundations/BetaNormalForm.agda` - current module with postulate
- `normalizer/Foundations/Encoding.agda` - defines the encoding with nested sums
