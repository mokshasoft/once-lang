# Fix Semantics Options

Analysis of options for properly formalizing recursive type semantics in Agda.

## Background

The current `Fix F` semantics use a trivial newtype wrapper, making fold/unfold proofs trivially `refl`. The correct semantics should satisfy:

```
Fix F ≅ F[Fix F / X]   -- F with recursive occurrences substituted
```

This document compares four approaches to fix this semantic gap.

---

## Quick Comparison

### Complexity Impact

| Aspect | Polynomial Functors | Sized Types | Well-Founded | QIITs |
|--------|:------------------:|:-----------:|:------------:|:-----:|
| Proof setup | ~150 lines | ~200 lines | ~100 lines | ~250 lines |
| Per new type | 0 lines | 0 lines | ~30 lines | 0 lines |
| Per new function | 0 lines | ~5-10 lines | ~20 lines | ~5 lines |
| User syntax change | None | None (if hidden) | None | None |
| User mental model change | None | None (if hidden) | None | None |
| Forced complexity | **None** | None (if hidden) | **None** | None |

### Feature Support

| Feature | Polynomial Functors | Sized Types | Well-Founded | QIITs |
|---------|:------------------:|:-----------:|:------------:|:-----:|
| Nat, List, Tree | ✓ | ✓ | ✓ | ✓ |
| Dependent types | ✓ | ✓ | ✓ | ✓ |
| QTT / Linearity | Excellent | Tricky | Good | Unknown |
| CPS / Continuations | ✓ | ✓ | ✓ | ✓ |
| `Fix (X -> A)` patterns | ✗ | Some | ✓ | ✓ |
| Soundness | ✓ | ✓ | ✓ | ✓ |

### Verification Impact

| Task | Polynomial Functors | Sized Types | Well-Founded | QIITs |
|------|:------------------:|:-----------:|:------------:|:-----:|
| Structural recursion termination | Automatic | Automatic | Automatic | Automatic |
| Non-structural recursion | Must use cata | Size annotations | Direct proof | Direct proof |
| Induction principles | Free | Free | Manual per type | Free |
| Program correctness proofs | Standard | Standard | Standard | HoTT-style |

### Overall Assessment

| Criterion | Polynomial Functors | Sized Types | Well-Founded | QIITs |
|-----------|:------------------:|:-----------:|:------------:|:-----:|
| Implementation effort | **Low** | Medium | High | Very High |
| Ongoing proof burden | **Lowest** | Medium | High | Medium-High |
| Once compatibility | **Excellent** | Good | Good | Experimental |
| Future extensibility | Good | Good | **Best** | Best |

### Proof Complexity for Future Compiler Features

How each option affects the effort to verify new compiler features:

| Future Feature | Polynomial Functors | Sized Types | Well-Founded | QIITs |
|----------------|:------------------:|:-----------:|:------------:|:-----:|
| New recursive type (e.g., Tree) | **0 lines** | 0 lines | ~30 lines | 0 lines |
| New recursion scheme (e.g., para) | **~10 lines** | ~20 lines | ~40 lines | ~15 lines |
| Pattern matching compilation | **Low** | Medium | Medium | Medium |
| Optimization passes | **Low** | Medium | High | Medium |
| QTT quantity checking | **Low** | High | Medium | Unknown |
| Dependent type extensions | **Low** | Medium | Low | Low |
| Type inference changes | **None** | None | None | None |
| New primitive types | **None** | None | None | None |

**Key insight**: Polynomial functors give the most "for free" — `fmap`, induction principles, and fusion laws derive automatically from the functor structure. Other options require manual proofs for each new type or recursion pattern.

#### Optimization Pass Example

To verify a deforestation optimization like `map f . map g = map (f . g)`:

| Option | Proof Effort |
|--------|--------------|
| Polynomial | Free from functor laws |
| Sized | ~15 lines (size bookkeeping) |
| Well-Founded | ~30 lines (explicit fmap proofs) |
| QIITs | ~10 lines (path reasoning) |

#### Adding a New Recursion Scheme

To add `para : (F (μF × A) → A) → μF → A` (paramorphism):

| Option | Proof Effort |
|--------|--------------|
| Polynomial | Define + ~10 lines for properties |
| Sized | Define + ~20 lines (size handling) |
| Well-Founded | Define + ~40 lines (termination) |
| QIITs | Define + ~15 lines |

### Complexity of Verifying Once Programs

How each option affects users who want to prove properties about their Once programs:

| Verification Task | Polynomial Functors | Sized Types | Well-Founded | QIITs |
|-------------------|:------------------:|:-----------:|:------------:|:-----:|
| Prove `sum (append xs ys) = add (sum xs) (sum ys)` | **Standard induction** | Standard | Standard | HoTT-style |
| Prove termination of structural recursion | **Automatic** | Automatic | Automatic | Automatic |
| Prove termination of non-structural recursion | Restructure to cata | Size annotations | Direct proof | Direct proof |
| Prove `map f . map g = map (f . g)` | **Free (functor law)** | Manual | Manual | Free (path) |
| Prove properties about custom recursive types | **Free induction principle** | Free | Manual setup | Free |
| Reason about linearity in recursive functions | **Straightforward** | Complex | Moderate | Unknown |

#### Example: Verifying a List Function

User writes:
```
sum : List Nat -> Nat
sum = cata (\case inl _ -> zero; inr (a, acc) -> add a acc)
```

To prove `sum (append xs ys) = add (sum xs) (sum ys)`:

| Option | What User Must Do |
|--------|-------------------|
| Polynomial | Use derived induction principle, ~5-10 lines |
| Sized | Same, but size annotations may leak into proof, ~10-15 lines |
| Well-Founded | Must first prove List has valid induction, ~20-30 lines |
| QIITs | Use path induction, different style, ~10-15 lines |

#### Example: Non-Structural Recursion

User writes:
```
merge : List Nat -> List Nat -> List Nat
merge xs ys = case (unfold xs, unfold ys) of
  (inl _, _) -> ys
  (_, inl _) -> xs
  (inr (a, xs'), inr (b, ys')) ->
    if a <= b
    then fold (inr (a, merge xs' ys))
    else fold (inr (b, merge xs ys'))
```

| Option | What User Must Do |
|--------|-------------------|
| Polynomial | Rewrite using mutual cata or sized wrapper |
| Sized | Add size annotations to prove termination |
| Well-Founded | Prove termination via lexicographic ordering |
| QIITs | Similar to well-founded |

**Note**: Most programs use structural recursion (cata/fold), where all options behave identically. Non-structural recursion is rare.

#### Impact on Proof Assistants / External Verification

If users want to verify Once programs in an external proof assistant:

| Option | Extraction Quality | External Reasoning |
|--------|-------------------|-------------------|
| Polynomial | Clean (functor codes erase) | Standard induction |
| Sized | Sizes may appear in extracted code | Must handle sizes |
| Well-Founded | Accessibility proofs erase | Standard induction |
| QIITs | Paths erase but complex extraction | HoTT background needed |

---

## Option 1: Polynomial Functors

### The Idea

Define a universe of codes for strictly positive functors:

```agda
data Functor : Set where
  K    : Type → Functor           -- Constant
  Id   : Functor                  -- Recursive position
  _⊕_  : Functor → Functor → Functor  -- Sum
  _⊗_  : Functor → Functor → Functor  -- Product

⟦_⟧F : Functor → Set → Set
⟦ K A ⟧F X = ⟦ A ⟧
⟦ Id ⟧F X = X
⟦ F ⊕ G ⟧F X = ⟦ F ⟧F X ⊎ ⟦ G ⟧F X
⟦ F ⊗ G ⟧F X = ⟦ F ⟧F X × ⟦ G ⟧F X

data μ (F : Functor) : Set where
  ⟨_⟩ : ⟦ F ⟧F (μ F) → μ F
```

### User Syntax

**Unchanged:**
```
type Nat = Fix (Unit + X)
type List A = Fix (Unit + A * X)

zero = fold (inl unit)
succ n = fold (inr n)
```

### What It Can Express

| Type | Encoding | Status |
|------|----------|:------:|
| `Nat` | `Fix (K Unit ⊕ Id)` | ✓ |
| `List A` | `Fix (K Unit ⊕ K A ⊗ Id)` | ✓ |
| `Tree A` | `Fix (K A ⊕ Id ⊗ Id)` | ✓ |
| `RoseTree A` | `Fix (K A ⊗ List Id)` | ✓ |
| All standard data types | Polynomial encoding | ✓ |

### What It Cannot Express

| Type | Why | Needed? |
|------|-----|:-------:|
| `Fix (X -> A)` | X in negative position | Rarely |
| `Fix (A -> X)` | Function in recursive position | Rarely |
| Church/Scott encodings | Higher-order | No (native Fix is better) |
| PHOAS | Negative occurrence | No (use de Bruijn) |

### Category Theory Connection

Polynomial functors form the **free cartesian category** on one generator. This aligns with Once's CCC foundation. Initial algebras of polynomial functors always exist in Set.

### QTT Compatibility

Excellent. No function types in recursive structure means resource tracking is straightforward. The derived `fmap` respects linearity automatically.

---

## Option 2: Sized Types

### The Idea

Track recursion depth via size indices:

```agda
{-# OPTIONS --sized-types #-}

data μ (F : Set → Set) (i : Size) : Set where
  ⟨_⟩ : {j : Size< i} → F (μ F j) → μ F i
```

### User Syntax

**If hidden (recommended):** Unchanged
```
type Nat = Fix (Unit + X)
```

**If exposed:** Complex
```
type Nat : Size -> Type
type Nat i = Fix (Unit + X) i
```

### Tradeoffs

- More expressive than polynomial functors
- Size inference can fail unexpectedly
- Agda-specific (not portable)
- QTT interaction is complex and not fully understood

---

## Option 3: Well-Founded Recursion

### The Idea

Define `μF` as inductive type, justify recursion via accessibility:

```agda
data μ (F : Set → Set) : Set where
  ⟨_⟩ : F (μ F) → μ F

-- Termination via well-founded induction
cata : ∀ {F A} → (F A → A) → μ F → A
cata alg ⟨ x ⟩ = alg (fmap (cata alg) x)
```

### User Syntax

**Unchanged:**
```
type Nat = Fix (Unit + X)
```

### Tradeoffs

- Most general (can express any functor)
- Each type needs explicit `fmap`
- Each recursive function needs termination proof
- Highest ongoing proof burden
- Good QTT compatibility with explicit resource tracking

### When It Matters

Non-structural recursion like `merge`:

```
merge : List Nat -> List Nat -> List Nat
merge xs ys = case (unfold xs, unfold ys) of
  (inl _, _) -> ys
  (_, inl _) -> xs
  (inr (a, xs'), inr (b, ys')) ->
    if a <= b
    then fold (inr (a, merge xs' ys))
    else fold (inr (b, merge xs ys'))
```

Option 1 requires restructuring to `cata`. Option 3 allows direct proof.

---

## Option 4: QIITs

### The Idea

Use higher inductive types with path constructors:

```agda
{-# OPTIONS --cubical #-}

data μ (F : Set → Set) : Set where
  ⟨_⟩ : F (μ F) → μ F
  -- Path constructors for equations
```

### Tradeoffs

- Very expressive (higher categorical semantics)
- Experimental Agda features
- Requires HoTT/cubical understanding
- QTT integration is research territory

---

## Special Cases

### CPS and Continuations

```
type Cont R A = (A -> R) -> R
```

This is **not recursive**. All options support it equally. The limitation on `Fix (X -> A)` doesn't affect normal CPS.

### Self-Interpretation

A self-interpreter for Once would need:

```
type Term = Fix (Var Nat + Lam Term + App Term Term + ...)
```

This is **polynomial** — representable in Option 1. The fundamental limitation is the halting problem, not the Fix semantics. A total language cannot have a self-interpreter for Turing-complete terms regardless of which option we choose.

### Dependent Types

All options support dependent types (Vec, Sigma, Pi, refinements). The Fix semantics choice is orthogonal to dependent types.

---

## Recommendation

**Option 1 (Polynomial Functors)** for Once because:

| Reason | Explanation |
|--------|-------------|
| Zero user impact | Syntax and mental model unchanged |
| Zero forced complexity | Users never see functor codes |
| Lowest proof burden | One-time setup, then automatic |
| Best QTT fit | No functions in recursive positions |
| Sufficient expressiveness | Covers all Once types |
| CCC alignment | Polynomial = free cartesian category |
| Sound by construction | Excludes problematic patterns |

### Upgrade Path

If Once later needs non-structural recursion exposed to users, Option 3 (well-founded) is the natural extension. This would be a deliberate language design decision, not forced by proof strategy.

---

## Implementation Plan

1. Add `Functor` type to `Once/Type.agda`
2. Change `Fix : Type → Type` to `Fix : Functor → Type`
3. Define `⟦_⟧F` interpretation with explicit recursive position
4. Define `μ` as proper inductive type
5. Prove `fold`/`unfold` form isomorphism `μF ≅ F(μF)`
6. Derive `fmap` and induction principles
7. Update existing proofs to use new structure

Estimated effort: ~150-200 lines of Agda, 1-2 days.
