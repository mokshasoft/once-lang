# Agda Formalization Lessons Learned

Practical lessons from formalizing the Once compiler in Agda.

## Agda Syntax Pitfalls

### `where` clauses cannot appear inside `let` bindings

```agda
-- BAD: Will fail with NotAValidLetBinding.WhereClausesNotAllowed
foo x =
  let helper = bar
        where
          bar = ...
  in helper x

-- GOOD: Use top-level where clause
foo x = helper x
  where
    helper = bar
    bar = ...
```

### `with` patterns block computation

When a function uses `with`, the result doesn't compute until the scrutinee is known:

```agda
-- evalSurface uses 'with' for case expressions
evalSurface ρ (case' s l r) with evalSurface ρ s
... | inj₁ a = evalSurface (a ∷ ρ) l
... | inj₂ b = evalSurface (b ∷ ρ) r
```

To prove properties about such functions, use `with` in the proof as well:

```agda
-- Create a helper that pattern matches on the with-scrutinee
case-analysis-inl : ... → evalSurface ρ s ≡ inj₁ a →
                    evalSurface ρ (case' s l r) ≡ evalSurface (a ∷ ρ) l
case-analysis-inl ρ s l r a eq with evalSurface ρ s | eq
... | inj₁ x | refl = refl
```

### Operator name conflicts

When importing modules with overlapping operator names, use renaming:

```agda
-- BAD: Ambiguous [_,_] from IR and Data.Sum
open import Data.Sum using ([_,_])
open import Once.IR

-- GOOD: Rename one of them
open import Once.Surface.Syntax renaming (_,_ to _▸_)
```

### Imports in `where` clauses don't affect type signatures

```agda
-- BAD: ∃-syntax not in scope for type signature
foo : ∃[ x ] P x
foo = x , proof
  where open import Data.Product using (∃-syntax)

-- GOOD: Import at module level
open import Data.Product using (∃-syntax)

foo : ∃[ x ] P x
foo = x , proof
```

## Proof Techniques

### Use `mutual` for mutually recursive proofs

When a main theorem needs helper lemmas that themselves need the theorem:

```agda
mutual
  main-theorem : ...
  main-theorem ... = ... helper ...

  helper : ...
  helper ... = ... main-theorem ...  -- can call main-theorem
```

### Prefer top-level definitions over nested `where` clauses

Top-level definitions are:
- Easier to debug (better error messages)
- Reusable across proofs
- Less prone to scoping issues

```agda
-- GOOD: Top-level helper
case-eval-helper : ... → ⟦ A ⟧ ⊎ ⟦ B ⟧ → ⟦ C ⟧
case-eval-helper ρ l r (inj₁ x) = evalSurface (x ∷ ρ) l
case-eval-helper ρ l r (inj₂ y) = evalSurface (y ∷ ρ) r

-- Then use in proof
lhs-simp = cong (case-eval-helper ρ l r) eq-s
```

### Function extensionality is a standard postulate

It's acceptable to postulate function extensionality:

```agda
postulate
  extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
                   (∀ x → f x ≡ g x) → f ≡ g
```

This is provable in Cubical Agda if a constructive proof is needed.

## Build System

### Dynamic library discovery in Makefile

Avoid hardcoded Nix store paths:

```makefile
# BAD: Breaks when Nix store changes
STD_LIB := /nix/store/abc123.../standard-library.agda-lib

# GOOD: Dynamic discovery
STD_LIB := $(shell find /nix/store -maxdepth 2 -name "standard-library.agda-lib" 2>/dev/null | head -1)
```

### Library name must match exactly

In `.agda-lib` files, the depend field must match the library name exactly:

```yaml
# If the library is named "standard-library-2.3", use that:
depend: standard-library-2.3

# NOT just:
depend: standard-library  # Wrong!
```

## Design Patterns

### De Bruijn indices avoid alpha-equivalence

Using de Bruijn indices for variable binding eliminates the need to reason about alpha-equivalence:

```agda
data Expr (Γ : Ctx n) : Type → Set where
  var : (i : Fin n) → Expr Γ (lookup Γ i)
  lam : Expr (Γ , A) B → Expr Γ (A ⇒ B)
```

### Context as nested product

Encoding typing contexts as nested products enables clean variable projection:

```agda
⟦ ∅ ⟧ᶜ     = Unit
⟦ Γ , A ⟧ᶜ = ⟦ Γ ⟧ᶜ * A

proj : Fin n → IR ⟦ Γ ⟧ᶜ (lookup Γ i)
proj zero    = snd
proj (suc i) = proj i ∘ fst
```

### Curry/apply trick for distribution

To distribute an environment through a case expression, use currying:

```agda
-- Γ * (A + B) → (Γ * A) + (Γ * B)
distribute = apply ∘ ⟨ [ curry (inl ∘ swap) , curry (inr ∘ swap) ] ∘ fst , snd ⟩ ∘ swap
```

This avoids the need for a primitive distribution combinator.
