# Agda Formalization Lessons Learned

Practical lessons from formalizing the Once compiler in Agda.

## Trusted Computing Base (TCB)

For a complete list of what is proven and what is postulated, see [What Is Proven](what-is-proven.md).

### On function extensionality and extraction

Function extensionality is used in the `lam` case of `elaborate-correct`:

```agda
elaborate-correct ρ (lam e) = extensionality λ a → elaborate-correct (a ∷ ρ) e
```

**Impact on extraction**: When extracting Agda to Haskell via MAlonzo, postulates become runtime errors. However, this particular use is safe because:

1. The `extensionality` postulate is only used in *proof terms* (equality witnesses)
2. Proof terms are erased during extraction—they have no computational content
3. The extracted compiler code never evaluates the postulate at runtime

**If you need a constructive proof**: Use Cubical Agda where function extensionality is provable via path types. This requires:
- Changing the equality type from `_≡_` to cubical paths
- Using `--cubical` flag
- More complex proof infrastructure

For Once, the current approach (postulate + erasure) is sound because we only extract the *computational* parts (elaborator, optimizer, codegen), not the proof terms.

### TCB summary

The trusted computing base includes:
1. Agda type checker
2. MAlonzo extraction (Agda → Haskell)
3. GHC (Haskell → native)
4. The `extensionality` postulate (justified by erasure)
5. Unverified components: parser, CLI, pretty-printer

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

## Code Generator Correctness Proofs

### Layered postulate strategy

When proving complex theorems about machine execution, introduce helper postulates that capture key execution properties, then build actual proofs on top of them:

```agda
-- Layer 1: Single-instruction execution helpers (postulated)
postulate
  run-single-mov : ∀ (s : State) (dst src : Reg) →
    halted s ≡ false → pc s ≡ 0 →
    ∃[ s' ] (run (mov (reg dst) (reg src) ∷ []) s ≡ just s'
           × readReg (regs s') dst ≡ readReg (regs s) src
           × halted s' ≡ true)

-- Layer 2: Multi-instruction sequence helpers (postulated, use layer 1)
postulate
  run-inl-seq : ∀ {A B} (s : State) → ... →
    ∃[ s' ] (run (compile-x86 {A} {A + B} inl) s ≡ just s' × ...)

-- Layer 3: Actual proofs (use layers 1-2)
compile-inl-correct : ∀ {A B} (a : ⟦ A ⟧) → ...
compile-inl-correct a = ... run-inl-seq ... encode-inl-construct ...
```

This separates "what needs to be true about execution" from "how we compose those facts".

### Encoding axioms bridge semantics and machine state

When bridging abstract semantics with concrete machine representation, encoding axioms form the interface:

```agda
postulate
  -- Deconstruction: reading from encoded values
  encode-pair-fst : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (m : Memory) →
    readMem m (encode (a , b)) ≡ just (encode a)

  -- Construction: building encoded values from memory layout
  encode-pair-construct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (p : Word) (m : Memory) →
    readMem m p ≡ just (encode a) →
    readMem m (p + 8) ≡ just (encode b) →
    p ≡ encode (a , b)
```

Construction axioms are essential for stack-allocated values (pairs, sums) where code builds the encoding rather than receiving it.

### Tuple projection requires careful counting

When dealing with existential witnesses with many components, projection requires careful `proj₂` chains:

```agda
-- Helper returns 5-tuple: (s', (run-eq, (halt-eq, (rax-eq, (tag-eq, val-eq)))))
helper : ∃[ s' ] (run ... ≡ just s'
                × halted s' ≡ true
                × readReg (regs s') rax ≡ ...
                × readMem ... ≡ just 0
                × readMem ... ≡ just ...)

-- Extracting components:
s' = proj₁ helper
run-eq = proj₁ (proj₂ helper)
halt-eq = proj₁ (proj₂ (proj₂ helper))
rax-eq = proj₁ (proj₂ (proj₂ (proj₂ helper)))
tag-eq = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ helper))))
val-eq = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ helper))))
```

### Provide explicit type arguments to avoid metavariables

When pattern matching on constructors with implicit type arguments, provide explicit annotations:

```agda
-- BAD: Unsolved metavariables
codegen-x86-correct (curry f) x = curry-correct f x
  where postulate curry-correct : ∀ {A B C} (f : IR (A * B) C) (x : ⟦ A ⟧) → ...

-- GOOD: Explicit type annotations
codegen-x86-correct {A} {B ⇒ C} (curry {A} {B} {C} f) x = curry-correct f x
  where postulate curry-correct : (f : IR (A * B) C) (x : ⟦ A ⟧) → ...
```

### Case split on sum types in proofs

For theorems about case analysis, case split on the input in the proof:

```agda
compile-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A ⟧ ⊎ ⟦ B ⟧) → ...

-- Case split matches semantic case analysis
compile-case-correct f g (inj₁ a) = ... run-case-inl ...
compile-case-correct f g (inj₂ b) = ... run-case-inr ...
```

This mirrors the structure of `eval [ f , g ]` which pattern matches on the sum.

### Main theorem order matters

The main correctness theorem must come after all per-generator theorems:

```agda
-- Per-generator proofs first
compile-id-correct : ...
compile-fst-correct : ...
-- ... all other generator proofs ...

-- Main theorem last (uses all generator proofs)
codegen-x86-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) → ...
codegen-x86-correct id x = compile-id-correct x
codegen-x86-correct fst (a , b) = compile-fst-correct a b
-- ... case for each IR constructor ...
```

### `with` abstraction blocks definitional equality in step/exec proofs

When proving execution properties, Agda's `with` abstraction prevents direct computation. The `step` and `execInstr` functions use `with` to pattern match on runtime values:

```agda
-- In Semantics.agda
step prog s with halted s
... | true = just s
... | false with fetch prog (pc s)
...   | nothing = just (record s { halted = true })
...   | just instr = execInstr prog s instr

execInstr prog s (mov dst src) with readOperand s src
... | nothing = nothing
... | just v = just (record (writeOperand s dst v) { pc = pc s + 1 })
```

This means proofs cannot use `refl` directly even when the computation should obviously succeed. Instead, introduce postulates at this layer and build proofs on top:

```agda
-- Postulate the low-level step behavior (blocked by with)
postulate
  step-exec : ∀ (prog : List Instr) (s : State) (i : Instr) →
    halted s ≡ false →
    fetch prog (pc s) ≡ just i →
    step prog s ≡ execInstr prog s i

-- Derive specific cases from the general postulate
step-exec-0 : ∀ (i : Instr) (is : List Instr) (s : State) →
  halted s ≡ false → pc s ≡ 0 →
  step (i ∷ is) s ≡ execInstr (i ∷ is) s i
step-exec-0 i is s h-false pc-0 =
  step-exec (i ∷ is) s i h-false (subst (λ p → fetch (i ∷ is) p ≡ just i) (sym pc-0) refl)

-- Build higher-level proofs using exec lemmas
exec-two-steps : ∀ (n : ℕ) (prog : List Instr) (s s1 s2 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ true →
  exec (suc (suc n)) prog s ≡ just s2
```

The key insight: postulates at the `with`-boundary are unavoidable without rewriting the operational semantics, but everything above that layer can be proven by composition. This gives a clean separation between "trusted execution semantics" and "compositional proof structure".

### Handle special IR cases explicitly

Some IR constructors need special handling in the main theorem:

```agda
-- Initial: no inputs exist (Void has no inhabitants)
codegen-x86-correct initial ()  -- absurd pattern

-- Terminal: need to connect rax=0 with encode tt
codegen-x86-correct terminal x =
  let (s , run-eq , rax-0) = compile-terminal-correct x
  in s , run-eq , trans rax-0 (sym encode-unit)

-- Curry/apply: remain postulated (future work)
codegen-x86-correct (curry f) x = curry-correct f x
  where postulate curry-correct : ...
```
