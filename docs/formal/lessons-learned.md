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

### Jump instructions simplify closure proofs

When generated code uses `jmp` to a hardcoded label that's beyond the program bounds (e.g., `jmp 400` in a 12-instruction program), the fetch at that PC fails and execution halts. This simplifies proofs because:

1. We don't need to trace through the thunk/closure code at runtime
2. The halt condition is triggered by out-of-bounds fetch, not `ret` or `ud2`
3. A local postulate can encapsulate the list-length proof

```agda
-- In run-curry-seq proof: jmp 400 sets pc=400, but program has ~12 instructions
-- fetch at 400 fails, causing immediate halt

step5 : step prog s4 ≡ just s5  -- s5 has pc=400 after jmp
step5 = trans (step-exec prog s4 (jmp 400) ...) (execJmp prog s4 400)

-- Local postulate: program is shorter than 400 instructions
fetch-fail : fetch prog 400 ≡ nothing
fetch-fail = fetch-at-400-fails prog
  where
    postulate
      fetch-at-400-fails : ∀ (p : List Instr) → fetch p 400 ≡ nothing
```

The postulate `fetch-at-400-fails` is safe because `compile-x86 (curry f)` produces approximately `12 + len(compile-x86 f)` instructions, which is always far less than 400 for reasonable programs. A full proof would require showing this bound holds for all IR terms.

### Use `exec-N-steps` helpers for multi-instruction sequences

When proving properties about N-instruction sequences followed by halt, create helpers like `exec-six-steps`:

```agda
exec-six-steps : ∀ (n : ℕ) (prog : List Instr) (s s1 s2 s3 s4 s5 s6 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  step prog s5 ≡ just s6 → halted s6 ≡ true →
  exec (suc (suc (suc (suc (suc (suc n)))))) prog s ≡ just s6
```

These compose using `trans` with earlier helpers (`exec-five-steps`, etc.).

### Mutual recursion in codegen correctness proofs

The remaining postulates (`run-generator`, `run-seq-compose`, `run-case-inl/inr`, `run-pair-seq`) form a mutually-dependent cluster:

1. `run-generator` needs to prove correctness for all IR constructors
2. For recursive constructors (`g ∘ f`, `[ f , g ]`, `⟨ f , g ⟩`), the proof needs:
   - The helper (e.g., `run-case-inl`) to handle instruction tracing
   - Recursive calls to `run-generator` for sub-IRs

This requires mutual induction:

```agda
mutual
  run-generator : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) → ...

  -- Base cases: direct proofs
  run-generator id x s ... = ... (mov rax, rdi)
  run-generator fst (a , b) s ... = ... (load from memory)
  run-generator inl a s ... = ... (uses run-inl-seq)

  -- Recursive cases: use helpers + induction hypotheses
  run-generator (g ∘ f) x s ... =
    let f-ih = run-generator f x s ...
        g-ih = run-generator g (eval f x) s' ...
    in run-seq-compose-helper f g x s f-ih g-ih

  run-generator [ f , g ] (inj₁ a) s ... =
    let f-ih = run-generator f a s' ...
    in run-case-inl-helper f g a s f-ih
```

The non-recursive helpers (`run-inl-seq`, `run-inr-seq`, `run-curry-seq`) can be proven independently because they don't involve nested IR execution. Recursive helpers must be part of the mutual block.

### Computed labels enable complete branch proofs

**Problem**: Placeholder label values (100, 200, 300, 400) in codegen cause proofs to fail because jump targets don't match actual instruction positions.

**Solution**: Use a `compile-length` function to compute instruction counts, then calculate actual jump targets:

```agda
-- Calculate the number of instructions generated for an IR morphism
compile-length : ∀ {A B} → IR A B → ℕ
compile-length id = 1
compile-length (g ∘ f) = (compile-length f + 1) + compile-length g
compile-length [ f , g ] = (8 + compile-length f) + compile-length g
compile-length (curry f) = 12 + compile-length f
-- ... etc for each constructor

-- Use computed labels in code generation
compile-x86 [ f , g ] =
  let len-f = compile-length f
      len-g = compile-length g
      right-branch = 5 + len-f      -- actual position of right branch
      end-label = (7 + len-f) + len-g  -- actual position of end
  in
  mov (reg r15) (mem (base rdi)) ∷
  cmp (reg r15) (imm 0) ∷
  jne right-branch ∷               -- computed, not placeholder
  mov (reg rdi) (mem (base+disp rdi 8)) ∷
  compile-x86 f ++
  jmp end-label ∷                  -- computed, not placeholder
  label right-branch ∷
  mov (reg rdi) (mem (base+disp rdi 8)) ∷
  compile-x86 g ++
  label end-label ∷ []
```

**Why this matters**: With computed labels, both branches are provable:
- `run-case-inl-id`: tag=0, `jne 6` not taken, executes left branch
- `run-case-inr-id`: tag=1, `jne 6` taken, jumps to correct position, executes right branch

Previously, `run-case-inr-id` was impossible because `jne 100` would jump out of bounds (program only had ~10 instructions).

**Key insight**: The `compile-length` function must be defined for all IR constructors and must exactly match the instruction count produced by `compile-x86`. Any mismatch causes proofs to fail with concrete instruction position mismatches.

## MAlonzo Extraction and Integration

### String equality explodes transitive dependencies

Adding decidable equality for types containing strings (like `TVar : String → Type`) pulls in massive dependency chains:

```agda
-- This single import...
open import Data.String.Properties using () renaming (_≟_ to _≟String_)

-- ...brings in ~180 additional modules including:
-- Data.List.*, Data.Nat.*, Algebra.*, Relation.Binary.*, Function.*
```

**Impact**: Our cabal file went from ~20 MAlonzo modules to ~200 modules.

**Mitigation options**:
1. Accept the dependency cost (chosen approach)
2. Use a simpler decidability mechanism (e.g., boolean equality without proofs)
3. Avoid string-indexed types in the verified core

### Type extensions cause unsolved metavariables in downstream proofs

Adding new constructors to the `Type` datatype breaks proofs that pattern match on types with implicit arguments:

```agda
-- Before: 7 type constructors, proofs worked
data Type : Set where
  Unit Void _*_ _+_ _⇒_ Eff Fix : ...

-- After: 11 type constructors, x86 proofs fail with unsolved metas
data Type : Set where
  Unit Void _*_ _+_ _⇒_ Eff Fix Int Str Buffer TVar : ...
```

**Why it happens**: Pattern matches like `compile-x86-correct {A} {B} ir x` can no longer infer `A` and `B` when there are more possible cases.

**Fix**: Provide explicit type annotations at every pattern match:

```agda
-- BAD: Ambiguous after type extension
codegen-x86-correct (curry f) x = ...

-- GOOD: Explicit type arguments
codegen-x86-correct {A} {B ⇒ C} (curry {A} {B} {C} f) x = ...
```

### Two-stage IR isolates proof impact

The Surface IR → Core IR architecture pays off during extension:

```
Surface IR (extended)  →  desugar  →  Core IR (unchanged)
      ↓                                      ↓
Type changes here              Optimizer proofs unaffected
```

When we added `Int`, `Str`, `Buffer`, `TVar` to `Type`:
- **Affected**: Type equality (`_≟Type_`), semantics (`⟦_⟧`)
- **Unaffected**: All optimizer proofs (they operate on Core IR structure, not type details)

This separation meant we could extend types without touching any optimization correctness proofs.

### MAlonzo erases types—use placeholders when converting back

MAlonzo-generated code erases type information. When converting Core IR back to Haskell IR:

```haskell
fromMAlonzoCoreIR :: MC.T_IR_4 -> H.IR
fromMAlonzoCoreIR ir = case ir of
  MC.C_id_8 -> H.Id H.TUnit  -- Type erased, use placeholder
  MC.C_fst_22 -> H.Fst H.TUnit H.TUnit  -- Both types erased
  MC.C__'8728'__16 mT g f ->
    H.Compose (fromMAlonzoCoreIR g) (fromMAlonzoCoreIR f)
    -- mT (middle type) is available but we ignore it
```

**Why placeholders work**: The Haskell backend re-infers types during code generation. The IR structure (which morphism, how composed) is preserved; only type annotations are lost.

### Cabal requires explicit MAlonzo module listing

All MAlonzo-generated modules must be explicitly listed in `other-modules`:

```cabal
other-modules:
    MAlonzo.RTE
    MAlonzo.Code.Once.Type
    MAlonzo.Code.Once.IR
    -- ... 200+ modules ...
    MAlonzo.Code.Data.String.Properties
```

**No automatic discovery**: GHC's linker fails with "undefined reference" if any module is missing.

**Maintenance burden**: After regenerating MAlonzo code, run:
```bash
find formal/_build/malonzo -name "*.hs" | \
  sed 's|.*/malonzo/||; s|\.hs$||; s|/|.|g' | sort
```
Then update the cabal file with any new modules.

### Type equality case explosion

Adding N new type constructors requires O(N²) new cases in decidable equality:

```agda
-- Each new type needs comparison with ALL existing types
Int ≟Type Int = yes refl
Int ≟Type Unit = no (λ ())
Int ≟Type Void = no (λ ())
Int ≟Type (_ * _) = no (λ ())
-- ... 10 more cases for Int vs other types ...

-- Then Str vs all types, Buffer vs all types, TVar vs all types...
```

For our 4 new types + 7 existing = 11 total types, we added ~100 new cases.

**Alternative**: Use a type universe with generic decidable equality, but this changes the API significantly.
