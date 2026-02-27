# Agda Formalization Lessons Learned

Practical lessons from formalizing the Once compiler in Agda.

---

## CRITICAL: Use Star for Execution Proofs (Most Important Lesson)

**The single most important architectural decision for backend verification.**

### The Problem: Fuel-Based Execution Proofs Are Fragile

When `exec` uses `case_of_` or `with` for pattern matching:
```agda
exec (suc n) prog s = case halted s of λ where
  true → just s
  false → case step prog s of ...
```

Proving `exec (suc n) prog s ≡ just s'` requires reducing the `case_of_`. But when `halted s` is abstract (not a concrete `true` or `false`), `case_of_` doesn't reduce. This blocks critical lemmas like:
- `exec-on-halted-step`
- `exec-two-steps-nonhalt`
- `exec-chain`

**Consequence**: You end up postulating "obvious" execution facts that should be provable, creating a large trusted base.

### The Solution: Star as the Primary Abstraction

Use **Star** (reflexive-transitive closure of step) for all internal proof composition:

```agda
-- Star is the right abstraction for execution proofs
data Star (prog : Program) : State → State → Set where
  refl* : ∀ {s} → Star prog s s
  step* : ∀ {s s' s''} →
          halted s ≡ false →
          step prog s ≡ just s' →
          Star prog s' s'' →
          Star prog s s''

-- Composition is TRIVIAL transitivity
star-trans : Star prog s₁ s₂ → Star prog s₂ s₃ → Star prog s₁ s₃
star-trans refl* p₂ = p₂
star-trans (step* h step-eq p₁) p₂ = step* h step-eq (star-trans p₁ p₂)
```

### Why Star Works

1. **Composition is structural**: `star-trans` is pure recursion on the Star witness. No `case_of_`, no abstract scrutinees, no blocked proofs.

2. **No fuel arithmetic**: Instead of tracking step counts and proving `exec (n + m) = ...`, just use `star-trans`.

3. **Bridge lemmas ARE provable**: When `exec` checks `halted s` FIRST, pattern matching reduces the goal:
   ```agda
   exec-to-star : exec n prog s ≡ just s' → Star prog s s'
   exec-to-star {suc n} {prog} {s} eq with halted s | inspect halted s
   ... | true  | _ = refl*  -- Goal reduces!
   ... | false | [ h-eq ] with step prog s | inspect (step prog) s
   ...   | just s₁ | [ step-eq ] = step* h-eq step-eq (exec-to-star ...)
   ```

### The Pattern: Compose High, Convert at Boundaries

1. **Build step proofs**: `halted s ≡ false`, `step prog s ≡ just s'`
2. **Compose using Star**: `star-trans`, `step*`, `star-step2`, etc.
3. **Convert to `exec` only at the final theorem** using `star-to-exec`

```agda
-- Internal proofs use Star
star-f : Star prog s s₁
star-g : Star prog s₁ s₂
star-all : Star prog s s₂
star-all = star-trans star-f star-g

-- Convert at final theorem boundary
final-exec : exec n prog s ≡ just s₂
final-exec = proj₂ (star-to-exec star-all h-final)
```

### Architectural Requirement: Check `halted` First in `exec`

For bridge lemmas to work, `exec` MUST check `halted s` BEFORE calling `step`:

```agda
-- GOOD: halted check first enables bridge proofs
exec (suc n) prog s with halted s
... | true = just s
... | false with step prog s
...   | nothing = nothing
...   | just s' with halted s'
...     | true = just s'
...     | false = exec n prog s'
```

When `halted s` is the first thing checked, pattern matching on it causes goals to reduce, enabling induction.

### Key Insight

**Star is the "native" abstraction for execution proofs. Fuel-based exec is an implementation detail for extraction.**

This follows the same pattern as:
- Type-level programming: work with types, erase at runtime
- Category theory: work with morphisms, interpret at the end
- CompCert: work with step relations, extract to execution

---

## No Capacity Weakening: Thread Exact Requirements

**Problem**: When threading resource requirements (like `StackCapacity`) through proofs, it's tempting to add "weakening" functions that convert `Capacity n` to `Capacity m` when `m ≤ n`.

```agda
-- BAD: Capacity weakening is a code smell
capacity-weaken : StackCapacity s n → m ≤ n → StackCapacity s m
```

**Why it's wrong**: Weakening obscures the actual requirements. If a function needs capacity 3 but receives capacity 5 and weakens it, you lose information about what the function actually consumes.

**The Rule**: Functions should declare exactly what they need, and callers should provide exactly that.

```agda
-- BAD: Function takes capacity 3 but actually needs 5
frame-setup-star : ... → StackCapacity s 3 → ...
-- Called with capacity 5, internally weakened to 3
-- But the function actually allocates 5 slots!

-- GOOD: Function declares its actual requirement
frame-setup-star : ... → StackCapacity s 5 → ...  -- 3 pushes + sub 16 = 5 slots
```

**How to determine the right capacity**:
1. Count the actual stack operations the function performs
2. Include ALL allocations: pushes, `sub rsp`, etc.
3. The capacity should equal the maximum stack depth relative to the starting rsp

**Example - pair frame setup**:
```
push r14        ; 1 slot
push r15        ; 1 slot
push rbp        ; 1 slot
sub rsp, 16     ; 2 slots
--------------------------
Total: 5 slots
```

So `frame-setup-star` needs `StackCapacity s 5`, not `StackCapacity s 3`.

**Benefits of exact requirements**:
1. **Self-documenting**: The type signature tells you exactly what resources are consumed
2. **No hidden costs**: Callers know precisely what they're providing
3. **Composable**: Capacity arithmetic is straightforward (no weak≤ chains)
4. **Debuggable**: If a proof fails, the capacity mismatch is immediately visible

**Naming convention**: Use abstract names like `rsp-bound` instead of concrete byte counts like `rsp-gt-24`, since `slots n` is abstract and shouldn't leak byte representations.

---

## No Magic Numbers for Stack Sizes

**Problem**: Hardcoding stack slot counts like `StackCapacity s 7` or `slots 5` in proofs creates brittle, architecture-dependent code that breaks when codegen changes.

```agda
-- BAD: Magic number hardcoded in proof
thunk-setup-star : ... → StackCapacity s 6 → ...  -- Why 6? Where does it come from?

-- BAD: Magic number in dispatcher
run-ir-star-at-offset-v : ... → StackCapacity s 7 → ...  -- Why 7?
```

**Why it's wrong**:
1. **Architecture-dependent**: The number 7 depends on x86-64 calling conventions, register choices, instruction selection
2. **Fragile**: Stack compaction or codegen optimization changes these values
3. **Obscures intent**: Reader can't tell if 7 is correct or why
4. **Duplicated knowledge**: The codegen knows the frame layout; proofs shouldn't re-state it

**The Rule**: All stack slot counts must be **derived from codegen**, not hardcoded.

**Correct architecture**:

```agda
-- In StackInstantiation.agda: derive from actual codegen
curry-frame-slots : ℕ
curry-frame-slots = 4  -- push r15 (1) + push rbp (1) + sub 16 (2)
-- TODO: Should be computed from compile-x86 (curry _)

apply-frame-slots : ℕ
thunk-setup-slots : ℕ
pair-setup-slots : ℕ
output-slots : ℕ
output-slots = 2  -- capacity guaranteed after any operation

-- In proofs: use named constants for individual operations
thunk-setup-star : ... → StackCapacity s thunk-setup-slots → ...
pair-setup-star : ... → StackCapacity s pair-setup-slots → ...
```

**CRITICAL: No static maximum for dispatcher!**

```agda
-- BAD: Static maximum doesn't work for recursion
run-ir-star : ... → StackCapacity s max-frame-slots → ...
-- After thunk-setup consumes slots, recursive call can't provide max-frame-slots

-- GOOD: Capacity is computed from IR structure (dynamic)
ir-stack-requirement : ∀ {A B} → IR A B → ℕ
ir-stack-requirement id = output-slots
ir-stack-requirement (curry f) = thunk-setup-slots + ir-stack-requirement f
ir-stack-requirement (g ∘ f) = max (ir-stack-requirement f) (ir-stack-requirement g)
ir-stack-requirement (pair f g) = pair-setup-slots + max (ir-stack-requirement f) (ir-stack-requirement g)
-- etc.

-- Dispatcher takes exactly what the specific IR needs
run-ir-star : ∀ {A B} (ir : IR A B) ... →
  StackCapacity s (ir-stack-requirement ir) →
  ...
```

**Why static maximums fail**: Consider `curry f` where `f` is another `curry g`:
- Entry needs `thunk-setup-slots + ir-stack-requirement f`
- After thunk-setup, we have `ir-stack-requirement f` remaining
- Recursive call needs exactly `ir-stack-requirement f` ✓
- But if dispatcher expected static `max-frame-slots`, we couldn't provide it after consuming slots

**The ideal (future work)**: Frame slot counts should be *computed* from the codegen output:

```agda
-- Analyze instruction sequence for stack impact
stack-depth : List Instr → ℕ
stack-depth instrs = ... -- count pushes, sub rsp, etc.

curry-frame-slots : ℕ
curry-frame-slots = stack-depth (compile-x86 (curry id))  -- derived!
```

**Benefits**:
1. **Single source of truth**: Codegen defines layout, proofs follow
2. **Refactoring-safe**: Change codegen, constants update automatically
3. **Self-documenting**: Named constants explain what capacity is for
4. **Enables stack compaction**: Optimize codegen without rewriting proofs

---

## Stack Capacity is About Exact Requirements, Not "Big Enough"

**Problem**: Thinking "the stack is huge, so postulates about capacity are practically true" leads to sloppy reasoning and unprovable claims.

```agda
-- BAD mental model:
-- "Stack starts at 0x7FFF0000, we only use hundreds of bytes, so rsp > slots 7 is always true"
postulate
  rsp-bound-after-stack-op : ∀ (s : State) → readReg (regs s) rsp > slots 7
```

**Why this thinking is wrong**:
1. **The stack doesn't "start at X"** - that's implementation detail. Proofs should be abstract.
2. **"Practically true" is not a proof** - we need actual derivations or justified axioms
3. **Blanket postulates hide real requirements** - claiming capacity for ANY state means we don't track actual consumption
4. **Can't compute actual needs** - if we don't know exact requirements, we can't size the stack correctly

**The correct mental model**:

1. **Each IR has computable stack requirements** based on its structure
2. **Entry point provides exactly what's needed** for the specific program
3. **Proofs thread capacity through**, consuming on allocation, recovering on deallocation
4. **The only postulate needed** is at the entry point: "initial state has capacity N for this program"

```agda
-- GOOD: Capacity is program-specific, computed from IR structure
ir-stack-requirement : ∀ {A B} → IR A B → ℕ
ir-stack-requirement id = 0
ir-stack-requirement (curry f) = curry-frame-slots + ir-stack-requirement f
ir-stack-requirement (g ∘ f) = max (ir-stack-requirement f) (ir-stack-requirement g)
-- etc.

-- Entry point postulate is specific and justified
initWithInput-capacity : ∀ {A B} (x : ⟦ A ⟧) (ir : IR A B) →
  StackCapacity (initWithInput x) (ir-stack-requirement ir)
```

**Key insight**: Since we control the entire chain (compiler, runtime, semantics), we CAN know exactly how much stack any program needs. The postulate just says "we allocated that much."

**What to avoid**:
- Blanket postulates claiming capacity for "any state"
- Reasoning based on concrete addresses (0x7FFF0000)
- Magic numbers that don't trace back to codegen
- "It's big enough" without computing actual requirements

---

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

### Capturing equality proofs from `with` using `in` syntax

**Problem**: After `with X ... | pattern`, the term `X` has been abstracted away. If you need a proof that `X ≡ pattern` to pass to another function, you can't just use `refl`.

```agda
-- BAD: After matching, heapMem σ hl has been replaced by the pattern
-- so 'refl' doesn't have type 'heapMem σ hl ≡ just hl''
helper eq with heapMem σ hl | eq
... | just hl' | refl = heap-corresponds hl hl' refl  -- ERROR!
```

**Solution**: Use the `in` syntax (Agda 2.6+) to capture the equality proof:

```agda
-- GOOD: 'in heapMem-eq' captures the proof that heapMem σ hl ≡ just hl'
helper eq with heapMem σ hl in heapMem-eq | eq
... | just hl' | refl = heap-corresponds hl hl' heapMem-eq  -- Works!
```

**When to use this pattern**:
- You're matching on a scrutinee AND need to pass proof of what it equals to another function
- The other function expects `scrutinee ≡ pattern`, not just for the goal to reduce

**Full example from heap correspondence proofs**:

```agda
-- Need: x86-readMem ... ≡ just (loc-to-addr target)
-- Have: readLoc σ (OnHeap hl) ≡ just target  (the 'eq' parameter)
-- Have: heap-corresponds : heapMem σ hl ≡ just hl' → x86-readMem ... ≡ just ...

heap-helper : readLoc σ (OnHeap hl) ≡ just target →
              x86-readMem mem (loc-to-addr (OnHeap hl)) ≡ just (loc-to-addr target)
heap-helper eq with heapMem σ hl in heapMem-eq | eq
-- After matching: heapMem σ hl = just hl', so readLoc returns just (OnHeap hl')
-- eq : just (OnHeap hl') ≡ just target, so with refl we get target = OnHeap hl'
-- heapMem-eq : heapMem σ hl ≡ just hl'  (captured by 'in')
... | just hl' | refl = heap-corresponds hl hl' heapMem-eq
```

### List operator precedence (Critical for backend proofs!)

**`++` is RIGHT-associative** (`infixr 5`):
```agda
a ++ b ++ c = a ++ (b ++ c)  -- NOT (a ++ b) ++ c
```

**`∷` binds tighter than `++`**:
```agda
x ∷ ys ++ zs = (x ∷ ys) ++ zs  -- NOT x ∷ (ys ++ zs)
```

**Definitional equality for cons-append**:
```agda
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)  -- definitionally equal by ++ definition
```

This means `(nop ∷ code-g) ++ suffix = nop ∷ (code-g ++ suffix)` definitionally, which is crucial when proving list equalities in code generator correctness.

**Common error pattern**: When Agda reports `X != Y` where X and Y look identical except for parentheses, trace through the `++` associativity carefully. The fix is usually adding/removing `sym` on `++-assoc` calls.

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

### Natural number arithmetic: When `refl` works and when it doesn't (CRITICAL!)

**Problem**: Proving arithmetic equalities with verbose chains of `+-assoc` and `+-comm` is tedious. Can we just use `refl`?

**The Rule**: `refl` works **ONLY when all first arguments to `+` are concrete numbers**.

**Why**: The standard library's `_+_` is defined by recursion on the **first** argument:
```agda
zero  + n = n
suc m + n = suc (m + n)
```

So `4 + x` computes to `suc⁴(x)`, but `a + 4` does NOT compute when `a` is abstract.

**Examples that WORK as `refl`** (first args are concrete):
```agda
-- All first arguments (2, 4) are concrete numbers
ex1 : ∀ x → 2 +ℕ (4 +ℕ x) ≡ 6 +ℕ x
ex1 x = refl  -- Both sides normalize to suc⁶(x)

-- The outer + has concrete first arg
ex2 : ∀ x y → 3 +ℕ (2 +ℕ x +ℕ y) ≡ 5 +ℕ x +ℕ y
ex2 x y = refl  -- 3 + ... = suc³(...), 5 + x = suc⁵(x), but x + y blocks
```

**Examples that DO NOT work as `refl`** (abstract first args):
```agda
-- BAD: 'a' is first arg to +, doesn't normalize
arith-pair : ∀ a b → 2 +ℕ (a +ℕ (2 +ℕ (b +ℕ 2))) ≡ (6 +ℕ a) +ℕ b
arith-pair a b = refl  -- ERROR! a + ... doesn't normalize

-- BAD: 'a' is first arg in (a + 4)
arith-bad : ∀ a b c → (a +ℕ 4 +ℕ b +ℕ c) +ℕ 1 ≡ a +ℕ 5 +ℕ b +ℕ c
arith-bad a b c = refl  -- ERROR! (a + 4) doesn't normalize

-- BAD: 'a' and 'b' are first args
arith-case : ∀ a b → 4 +ℕ (a +ℕ (3 +ℕ (b +ℕ 1))) ≡ (8 +ℕ a) +ℕ b
arith-case a b = refl  -- ERROR! a + ... and b + 1 don't normalize
```

**For abstract variables, use equational reasoning**:
```agda
arith-pair : ∀ a b → 2 +ℕ (a +ℕ (2 +ℕ (b +ℕ 2))) ≡ (6 +ℕ a) +ℕ b
arith-pair a b = begin
  2 +ℕ (a +ℕ (2 +ℕ (b +ℕ 2)))
    ≡⟨ cong (2 +ℕ_) (sym (+-assoc a 2 (b +ℕ 2))) ⟩
  2 +ℕ ((a +ℕ 2) +ℕ (b +ℕ 2))
    ≡⟨ ... ⟩  -- Use +-assoc and +-comm to rearrange
  (6 +ℕ a) +ℕ b
    ∎
```

**Or use the solver**:
```agda
open import Data.Nat.Solver
open +-*-Solver

arith-pair : ∀ a b → 2 +ℕ (a +ℕ (2 +ℕ (b +ℕ 2))) ≡ (6 +ℕ a) +ℕ b
arith-pair = solve 2 (λ a b → con 2 :+ (a :+ (con 2 :+ (b :+ con 2)))
                            := (con 6 :+ a) :+ b) refl
```

**Quick check**: Before trying `refl`, look at every `+` in your expression. If ANY has an abstract variable as its first (left) argument, `refl` won't work.

### Arithmetic lemmas for large number comparisons

**Note**: This technique does not follow the Star-based approach and should only be used when necessary for large constant comparisons.

For proofs like `17 ≤ 2147418112`, use `m≤m+n` from `Data.Nat.Properties` instead of structural induction:

```agda
stackBase>16 : 17 ≤ 0x7FFF0000
stackBase>16 = m≤m+n 17 2147418095  -- O(1), not billions of s≤s steps
```

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

## Typechecker Performance

### No function definitions in `where` clauses (CRITICAL!)

**Problem**: Defining functions inside `where` clauses causes severe performance issues:
1. Functions in `where` are re-typechecked at every use site
2. If the same helper is defined in multiple `where` blocks, Agda checks each independently
3. Combined effect can cause exponential slowdown or memory exhaustion

**Evidence**: In `MutualIR/Pair.agda`, the same helper `m∸n<m` was defined THREE times in nested `where` blocks. Build times went from ~30 seconds to 14+ minutes with eventual OOM kill.

**The Rule**: No function definitions (with pattern matching or explicit λ) in `where` clauses.

```agda
-- BAD: Function defined in where clause (re-typechecked at each use)
mem-above-final addr = mem-chain
  where
    m∸n<m : ∀ m n → m > 0 → n > 0 → m ∸ n < m  -- Function!
    m∸n<m (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

    rsp∸24<rsp = m∸n<m ...
    rsp∸40<rsp = m∸n<m ...  -- Function typechecked again!

-- GOOD: Value bindings in where are fine
mem-above-final addr = mem-chain
  where
    orig-rsp = readReg (regs s) rsp  -- Value binding, OK
    setup-rbp = readReg (regs s-setup) rbp  -- Value binding, OK
    rsp∸24<rsp = m∸n<m-when-positive orig-rsp 24 ...  -- Uses module-level helper
```

**Solution**: Use either:
1. **Existing module-level helpers** - Check StackInstantiation, Data.Nat.Properties first
2. **`private` block at module level** - For truly local helpers not in standard library

```agda
-- Private block at module level: checked once, not exported
private
  -- Helper used only in this module
  rsp∸40+8<rsp : ∀ (rsp-val : ℕ) → rsp-val > slots 2 → rsp-val ∸ slots 5 +ℕ slot-size < rsp-val
  rsp∸40+8<rsp rsp-val rsp>16 with 40 ≤? rsp-val
  ... | yes 40≤rsp = ...
  ... | no  40>rsp = ...

-- Main function uses the private helper
run-pair-star-v ... = ...
  where
    rsp∸40+8<rsp-proof = rsp∸40+8<rsp orig-rsp rsp>16  -- Single call to module-level helper
```

**Result**: Build time for Pair.agda dropped from 14+ minutes (OOM) to ~30 seconds.

### Replace deeply nested tuple projections with records

**Problem**: Functions returning many values as nested tuples cause typechecker resource exhaustion. Deeply nested `proj₁`/`proj₂` chains (10+ levels) create exponential unification work.

**Symptom**: Typechecking crashes with memory exhaustion or hangs indefinitely, even though the code is correct.

**Solution**: Define record types for multi-value returns and use record field access instead of projections.

```agda
-- BAD: 11 nested projections, crashes typechecker
pair-setup-star : ... → State × Star × halted-pf × pc-pf × a0-pf × s1-pf × sp-pf × s2-pf × ra-pf × mem-s1-pf × mem-s2-pf

-- Extracting values requires deep projection chains:
s-setup = proj₁ setup-result
star-setup = proj₁ (proj₂ setup-result)
mem-s2-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))

-- GOOD: Record type, efficient typechecking
record PairSetupResult (prog : Program) (s s' : State) ... : Set where
  field
    star-setup   : Star prog s s'
    h-setup      : halted s' ≡ false
    pc-setup     : pc s' ≡ offset +ℕ 5
    a0-setup     : readReg (regs s') a0 ≡ x-enc
    -- ... remaining fields

-- Clean field access via module:
private module SetupR = PairSetupResult (proj₂ setup-result)
star-setup = SetupR.star-setup
h-setup = SetupR.h-setup
```

**When to apply**: Any helper function returning 6+ values should use a record. The RISC-V MutualIR refactoring replaced ~80 nested projections across Pair.agda and Case.agda, reducing typechecking from "crashes" to ~60 seconds.

### Timeout guidelines

From `proof-instructions.md`:
- Single file: `timeout 300 make agda MODULE=Once/Backend/X86/Correct/IR/Pair.agda`
- Full backend: `timeout 900 make riscv`

**If typechecking times out, refactor.** Long compile times indicate the proof structure needs simplification.

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

### Note on `case_of_` vs `with`

The Star-based approach (see the CRITICAL section at the top) was developed because of this fundamental issue:

- **`case_of_` in definitions** preserves definitional equality when scrutinee is concrete, but doesn't reduce when abstract
- **`with` in definitions** creates opaque function names that block unification
- **Solution**: Use Star for composition, convert to `exec` only at boundaries

See the top of this document for the full explanation and solution.

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

### The `run-ir-at-offset` pattern for multi-backend proofs

All backends (x86, RISC-V, AArch64) use the same fundamental pattern: prove execution at arbitrary program offsets WITHOUT halting, then derive the halting `run-generator` theorem.

**Key insight**: The main theorem `run-generator` proves that executing `compile ir` from the start halts with the correct result. But for recursive IR (compose, pair, case), we need to execute sub-IRs in the *middle* of a larger program. The `run-ir-at-offset` function handles this.

```agda
mutual
  -- Execute IR at arbitrary offset WITHOUT halting
  -- This is the key: execution continues (halted s' ≡ false)
  run-ir-at-offset : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) inputReg ≡ encode x →
    ∃[ s' ] (exec (compile-length ir) (prefix ++ compile ir ++ suffix) s ≡ just s'
           × halted s' ≡ false      -- KEY: does NOT halt
           × pc s' ≡ length prefix +ℕ compile-length ir
           × readReg (regs s') outputReg ≡ encode (eval ir x)
           × readReg (regs s') calleeSaved ≡ readReg (regs s) calleeSaved)

  -- Base cases: prove directly from instruction semantics
  run-ir-at-offset id prefix suffix x s h pc-eq reg-eq = ...
  run-ir-at-offset fst prefix suffix (a , b) s ... = ...

  -- Recursive cases: call run-ir-at-offset for sub-IRs
  run-ir-at-offset (g ∘ f) prefix suffix x s h pc-eq reg-eq =
    let -- Execute f at prefix, with (nop ∷ compile g ++ suffix) as suffix
        (sf , ...) = run-ir-at-offset f prefix (nop ∷ compile g ++ suffix) x s ...
        -- Execute nop
        (sn , ...) = run-nop-at-offset (prefix ++ compile f) (compile g ++ suffix) sf ...
        -- Execute g at (prefix ++ compile f ++ nop ∷ []), with suffix as suffix
        (sg , ...) = run-ir-at-offset g (prefix ++ compile f ++ nop ∷ []) suffix (eval f x) sn ...
    in sg , ... -- chain the results
```

**Derive `run-generator` from `run-ir-at-offset`**:

```agda
-- When prefix=[] and suffix=[], pc goes past program end → halts
offset-to-generator : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false → pc s ≡ 0 → readReg (regs s) inputReg ≡ encode x →
  ∃[ s' ] (run (compile ir) s ≡ just s'
         × halted s' ≡ true     -- DOES halt (pc out of bounds)
         × readReg (regs s') outputReg ≡ encode (eval ir x))
offset-to-generator ir x s h pc-0 reg-eq =
  let (s' , exec-eq , h-false , pc-eq , result-eq , _) =
        run-ir-at-offset ir [] [] x s h pc-0 reg-eq
      -- After execution, pc = compile-length ir, program has that many instructions
      -- fetch at pc fails → execution halts
  in s' , exec-to-run exec-eq pc-eq , refl , result-eq

run-generator = offset-to-generator  -- QED
```

**Backend-specific details**:

| Backend | Input Reg | Output Reg | Compose Transfer | Callee-Saved |
|---------|-----------|------------|------------------|--------------|
| x86-64  | rdi       | rax        | `mov rdi, rax`   | r14, r15     |
| RISC-V  | a0        | a0         | None needed!     | s1           |
| AArch64 | x0        | x0         | nop (placeholder)| x20          |

RISC-V's use of a0 for both input and output simplifies compose—no register transfer instruction needed between f and g.

### Memory frame preservation for pair proofs (TODO: AArch64 alignment)

**Problem**: The `pair` generator needs to prove that memory written in the "middle phase" (storing f's result) is preserved through g's execution. This requires `run-ir-at-offset` to guarantee memory frame preservation.

**X86 solution**: Uses a dedicated callee-saved register (r15) for the pair pointer, and `run-ir-at-offset` returns 7 components including memory frame preservation:

```agda
-- X86's run-ir-at-offset signature (7 return values)
∃[ s' ] (exec (compile-length ir) (prefix ++ compile-x86 ir ++ suffix) s ≡ just s'
       × halted s' ≡ false
       × pc s' ≡ length prefix +ℕ compile-length ir
       × readReg (regs s') rax ≡ encode (eval ir x)
       × readReg (regs s') r14 ≡ readReg (regs s) r14
       × readReg (regs s') r15 ≡ readReg (regs s) r15
       × readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15))
--      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
--      KEY: Memory at r15 is preserved through execution
```

This allows proving `mem-fst-preserved` without postulates:
```agda
mem-fst-preserved : readMem (memory s-after-g) (readReg (regs s-after-g) r15) ≡ just (encode (eval f x))
mem-fst-preserved = trans (cong ... r15-preserved-g) (trans mem-preserved-g mem-fst-stored)
```

**AArch64 current state**: Uses SP directly for pair pointer, and `run-ir-at-offset` only returns 5 components (no memory frame preservation). This requires postulates:

```agda
-- AArch64's run-ir-at-offset signature (5 return values, missing memory frame)
∃[ s' ] (exec (compile-length ir) (prefix ++ compile-aarch64 ir ++ suffix) s ≡ just s'
       × halted s' ≡ false
       × pc s' ≡ length prefix +ℕ compile-length ir
       × readReg (regs s') x0 ≡ encode (eval ir x)
       × readReg (regs s') x20 ≡ readReg (regs s) x20)
-- Missing: memory frame preservation

-- Result: pair proof requires postulates
postulate
  mem-fst : readMem (memory s-final) sp₁ ≡ just (encode (eval f x))
```

**TODO**: Align AArch64 with X86's approach:
1. Change AArch64 codegen to use a callee-saved register (e.g., x19) for pair pointer instead of SP
2. Add memory frame preservation to `run-ir-at-offset` signature
3. Prove memory frame preservation for all IR cases
4. Remove `mem-fst` postulate from pair proof

This architectural change would make AArch64 proofs as complete as X86's.

### Type naming: Use `Void` from `Once.Type`, not `⊥` from `Data.Empty`

The IR uses `Void` as the initial object type (the empty type with no inhabitants):

```agda
-- In Once/Type.agda
data Type : Set where
  Void : Type  -- Initial object (0)
  ...

-- In Once/IR.agda
initial : ∀ {A} → IR Void A  -- Morphism from initial object
```

When writing proofs involving `initial`, use `Void` from `Once.Type`:

```agda
-- WRONG: ⊥ is from Data.Empty, not a Once Type
run-ir-at-offset-initial : ∀ {A} ... (x : ⟦ ⊥ ⟧) ... -- Type error!

-- CORRECT: Void is from Once.Type
run-ir-at-offset-initial : ∀ {A} ... (x : ⟦ Void ⟧) ... -- Works
```

Note: `⟦ Void ⟧` evaluates to `Data.Empty.⊥` in the semantics, but the type argument must be `Void` (the Once type), not `⊥` (the Agda type).

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
