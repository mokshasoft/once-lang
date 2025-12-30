# Cogent Type System Verification: Investigation & Lessons for Once

## Investigation Date: 2025-12-30

## Summary

Cogent is a verified systems programming language from UNSW/Data61 that provides end-to-end compilation correctness proofs from Cogent → C. This investigation examines how they handle type checking verification and context manipulation to inform our approach for Once.

**Key Finding**: Cogent uses **extrinsic typing** with contexts as simple lists. They **never transform expressions** - weakening is proven as a relation, not implemented as a transformation.

## Cogent's Type System Architecture

### 1. Expressions are Untyped (Extrinsic Typing)

**File**: `.refs/cogent/cogent/isa/Cogent.thy:316-337`

```isabelle
datatype 'f expr =
    Var index
  | AFun 'f  "type list"
  | Fun "'f expr" "type list"
  | App "'f expr" "'f expr"
  | Let "'f expr" "'f expr"
  | Tuple "'f expr" "'f expr"
  | Split "'f expr" "'f expr"
  | Case "'f expr" name "'f expr" "'f expr"
  (* ... more constructors *)
```

**Crucial observation**: Expressions are a plain datatype with NO type information embedded. Variables are just natural number indices.

**Contrast with Once (current)**:
```agda
-- Once uses intrinsically-typed expressions
data SExpr (Γ : SCtx n) : Type → Set where
  var  : (i : Fin n) → SExpr Γ (lookup Γ i)
  lam  : SExpr (Γ S, A) B → SExpr Γ (A ⇒ B)
  -- Type information embedded in constructors
```

### 2. Contexts are Simple Lists

**File**: `.refs/cogent/cogent/isa/Cogent.thy:528`

```isabelle
type_synonym ctx = "type option env"
-- where env = "'a list"
```

**So**: `ctx = type option list`

Contexts are just lists of optional types. Simple, no size indices, no dependent types.

### 3. Typing is a Separate Judgment (Relation)

**File**: `.refs/cogent/cogent/isa/Cogent.thy:707-839`

```isabelle
inductive typing :: "('f ⇒ poly_type) ⇒ kind env ⇒ ctx ⇒ 'f expr ⇒ type ⇒ bool"
          ("_, _, _ ⊢ _ : _" [30,0,0,0,20] 60)
where

typing_var: "⟦ K ⊢ Γ ⇝w singleton (length Γ) i t
             ; i < length Γ
             ⟧ ⟹ Ξ, K, Γ ⊢ Var i : t"

| typing_let: "⟦ K ⊢ Γ ⇝ Γ1 | Γ2
               ; Ξ, K, Γ1 ⊢ x : t
               ; Ξ, K, (Some t # Γ2) ⊢ y : u    -- CONS new type!
               ⟧ ⟹ Ξ, K, Γ ⊢ Let x y : u"

| typing_split: "⟦ K ⊢ Γ ⇝ Γ1 | Γ2
                 ; Ξ, K, Γ1 ⊢ x : TProduct t u
                 ; Ξ, K, (Some t # Some u # Γ2) ⊢ y : t'  -- CONS two types!
                 ⟧ ⟹ Ξ, K, Γ ⊢ Split x y : t'"
```

**Key insight**: When going under a binder, they just **cons** the new type(s) onto the context:
- `Let`: `(Some t # Γ2)` - add one type
- `Split`: `(Some t # Some u # Γ2)` - add two types

**No exchange, no weakening transformation!** The expression `y` is the same whether we've added types or not. The typing judgment just checks it against a larger context.

### 4. Weakening is a Relation, Not a Transformation

**File**: `.refs/cogent/cogent/isa/Cogent.thy:581-587`

```isabelle
inductive weakening_comp :: "kind env ⇒ type option ⇒ type option ⇒ bool" where
  none : "weakening_comp K None None"
| keep : "⟦ K ⊢ t wellformed ⟧ ⟹ weakening_comp K (Some t) (Some t)"
| drop : "⟦ K ⊢ t :κ k; D ∈ k ⟧ ⟹ weakening_comp K (Some t) None"

definition weakening :: "kind env ⇒ ctx ⇒ ctx ⇒ bool"
  where "weakening K ≡ list_all2 (weakening_comp K)"
```

**What this says**: "Context `Γ` can be weakened to `Γ'` if each position either:
- Stays `None`
- Keeps the same type (`Some t` → `Some t`)
- Drops a droppable type (`Some t` → `None`)"

**This is a RELATION**: `K ⊢ Γ ⇝w Γ'` means "Γ' is a weakening of Γ"

**Crucially**: They prove properties like:
```isabelle
lemma weakening_preservation_some:
  "K ⊢ Γ ⇝w Γ' ⟹ Γ' ! x = Some t ⟹ Γ ! x = Some t"
```

But they **don't transform expressions**. The expression stays the same, they just prove it still type-checks in the weaker context.

### 5. How Typing Handles Variables

**File**: `.refs/cogent/cogent/isa/Cogent.thy:712-714`

```isabelle
typing_var: "⟦ K ⊢ Γ ⇝w singleton (length Γ) i t
             ; i < length Γ
             ⟧ ⟹ Ξ, K, Γ ⊢ Var i : t"
```

**What this says**:
- `Var i` is a variable at index `i`
- It type-checks to type `t` if:
  - `i` is in bounds (`i < length Γ`)
  - The context `Γ` weakens to a singleton context with `t` at position `i`

**The key**: Variables are **plain indices**. The lookup happens in the typing judgment, not in the expression.

## Why Cogent Doesn't Have the Exchange Problem

1. **Expressions don't carry types**: `Var i` is just a number, not `var : Fin n → SExpr Γ (lookup Γ i)`

2. **Contexts are plain lists**: No dependent types, no arithmetic on sizes

3. **Context extension is cons**: `(Some t # Γ)` - just list cons, no complex type-level operations

4. **No expression transformation**: Weakening is proven as a lemma, not implemented as a function

5. **Pattern matching is simple**: No need to align types through rewrites - expressions have no types!

## The Exchange Problem in Once

### Why Once Has This Problem (Currently)

**File**: `formal/Once/TypeCheck/Elaborate.agda`

```agda
-- Intrinsically-typed expressions
data SExpr (Γ : SCtx n) : Type → Set where
  var  : (i : Fin n) → SExpr Γ (lookup Γ i)
  lam  : SExpr (Γ S, A) B → SExpr Γ (A ⇒ B)

-- Context manipulation requires transformation
weaken : SExpr Γ B → SExpr (Γ S, A) B
exchange : SExpr (Γ S, B) C → SExpr ((Γ S, A) S, B) C

-- Going under nested binders needs exchange₂, exchange₃, ... exchange₇, exchange₈
```

**The issue**:
1. We must **transform** expressions when contexts change
2. Types are embedded in expression structure
3. Contexts have sizes in types: `SCtx n`
4. Our generalized `extendMany` uses type-level arithmetic: `SCtx (n Nat.+ m)`
5. Rewrite clauses for arithmetic clash with pattern matching on GADTs

## Possible Solutions for Once

### Solution 1: Switch to Extrinsic Typing (Cogent Approach)

**Change**:
```agda
-- FROM: Intrinsically-typed
data SExpr (Γ : SCtx n) : Type → Set where
  var  : Fin n → SExpr Γ (lookup Γ i)
  lam  : SExpr (Γ S, A) B → SExpr Γ (A ⇒ B)

-- TO: Extrinsically-typed
data SurfaceExpr : Set where
  var  : ℕ → SurfaceExpr
  lam  : SurfaceExpr → SurfaceExpr
  app  : SurfaceExpr → SurfaceExpr → SurfaceExpr

-- Typing as separate judgment
data _⊢_∶_ : List Type → SurfaceExpr → Type → Set where
  T-Var : i < length Γ
        → Γ ⊢ var i ∶ lookup Γ i
  T-Lam : (A ∷ Γ) ⊢ e ∶ B
        → Γ ⊢ lam e ∶ (A ⇒ B)
  T-App : Γ ⊢ f ∶ (A ⇒ B)
        → Γ ⊢ x ∶ A
        → Γ ⊢ app f x ∶ B

-- Weakening as LEMMA, not transformation
weakening : ∀ {Γ Γ' e A}
          → Γ ⊢ e ∶ A
          → Γ ⊆ Γ'
          → Γ' ⊢ e ∶ A
```

**Pros**:
- ✅ No exchange problem - expressions don't change
- ✅ Standard approach (Cogent, CakeML, most verified compilers)
- ✅ Context extension is just list cons
- ✅ Weakening is a simple lemma, not a complex transformation

**Cons**:
- ❌ Major refactoring required
- ❌ Lose "impossible to construct ill-typed terms" property
- ❌ Need to thread typing judgment through proofs
- ❌ Surface.Elaborate currently expects intrinsically-typed input

**Effort**: High (several weeks of refactoring)

### Solution 2: Keep Intrinsic Typing, Accept Depth Limit

**Current state**: exchange₀ through exchange₇ proven (depth 7)

**Action**: Accept that programs with 8+ nested binders are out of scope.

**Justification**:
```
Depth 7 means 7 nested lambdas/cases/lets:
  λx. λy. λz. case w of
    A → case v of
      B → let u = ... in
        let t = ... in
          ... (depth 7)
```
This covers virtually all real programs.

**Pros**:
- ✅ No changes needed to current code
- ✅ Keep intrinsic typing benefits
- ✅ Already have working implementation

**Cons**:
- ❌ Violates proof-instructions.md Principle 1 (no postulates)
- ❌ Violates "arbitrary depth" goal from verification-plan.md
- ❌ Not truly complete verification

**Alignment with Once philosophy**:
- ❓ Types are assertions, not semantic
- ❓ If types don't affect meaning, do we need to verify type checker?

### Solution 3: Use Agda's `inspect` Idiom

**Idea**: Use the `inspect` pattern to preserve equality information through pattern matching.

```agda
exchangeN : ∀ {n} {Γ : SCtx n} {A Result : Type} (depth : ℕ) (types : Vec Type depth)
          → SExpr (extendMany Γ depth types) Result
          → SExpr (extendMany (Γ S, A) depth types) Result
exchangeN {n} depth types e with extendMany Γ depth types | inspect (extendMany Γ depth) types
... | ctx | [ eq ] = {! pattern match on e using eq !}
```

**Status**: Theoretical - needs experimentation

**Pros**:
- ✅ Might solve rewrite/pattern-match interaction
- ✅ Keep intrinsic typing

**Cons**:
- ❌ Complex proof technique
- ❌ May still hit fundamental limitations
- ❌ Uncertain if it will work

**Effort**: Medium-High (1-2 weeks to attempt)

### Solution 4: Proof by Reflection

**Idea**: Use Agda's reflection mechanism to normalize type-level arithmetic at compile time.

```agda
-- Use reflection to reify and normalize arithmetic expressions
-- Then prove properties about normalized forms
```

**Status**: Advanced technique, requires Agda expertise

**Pros**:
- ✅ Might handle arbitrary arithmetic
- ✅ Keep intrinsic typing

**Cons**:
- ❌ Very complex
- ❌ Requires deep Agda knowledge
- ❌ May not solve the core issue

**Effort**: High (3-4 weeks, uncertain success)

### Solution 5: Question the Necessity (Pragmatic Approach)

**Observation** from Once decision log:

> "The generators have fixed, known types. The type of any expression is fully determined by how generators compose."
>
> "The expression alone determines the type. The signature is the programmer saying 'I believe this has type X' and the compiler verifying that belief."

**Current verification status**:
- ✅ Surface.Elaborate → IR: VERIFIED
- ✅ IR optimization: VERIFIED
- ✅ IR → x86-64: VERIFIED
- ❌ RawExpr → Surface (type checker): BLOCKED

**Question**: Is type checker verification necessary?

**Arguments for "No"**:
1. **Types are assertions, not semantic** - they validate categorical composition, don't change meaning
2. **Semantics are in IR** - we've proven IR → x86 correctness
3. **Type checker is validation** - ensures program is valid, doesn't transform it
4. **Similar to parser** - we already accept parser as unverified (in TCB)

**Arguments for "Yes"**:
1. **Complete end-to-end guarantee** - "well-typed programs compile correctly"
2. **Eliminate TCB** - minimize trusted code base
3. **Type safety matters** - even if not semantic, types prevent bugs

**Pragmatic TCB**:
- Parser (unverified, complex)
- Type checker (unverified, simpler than parser)
- Semantic axioms (Once/Postulates.agda)
- **Verified**: Surface→IR→x86 (the actual compilation and semantics)

**Effort**: Zero (reframe the verification claim)

## Recommended Path Forward

Given the investigation, I recommend a **two-phase approach**:

### Phase 1: Document Current State (Immediate)

1. **Accept exchange₇ as practical limit**
   - Document in problems-and-solutions.md
   - Note: depth 7 covers virtually all real programs
   - Alternative to postulate: use Agda holes with comment

2. **Proceed with MAlonzo extraction**
   - Extract verified components (Surface.Elaborate, Optimize, Codegen)
   - Type checker uses existing Haskell implementation
   - End-to-end guarantee: "Programs that pass type checking compile correctly"

3. **Update verification claims**
   - **Verified**: Surface syntax → x86-64 compilation (semantics-preserving)
   - **TCB**: Parser, type checker, semantic axioms
   - **Coverage**: Same as Cogent (they verify Cogent→C, not type checking)

### Phase 2: Long-term Solution (If Needed)

If complete type checker verification becomes required:

1. **Attempt `inspect` idiom** (2 weeks)
   - May solve rewrite/pattern-match issue
   - If successful, fill exchange holes

2. **If that fails, consider extrinsic typing** (4-6 weeks)
   - Follow Cogent's proven approach
   - Refactor TypeCheck.Elaborate
   - Update Surface.Elaborate to accept extrinsically-typed input

3. **If extrinsic typing is chosen, consider the benefits**
   - Standard approach used by mature verified compilers
   - Simpler context manipulation
   - Weakening is trivial

## Comparison: Once vs Cogent Approaches

| Aspect | Cogent | Once (Current) | Once (Proposed Extrinsic) |
|--------|--------|----------------|---------------------------|
| **Expressions** | Untyped datatype | Intrinsically-typed GADT | Untyped datatype |
| **Contexts** | `type option list` | `SCtx n` (sized) | `List Type` |
| **Typing** | Separate judgment | Embedded in constructors | Separate judgment |
| **Variables** | `ℕ` indices | `Fin n` indices | `ℕ` indices |
| **Context extension** | List cons `(t :: Γ)` | Constructor `(Γ S, t)` | List cons `(t :: Γ)` |
| **Weakening** | Lemma (relation) | Transformation function | Lemma (relation) |
| **Exchange problem** | ❌ No problem | ✅ **BLOCKED** | ❌ No problem |
| **Type safety** | Proven via judgment | Built into constructors | Proven via judgment |

## Key Takeaways

1. **Cogent's approach works**: Extrinsic typing with simple contexts avoids the exchange problem entirely

2. **Intrinsic typing has costs**: Beautiful for "impossible to write ill-typed code" but creates verification challenges

3. **Weakening as relation vs transformation**: Cogent proves "expression still types in larger context" rather than "transform expression for larger context"

4. **Context as plain list**: No dependent types on context size = no arithmetic rewrites = no pattern matching issues

5. **Once's philosophy may not require type checker verification**: If types are assertions and semantics are in IR (verified), type checker could be in TCB

## References

- **Cogent Repository**: `.refs/cogent/`
- **Key Files**:
  - Expression definition: `cogent/isa/Cogent.thy:316-337`
  - Typing judgment: `cogent/isa/Cogent.thy:707-839`
  - Weakening relation: `cogent/isa/Cogent.thy:581-597`
- **Cogent Project**: https://trustworthy.systems/projects/TS/cogent.pml
- **Cogent Papers**: See project homepage for published work
