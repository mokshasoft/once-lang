# Exchange Problem: Analysis and Alternative Approaches

## The Question

**Do we even need the `exchange` proof?** And if so, **why can't we use a different approach?**

## What We're Currently Trying to Prove

```agda
exchange : ∀ {n} {Γ : SCtx n} {A B C : Type}
         → SExpr (Γ S, B) C → SExpr ((Γ S, A) S, B) C
```

**In English**: "If I have an intrinsically-typed expression of type C in context (Γ, B), I can **transform** it into an expression of type C in context ((Γ, A), B)."

This is needed for:
- `weaken` in TypeCheck.Elaborate when going under binders
- Inserting types into contexts during type checking/elaboration

**The Problem**: We're trying to **transform intrinsically-typed expressions**, which embeds context sizes in types. The rewrite mechanism for arithmetic normalization conflicts with pattern matching on these GADTs.

## How Other Verified Compilers Handle This

### Cogent (Isabelle/HOL)

**Approach**: Extrinsic typing with weakening as a **relation**, not a transformation.

```isabelle
inductive weakening_comp :: "kind env ⇒ type option ⇒ type option ⇒ bool" where
  none : "weakening_comp K None None"
| keep : "⟦ K ⊢ t wellformed ⟧ ⟹ weakening_comp K (Some t) (Some t)"
| drop : "⟦ K ⊢ t :κ k; D ∈ k ⟧ ⟹ weakening_comp K (Some t) None"

definition weakening :: "kind env ⇒ ctx ⇒ ctx ⇒ bool" where
  "weakening K ≡ list_all2 (weakening_comp K)"
```

**Key insight**: They prove "**if** expression `e` has type `t` in context `Γ`, **then** `e` has type `t` in weaker context `Γ'`."

They **don't transform expressions** - expressions are untyped. Typing is a separate judgment.

**File**: `.refs/cogent/cogent/isa/Cogent.thy:581-587`

### CakeML (HOL4)

**Approach**: Also extrinsic typing with de Bruijn indices in types, not expressions.

```sml
Datatype:
 t =
   Tvar tvarN
 | Tvar_db num     (* deBruijn indexed type variables *)
 | Tapp (t list) type_ident
End
```

Expressions are separate from types - typing judgments relate them.

**File**: `.refs/cakeml/semantics/typeSystemScript.sml`

## Once's Unique Type System Philosophy

From `docs/compiler/decision-log.md` (D007):

> **"The generators have fixed, known types. The type of any expression is fully determined by how generators compose - there's no ambiguity, no choice for the compiler to make."**

> **"The expression alone determines the type. The signature is the programmer saying 'I believe this has type X' and the compiler verifying that belief."**

**Crucial property**: Types don't change semantics! From the decision log:

- The 12 categorical generators are the **sole truth**
- Types are **assertions** that the programmer understands the composition correctly
- Types are about ensuring valid categorical composition, **not semantic meaning**
- Semantics are defined on IR, which is already proven correct

## The Core Question

**Why are we using intrinsically-typed Surface expressions at all?**

Current architecture:
```
RawExpr → [inferElab] → SExpr (intrinsically-typed) → [elaborate] → IR → x86-64
```

The `SExpr` type embeds typing information:
```agda
data SExpr (Γ : SCtx n) : Type → Set where
  var  : (i : Fin n) → SExpr Γ (lookup Γ i)
  lam  : SExpr (Γ S, A) B → SExpr Γ (A ⇒ B)
  -- ...
```

**Benefits of intrinsic typing**:
1. ✅ Type checking and elaboration happen together
2. ✅ Impossible to construct ill-typed terms
3. ✅ Type safety "for free"

**Costs of intrinsic typing**:
1. ❌ Exchange proof is blocked by Agda type system limitations
2. ❌ Cannot pattern match after arithmetic rewrites
3. ❌ Complex context manipulation

## Alternative Approach: Extrinsic Typing

What if we followed Cogent/CakeML?

```agda
-- Untyped surface expressions (or simply-typed without context indices)
data SurfaceExpr : Set where
  var  : ℕ → SurfaceExpr
  lam  : SurfaceExpr → SurfaceExpr
  app  : SurfaceExpr → SurfaceExpr → SurfaceExpr
  -- ...

-- Typing judgment as a relation
data _⊢_∶_ : SCtx → SurfaceExpr → Type → Set where
  T-Var : ∀ {Γ i} → i < length Γ
        → Γ ⊢ var i ∶ lookup Γ i
  T-Lam : ∀ {Γ e A B}
        → (Γ , A) ⊢ e ∶ B
        → Γ ⊢ lam e ∶ (A ⇒ B)
  -- ...

-- Weakening as a RELATION, not a transformation
weakening : ∀ {Γ Γ' e A}
          → Γ ⊢ e ∶ A
          → Γ ⊆ Γ'      -- Context inclusion
          → Γ' ⊢ e ∶ A
```

**No exchange problem!** We don't transform expressions - we just prove they still type-check in a larger context.

### Trade-offs

**Pros**:
- ✅ No exchange/rewrite interaction issues
- ✅ Standard approach used by Cogent, CakeML
- ✅ Easier to prove weakening (it's just a lemma, not a transformation)
- ✅ Expressions remain simple

**Cons**:
- ❌ Lose "impossible to construct ill-typed terms" property
- ❌ Need separate typing judgment
- ❌ More complex to state soundness (need to thread typing judgment through)
- ❌ Major refactor of existing Once.TypeCheck.Elaborate module

## What Does Once Actually Need?

Let's trace through what we're verifying:

1. **TypeCheck.Elaborate**: `RawExpr → Maybe (Type × SurfaceExpr)`
   - Current: produces intrinsically-typed `SExpr`
   - Needed: prove that if it succeeds, the result is well-typed

2. **Surface.Elaborate**: `SurfaceExpr → IR` (already proven!)
   - Takes Surface syntax → categorical IR
   - Correctness already proven

3. **End-to-end**: Compose these to show `RawExpr → IR` preserves semantics

**Key observation**: The **semantics are defined on IR**, not Surface syntax!

Surface.Elaborate correctness theorem (from `Once/Surface/Correct.agda`):
```agda
elaborate-correct : ∀ e ρ
                  → ⟦ elaborate e ⟧ ρ ≡ ⟦ e ⟧ᵉ ρ
```

This says: elaboration from Surface → IR preserves semantics.

**The crucial question**: Do we need intrinsically-typed Surface expressions, or can we use extrinsically-typed ones and prove:
- Type inference produces valid typing judgments
- Elaboration preserves semantics (regardless of typing)

## Possible Solutions

### Option 1: Continue with Intrinsic Typing (Current Approach)
- **Path**: Solve the rewrite/pattern-match interaction
- **Methods**: proof-by-reflection, inspect idiom, view patterns, or manual equality transport
- **Risk**: May be fundamentally blocked by Agda limitations
- **Status**: Attempted, hit technical blocker

### Option 2: Switch to Extrinsic Typing (Cogent/CakeML Approach)
- **Path**: Refactor to separate expressions from typing judgment
- **Benefit**: Standard approach, proven to work
- **Cost**: Major refactoring, lose intrinsic type safety
- **Compatibility**: Once.Surface.Elaborate may need updates

### Option 3: Hybrid Approach
- **Path**: Use extrinsic typing only for TypeCheck.Elaborate, keep intrinsic for rest
- **Benefit**: Isolate the problem, minimize changes
- **Question**: How to bridge extrinsic → intrinsic at the boundary?

### Option 4: Question the Necessity
- **Path**: Examine whether we even need to verify TypeCheck.Elaborate
- **Reasoning**: If semantics are entirely in IR (already proven), and type checking is just validation, maybe we don't need to verify the type checker itself?
- **Risk**: Violates "full end-to-end verification" goal
- **Consideration**: What does the TCB include?

## Recommended Next Steps

1. **Clarify the verification goal**:
   - What exactly are we trying to prove end-to-end?
   - Is type checker correctness necessary, or is IR correctness sufficient?
   - What should be in the TCB?

2. **Examine Surface.Elaborate assumptions**:
   - Does it assume well-typed inputs?
   - Or does it work on any Surface syntax and preserve structure?

3. **Consider pragmatic scope**:
   - Once's philosophy: generators are truth, types are assertions
   - Perhaps type checker verification is beyond minimal TCB?
   - Focus: prove IR→x86 correctness (which is done!)

## Questions for Discussion

1. **What are we actually trying to guarantee with end-to-end verification?**
   - That well-typed programs compile correctly? (requires type checker verification)
   - That all programs compile correctly? (only need IR→x86, which we have!)

2. **Given Once's type system philosophy (types as assertions, generators as truth), is type checker verification necessary?**
   - The categorical semantics are in IR
   - Type checking ensures categorical composition is valid
   - But if we trust the type checker (unverified), does that violate the TCB?

3. **Would extrinsic typing align better with Once's philosophy?**
   - "The expression alone determines the type"
   - Suggests separation of expression and typing judgment
   - Typing is verification, not construction

4. **What's the minimal verification needed to claim "verified compilation"?**
   - Parser (unverified by design - covered)
   - Type checker (currently trying to verify - BLOCKED)
   - Elaboration Surface→IR (verified - ✓)
   - Optimization (verified - ✓)
   - Code generation IR→x86 (verified - ✓)
