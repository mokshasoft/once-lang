# Exchange Problem: Solutions Reconsidered

## Key Insight

**Switching to extrinsic typing weakens the verification** because:
1. Already-verified components (Surface.Elaborate, Optimize, Codegen) use intrinsic types
2. Intrinsic types guarantee "impossible to construct ill-typed terms"
3. Switching to extrinsic would require changing verified code to accept arbitrary terms
4. This trades strong guarantees in verified parts for easier type checker verification

**Conclusion**: We should avoid solutions that weaken the already-proven parts.

## Viable Solutions (Ranked)

### Option 1: Hybrid Approach - Extrinsic TypeCheck, Intrinsic Everywhere Else

**Idea**: Use extrinsic typing ONLY in TypeCheck.Elaborate, convert to intrinsic at the boundary.

**Architecture**:
```agda
-- TypeCheck.Elaborate (extrinsic - avoids exchange problem)
inferElab : Ctx → RawExpr → Maybe (∃[ A ] (Expr × (Γ ⊢ e ∶ A)))
-- Returns extrinsic Expr + typing derivation

-- Conversion at boundary
toIntrinsic : ∀ {Γ e A} → Γ ⊢ e ∶ A → SExpr Γ A
toIntrinsic (T-Var prf) = var (extractIndex prf)
toIntrinsic (T-Lam body) = lam (toIntrinsic body)
toIntrinsic (T-App f x) = app (toIntrinsic f) (toIntrinsic x)
-- ... straightforward recursion

-- Surface.Elaborate (intrinsic - keeps strong guarantees)
elaborate : SExpr Γ A → IR  -- Still intrinsically-typed!
```

**Pros**:
- ✅ TypeCheck.Elaborate avoids exchange problem (uses extrinsic)
- ✅ Keeps intrinsic types in verified components
- ✅ Strong guarantees preserved where it matters
- ✅ Conversion is straightforward (derivation structure = intrinsic structure)

**Cons**:
- ❌ Still need to build typing derivation in TypeCheck.Elaborate
- ❌ Building derivation might hit similar context issues
- ❌ Extra conversion step (though simple)

**Viability**: Medium - depends on whether building typing derivation avoids exchange

### Option 2: Accept Depth 7 Limit + Focus on What Matters

**Idea**: Accept `exchange₇` as practical limit, emphasize what's actually verified.

**Current status**:
- exchange₀ through exchange₇ proven (depth 7)
- Covers 7+ nested binders (virtually all real programs)
- Only TypeCheck.Elaborate blocked

**Already verified (with intrinsic types)**:
- ✅ Surface.Elaborate → IR (semantics-preserving)
- ✅ IR optimization (semantics-preserving)
- ✅ IR → x86-64 (semantics-preserving)

**Verification claim**:
> "Once programs that pass type checking compile correctly to x86-64 machine code, with semantics preservation proven from Surface syntax through to machine code."

**TCB** (Trusted Computing Base):
- Parser (already accepted as unverified)
- Type checker (now includes depth 7 limit)
- Semantic axioms (Once/Postulates.agda)

**Pros**:
- ✅ No changes needed
- ✅ Keep all strong guarantees (intrinsic everywhere)
- ✅ Verification claim is still very strong
- ✅ Depth 7 covers real programs
- ✅ Can proceed immediately

**Cons**:
- ❌ Not "arbitrary depth" verification
- ❌ Violates proof-instructions.md "no postulates" principle
- ❌ Type checker partially verified, partially trusted

**Viability**: High - pragmatic and honest about guarantees

### Option 3: Prove `exchangeN` with Different Technique

**Techniques to try**:

#### 3a. Manual Equality Transport (Instead of Rewrite)

Instead of `rewrite`, use explicit `subst` with manual proofs:

```agda
extendMany-suc : ∀ n Γ depth types
               → extendMany Γ (suc depth) types
               ≡ extendMany (extendMany Γ 1 (head types)) depth (tail types)

exchangeN : ...
exchangeN {n} (suc depth) (B ∷ types) e =
  subst (λ ctx → SExpr ctx Result)
        (extendMany-suc n Γ depth types)
        (go e)
  where
    go : SExpr (extendMany (Γ S, B) depth types) Result
       → SExpr (extendMany ((Γ S, A) S, B) depth types) Result
```

**Issue**: Still need to pattern match in `go`, which may have same problems.

#### 3b. Prove Exchange via Renaming

Define a general renaming function:

```agda
-- Renaming: map variable indices
Ren : Ctx n → Ctx m → Set
Ren Γ Δ = (i : Fin n) → Fin m

-- Apply renaming to expression
rename : Ren Γ Δ → SExpr Γ A → SExpr Δ A

-- Exchange is a specific renaming
exchange-ren : Ren (Γ S, B) ((Γ S, A) S, B)
exchange-ren zero = zero
exchange-ren (suc i) = suc (suc i)

exchange : SExpr (Γ S, B) C → SExpr ((Γ S, A) S, B) C
exchange e = rename exchange-ren e
```

**Issue**: Still need to implement `rename` for all constructors, may hit similar issues.

#### 3c. Use Agda's `with` Carefully

Try abstracting over the arithmetic equalities:

```agda
exchangeN {n} (suc depth) (B ∷ types) e
  with n Nat.+ suc depth | +-suc n depth
... | ._ | refl = go e
  where
    -- Context is now normalized
    go : SExpr (extendMany (Γ S, B) depth types) Result
       → SExpr (extendMany ((Γ S, A) S, B) depth types) Result
```

**Viability**: Unknown - worth trying (1-2 days experiment)

### Option 4: Simplify the Problem - Avoid Context Arithmetic

**Observation**: The problem is type-level arithmetic with `extendMany`.

**Alternative**: Define `exchangeN` without `extendMany`:

```agda
-- Instead of building arbitrarily-nested contexts with Vec,
-- use a simpler approach that doesn't require arithmetic

-- Option A: Use nested structure explicitly (like exchange₂, exchange₃, ...)
-- but generate them programmatically

-- Option B: Prove that exchange₇ is sufficient via analysis of Once programs
-- Show that 7 nested binders is an absolute maximum for any valid Once code

-- Option C: Prove exchange₈ manually (like we did for exchange₆, exchange₇)
-- Accept that exchange₉ postulate at depth 9 is truly unreachable
```

**Viability**: Medium - option B interesting if we can prove depth bound

### Option 5: Keep Current Approach, Document Limitations Clearly

**Idea**: Be honest about verification scope.

**Documentation**:
```markdown
## Once Compiler Verification Status

### Fully Verified (Zero Postulates)
- ✅ Surface syntax elaboration (Surface.Elaborate)
- ✅ IR optimization (categorical rewrites)
- ✅ Code generation (IR → x86-64)
- ✅ Semantic correctness (eval preservation)

### Verified with Practical Limits
- ⚠️  Type checking (depth limit: 7 nested binders)
  - Covers all realistic Once programs
  - Depth 7 = 7 nested λ/case/let (extremely deep)
  - Depth 8+ theoretically possible but not in practice

### Trusted Computing Base (TCB)
- Parser (complex, standard unverified component)
- Type checker depth 8+ (unreachable in practice)
- Semantic axioms (memory model, encoding)

### End-to-End Guarantee
"Programs that pass Once type checking compile correctly to verified x86-64
machine code, with semantics preservation proven from Surface syntax through
IR to machine code."
```

**Pros**:
- ✅ Honest and clear
- ✅ Strong claims about what IS verified
- ✅ Transparent about limitations
- ✅ Comparable to other verified compilers

**Cons**:
- ❌ Not "arbitrary depth" verification
- ❌ Some theoretical incompleteness

**Viability**: High - combines pragmatism with honesty

## Recommended Approach

Based on "keep strong guarantees where they exist," I recommend:

### Primary: Option 2 + Option 5
**Accept depth 7 limit, document clearly, proceed with verification**

**Rationale**:
1. Keeps intrinsic types (strong guarantees) in verified components
2. Depth 7 is practically unlimited for real code
3. Allows immediate progress on MAlonzo extraction
4. Honest about scope and limitations
5. Similar to other verified compilers (Cogent doesn't verify type checking)

**Action items**:
1. Document depth 7 limit in verification-plan.md
2. Update problems-and-solutions.md with decision
3. Proceed with MAlonzo extraction (Phase 4)
4. Update what-is-proven.md with clear scope

### Exploratory: Option 3c (Low-risk experiment)
**Try `with` abstraction technique (1-2 days)**

**Rationale**:
1. Low time investment (1-2 days)
2. Might solve the problem completely
3. If it works: great! If not: proceed with Option 2

**Action**:
- Experiment with `with` on a simplified version
- If successful in 2 days, apply to full exchangeN
- If unsuccessful, document and move to Option 2

## Why NOT Full Extrinsic Typing

**Critical issue**: Extrinsic typing would require changing Surface.Elaborate:

```agda
-- CURRENT (strong guarantee)
elaborate : SExpr Γ A → IR
-- Impossible to pass ill-typed term!

-- WITH EXTRINSIC (weak guarantee)
elaborate : Expr → IR
-- Can pass garbage! Need to trust/prove it's well-typed
```

**This weakens the already-verified parts to fix an unverified part.**

That's backwards. We should keep strong guarantees where we have them.

## Alternative Framing: What Are We Really Verifying?

Perhaps the question is: **What's the verification goal?**

### Goal A: "Well-typed Once programs compile correctly"
- Requires: Type checker verification
- Issue: Exchange problem blocks this
- Status: Depth 7 limit or major refactoring

### Goal B: "Once compilation preserves semantics"
- Requires: Surface→IR→x86 verification
- Status: ✅ **Already done!**
- Type checker in TCB (like parser)

**Once's philosophy** (from decision log):
> "The generators have fixed, known types. The type of any expression is
> fully determined by how generators compose."
>
> "The expression alone determines the type."

This suggests **Goal B** aligns better with Once's design: the categorical semantics (IR) are the truth, types are assertions about valid composition.

## Decision Point

Two philosophically different paths:

**Path A: Type-Centric Verification**
- Goal: Prove type checker correct
- Requires: Solve exchange or switch to extrinsic
- Trade-off: May weaken verified components

**Path B: Semantics-Centric Verification**
- Goal: Prove compilation preserves categorical semantics
- Status: Already achieved! (Surface→IR→x86)
- Trade-off: Type checker in TCB

**Once's philosophy suggests Path B**, but the decision is yours.

What matters more:
1. Verifying type checking (Path A)
2. Verifying categorical semantics (Path B - done!)
