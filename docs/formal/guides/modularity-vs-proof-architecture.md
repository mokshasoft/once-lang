# Modularity vs Proof Architecture: A Critical Distinction

**Date**: 2026-01-05
**Status**: Clarification Document
**Purpose**: Distinguish code organization from proof properties

## The Confusion

We've been using the term "modular" for two completely different concepts:

1. **Code Modularity**: How code is organized (files, functions, structure)
2. **Proof Architecture**: What properties we prove (local vs global invariants)

**These are independent!** You can have:
- ✅ Modular code with local properties
- ✅ Modular code with global properties ← **This is the key insight!**
- ✅ Monolithic code with local properties
- ✅ Monolithic code with global properties

## Code Modularity (Organization)

**Definition**: How code is structured for maintainability and compilation speed.

### Modular Code Organization

```agda
-- Each IR term has its own proof function
run-inl-proof  : ... → Result
run-inr-proof  : ... → Result
run-pair-proof : ... → Result
run-curry-proof : ... → Result
run-apply-proof : ... → Result

-- Benefits:
-- ✅ Easy to navigate (find curry proof → look in curry file)
-- ✅ Parallel compilation (Agda can type-check files independently)
-- ✅ Clear responsibilities (each function proves one IR term)
-- ✅ Maintainable (changes to curry don't affect apply code)
```

### Monolithic Code Organization

```agda
-- Single giant function proving all IR terms at once
run-entire-program-proof : ... → Result
run-entire-program-proof prog =
  case prog of
    inl x → ...
    inr x → ...
    pair x y → ...
    curry f → ...
    apply f x → ...

-- Drawbacks:
-- ❌ Hard to navigate (10,000+ line function)
-- ❌ Sequential compilation (must type-check everything)
-- ❌ Unclear responsibilities (everything in one place)
-- ❌ Hard to maintain (changes affect everything)
```

## Proof Architecture (What We Prove)

**Definition**: What properties we establish (independent of code organization).

### Local Properties (No Global Invariants)

```agda
-- Each IR term proven independently, no shared knowledge
run-apply-proof : (x : ⟦ (A ⇒ B) * A ⟧) → ... → Result

-- What we know:
-- - x has type (A ⇒ B) * A
-- - That's ALL we know!
-- - We don't know where x came from
-- - We don't know if it's a well-formed closure
-- - We need a POSTULATE to assume it works
```

### Global Properties (With Global Invariants)

```agda
-- Each IR term proven independently, BUT with shared global knowledge
run-apply-proof : (x : ⟦ (A ⇒ B) * A ⟧) →
                  AllClosuresWellFormed prog →  -- ← Global invariant!
                  ... → Result

-- What we know:
-- - x has type (A ⇒ B) * A
-- - ALL closures in prog are well-formed (global invariant)
-- - Therefore x MUST be well-formed (if it's a closure)
-- - No postulate needed!
```

## The Key Insight: Modular Code + Global Properties

**You can have BOTH modular code organization AND global invariants!**

### Current AArch64 Architecture (Modular Code + Local Properties)

```agda
-- File: Once/Backend/AArch64/Correct/IR/Curry.agda
run-curry-star-direct : (f : IR i (A * B) C) → (x : ⟦ A ⟧) → ... → Result

-- File: Once/Backend/AArch64/Correct/IR/Apply.agda
run-apply-star-direct : (x : ⟦ (A ⇒ B) * A ⟧) → ... → Result
run-apply-star-direct x ... =
  -- Problem: We don't know if x is well-formed!
  -- Solution: Use postulate
  let ... = apply-produces-result x ... in ...
```

**Code organization**: ✅ Modular (each IR term in separate file)
**Proof architecture**: ❌ Local properties (no global invariants → needs postulate)

### Proposed Architecture (Modular Code + Global Properties)

```agda
-- File: Once/Backend/AArch64/Correct/IR/Curry.agda
run-curry-star-direct : (f : IR i (A * B) C) → (x : ⟦ A ⟧) →
                        AllClosuresWellFormed prog →  -- ← Thread invariant
                        ... →
                        Result × AllClosuresWellFormed prog'  -- ← Preserve invariant

-- File: Once/Backend/AArch64/Correct/IR/Apply.agda
run-apply-star-direct : (x : ⟦ (A ⇒ B) * A ⟧) →
                        AllClosuresWellFormed prog →  -- ← Receive invariant
                        ... → Result
run-apply-star-direct x inv ... =
  -- We KNOW x is well-formed (from global invariant)!
  -- No postulate needed!
  let wf-proof = inv x ... in
  run-apply-with-wf x wf-proof ...  -- ← Use the proof!
```

**Code organization**: ✅ Modular (each IR term still in separate file)
**Proof architecture**: ✅ Global properties (global invariants → no postulate!)

## Comparison to CompCert

### CompCert: Needs Calling Convention Axioms

**Why**: Separate compilation
- C file A defines function `foo`
- C file B calls function `foo`
- CompCert compiles A and B separately
- Cannot prove calling convention is followed (doesn't see both sides)
- Must axiomatize calling conventions

### Once: Can Prove Calling Convention

**Why**: Whole-program compilation
- Once compiles entire program at once
- Sees both curry (which creates closures) and apply (which uses them)
- Can prove calling convention is followed by construction
- No need for axioms!

**The difference**:
- CompCert: Separate compilation → fundamentally needs axioms
- Once: Whole-program compilation → can prove everything

## What's Needed to Eliminate the Apply Postulate

### Step 1: Define Global Invariant

```agda
-- Once/Backend/AArch64/Correct/GlobalInvariant.agda

data AllClosuresWellFormed (prog : Program) : Set where
  all-closures-wf :
    (∀ (addr : ℕ) (cl : Closure A B) →
      IsClosure prog addr cl →
      ClosureWellFormed prog addr cl) →
    AllClosuresWellFormed prog
```

### Step 2: Thread Through All IR Terms

```agda
-- Update signature of run-ir-star-at-offset
run-ir-star-at-offset :
  (ir : IR i A B) →
  (x : ⟦ A ⟧) →
  AllClosuresWellFormed prog →  -- ← Add this
  ... →
  ∃[ s' ] (IRStarResult ir prog s s' x offset
         × AllClosuresWellFormed prog)  -- ← And this

-- Each IR term implementation:
-- - inl: Preserves invariant trivially (doesn't create closures)
-- - inr: Preserves invariant trivially (doesn't create closures)
-- - pair: Preserves invariant trivially (doesn't create closures)
-- - curry: Proves new closure is well-formed, adds to invariant
-- - apply: Uses invariant to extract ClosureWellFormed proof
```

### Step 3: Prove Initial Invariant

```agda
-- Prove that when starting from an empty program or well-typed program,
-- the invariant holds
initial-invariant : ∀ (prog : Program) →
                    WellTyped prog →
                    AllClosuresWellFormed prog
```

### Step 4: Update Apply Implementation

```agda
-- Once/Backend/AArch64/Correct/IR/Apply.agda

run-apply-star-direct :
  (x : ⟦ (A ⇒ B) * A ⟧) →
  AllClosuresWellFormed prog →  -- ← New parameter
  ... →
  ∃[ s' ] IRStarResult apply ...

run-apply-star-direct x inv ... =
  -- Extract closure from x (since apply receives (closure, arg))
  let (cl , arg) = x in

  -- Extract well-formedness proof from global invariant
  let cl-wf = extract-closure-wf inv cl in

  -- Use the postulate-free path!
  run-apply-with-wf cl arg cl-wf ...

  -- No postulate needed! ✅
```

## Estimated Effort

### Changes Required

1. **Define global invariant** (~50 lines)
2. **Update signatures** (~30 files, ~5 lines each = ~150 lines)
3. **Thread invariant through compose/pair/case** (~200 lines)
4. **Update curry to prove preservation** (~100 lines)
5. **Update apply to use invariant** (~100 lines)
6. **Prove initial invariant** (~100 lines)

**Total**: ~700 lines of proof code changes

### Timeline Estimate

- **Experienced with codebase**: 1-2 weeks
- **Less familiar**: 3-4 weeks

### Benefits

- ✅ Zero postulates for apply
- ✅ Stronger verification
- ✅ Still modular code organization
- ✅ Proof that calling convention is followed by construction

### Costs

- ❌ All IR term signatures change (but calls stay modular)
- ❌ More complex proof (but not significantly harder)
- ❌ Initial effort to restructure

## Recommendation

Given that:
1. This IS provable (Once does whole-program compilation)
2. Code remains modular (organization unchanged)
3. Effort is reasonable (~700 lines over 1-2 weeks)
4. Result is stronger verification (zero postulates)

**Recommendation**: This should be done if zero-postulate verification is required.

## Terminology Going Forward

To avoid confusion, use:

- **"Modular code"**: Code organized into separate functions/files
- **"Local properties"**: Proving each piece independently without global knowledge
- **"Global properties"**: Proving each piece with shared global invariants
- **"Whole-program properties"**: Properties that hold across the entire program

**Do NOT use "modular" to mean "local properties"!**

## References

- `Once/Backend/AArch64/Correct/ClosureWellFormed.agda` - Infrastructure already exists!
- `docs/formal/guides/apply-postulate-status.md` - Previous investigation
- `docs/formal/guides/apply-postulate-elimination-attempt.md` - Implementation attempt

## See Also

This distinction appears in other verification contexts:
- **Modular verification** (Spec#, Dafny): Prove methods independently with contracts
- **Whole-program analysis** (Abstract interpretation): Analyze entire program for global properties
- **CompCert**: Modular code with calling convention axioms (separate compilation)
- **CakeML**: Whole-program proofs (bootstrapping theorem prover)

Once is more like CakeML than CompCert - we compile the whole program, so we should be able to prove whole-program properties!
