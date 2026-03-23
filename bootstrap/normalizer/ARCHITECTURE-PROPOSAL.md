# Architecture Proposal: Restructuring Correctness vs Implementation

## Current Problem

The Implementation/ directory is very large (~5500 lines) while Correctness/ is small (~300 lines). This seems inverted - Implementation should just define the normalizer and prove it satisfies a spec, while Correctness should contain the general theory.

### Current Line Counts

```
Correctness/                    ~300 lines (small, parametric)
Implementation/                ~5500 lines (large, contains everything)
```

### Current Structure

```
Correctness/
  ├── Correctness.agda      -- Parametric: "IF fixpoint THEN correct"
  ├── FixpointTheorem.agda  -- Parametric: "IF fixpoint THEN beta-normal"
  ├── Record.agda           -- CorrectNormalizer record
  ├── Preserves.agda        -- Preservation theorem
  ├── ProducesNF.agda       -- Produces normal form
  └── Terminates.agda       -- Termination

Implementation/
  ├── Normalizer.agda       -- Define normalize + many lemmas (1769 lines!)
  ├── NoRedex.agda          -- Define NoRedex predicate
  ├── NormalForm.agda       -- Theorems about NoRedex terms
  ├── Normalize.agda        -- Re-exports
  ├── NormalizeLemmas.agda  -- More lemmas
  └── Normalize/
      ├── Chain.agda        -- Proof combinators
      ├── Dispatch.agda     -- Tag dispatchers (is-id, is-pair, etc.)
      ├── Handlers.agda     -- Handler definitions
      ├── NoRedexHandlers.agda
      ├── NoRedexRebuild.agda
      ├── NstepDispatch.agda
      ├── Rebuild.agda
      └── Fixpoint/
          ├── MainTheorem.agda   -- noredex-fixpoint by structural induction
          ├── BaseSimple.agda    -- Base cases
          ├── BaseRecursive.agda -- More base cases
          └── DispatchLemmas.agda -- Helper lemmas (707 lines!)
```

## The Core Issue

The theorem `noredex-fixpoint`:
```agda
noredex-fixpoint : ∀ {A B} (t : Term A B) → NoRedex t →
                   (normalize ∘ encode t) ⟶* encode t
```

This is proved by **direct calculation** in Implementation/, tracing through all 15 constructors. But this is really a **general property** of any normalizer that handles each case correctly.

## Proposed Structure

### Correctness/ (General Theory)

```
Correctness/
  ├── NormalizerSpec.agda       -- NEW: Define what makes a normalizer correct
  │   │
  │   │  -- A normalizer spec says: for each constructor, the handler
  │   │  -- produces the right result
  │   │  record NormalizerSpec (N : Term TermCode' TermCode') : Set where
  │   │    field
  │   │      -- For NoRedex terms at each position, handler preserves encoding
  │   │      handle-id-preserves : ...
  │   │      handle-comp-preserves : (for non-redex compositions)
  │   │      handle-fst-preserves : ...
  │   │      ... (15 fields, one per constructor)
  │   │
  ├── SpecImpliesFixpoint.agda  -- NEW: The main theorem
  │   │
  │   │  -- THEOREM: If N satisfies spec, then noredex-fixpoint holds
  │   │  spec-implies-fixpoint : NormalizerSpec N →
  │   │                          ∀ t → NoRedex t →
  │   │                          (N ∘ encode t) ⟶* encode t
  │   │
  │   │  -- This contains the structural induction on terms
  │   │  -- Currently in Implementation/Normalize/Fixpoint/MainTheorem.agda
  │   │
  ├── FixpointImpliesCorrect.agda  -- Existing (parametric)
  ├── FixpointUniqueness.agda      -- FUTURE: Uniqueness of fixpoint
  └── ... (existing files)
```

### Implementation/ (Concrete Normalizer)

```
Implementation/
  ├── Normalizer.agda         -- Define normalize (SMALLER - just definitions)
  │   │
  │   │  -- The normalizer definition
  │   │  normalize : Term TermCode' TermCode'
  │   │  normalize = cata TermF normalize-step
  │   │
  │   │  -- The algebra (15 handlers)
  │   │  normalize-step : Term (⟦ TermF ⟧F TermCode') TermCode'
  │   │
  ├── Handlers/               -- Handler definitions and basic properties
  │   ├── Definitions.agda    -- handle-id, handle-comp, etc.
  │   └── NoRedex.agda        -- NoRedex proofs for handlers
  │
  ├── SatisfiesSpec.agda      -- NEW: Prove normalize satisfies spec
  │   │
  │   │  normalize-spec : NormalizerSpec normalize
  │   │  normalize-spec = record
  │   │    { handle-id-preserves = ...
  │   │    ; handle-comp-preserves = ...  -- uses is-id-pos-N lemmas
  │   │    ; ...
  │   │    }
  │   │
  └── Fixpoint.agda           -- NEW: Derive fixpoint from spec
      │
      │  -- Fixpoint follows automatically!
      │  normalize-fixpoint : (normalize ∘ encode normalize) ⟶* encode normalize
      │  normalize-fixpoint = spec-implies-fixpoint normalize-spec
      │                         normalize normalize-noredex
```

## What Moves Where

### To Correctness/ (General Theory)

| Currently In | Move To | What |
|--------------|---------|------|
| `Implementation/Normalize/Fixpoint/MainTheorem.agda` | `Correctness/SpecImpliesFixpoint.agda` | Structural induction on NoRedex terms |
| `Implementation/NoRedex.agda` (NoRedex definition) | `Foundations/NoRedex.agda` or `Correctness/NoRedex.agda` | The predicate is general |

### Stays in Implementation/ (Concrete Facts)

| File | Why It Stays |
|------|--------------|
| `Normalizer.agda` (definitions only) | Defines the concrete normalize |
| `Handlers.agda` | Concrete handler definitions |
| `DispatchLemmas.agda` | Lemmas about our specific handlers (is-id-pos-N) |
| `SatisfiesSpec.agda` (new) | Proves our normalize satisfies the spec |

### Could Be Simplified/Removed

| File | Issue |
|------|-------|
| `Normalizer.agda` | Contains ~1000 lines of fmap lemmas that might belong elsewhere |
| `Dispatch.agda` | Tag dispatchers - could be generated or simplified |
| `NstepDispatch.agda` | Similar repetitive structure |

## Benefits of Restructuring

1. **Clearer separation**: Correctness/ has general theory, Implementation/ has concrete facts
2. **Reusability**: The spec + theorem could apply to other normalizers
3. **Smaller Implementation/**: Most of the structural induction moves out
4. **Easier to understand**: "normalize satisfies spec" is more intuitive than "trace through 15 cases"

## The 15-Constructor Problem Remains

Even with restructuring, we still have 15 term constructors. This means:
- 15 fields in NormalizerSpec
- 15 proofs in SatisfiesSpec
- The spec-implies-fixpoint theorem has 15 cases

But the **structure** becomes clearer:
- Correctness/ says "if handlers are correct, fixpoint holds" (general)
- Implementation/ says "our handlers are correct" (specific)

## Questions to Consider

1. Should NoRedex be in Foundations/ or Correctness/?
2. Should the fmap lemmas (fmap-1-inr, etc.) be generated by a macro/reflection?
3. Could we use a different encoding (balanced tree) to reduce case explosion?
4. Is there a way to prove handler correctness more uniformly?

## Estimated Impact

After restructuring:
```
Correctness/    ~800 lines  (gains structural induction)
Implementation/ ~3500 lines (loses structural induction, gains SatisfiesSpec)
Foundations/    ~1800 lines (gains NoRedex?)
```

The total stays similar, but the **conceptual organization** is cleaner.
