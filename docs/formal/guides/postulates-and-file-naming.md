# Postulates, Axioms, and File Naming

This guide explains how to understand what is proven vs assumed in the Once
formal verification, and how file naming conventions communicate this.

## The Problem

Agda's `postulate` keyword is used for three fundamentally different purposes:

1. **Axioms** - Foundational assumptions that DEFINE the system
2. **Primitives** - External interfaces that CANNOT be internalized
3. **Stubs** - Incomplete proofs (technical debt)

Using the same keyword for all three is confusing. This guide explains how
to distinguish them and how file naming should reflect these distinctions.

## Conceptual Categories

### Axioms (Definitional)

Axioms are foundational assumptions that **define** the semantic model.
They are not "unproven theorems" - they ARE the definition of what things mean.

**Examples:**
- `evalPrim : String → ⟦ A ⟧ → ⟦ B ⟧` - Defines what primitive operations compute
- `extensionality` - Mathematical axiom (function extensionality)
- `encode-pair-addr` - Defines memory layout for pairs

**Key property:** These CANNOT be proven because they define the model itself.
Asking to "prove evalPrim" is like asking to "prove what addition means."

**Where they belong:** In `Semantics.agda` files, because they ARE part of
the semantic definition.

### Primitives (FFI Boundaries)

Primitives are interfaces to external systems that cannot be modeled in Agda.
They represent the boundary between the formal model and the real world.

**Examples:**
- `threadCreate` - OS thread creation
- `malloc` - Memory allocation
- `write` - File I/O

**Key property:** These CANNOT be proven because they involve external systems.
The correctness assumption is that the runtime implements them correctly.

**Where they belong:** In `Primitive/*.agda` files, clearly separated.

### Stubs (Technical Debt)

Stubs are placeholders for proofs that COULD be completed but haven't been.
They represent incomplete work, not fundamental limitations.

**Examples:**
- `ℤ-div : ℤ → ℤ → ℤ` - Avoids threading NonZero proofs
- `helper : _` - Placeholder in proof development
- Proof cases marked "TODO"

**Key property:** These COULD be eliminated with more work.

**Where they belong:** In dedicated `Stubs.agda` files, OR clearly marked
inline with comments indicating they are technical debt.

## File Naming Conventions

### `Semantics.agda`

**Purpose:** Define what programs MEAN (denotational semantics).

**Should contain:**
- Type denotation: `⟦_⟧ : Type → Set`
- Evaluation: `eval : IR A B → ⟦ A ⟧ → ⟦ B ⟧`
- Axioms that DEFINE the semantic model

**Should NOT contain:**
- Stubs (incomplete proofs)
- Proofs about semantics (those go in `Correct.agda`)

**Example:**
```agda
-- This is CORRECT in Semantics.agda:
-- evalPrim is an AXIOM that defines what primitives mean
postulate
  evalPrim : ∀ {A B : Type} → String → ⟦ A ⟧ → ⟦ B ⟧

eval (Prim name) x = evalPrim name x  -- Axiom used in definition
```

### `Primitive/*.agda`

**Purpose:** FFI boundaries to external systems.

**Should contain:**
- Postulates for external operations (threads, memory, I/O)
- Type signatures for runtime-provided functions

**Key insight:** Everything here is intentionally opaque. These files
represent the TRUST BOUNDARY with the external world.

### `Stubs.agda`

**Purpose:** Collect technical debt in one visible place.

**Should contain:**
- Incomplete proofs that could theoretically be finished
- Workarounds for stdlib limitations
- Clearly documented reasons for each stub

**Example:**
```agda
-- STUB: Agda stdlib requires NonZero proof for division.
-- To eliminate: thread NonZero proofs through ArithIR.
postulate
  ℤ-div : ℤ → ℤ → ℤ
```

### `Correct.agda` / `Correct/*.agda`

**Purpose:** Correctness proofs.

**Should contain:**
- Theorems about the system
- Proofs that implementations match specifications

**May contain:**
- Inline stubs for incomplete proof cases (clearly marked)

**Goal:** Minimize stubs here. Each stub represents a proof gap.

### `Postulates.agda`

**Purpose:** Central registry of axioms (not stubs).

**Should contain:**
- Mathematical axioms (extensionality, etc.)
- Cross-cutting assumptions used by multiple modules
- Documentation of why each axiom is needed

**Should NOT contain:**
- Stubs (technical debt)
- Module-specific axioms (those stay in their modules)

## How to Identify What's Proven vs Assumed

### Quick Assessment

1. **Check file name:**
   - `Primitive/*.agda` → FFI boundary (intentional)
   - `Stubs.agda` → Technical debt
   - `Semantics.agda` → Definitions + axioms (intentional)
   - `Correct.agda` → Proofs (stubs here = proof gaps)

2. **Run `make count-postulates`:**
   - Shows postulate count by file
   - High counts in `Primitive/` = normal (FFI)
   - High counts in `Correct/` = proof gaps

3. **Check postulate context:**
   - In a `where` clause with `_` type = likely a stub
   - Top-level with full type signature = likely axiom or primitive

### Reading the Numbers

Current breakdown (approximate):
```
FFI Primitives:     ~83  (intentional - Primitive/*.agda)
Axioms:             ~15  (intentional - Semantics.agda, Postulates.agda)
Trust Boundaries:   ~10  (intentional - Backend/*/Postulates.agda)
Stubs/Proof Gaps:   ~65  (technical debt - various Correct/*.agda)
```

## Migration Plan

The current codebase has some stubs in `Semantics.agda` files that should
be moved. When refactoring:

1. **Keep in `Semantics.agda`:** Axioms that define the model
2. **Move to `Stubs.agda`:** Technical workarounds (like `ℤ-div`)
3. **Document:** Add comments explaining why each postulate exists

### Example: `Arith/Semantics.agda`

Current (problematic):
```agda
-- In Arith/Semantics.agda
postulate
  ℤ-div : ℤ → ℤ → ℤ  -- This is a STUB, not semantics!
```

Should become:
```agda
-- In Arith/Stubs.agda
-- STUB: Avoids NonZero proof requirement from stdlib.
-- To eliminate: Use Data.Integer.DivMod with NonZero proofs.
postulate
  ℤ-div : ℤ → ℤ → ℤ

-- In Arith/Semantics.agda
open import Once.Arith.Stubs using (ℤ-div)  -- Explicit import
```

## Summary

| File Pattern | Contains | Postulates Are |
|--------------|----------|----------------|
| `Semantics.agda` | Definitions | Axioms (intentional) |
| `Primitive/*.agda` | FFI interfaces | Primitives (intentional) |
| `Stubs.agda` | Technical debt | Stubs (to be eliminated) |
| `Postulates.agda` | Central axioms | Axioms (intentional) |
| `Correct/*.agda` | Proofs | Proof gaps (to be eliminated) |

The goal: Make it instantly clear from the file name whether postulates
are intentional (axioms/primitives) or technical debt (stubs).
