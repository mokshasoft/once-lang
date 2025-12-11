# What Is Proven

Current formal verification status for the Once compiler.

## Summary

The Once compiler is **partially verified** in Agda. The core semantics and elaboration from surface syntax to IR are proven correct. Code generation and optimization verification are in progress.

| Component | Status | Notes |
|-----------|--------|-------|
| Core IR semantics | ✓ Proven | 12 generators, denotational semantics |
| Categorical laws | ✓ Proven | 17 CCC law proofs |
| Type soundness | ✓ Proven | Progress, preservation, canonical forms |
| Elaboration | ✓ Proven | Surface syntax → IR preserves semantics |
| Optimization | Not started | Each rewrite rule needs proof |
| C code generation | Not started | IR → C semantics preservation |
| QTT enforcement | Not started | Linear resource tracking |

## What Is Proven

### Core IR Semantics (Phase V1)

The 12 categorical generators and their denotational semantics are defined in Agda:

- `Type.agda` - Types: Unit, Void, products, sums, functions
- `IR.agda` - The 12 generators as a GADT
- `Semantics.agda` - Evaluation function `eval : IR A B → ⟦A⟧ → ⟦B⟧`

### Categorical Laws (Phase V2)

17 theorems proving the IR satisfies cartesian closed category laws:

| Law | Theorem |
|-----|---------|
| Left identity | `eval (id ∘ f) x ≡ eval f x` |
| Right identity | `eval (f ∘ id) x ≡ eval f x` |
| Associativity | `eval ((f ∘ g) ∘ h) x ≡ eval (f ∘ (g ∘ h)) x` |
| Fst-pair | `eval (fst ∘ ⟨f,g⟩) x ≡ eval f x` |
| Snd-pair | `eval (snd ∘ ⟨f,g⟩) x ≡ eval g x` |
| Pair-eta | `eval ⟨fst,snd⟩ x ≡ x` |
| Case-inl | `eval ([f,g] ∘ inl) x ≡ eval f x` |
| Case-inr | `eval ([f,g] ∘ inr) x ≡ eval g x` |
| Case-eta | `eval [inl,inr] x ≡ x` |
| Curry-apply | `eval (apply ∘ ⟨curry f ∘ fst, snd⟩) x ≡ eval f x` |
| ... | (and 7 more) |

### Type Soundness (Phase V3)

- **Progress**: Well-typed terms evaluate (don't get stuck)
- **Preservation**: Evaluation preserves types
- **Canonical forms**: Values have expected structure
- **Compositionality**: `eval (g ∘ f) x ≡ eval g (eval f x)`

### Elaboration Correctness (Phase V4)

The main theorem:

```
elaborate-correct : ∀ ρ e. evalSurface ρ e ≡ eval (elaborate e) (interpEnv ρ)
```

This proves that elaborating surface syntax (with lambdas and variables) to point-free IR preserves semantics. The elaboration handles:

- Lambda elimination via currying
- Variable resolution via projection chains
- Case expression distribution

## What Is Postulated

| Postulate | Location | Justification |
|-----------|----------|---------------|
| `extensionality` | `Once/Surface/Correct.agda` | Function extensionality |

Function extensionality is used only in proof terms, which are erased during extraction. The postulate never executes at runtime.

## Trusted Computing Base

The following must be trusted without proof:

1. **Agda type checker** - Verifies the proofs
2. **MAlonzo extraction** - Translates Agda to Haskell
3. **GHC** - Compiles extracted Haskell
4. **C compiler** - Compiles generated C code
5. **Parser** - Not verified (megaparsec-based)
6. **CLI** - Not verified (optparse-applicative)

This is comparable to CakeML (HOL4 + PolyML + OS) and CompCert (Coq + OCaml + OS).

## Remaining Work

| Phase | Description | Estimated Effort |
|-------|-------------|------------------|
| V5 | Optimization correctness | 1-2 weeks |
| V6 | C backend semantics | 2-3 weeks |
| V7 | Code generation correctness | 4-6 weeks |
| V8 | QTT verification | 2-3 weeks |
| V9 | End-to-end theorem | 1 week |
| V10 | Extraction integration | 2-3 weeks |

## Proof Files

All proofs are in the `formal/` directory:

```
formal/Once/
├── Type.agda              # Type definitions
├── IR.agda                # IR (12 generators)
├── Semantics.agda         # Denotational semantics
├── Category/
│   └── Laws.agda          # 17 CCC law proofs
├── TypeSystem/
│   ├── Typing.agda        # Typing rules
│   └── Soundness.agda     # Progress, preservation
└── Surface/
    ├── Syntax.agda        # Surface expression type
    ├── Elaborate.agda     # Elaboration function
    └── Correct.agda       # Elaboration correctness
```

## See Also

- [Formal Verification Plan](../compiler/formal-verification-plan.md) - Detailed verification roadmap
- [Verification Strategy](../design/formal/verification-strategy.md) - Why Agda, architecture decisions
- [Lessons Learned](lessons-learned.md) - Practical Agda lessons from this formalization
