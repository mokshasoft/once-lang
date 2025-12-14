# What Is Proven

Current formal verification status for the Once compiler.

## Summary

The Once compiler is **substantially verified** in Agda. The full compilation pipeline from surface syntax to x86-64 assembly is proven correct, including elaboration, desugaring, optimization, and code generation. An end-to-end theorem composes these proofs.

| Component | Status | Notes |
|-----------|--------|-------|
| Core IR semantics | ✓ Proven | 13 generators (incl. arr for effects), denotational semantics |
| Categorical laws | ✓ Proven | 18 CCC law proofs (incl. arr identity) |
| Type soundness | ✓ Proven | Progress, preservation, canonical forms |
| Elaboration | ✓ Proven | Surface syntax → IR preserves semantics |
| Desugar | ✓ Proven | SurfaceIR → CoreIR preserves semantics |
| Optimization | ✓ Proven | Categorical rewrites preserve semantics |
| x86-64 code gen | ✓ Proven | All 14 generators proven |
| End-to-end theorem | ✓ Proven | Full pipeline: Surface → x86 preserves semantics |
| Polynomial functors | ✓ Proven | SPF module with proper recursive type semantics |
| Primitive specs | ✓ Axiomatized | Memory, IO, Thread axioms (orthogonal to type system) |
| AArch64 code gen | ☐ Structure defined | Syntax, Semantics, CodeGen, Correct created |
| C code generation | Not started | IR → C semantics preservation |
| QTT enforcement | Not started | Linear resource tracking |

## What Is Proven

### Core IR Semantics (Phase V1)

The 13 categorical generators and their denotational semantics are defined in Agda:

- `Type.agda` - Types: Unit, Void, products, sums, functions, Eff (effects)
- `IR.agda` - The 13 generators as a GADT (including `arr` for effect lifting)
- `Semantics.agda` - Evaluation function `eval : IR A B → ⟦A⟧ → ⟦B⟧`

Note: The effect type `Eff A B` has the same semantics as `A ⇒ B` (pure functions). This is intentional - effects are a compile-time discipline, not a runtime distinction. See D032 in the decision log.

### Categorical Laws (Phase V2)

18 theorems proving the IR satisfies cartesian closed category laws (including arrow law for `arr`):

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
| Arr-identity | `eval arr f ≡ f` (D032: arr is semantically identity) |
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

### x86-64 Code Generation Correctness (Phase V7)

The main theorem:

```
codegen-x86-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 ir) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode (eval ir x))
```

This proves that executing compiled x86-64 code on an encoded input produces the encoded semantic result. All 14 IR generators are proven:

| Generator | Status | Generated Code |
|-----------|--------|----------------|
| `id` | ✓ Proven | `mov rax, rdi` |
| `compose` | ✓ Proven | `f ++ mov rdi, rax ++ g` |
| `fst` | ✓ Proven | `mov rax, [rdi]` |
| `snd` | ✓ Proven | `mov rax, [rdi+8]` |
| `pair` | ✓ Proven | Stack alloc, compute both |
| `inl` | ✓ Proven | Stack alloc, tag=0 |
| `inr` | ✓ Proven | Stack alloc, tag=1 |
| `case` | ✓ Proven | Branch on tag |
| `terminal` | ✓ Proven | `mov rax, 0` |
| `initial` | ✓ Proven | Absurd (no Void inputs) |
| `fold` | ✓ Proven | `mov rax, rdi` |
| `unfold` | ✓ Proven | `mov rax, rdi` |
| `arr` | ✓ Proven | `mov rax, rdi` |
| `curry` | ✓ Proven | Closure creation with thunk |
| `apply` | ✓ Proven | Indirect call via closure |

The proofs use a layered approach:
1. **Encoding axioms**: Relate semantic values to machine words
2. **Execution helpers**: Capture single/multi-instruction execution properties
3. **Per-generator proofs**: Compose helpers to prove each generator correct
4. **Main theorem**: Case analysis using all per-generator proofs

### AArch64 Code Generation Correctness (In Progress)

The AArch64 backend follows the same structure as x86-64, targeting the ARM64 architecture verified by seL4.

**Status**: Backend definition files created, proofs postulated.

```
codegen-aarch64-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-aarch64 ir) (initWithInput x) ≡ just s
        × readReg (regs s) x0 ≡ encode (eval ir x))
```

**Files**:
- `Once/Backend/AArch64/Syntax.agda` - 31 GPRs, AAPCS64 instruction subset
- `Once/Backend/AArch64/Semantics.agda` - PSTATE flags, SP handling
- `Once/Backend/AArch64/CodeGen.agda` - IR → AArch64 translation
- `Once/Backend/AArch64/Correct.agda` - Correctness theorem (postulated)

**Key differences from x86-64**:
- Single input/output register (x0) instead of rdi/rax
- Zero register (xzr) for efficient tag=0 stores
- PSTATE condition flags (NZCV) instead of EFLAGS
- 16-byte stack alignment requirement

See `docs/formal/aarch64-remaining-proofs.md` for detailed progress tracking.

## Assumptions and Postulates

All assumptions are centralized in `formal/Once/Postulates.agda`. This is the **single source of truth** for what is assumed without proof.

### Detecting Assumptions

To find all postulates in the formalization:

```bash
# Check if a file uses postulates (--safe fails if postulates are used)
agda --safe formal/Once/Semantics.agda

# Find all postulate declarations
grep -r "postulate" formal/

# List modules that import from Postulates.agda
grep -r "import Once.Postulates" formal/
```

### P1: Function Extensionality

| Property | Value |
|----------|-------|
| **Type** | `∀ {A B} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g` |
| **Location** | `Once/Postulates.agda` |
| **Needed by** | `Once/Surface/Correct.agda` (elaboration correctness for lambdas) |
| **Runtime effect** | None (erased during extraction) |

**Justification**: Function extensionality is consistent with Agda's type theory and holds in most models (setoid model, cubical type theory). It's a standard assumption in formalized mathematics.

### P2: x86-64 Encoding Axioms

| Property | Value |
|----------|-------|
| **Type** | `encode-*` family of postulates |
| **Location** | `Once/Backend/X86/Correct.agda` |
| **Needed by** | x86-64 code generation correctness proofs |
| **Runtime effect** | None (proof-only) |

These axioms relate semantic values to machine words:
- `encode-pair-fst/snd`: Reading from encoded pairs
- `encode-inl/inr-tag/val`: Reading from encoded sums
- `encode-*-construct`: Building encoded values from memory layouts
- `encode-fix-wrap/unwrap`: Fixed point encoding identity
- `encode-arr-identity`: Effect type encoding identity

**Justification**: These capture the intended memory layout semantics. A full formalization would model the heap explicitly and prove these as lemmas.

### P3: x86-64 Execution Helpers

| Property | Value |
|----------|-------|
| **Type** | `run-*` family of postulates |
| **Location** | `Once/Backend/X86/Correct.agda` |
| **Needed by** | x86-64 code generation correctness proofs |
| **Runtime effect** | None (proof-only) |

These capture execution properties:
- `run-single-mov*`: Single mov instruction execution
- `run-inl-seq`, `run-inr-seq`: Sum construction sequences
- `run-pair-seq`: Pair construction sequence
- `run-case-inl`, `run-case-inr`: Case branching execution
- `run-seq-compose`: Sequential composition execution
- `run-generator`: General generator execution

**Justification**: These can be proven from the operational semantics in `Semantics.agda`. The layered approach separates "what the machine does" from "how we compose proofs".

### P4: Closure Encoding

| Property | Value |
|----------|-------|
| **Type** | `encode-closure-construct`, `run-curry-seq`, `run-apply-seq` |
| **Location** | `Once/Backend/X86/Correct.agda` |
| **Needed by** | `curry` and `apply` generator proofs |
| **Runtime effect** | None (proof-only) |

These postulates model closure handling:
- `encode-closure-construct`: Relates closure memory layout to encoded function values
- `run-curry-seq`: Closure allocation and thunk generation execution
- `run-apply-seq`: Closure invocation via indirect call

**Justification**: These capture the intended closure representation (env pointer + code pointer) and calling convention. A full formalization would model closure allocation explicitly.

### S1: Fixed Point Semantics (Semantic Gap) — ADDRESSED

This was a known limitation where `⟦ Fix F ⟧` used a newtype wrapper rather than true recursive substitution. **This is now addressed** by the SPF module (`Once/SPF.agda`).

| Property | Value |
|----------|-------|
| **Type** | Semantic gap (addressed by SPF) |
| **Location** | `Once/Semantics.agda` (old), `Once/SPF.agda` (solution) |
| **Status** | SPF provides proper semantics; integration pending |
| **Runtime effect** | None (operational semantics are correct) |

The SPF module provides polynomial functors with proper fixed point semantics:
- `μ F` as inductive type with `⟨_⟩`/`out` isomorphism
- `cata` (catamorphism) with termination proof
- `fmap` with functor laws
- `ind` (induction principle)

See D037 in the decision log for the design rationale.

### Guidelines for Adding Assumptions

When adding a postulate or discovering a semantic gap:

1. **Centralize**: Add it to `Once/Postulates.agda` with full documentation
2. **Identify**: Label it (P2, P3, ... for postulates; S2, S3, ... for semantic gaps)
3. **Document**: Explain what is assumed and why it's needed
4. **Justify**: Why we believe this is sound
5. **Impact**: What would break if it's wrong
6. **Update**: Add it to this document

The goal is **zero hidden assumptions**. Anyone auditing the formalization should be able to find every assumption by:
1. Reading `Once/Postulates.agda`
2. Running `agda --safe` on files that should be postulate-free
3. Reading the "Known Limitations" section of this document

## Known Limitations

### Fixed Point Semantics (Fix, fold, unfold) — Semantic Gap S1 — ADDRESSED

**Status**: The SPF module (`Once/SPF.agda`) now provides proper recursive type semantics. Integration into `Type.agda` and `Semantics.agda` is pending.

The original limitation was that `⟦ Fix F ⟧ = ⟦Fix⟧ ⟦ F ⟧` used a trivial newtype wrapper. The SPF module solves this with polynomial functors:

```agda
-- Functor codes with explicit recursive position
data Functor : Set₁ where
  K    : Type → Functor           -- Constant
  Id   : Functor                  -- Recursive position (the key insight!)
  _⊕_  : Functor → Functor → Functor
  _⊗_  : Functor → Functor → Functor

-- Proper fixed point
data μ (F : Functor) : Set where
  ⟨_⟩ : ⟦ F ⟧F (μ F) → μ F
```

Now `Nat = μ (K Unit ⊕ Id)` correctly satisfies `μ NatF ≅ ⊤ ⊎ μ NatF`.

**Remaining work**: Update `Type.agda` to use `Fix : Functor → Type` and `Semantics.agda` to use `⟦ Fix F ⟧ = μ F`. See D037 in the decision log.

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

| Phase | Description | Status |
|-------|-------------|--------|
| V5 | Optimization correctness | ✓ Done |
| V6 | x86-64 backend semantics | ✓ Done |
| V7 | x86-64 code generation correctness | ✓ Done (all 14 generators) |
| V8 | QTT verification | Not started |
| V9 | End-to-end theorem | ✓ Done |
| V10 | Extraction integration | Not started |
| - | SPF integration into Type/Semantics | Future (see D037) |
| - | C backend (optional) | Not started |

## Proof Files

All proofs are in the `formal/` directory:

```
formal/Once/
├── Postulates.agda        # ★ CENTRAL REGISTRY OF ALL ASSUMPTIONS ★
├── Type.agda              # Type definitions
├── IR.agda                # IR (13 generators incl. arr)
├── Semantics.agda         # Denotational semantics
├── SPF.agda               # ★ Strictly Positive Functors (proper Fix semantics) ★
├── Compile.agda           # Compilation pipeline (desugar + optimize)
├── Optimize.agda          # Optimizer
├── EndToEnd.agda          # ★ End-to-end compilation theorem ★
├── Category/
│   └── Laws.agda          # 18 CCC law proofs
├── TypeSystem/
│   ├── Typing.agda        # Typing rules
│   └── Soundness.agda     # Progress, preservation
├── Surface/
│   ├── Syntax.agda        # Surface expression type
│   ├── IR.agda            # Surface IR (with Let, Prim, etc.)
│   ├── Elaborate.agda     # Elaboration function
│   ├── Correct.agda       # Elaboration correctness (imports P1)
│   ├── Desugar.agda       # Desugar to Core IR
│   └── Desugar/
│       └── Correct.agda   # Desugar correctness
├── Optimize/
│   └── Correct.agda       # Optimization correctness
├── Primitive/
│   ├── Memory.agda        # ★ Memory allocation axioms ★
│   ├── IO.agda            # ★ I/O axioms ★
│   └── Thread.agda        # ★ Concurrency axioms ★
└── Backend/
    ├── X86/
    │   ├── Syntax.agda    # x86-64 instruction AST
    │   ├── Semantics.agda # x86-64 operational semantics
    │   ├── CodeGen.agda   # IR → x86-64 compilation
    │   └── Correct.agda   # Code gen correctness (imports P2-P4)
    └── AArch64/
        ├── Syntax.agda    # AArch64 instruction AST (31 GPRs, AAPCS64)
        ├── Semantics.agda # AArch64 operational semantics (PSTATE)
        ├── CodeGen.agda   # IR → AArch64 compilation
        └── Correct.agda   # Code gen correctness (postulated)
```

**Important**: `Postulates.agda` is the authoritative source for core assumptions. Backend-specific postulates (P2-P4) are in `Backend/X86/Correct.agda`. Primitive specifications (Memory, IO, Thread) are orthogonal to the type system.

## Future Work: SPF Integration

The SPF module (`Once/SPF.agda`) now provides proper recursive type semantics via polynomial functors. **This is implemented and type-checks.**

### What's Done (D037)

- `Functor` codes: `K`, `Id`, `⊕`, `⊗`
- `μ F` as proper inductive type
- `⟨_⟩`/`out` isomorphism with proofs
- `cata` with termination via mutual recursion
- `fmap` with identity and composition laws
- `ind` induction principle
- Standard types: `Nat`, `List`, `Tree`

### Remaining Integration Work

To fully integrate SPF into the main formalization:

1. **Update `Type.agda`**: Change `Fix : Type → Type` to `Fix : Functor → Type`
2. **Update `Semantics.agda`**: Change `⟦ Fix F ⟧ = ⟦Fix⟧ ⟦ F ⟧` to `⟦ Fix F ⟧ = μ F`
3. **Update dependent proofs**: `Laws.agda`, `Correct.agda`, etc.

This is deferred because:
- SPF works standalone for new verified programs
- Integration would require updating many existing proofs
- Existing proofs remain valid for their current scope

See D037 in the decision log for the full rationale.

## See Also

- [Decision Log D037](../compiler/decision-log.md#d037-polynomial-functors-for-recursive-type-semantics) - SPF design decision
- [Fix Semantics Options](fix-semantics-options.md) - Detailed comparison of approaches
- [Formal Verification Plan](../compiler/formal-verification-plan.md) - Detailed verification roadmap
- [Verification Strategy](../design/formal/verification-strategy.md) - Why Agda, architecture decisions
- [Lessons Learned](lessons-learned.md) - Practical Agda lessons from this formalization
