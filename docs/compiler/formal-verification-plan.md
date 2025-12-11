# Complete Verification Plan for Once Compiler

## Goal

Verify the `once build` command produces correct C code. Specifically:

**Correctness Theorem**: For any well-typed Once program `p`, executing the generated C code on input `x` produces the same result as evaluating the IR semantics on `x`.

```
∀ p x. typecheck(p) = Ok → run(compile(p), x) = eval(elaborate(p), x)
```

## Compiler Pipeline

```
┌─────────┐    ┌───────────┐    ┌───────────┐    ┌──────────┐    ┌─────────┐
│ Source  │───▶│   Parse   │───▶│ TypeCheck │───▶│Elaborate │───▶│Optimize │
│ (.once) │    │           │    │           │    │          │    │         │
└─────────┘    └───────────┘    └───────────┘    └──────────┘    └─────────┘
                    │                 │                │               │
                    ▼                 ▼                ▼               ▼
               Surface AST      Type-annotated    Core IR        Optimized IR
                                    AST
                                                                       │
                                                                       ▼
                                                               ┌─────────────┐
                                                               │  C CodeGen  │
                                                               └─────────────┘
                                                                       │
                                                                       ▼
                                                                  C Source
```

## Verification Phases

### Phase V1: Core IR Semantics ✓ (DONE)

**Status**: Completed in `formal/Once/`

**What**: Define IR and its denotational semantics in Agda.

**Deliverables**:
- `Type.agda` - Type datatype (Unit, Void, *, +, ⇒)
- `IR.agda` - IR datatype (12 generators)
- `Semantics.agda` - ⟦_⟧ : Type → Set, eval : IR A B → ⟦A⟧ → ⟦B⟧

**Theorems**: None yet (definitions only)

---

### Phase V2: Categorical Laws ✓ (DONE)

**Status**: Completed in `formal/Once/Category/Laws.agda`

**What**: Prove IR satisfies cartesian closed category laws.

**Deliverables**:
- `Category/Laws.agda` - All CCC law proofs

**Theorems** (17 total):
1. `eval-id-left` : eval (id ∘ f) x ≡ eval f x
2. `eval-id-right` : eval (f ∘ id) x ≡ eval f x
3. `eval-assoc` : eval ((f ∘ g) ∘ h) x ≡ eval (f ∘ (g ∘ h)) x
4. `eval-fst-pair` : eval (fst ∘ ⟨f,g⟩) x ≡ eval f x
5. `eval-snd-pair` : eval (snd ∘ ⟨f,g⟩) x ≡ eval g x
6. `eval-pair-eta` : eval ⟨fst,snd⟩ x ≡ x
7. `eval-pair-unique` : eval ⟨fst∘h, snd∘h⟩ x ≡ eval h x
8. `eval-case-inl` : eval ([f,g] ∘ inl) x ≡ eval f x
9. `eval-case-inr` : eval ([f,g] ∘ inr) x ≡ eval g x
10. `eval-case-eta` : eval [inl,inr] x ≡ x
11. `eval-case-unique` : eval [h∘inl, h∘inr] x ≡ eval h x
12. `eval-terminal-unique` : eval f x ≡ eval terminal x (for f : A → Unit)
13. `eval-initial-unique` : eval f x ≡ eval initial x (for f : Void → A)
14. `eval-curry-apply` : eval (apply ∘ ⟨curry f ∘ fst, snd⟩) x ≡ eval f x
15. `eval-curry-eta` : eval (curry (apply ∘ ⟨g∘fst, snd⟩)) a b ≡ eval g a b
16. `eval-bimap-id` : eval ⟨id∘fst, id∘snd⟩ x ≡ x
17. `eval-bicase-id` : eval [inl∘id, inr∘id] x ≡ x

---

### Phase V3: Type System Soundness ✓ (DONE)

**Status**: Completed in `formal/Once/TypeSystem/`

**What**: Define typing rules, prove type soundness.

**Deliverables**:
- `TypeSystem/Typing.agda` - Explicit typing rules, round-trip proof
- `TypeSystem/Soundness.agda` - Progress, preservation, canonical forms

**Theorems**:
1. `round-trip-ir` : ⌊ ⌈ f ⌉ ⌋ ≡ f (typing derivations ↔ IR)
2. `soundness` : IR A B → (⟦A⟧ → ⟦B⟧) (by construction)
3. `canonical-unit` : (x : ⟦Unit⟧) → x ≡ tt
4. `canonical-void` : (x : ⟦Void⟧) → ⊥
5. `canonical-product` : (x : ⟦A*B⟧) → ∃ a b. x ≡ (a,b)
6. `canonical-sum` : (x : ⟦A+B⟧) → (∃ a. x ≡ inj₁ a) ⊎ (∃ b. x ≡ inj₂ b)
7. `compositionality` : eval (g ∘ f) x ≡ eval g (eval f x)

---

### Phase V4: Elaboration Correctness ✓ (DONE)

**Status**: Completed in `formal/Once/Surface/`

**What**: Prove elaboration from surface syntax to IR preserves semantics.

**Deliverables**:
- `formal/Once/Surface/Syntax.agda` - Surface expression type with de Bruijn indices
- `formal/Once/Surface/Elaborate.agda` - Total elaboration function
- `formal/Once/Surface/Correct.agda` - Correctness proof

**Key Challenge**: Surface syntax has lambdas and variables; IR is point-free.

**Theorems**:
1. `elaborate-correct` : ∀ ρ e. evalSurface ρ e ≡ eval (elaborate e) (interpEnv ρ)

**Note**: The theorem is stronger than originally planned - elaboration is total (not partial with `Ok`), meaning the types guarantee only well-formed expressions reach elaboration. Uses function extensionality postulate for the lambda case (safe due to proof erasure during extraction).

**Scope**:
- Lambda elimination (λx.e becomes point-free combinator via curry)
- Variable resolution (de Bruijn indices to projection chains)
- Generator recognition (fst, snd, pair, etc.)
- Case expression distribution (environment distributed through branches)

---

### Phase V5: Optimization Correctness (TODO)

**Status**: Not started

**What**: Prove optimizations preserve semantics.

**Deliverables**:
- `formal/Once/Optimize.agda` - Optimization passes
- `formal/Once/Optimize/Correct.agda` - Correctness proofs

**Current optimizations** (from `Once/Optimize.hs`):
1. Identity elimination: `id ∘ f → f`, `f ∘ id → f`
2. Composition reassociation
3. Projection simplification: `fst ∘ ⟨f,g⟩ → f`

**Theorems**:
1. `optimize-correct` : ∀ ir x. eval (optimize ir) x ≡ eval ir x

**Note**: Each optimization rule needs individual proof.

---

### Phase V6: C Backend Semantics (TODO)

**Status**: Not started

**What**: Define a formal semantics for the C subset we generate.

**Deliverables**:
- `formal/Once/Backend/C/Syntax.agda` - C AST (structs, functions, expressions)
- `formal/Once/Backend/C/Semantics.agda` - Operational semantics for C subset

**Scope**: Define meaning of:
- Struct access (`.fst`, `.snd`)
- Function calls
- Conditionals (for sum types)
- Pointer operations (for functions)

**Key Decision**: How detailed? Options:
1. **Abstract**: Model C at high level, trust translation details
2. **Concrete**: Model actual C semantics (much harder)

**Recommendation**: Abstract model sufficient for Once's simple C output.

---

### Phase V7: Code Generation Correctness (TODO)

**Status**: Not started

**What**: Prove C code generator preserves IR semantics.

**Deliverables**:
- `formal/Once/Backend/C/CodeGen.agda` - IR → C translation
- `formal/Once/Backend/C/Correct.agda` - Correctness proof

**Main Theorem**:
```agda
codegen-correct : ∀ (ir : IR A B) (x : ⟦A⟧) →
                  runC (compile ir) (encodeA x) ≡ encodeB (eval ir x)
```

Where:
- `compile : IR A B → C_Function`
- `runC : C_Function → C_Value → C_Value`
- `encodeA : ⟦A⟧ → C_Value` (Agda value to C representation)

**Sub-theorems** (one per generator):
1. `compile-id` : runC (compile id) v ≡ v
2. `compile-compose` : runC (compile (g∘f)) v ≡ runC (compile g) (runC (compile f) v)
3. `compile-fst` : runC (compile fst) (struct a b) ≡ a
4. `compile-snd` : runC (compile snd) (struct a b) ≡ b
5. `compile-pair` : runC (compile ⟨f,g⟩) v ≡ struct (runC (compile f) v) (runC (compile g) v)
6. `compile-inl` : runC (compile inl) v ≡ tagged 0 v
7. `compile-inr` : runC (compile inr) v ≡ tagged 1 v
8. `compile-case` : runC (compile [f,g]) (tagged t v) ≡ if t=0 then runC (compile f) v else runC (compile g) v
9. `compile-terminal` : runC (compile terminal) v ≡ unit
10. `compile-initial` : (impossible - Void has no values)
11. `compile-curry` : runC (compile (curry f)) v ≡ closure f v
12. `compile-apply` : runC (compile apply) (closure f env, arg) ≡ runC f (env, arg)

---

### Phase V8: QTT Verification (TODO)

**Status**: Not started (Haskell implementation done in Phase 12)

**What**: Prove QTT enforcement is correct.

**Deliverables**:
- `formal/Once/QTT/Quantity.agda` - Quantity semiring
- `formal/Once/QTT/Context.agda` - Quantitative typing contexts
- `formal/Once/QTT/Linearity.agda` - Linearity proofs

**Theorems**:
1. `linear-no-dup` : quantity(x) = 1 → x not duplicated in IR
2. `zero-erased` : quantity(x) = 0 → x not in runtime IR
3. `qtt-semiring` : quantity operations form a semiring

---

### Phase V9: End-to-End Correctness (TODO)

**Status**: Not started

**What**: Compose all phases into end-to-end theorem.

**Main Theorem**:
```agda
compiler-correct : ∀ (source : String) →
  parse source = Ok ast →
  typecheck ast = Ok →
  elaborate ast = Ok ir →
  ∀ x. runC (compile (optimize ir)) (encode x) ≡ encode (eval ir x)
```

**This requires**:
- V4 (elaboration correct)
- V5 (optimization correct)
- V7 (codegen correct)

---

### Phase V10: Extraction and Integration (TODO)

**Status**: Not started

**What**: Extract verified Agda to Haskell, replace unverified code.

**Steps**:
1. Configure MAlonzo extraction in `formal/Extract/Main.agda`
2. Extract `IR.agda` → replace `Once/IR.hs`
3. Extract `Semantics.agda` → replace `Once/Eval.hs`
4. Extract `Optimize.agda` → replace `Once/Optimize.hs`
5. Extract `Backend/C/CodeGen.agda` → replace `Once/Backend/C.hs`
6. Update build to use extracted modules

**Deliverables**:
- `formal/Extract/Main.agda` - Extraction configuration
- Updated `once.cabal` using extracted modules
- Tests pass with extracted code

---

## Summary Table

| Phase | Name | Status | Key Theorem |
|-------|------|--------|-------------|
| V1 | Core IR Semantics | ✓ Done | (definitions) |
| V2 | Categorical Laws | ✓ Done | 17 CCC law proofs |
| V3 | Type Soundness | ✓ Done | Progress + Preservation |
| V4 | Elaboration | ✓ Done | elaborate-correct |
| V5 | Optimization | TODO | optimize-correct |
| V6 | C Semantics | TODO | (definitions) |
| V7 | Code Generation | TODO | codegen-correct |
| V8 | QTT | TODO | linear-no-dup |
| V9 | End-to-End | TODO | compiler-correct |
| V10 | Extraction | TODO | Tests pass |

## Estimated Effort

| Phase | Lines (est.) | Weeks (est.) |
|-------|--------------|--------------|
| V1-V4 | ~1100 | Done |
| V5 | ~200 | 1-2 |
| V6 | ~300 | 2-3 |
| V7 | ~600 | 4-6 |
| V8 | ~400 | 2-3 |
| V9 | ~100 | 1 |
| V10 | ~200 | 2-3 |
| **Total** | **~2900** | **~15-21 weeks** |

## What is NOT Verified

The following remain in the trusted computing base (TCB):

1. **Parser** - Megaparsec-based, not verified
2. **Agda type checker** - Must trust Agda itself
3. **MAlonzo extraction** - Must trust extraction mechanism
4. **GHC** - Compiles extracted Haskell
5. **C compiler** (gcc/clang) - Compiles generated C
6. **OS and hardware** - Runtime environment

This is comparable to CakeML (trusts HOL4, PolyML, OS) and CompCert (trusts Coq, OCaml, OS).

## Definition of Done

Verification is **complete** when:

1. ✓ Phases V1-V4 proven in Agda (DONE)
2. □ Phases V5-V8 proven in Agda
3. □ Phase V9 end-to-end theorem proven
4. □ Phase V10 extraction working, tests pass
5. □ Documentation updated with verification status
6. □ CI runs Agda type-checker on all proofs

At that point, we can claim:

> "The Once compiler from typed IR to C is formally verified. Any well-typed Once program compiles to C code that computes the same result as the IR semantics."

## Future Work

After verification is complete:

1. **Write blog post series** - Document the verification journey for Haskell Weekly or similar. Cover:
   - Why CCC-based IR makes verification tractable (~40x less code than CakeML)
   - The "sugar + verified core" architecture pattern
   - Practical challenges encountered during formalization
   - Recommendations for other language implementers considering formal verification

2. **Optimizer fixpoint iteration** - Run optimization passes repeatedly until no changes occur. Add CLI flag `--max-passes` to limit iterations. Needs decision on default behavior.

3. **Catalog of categorical optimizations** - Document all CCC laws usable as optimizations, identify which are implemented, and track proof status. The generators are well-studied; we should leverage existing mathematical literature.

4. **Tree shaking / dead code elimination** - When compiling, only include reachable functions. Mark entry points, trace call graph through both local project code and external dependencies, exclude all unreachable code from output.

5. **External library FFI** - Enable calling external C libraries (e.g., OpenSSL) via interpretations before native Once implementations exist. Important for adoption.

6. **Project file / dependency management** - Define a project file format for dependencies, build configuration, etc. Needs decision on naming (mathematical term?).

7. **Development process with proofs** - Decide between staging area (unverified `compiler/stage/` that may diverge) vs incremental (keep proofs in sync with every change). Incremental likely better to avoid drift.

8. **Self-hosting** - Write Once compiler in Once. Requires significant language features first (recursion schemes, etc.).

9. **Program verification** - Enable proving properties about Once programs. Example: dining philosophers with starvation-freedom proof. Related to reducing TCB (GHC is large and has bugs).

10. **Reduce trusted computing base** - Investigate alternatives to GHC in the TCB. Self-hosting Once could help here.
