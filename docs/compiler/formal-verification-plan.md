# Complete Verification Plan for Once Compiler

## Goal

Verify the `once build` command produces correct machine code with minimal trusted computing base. Specifically:

**Correctness Theorem**: For any well-typed Once program `p`, executing the generated x86-64 machine code on input `x` produces the same result as evaluating the IR semantics on `x`.

```
∀ p x. typecheck(p) = Ok → exec-x86(compile(p), x) = eval(elaborate(p), x)
```

## Why Direct Machine Code?

Analysis of approaches to reducing the trusted computing base (TCB):

| Approach | TCB | Notes |
|----------|-----|-------|
| C backend + gcc | gcc/clang (~15-20M lines) | Current implementation, large TCB |
| C backend + CompCert | CompCert extraction | Verified C compiler, less optimizing |
| LLVM + Vellvm | LLVM (~20M lines) | Trades one large TCB for another |
| Translation validation (seL4-style) | Lifter tool | Must re-verify each binary |
| **Direct x86-64 machine code** | **Assembler only** | **CakeML approach, minimal TCB** |

### Why This Is Feasible for Once

Unlike CakeML (~100K lines of proofs for ML → machine code), Once's categorical IR is dramatically simpler:

| CakeML | Once |
|--------|------|
| Full ML with recursion | 12 generators |
| Pattern matching compilation | Case is a primitive |
| Exception handling | Sums (no exceptions) |
| Garbage collector | Linear (^1) = no GC |
| Complex closure conversion | Curry/apply are primitives |
| Many optimization passes | Categorical laws at IR level |

Each generator compiles to a handful of instructions. For linear code: no heap, no GC, values flow through registers.

### Formal Semantics Available

- **x86-64**: Sail specification from REMS project (Cambridge) / ACL2
- **ARM64**: Official Sail specs from ARM Ltd. (future target)
- **RISC-V**: Clean formal Sail specs (future target)

## Compiler Pipeline

```
┌─────────┐    ┌───────────┐    ┌───────────┐    ┌──────────┐    ┌─────────┐
│ Source  │───▶│   Parse   │───▶│ TypeCheck │───▶│Elaborate │───▶│Optimize │
│ (.once) │    │           │    │           │    │          │    │         │
└─────────┘    └───────────┘    └───────────┘    └──────────┘    └─────────┘
                    │                 │                │               │
                    ▼                 ▼                ▼               ▼
               Surface AST      Type-annotated    Core IR        Optimized IR
                                    AST                                │
                                                          ┌────────────┴────────────┐
                                                          │                         │
                                                          ▼                         ▼
                                                  ┌──────────────┐          ┌─────────────┐
                                                  │ x86-64 CodeGen│          │  C CodeGen  │
                                                  │  (PRIMARY)   │          │ (secondary) │
                                                  └──────────────┘          └─────────────┘
                                                          │                         │
                                                          ▼                         ▼
                                                   x86-64 Machine             C Source
                                                       Code                 (portable)
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

### Phase V6: x86-64 Backend Semantics (TODO)

**Status**: Not started

**What**: Define formal semantics for x86-64 instruction subset used by Once.

**Deliverables**:
- `formal/Once/Backend/X86/Syntax.agda` - x86-64 instruction subset
- `formal/Once/Backend/X86/Semantics.agda` - Operational semantics (based on Sail x86)

**x86-64 Instructions Used** (minimal subset):

| Generator | x86-64 Instructions |
|-----------|---------------------|
| `id` | `nop` or `mov reg, reg` |
| `compose` | Sequencing (inline) |
| `fst` | `mov reg, [reg+0]` (load first field) |
| `snd` | `mov reg, [reg+8]` (load second field) |
| `pair` | `mov [reg+0], val1; mov [reg+8], val2` |
| `inl` | `mov [reg+0], 0; mov [reg+8], val` (tag + value) |
| `inr` | `mov [reg+0], 1; mov [reg+8], val` (tag + value) |
| `case` | `cmp [reg+0], 0; je/jne` (branch on tag) |
| `terminal` | `nop` (discard) |
| `initial` | `ud2` (unreachable) |
| `curry` | Store closure: `mov [reg], env; mov [reg+8], code_ptr` |
| `apply` | `call` through closure |

**Key Simplification**: For linear code (quantity 1), values live in registers - no heap allocation, no GC.

**Formal Foundation**: Base semantics on Sail x86-64 specification from REMS project.

---

### Phase V7: x86-64 Code Generation Correctness (TODO)

**Status**: Not started

**What**: Prove x86-64 code generator preserves IR semantics.

**Deliverables**:
- `formal/Once/Backend/X86/CodeGen.agda` - IR → x86-64 translation
- `formal/Once/Backend/X86/Correct.agda` - Correctness proof

**Main Theorem**:
```agda
codegen-x86-correct : ∀ (ir : IR A B) (x : ⟦A⟧) →
                      exec-x86 (compile-x86 ir) (encode-x86 x) ≡ encode-x86 (eval ir x)
```

Where:
- `compile-x86 : IR A B → X86_Instructions`
- `exec-x86 : X86_Instructions → X86_State → X86_State`
- `encode-x86 : ⟦A⟧ → X86_Value` (Agda value to x86 representation)

**Sub-theorems** (one per generator):
1. `compile-id-x86` : exec-x86 (compile-x86 id) v ≡ v
2. `compile-compose-x86` : exec-x86 (compile-x86 (g∘f)) v ≡ exec-x86 (compile-x86 g) (exec-x86 (compile-x86 f) v)
3. `compile-fst-x86` : exec-x86 (compile-x86 fst) (pair a b) ≡ a
4. `compile-snd-x86` : exec-x86 (compile-x86 snd) (pair a b) ≡ b
5. `compile-pair-x86` : exec-x86 (compile-x86 ⟨f,g⟩) v ≡ pair (exec-x86 (compile-x86 f) v) (exec-x86 (compile-x86 g) v)
6. `compile-inl-x86` : exec-x86 (compile-x86 inl) v ≡ tagged 0 v
7. `compile-inr-x86` : exec-x86 (compile-x86 inr) v ≡ tagged 1 v
8. `compile-case-x86` : exec-x86 (compile-x86 [f,g]) (tagged t v) ≡ if t=0 then exec-x86 (compile-x86 f) v else exec-x86 (compile-x86 g) v
9. `compile-terminal-x86` : exec-x86 (compile-x86 terminal) v ≡ unit
10. `compile-initial-x86` : (impossible - Void has no inhabitants)
11. `compile-curry-x86` : exec-x86 (compile-x86 (curry f)) v ≡ closure f v
12. `compile-apply-x86` : exec-x86 (compile-x86 apply) (closure f env, arg) ≡ exec-x86 (compile-x86 f) (env, arg)

**Calling Convention**: Define Once-specific calling convention optimized for combinators:
- Environment pointer in `r12`
- Argument in `rdi`
- Result in `rax`
- Linear values stay in registers when possible

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

**What**: Compose all phases into end-to-end theorem for x86-64.

**Main Theorem**:
```agda
compiler-correct : ∀ (source : String) →
  parse source = Ok ast →
  typecheck ast = Ok →
  elaborate ast = Ok ir →
  ∀ x. exec-x86 (compile-x86 (optimize ir)) (encode-x86 x) ≡ encode-x86 (eval ir x)
```

**This requires**:
- V4 (elaboration correct)
- V5 (optimization correct)
- V7 (x86-64 codegen correct)

**Result**: End-to-end verified compilation from Once source to x86-64 machine code.

---

### Phase V10: Extraction and Integration (TODO)

**Status**: Not started

**What**: Extract verified Agda to Haskell, replace unverified code.

**Steps**:
1. Configure MAlonzo extraction in `formal/Extract/Main.agda`
2. Extract `IR.agda` → replace `Once/IR.hs`
3. Extract `Semantics.agda` → replace `Once/Eval.hs`
4. Extract `Optimize.agda` → replace `Once/Optimize.hs`
5. Extract `Backend/X86/CodeGen.agda` → replace `Once/Backend/X86.hs`
6. Update build to use extracted modules

**Deliverables**:
- `formal/Extract/Main.agda` - Extraction configuration
- Updated `once.cabal` using extracted modules
- Tests pass with extracted code
- x86-64 binaries run correctly

---

### Phase V11: C Backend (OPTIONAL)

**Status**: Not started (current implementation exists but unverified)

**What**: Optionally verify the C backend for portability.

**Why Optional**:
- C backend keeps gcc/clang in TCB (~15-20M lines unverified)
- Primary value is portability to non-x86-64 platforms
- Lower priority than verified x86-64 backend

**Deliverables** (if pursued):
- `formal/Once/Backend/C/Syntax.agda` - C AST subset
- `formal/Once/Backend/C/Semantics.agda` - C operational semantics
- `formal/Once/Backend/C/CodeGen.agda` - IR → C translation
- `formal/Once/Backend/C/Correct.agda` - Correctness proof

**Alternative**: Use C backend without verification for platforms where:
- x86-64 is not available
- Quick prototyping is needed
- Full verification is not required

---

## Summary Table

| Phase | Name | Status | Key Theorem |
|-------|------|--------|-------------|
| V1 | Core IR Semantics | ✓ Done | (definitions) |
| V2 | Categorical Laws | ✓ Done | 17 CCC law proofs |
| V3 | Type Soundness | ✓ Done | Progress + Preservation |
| V4 | Elaboration | ✓ Done | elaborate-correct |
| V5 | Optimization | TODO | optimize-correct |
| V6 | **x86-64 Semantics** | TODO | (definitions) |
| V7 | **x86-64 CodeGen** | TODO | codegen-x86-correct |
| V8 | QTT | TODO | linear-no-dup |
| V9 | End-to-End | TODO | compiler-correct (x86-64) |
| V10 | Extraction | TODO | Tests pass |
| V11 | C Backend | OPTIONAL | codegen-c-correct |

## Estimated Effort

| Phase | Lines (est.) | Weeks (est.) |
|-------|--------------|--------------|
| V1-V4 | ~1100 | Done |
| V5 (Optimization) | ~200 | 1-2 |
| V6 (x86-64 Semantics) | ~400 | 3-4 |
| V7 (x86-64 CodeGen) | ~600 | 4-6 |
| V8 (QTT) | ~400 | 2-3 |
| V9 (End-to-End) | ~100 | 1 |
| V10 (Extraction) | ~200 | 2-3 |
| **Total (V1-V10)** | **~3000** | **~16-22 weeks** |
| V11 (C Backend, optional) | ~900 | 6-9 |

### Comparison to Other Verified Compilers

| Project | Lines of Proof | Target |
|---------|---------------|--------|
| CakeML | ~100,000 HOL4 | ML → machine code |
| CompCert | ~100,000 Coq | C → assembly |
| **Once** | **~3,000 Agda** | Once → x86-64 |

Once requires ~30-40x less proof code due to:
- 12 generators vs full language
- No GC (linear types)
- No exceptions (sums)
- Curry/apply as primitives (no closure conversion)
- Categorical laws handle optimization

## Trusted Computing Base (TCB)

### After V10 Completion (x86-64 Backend)

The following remain in the trusted computing base:

1. **Parser** - Megaparsec-based, not verified
2. **Agda type checker** - Must trust Agda itself
3. **MAlonzo extraction** - Must trust extraction mechanism
4. **GHC** - Compiles extracted Haskell (compiler only)
5. **OS and hardware** - Runtime environment

**Removed from TCB**: C compiler (gcc/clang) - no longer needed for verified path.

### TCB Comparison

| Project | TCB Components |
|---------|---------------|
| Once (x86-64) | Agda, MAlonzo, GHC, OS, HW |
| CakeML | HOL4, PolyML, OS, HW |
| CompCert | Coq, OCaml, **gcc** (for non-verified parts), OS, HW |
| Once (C backend) | Agda, MAlonzo, GHC, **gcc/clang**, OS, HW |

The x86-64 backend achieves a TCB comparable to CakeML - no C compiler required.

## Definition of Done

Verification is **complete** when:

1. ✓ Phases V1-V4 proven in Agda (DONE)
2. □ Phase V5 optimization correctness proven
3. □ Phases V6-V7 x86-64 backend proven in Agda
4. □ Phase V8 QTT correctness proven
5. □ Phase V9 end-to-end theorem proven
6. □ Phase V10 extraction working, x86-64 binaries run correctly
7. □ Documentation updated with verification status
8. □ CI runs Agda type-checker on all proofs

At that point, we can claim:

> "The Once compiler from typed IR to x86-64 machine code is formally verified. Any well-typed Once program compiles to machine code that computes the same result as the IR semantics. No C compiler is required in the trusted computing base."

This places Once alongside CakeML as one of the few languages with a fully verified compilation path to machine code.

## Future Work

After x86-64 verification is complete:

### Additional Verified Backends

1. **ARM64 backend** - Use ARM's official Sail specifications. High value due to Apple Silicon, AWS Graviton, mobile devices. Following the same pattern as x86-64, estimated ~1500 lines Agda.

2. **RISC-V backend** - Clean ISA with excellent formal semantics. Good for embedded systems and future hardware. Estimated ~1500 lines Agda.

3. **WebAssembly backend** - Formal semantics exist. Enables browser deployment with verification. Estimated ~1200 lines Agda.

### Compiler Improvements

4. **Optimizer fixpoint iteration** - Run optimization passes repeatedly until no changes occur. Add CLI flag `--max-passes` to limit iterations.

5. **Catalog of categorical optimizations** - Document all CCC laws usable as optimizations, identify which are implemented, and track proof status.

6. **Tree shaking / dead code elimination** - When compiling, only include reachable functions. Trace call graph, exclude unreachable code.

### Ecosystem

7. **External library FFI** - Enable calling external C libraries (e.g., OpenSSL) via interpretations before native Once implementations exist.

8. **Project file / dependency management** - Define a project file format for dependencies, build configuration, etc.

### Documentation

9. **Write blog post series** - Document the verification journey. Cover:
   - Why CCC-based IR makes verification tractable (~30-40x less code than CakeML)
   - The "sugar + verified core" architecture pattern
   - Practical challenges encountered during formalization
   - Recommendations for other language implementers

### Long-term

10. **Self-hosting** - Write Once compiler in Once. Would further reduce TCB by eliminating GHC.

11. **Program verification** - Enable proving properties about Once programs (e.g., dining philosophers with starvation-freedom proof).

12. **Further TCB reduction** - Investigate verifying MAlonzo extraction or using alternative extraction mechanisms.
