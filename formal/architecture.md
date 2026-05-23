# Once Compiler: Architecture and Proof Bridges

**Status:** Reference doc for the structural-gap-elimination refactor (Plan 0.14
follow-up, 2026-05-18). Captures the two-pipeline architecture, the bridges
between them, and where every remaining postulate sits.

## The two pipelines

```
                                  SOURCE (.once)
                                       │
                                       ▼
                         Parser → TypeCheck → Elaborate → Desugar
                                       │
                                       ▼
                                    CCC IR
                                       │
                         ┌─────────────┴─────────────┐
                         │                           │
                         ▼                           ▼
            ┌──────────────────────┐    ┌──────────────────────────┐
            │ RUNTIME pipeline     │    │ VERIFIED pipeline        │
            │                      │    │                          │
            │ ir-to-trace          │    │ Dispatcher.run-ir-wf     │
            │     │                │    │     │                    │
            │     ▼                │    │     ▼                    │
            │  AbstractTrace       │    │  IRResultAWF             │
            │     │                │    │  (proof object)          │
            │     │ compile-trace  │    │                          │
            │     ▼                │    │  compile-correct         │
            │  Target.Program      │    │  theorem                 │
            │     │                │    │                          │
            │     │ Emit           │    │  (proof-only;            │
            │     ▼                │    │   not extracted)         │
            │   .s file            │    │                          │
            │                      │    │                          │
            │  (extracted by       │    │                          │
            │   MAlonzo, runs at   │    │                          │
            │   user invocation)   │    │                          │
            └──────────────────────┘    └──────────────────────────┘
                         │                           │
                         └──── connected by ─────────┘
                              IRTraceCorrect (Bridge A)
                              DirectSimulation (Bridge B)
```

The two pipelines must agree. Their convergence is what makes "compile-correct"
a meaningful theorem.

## The three layers

| Layer | Type | Lives in |
|-------|------|----------|
| 1 | `IR A B` | `Once.CCC.IR` |
| 2 | `AbstractTrace` | `Once.CCC.Machine.SMCore` |
| 3 | `Program` (per-arch) | `Once.CCC.Target.<arch>.Syntax` |

And three semantic interpretations:

| Layer | Semantics function | Result type |
|-------|---------------------|-------------|
| 1 | `eval : IR A B → ⟦ A ⟧ → ⟦ B ⟧` | denotational |
| 2 | `exec-trace : AbstractTrace → LocState → AllocState → LocState × AllocState` | abstract operational |
| 3 | `exec-prog : Program → X86State → X86State` (per-arch) | concrete operational |

## The two bridges

### Bridge A: IR ↔ AbstractTrace

**Runtime side:** `ir-to-trace : IR A B → AbstractTrace` in
`Once.CCC.Codegen.IRToTrace`. Pure function, produces the abstract trace
extracted to the runtime compiler.

**Verified side:** `Dispatcher.run-ir-wf` returns an `IRResultAWF` containing:
- a `trace` field (the abstract trace the verified path chose)
- `trace-correct` and `alloc-correct` (proving the trace agrees with the
  IR's `eval` semantics)
- `result-place` (witnessing where the result value lives)

**The gap:** the `trace` field in `IRResultAWF` is a *free field*. Each
`run-X` helper picks its own trace by convention. Nothing in the type
system forces it to equal `ir-to-trace ir`. By convention, they match. By
type, they could diverge.

**Current bridge implementation:** `Once.CCC.Codegen.IRTraceCorrect` —
contains `ir-to-trace-correct` which dispatches per-IR and either constructs
a real proof of correspondence (via `run-X` + transport) or admits a
postulate.

### Bridge B: AbstractTrace ↔ Target.Program

**Compile side:** `compile-trace : AbstractTrace → Program` (per-arch,
e.g. `Once.CCC.Target.X86-64.AbstractToX86.compile-trace`).

**Simulation side:** `Once.CCC.Target.<arch>.DirectSimulation.trace-sim`
proves `Corresponds`-preservation: if abstract state corresponds to target
state, then after executing both, they still correspond.

**The gap:** `compile-trace` produces a `Program` with no proof attached.
`trace-sim` reasons about an abstract trace and a target program
independently — there's no type-level guarantee that the program
`trace-sim` reasons about is the one `compile-trace` actually emitted.

**Current bridge implementation:** `compile-correct` in
`Once.CCC.Target.X86-64.Correct.agda` invokes `Dispatcher.run-wf` and
returns the IRResultAWF's data. It does *not* reference `ir-to-trace` or
`compile-trace` — so despite its name, the current `compile-correct`
theorem is about the verified path's Dispatcher, not about what the
extracted compiler emits.

## Status of postulates (2026-05-18)

### Bridge A postulates (in `IRTraceCorrect.agda`)

- `ir-to-trace-correct-compose` — needs structural induction + trace
  decomposition lemma (`exec-trace-append` exists).
- `ir-to-trace-correct-pair` (both modes) — `PairAllocWF.setup-trace` has
  `instr-alloc-stack pair-heap-overhead` that `IRToTrace` omits; the spec
  drift makes the bridge non-definitional.
- `ir-to-trace-correct-apply` — needs closure-invariant threading
  via `decomposeClosureWF`.
- `ir-to-trace-correct-case` — composes
  `SumRecWF.case-dispatch-output-independent` +
  `case-dispatch-alloc-independent` (themselves postulates).
- `ir-to-trace-correct-inl-stack` / `ir-to-trace-correct-inr-stack` /
  `ir-to-trace-correct-curry-stack` — Stack-mode variants; not
  runtime-active because elaborator emits Heap.
- `ir-to-trace-correct-non-layer0` — catchall for recursion schemes
  (`In`, `Cata`, `Para`, `Ana`, `Hylo`, `Fuse`, `in-ν`).

Discharged: `id`, `fst`, `snd`, `terminal`, `arr`, `free-heap`, `out-μ`,
`Out`, `initial`, `SigOp` (via `exec-sigop-respects-semM`), `inl Heap`,
`inr Heap`, `curry Heap`.

### Bridge B postulates / known breakage

- `DirectSimulation.agda:92` — pre-existing `Corresponds` record drift
  (`rdi-eq : rdi-val xs ≡ readReg ... Input1` — type mismatch
  StoredValue vs ValueLocation since Plan 0.2.4.5 Stage B). Currently
  blocks `X86-64.CompileCorrect` from typechecking.
- `Simulation.sigop-codegen-faithful` — per-arch SigOp codegen
  correspondence axiom.

## Hidden vs visible gaps

A *visible gap* is one declared as a named postulate, located in a
predictable place, with explanatory comments. A *hidden gap* is one where
two independently-constructed values are assumed to agree by convention
with no type-level enforcement.

| Where | Visible | Hidden |
|-------|---------|--------|
| Bridge A trace equality | Partially — each per-IR postulate names the equality | The base `trace` field in `IRResultAWF` admits *any* trace by construction |
| Bridge B program correspondence | Partially — `trace-sim` is the theorem | `compile-trace` and `trace-sim` reason about independently-constructed `Program`s |
| `--alloc` CLI flag | n/a | The flag is parsed by CLI but `Desugar.agda` hardcodes `Heap`, so the value is silently dropped |

## Structural fixes (the refactor)

### Phase 1A: eliminate Bridge A's hidden gap

Add a field to `IRResultBase`:

```agda
trace-is-ir-to-trace :
  trace ≡ ir-to-trace-at-frontier (next-slot alloc) ir
```

This forces every `run-X` helper to *prove* its trace equals
`ir-to-trace`. Spec divergence becomes a type error. Currently-by-
convention agreement becomes type-level fact.

### Phase 1B: eliminate Bridge B's hidden gap

Refactor `compile-trace` to be proof-carrying:

```agda
compile-trace-correct :
  ∀ (trace : AbstractTrace) →
  Σ Program (λ prog →
    ∀ s alloc xs → Corresponds s xs alloc →
    Corresponds (proj₁ (exec-trace trace s alloc)) (exec-prog prog xs) ...)
```

Then anyone holding a `Program` from `compile-trace-correct` also holds
the correspondence proof. No way to produce a `Program` without
producing the proof that it matches the abstract trace.

### Phase 0.5: wire `--alloc` through Desugar

Parameterize `desugar` on `AllocMode`. Thread CLI's `--alloc` choice
to `desugar` via `Once.Compile`. Removes the silently-dropped CLI flag,
makes Stack-mode programs a real runtime path.

## Sequencing decision (2026-05-18)

Doing Phase 0 (this doc) + Phase 0.5 (--alloc wiring) first.
Then Phase 1A + 2A-4A (Bridge A structural elimination).
Then re-evaluate before Bridge B.
