# Once — Compiler Architecture (One Page)

## Goal

End-to-end **machine-checked correctness**: a Once source program
compiled against a target environment satisfies the surface-level
semantics prescribed by `eval`. Every pipeline stage is a function
with a refinement proof; the top-level theorem
(`Once.Compile.EndToEnd`) composes them.

**The proofs typecheck under Agda's `--safe`.** The compile
function is **parameterised over its environment** — the target
machine model, the SigOp set (syscalls, I/O, hardware primitives,
or any other effectful operations), the allocator interface — so
the proof chain contains no free-floating postulates. What the
user plugs in is their choice and determines the trust surface:
plugging in a pure Agda interpreter gives a closed proof (trust
= 0); plugging in a formally proven external implementation (e.g.
seL4-style verified syscalls) inherits that implementation's own
guarantees; plugging in a trusted-to-spec real implementation
makes the spec the trust point. Whatever the user installs is
visible in the top-level signature — there are no hidden
postulates inside the proof chain to go digging for.

## Module Tiers

The codebase is layered into four tiers and **dependency arrows point
only UP** — no tier imports a tier below it. The two middle tiers (the
*meaning* and the *compiler*) are independent siblings, joined at the top
by adequacy. A module's namespace prefix tells you its tier.

```
                    ADEQUACY  (join) ............ Once.Adequacy.*
              machine-trace (compile src) ≡ projTrace ⟦src⟧ˢ
                   ╱                              ╲
     DENOTATION (spec) ......... Once.Denotation.*    OPERATIONAL (impl)
     the meaning: trace monad,                        Once.CCC.{Machine,
     source denotation ⟦_⟧ˢ,                          Codegen,Target,Eval},
     observable Behavior                              Once.Optimize · Place
                   ╲                              ╱
              KERNEL  (object language + point-free syntax)
   Once.{Type, Word, Functor.*, Semantics.{Functor,Value}, IR, SigOp.Info}
              — depends only on the standard library
```

- **Kernel** — the object language and its point-free IR (`Once.IR`), the
  type language (`Once.Type`), the machine word (`Once.Word`, D054), the
  polynomial-functor + value-model semantics (`Once.Semantics.{Functor,
  Value}`), and the SigOp descriptor (`Once.SigOp.Info`). Imports only the
  stdlib. The shared vocabulary both the spec and the compiler are written
  against.
- **Denotation (spec)** — the *meaning*: `eval`'s observable extension via
  the trace monad, the source denotation `⟦_⟧ˢ`, and the observable
  `Behavior`. Self-contained — imports the kernel, nothing operational.
  Typechecks escape-hatch-clean (`make denot-safe`): the only axioms are
  `funext` + `bisimS-to-eq`; the residual domain contracts are the
  SigOp/arith value specs.
- **Operational (impl)** — the compiler proper: the abstract machine, the
  per-IR well-formedness proofs codegen needs (`Once.CCC.Machine.IR.*WF`),
  IR→trace lowering, the optimizer, and the per-target backends.
- **Adequacy (join)** — the grand theorem (`Once.Adequacy.*`) tying the two
  middle tiers together: target execution refines the source meaning. The
  elaboration-preserves-meaning bridge (`faithful`) lives here too, since it
  references the elaborator (operational), not pure denotation.

The kernel was lifted out of the operational `Once.CCC.*` namespace (D066)
precisely so the namespace mirrors this layering.

## Pipeline

| Stage | Module | What | Correctness |
|---|---|---|---|
| **1. Parse** | `Grammar` / `Parser` | Source text → `Module` AST | Grammar round-trip (`ParserRelation`, `Roundtrip`) |
| **2. Type-check** | `TypeCheck` | Validate signatures, elaborate raw → `Surface` with full kind/type annotations | `TypeCheck.Soundness` + `Completeness` |
| **3. Surface → IR** | `Surface.Elaborate` | Translate to point-free cartesian-closed IR (`IR A B`) | `Surface.Correct.elaborate-correct` (semantic preservation) |
| **4. Optimise** | `Optimize` / `Fusion` / `Escape` | Categorical-law rewrites, fusion of recursive schemes, escape analysis | Each rewrite preserves `eval` |
| **5. Place** | `Place` | For each value-producing IR node, pick `AllocMode` (Stack vs Allocator) and — for Allocator-mode calls — pick which concrete allocator backs them, based on escape / lifetime / size analysis. Also emit `free` *instructions* (these live in the abstract trace, not the IR — there is no `free` IR constructor) for any allocator memory used. | Both choices are stamped onto the IR + the corresponding free instructions are emitted; downstream stages just execute what Place decided |
| **6. Codegen** | `CCC.Target.<arch>` | Emit machine instructions per IR node; each value-producing node's per-use-site mode tag picks the Stack-mode or Heap-mode implementation | `CCC.Target.<arch>.Correct.compile-correct` (target preserves `eval`) |
| **7. Assembly** | `Compiler` | Wire the chain into one `CorrectCompiler` record consumed by the CLI | If the assembly typechecks, the compiler is correct (modulo declared postulates) |

## IR Core

The IR (`Once.IR`, kernel tier) is a **point-free categorical core**.
Every IR is a morphism
`IR A B`; composition is `_∘_`, products are `⟨_,_⟩` / `fst` / `snd`,
sums are `inl` / `inr` / `case`, recursive types use `μ` / `In` /
`cata` and `ν` / `Out` / `ana`. Primitive operations that are not
built from the categorical core live in `SigOp` / `Eff` (see
**SigOps** below).

A single semantic interpreter `eval : IR A B → ⟦A⟧ → ⟦B⟧` defines
what each IR mathematically computes — `⟦A⟧` is the Agda Set that
the IR-type `A` denotes, and `eval` is a recursive function that
interprets each constructor (composition is function composition,
pair is tupling, cata folds the algebra over the μ-value, ...).
`eval` is the ground truth that the compilation chain has to
preserve.

## SigOps

A **SigOp** ("signature operation") is a named primitive operation
that's not constructed from the categorical core — it could be a
syscall, an I/O primitive, a hardware op, an arithmetic primitive
like negation, or anything else the program needs. Each SigOp has
a name and a signature `A → B`. Once programs invoke them by
composing SigOps into the IR like any other morphism.

The CCC layer doesn't define what a SigOp *computes* — that's the
plugin's job — but it does require every SigOp to satisfy a
**CCC contract** (the `PreservesCCC` record in the code): a small
set of proof obligations stating that the SigOp's runtime
behaviour doesn't violate the invariants the rest of the CCC
proofs depend on (frame preservation, scratch reclamation, alloc
discipline, pointer discipline, …). Whoever emits a SigOp must
discharge `PreservesCCC`; once they do, every IR composition that
uses that SigOp inherits CCC's correctness — there is no need to
re-prove the surrounding composition.

`main : Eff Unit Unit` has no return value. The **observable
behaviour** of a Once program is the **trace of SigOp invocations**
it produces, in order, with their arguments (e.g. an "exit code"
is the argument to `linux.exit`, not a returned value). What each
SigOp's runtime *does* is supplied by whatever the user plugs into
the compile function's environment parameter (see Goal): a pure
Agda implementation, a formally proven external one (seL4-style
verified syscalls), or a trusted-to-spec real syscall — the
IR-level proofs are agnostic. Correctness shows that the compiled
program issues exactly the SigOp invocations the source program
asked for, in the same order, with the same arguments; what the
plugin does *with* those invocations is the plugin's contract.

## AllocMode

Each value-producing IR constructor (pair, inl/inr, In, in-ν, curry,
...) carries an `AllocMode ∈ {Stack, Allocator}` tag **per use site**
(the current code spells the second one `Heap`; same thing).
**`AllocMode` says where the *output* lives**, not what happens
during execution:

- **Stack mode** — the output value occupies one or more stack
  slots (addressed by slot index, no frame indirection).
- **Allocator mode** — the output value sits in cells supplied by
  an allocator, reached via a pointer (`AtDynamic`). All allocators
  expose the same malloc-like interface, so the IR-level
  implementation is uniform; *which* concrete allocator (general
  malloc, a fixed-size mempool, a region, an arena, ...) backs each
  call is a separate choice made by Place.

**The mode tag is a *use-site* annotation, not an IR-level
commitment.** Each value-producing IR has exactly two
implementations — one for Stack mode, one for Allocator mode (e.g.
`PairStackWF.run-pair` vs `PairAllocWF.run-pair-heap` for `pair`). The
Dispatcher routes by the use-site tag. Simple non-allocating IRs
(`id`, `fst`, `snd`, ...) are mode-polymorphic — one implementation
typechecks at any mode.

An IR cannot decide its own mode because it sees only a local
window of the program; whether a value is "long-lived enough to
need an allocator" — and which concrete allocator to route an
Allocator-mode call to — are non-local properties. Only Place has
the global view to make those calls.

## Pointer Discipline

Cross-storage references are constrained one-way:

| From → To | Allowed? |
|---|---|
| Stack value → Allocator pointer | ✓ |
| Allocator object → Allocator pointer | ✓ |
| Allocator object → Stack location | **✗ forbidden** |

The forbidden direction (allocator → stack) would let an allocator
object outlive the stack location it references — a classic
dangling-pointer situation. Banning it means the heap is a
self-contained graph rooted in stack values, and stack lifetime
reasoning never has to bleed into allocator-object reasoning. The
proof obligations rely on this: once Place has placed everything,
no IR can violate it because the per-IR Allocator-mode
implementation only writes pointers obtained from the allocator
into its cells.

**Output sizes are not always statically known.** IRs over
non-recursive types (products, sums, primitives) have output sizes
fixed at compile time. IRs whose output type involves a μ-recursive
type (cata results, list-building algebras, etc.) have
**runtime-dependent sizes** — determined by the input data at
execution time. Both kinds of IRs can target either `AllocMode`:
runtime-sized outputs grow incrementally past the frontier (the IR
issues a sequence of bumps as it produces each element) rather
than requiring one up-front allocation. The stack-side
implementation strategies — incremental frontier advance, scratch
discipline, in-place overwrite for size-preserving functor maps,
linear-consumption reclamation — are spelled out in
`docs/design/ir-stack-layout.md`.

## Scratch & Reclamation

Every IR uses **scratch** during execution for its intermediate
work. Scratch always lives on the stack, past the frontier — i.e.,
at slot indices beyond where the IR's output ends. **Both Stack-mode
and Heap-mode IRs share this scratch discipline:** intermediate
computations happen in stack slots regardless of where the final
output lives.

Stack layout sketch for any execution. Three slot-index positions
matter:

```
[ slots used before this IR | IR output slots | IR scratch slots ]
                              ↑                ↑                  ↑
                       start frontier    final frontier      peak
                       (next-slot at     (next-slot after    (max-slot-written
                        IR start)         IR returns)         during execution)
```

- **start frontier** = `next-slot alloc` (before the IR runs)
- **final frontier** = `next-slot (apply-bump bump alloc)` (after
  the IR returns; scratch is gone, output sits between start and
  final)
- **peak** = `max-slot-written` (highest slot index touched during
  execution, including scratch; only visible mid-trace)

"Past" / "frontier" are abstract: slot indices are monotonic
identifiers, not memory addresses. Some targets grow the physical
stack up, others down — the abstract model is independent of that.

**Every IR fully reclaims its scratch before returning.** After the
IR completes, no scratch slots remain past the new frontier. The
frontier has advanced by exactly the IR's stack output footprint
(zero for Heap-mode outputs; static for fixed-size Stack outputs;
runtime-determined for recursive Stack outputs). The proof
obligation
`alloc-correct : proj₂ (exec-trace trace s alloc) ≡ apply-bump bump alloc`
ties the trace's final alloc state to the producer's declared
`bump`, so a trace that grew the stack and forgot to reclaim it
back to the declared frontier is a type error.

**Allocator usage.** Allocations come in three flavours by who
owns the matching `free`:

- **Transient allocations** — internal to a single IR's execution
  (rare; avoided by design — prefer stack scratch). The IR's own
  per-mode implementation pairs every transient `alloc` with a
  matching `free` inside its own trace. From the caller's view
  these are invisible: by the time the IR returns, the transient
  memory is gone.
- **Locally-consumed sub-IR outputs** — a sub-IR allocates an
  Allocator-mode output that the surrounding compositional IR
  (`compose`, `pair`, `case`, …) consumes internally and does not
  propagate to its own output. The compositional IR sees the
  whole flow locally, so *it* emits the matching `free` in its
  own trace at the point of consumption. What the sub-IR
  considers persistent becomes transient from the parent IR's
  perspective.
- **Escaping allocations** — the Allocator-mode output of an IR
  that survives past its immediate consumer too, eventually
  becoming part of the surrounding program's output or being
  held in long-lived data. The matching `free` belongs to
  whatever later point in the program first observes the value
  becoming dead. The Place stage does the cross-IR lifetime
  analysis and inserts that `free` at the right spot — only
  Place sees far enough.

**No IR — Stack or Allocator — is allowed to leak memory.** After
the IR returns, the live allocator memory traceable to this IR is
exactly its escaping output value (zero for Stack-mode IRs).
After the surrounding program later drops the last reference,
Place's emitted `free` reclaims it.

## Quantities

Each value in Once carries a usage **quantity** drawn from
`{0, 1, ω}`:

- **0** (erased) — type-level only; the value is not present at
  runtime and the compiler removes it entirely.
- **1** (linear) — used exactly once at runtime.
- **ω** (many) — unrestricted; used any number of times, possibly
  including zero.

Each quantity unlocks different optimisations. 0-values disappear
from the runtime — zero memory, zero instructions. 1-values
support destructive consumption: the consumer can overwrite the
input's storage in place, a sub-IR result flowing into a linear
consumer can have its slot reused or its allocation reclaimed
immediately, no copies or parallel buffers needed. ω-values may
be read multiple times and need a copy / share / refcount
strategy.

**Once infers quantities.** The compiler analyses every value
and picks the most restrictive quantity that fits, then applies
the corresponding optimisations. The programmer does not declare
anything for this to happen — if a value is provably linear, it
is treated as linear; if it is provably erasable, it is erased.

A programmer can **opt in** to a quantity at the type level when
they want it to be a *contract* — e.g. an interface function that
requires its callers to consume an argument exactly once, or a
type-level proof that must be erased at runtime. Annotations are
purely for type-enforced quantities; they do not change what the
compiler does with unannotated code.

So Once is **also linear** — and **also erased** — but it is
*not* a strictly quantitative language where the programmer must
mark every value's usage discipline up front. Quantities are
opportunities the compiler exploits, not burdens the programmer
carries.

## Proof Architecture

The CCC layer (`Once.CCC.Machine.IR.*WF`) carries the per-IR proofs
that codegen needs. Each producer constructs an `IRResultAWF m ir x s
alloc` consisting of:

- **`IRResultBase`** — the trace executed, the final state, the
  declared `bump : AllocBump`, plus tied-down equalities:
  - `trace-correct` : `proj₁ (exec-trace trace s alloc) ≡ final-state`
  - `alloc-correct` : `proj₂ (exec-trace trace s alloc) ≡ apply-bump bump alloc`
  - `trace-is-ir-to-trace` : `trace ≡ ir-to-trace-at-frontier _ ir`
  - `result-place` : the result location's shape matches `m`
- **`IRStackBudget`** — stack budget bookkeeping (`max-slot-written`,
  `frontier-slot-stable`, write/read bounds).
- **`IRHeapBudget`** — heap budget bookkeeping (`max-heap-ref-written`,
  consistency between `heap-budget` and `bump`).

`alloc-correct` ties the trace to the bump (so a producer cannot
declare a bump that lies about what the trace did to the alloc
state). `trace-is-ir-to-trace` ties the trace to the IR (so codegen
cannot drift from the IRToTrace spec). `result-place` ties the
result location to the mode tag.

## End-to-End Theorem

`Once.Compile.EndToEnd` composes:

```
elaborate-correct  (Surface → IR)
∘ compile-correct  (IR → target)
```

into a single statement that surface evaluation matches target
execution. The CLI consumes the result via `Once.Compiler`.

## Conventions

- **One file per concept**; large files are split into a directory
  (`PairStackWF/Validity.agda`, `Bounds.agda`, `Assembly.agda`,
  `Setup.agda`, `Middle.agda`, `Finalize.agda`).
- **No postulates** in producer code. `SMP.!!` placeholders are
  visible debt; the goal state has none.
- **No `--no-positivity-check`, `--no-termination-check`, or `--type-in-type`** outside explicitly marked workarounds.
- **`abstract` blocks** wrap proof chains that downstream consumers
  only need propositionally (keeps elaboration tractable).
