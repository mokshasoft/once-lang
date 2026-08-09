# Residual ledger — the x86-64 ↔ abstract-machine correspondence

Every postulate in the x86-64 correspondence cone, what class it is, and what
would discharge it. **Keep this current**: a residual that changes state without
its row changing is how a stale pointer like `cata-correct`'s survives (that one
named `CataNat*` as its discharge four days before two thirds of `CataNat*` were
deleted).

## Why the count went UP, and why that is correct

`master` assumed the entire simulation as ONE postulate (`conc-flat-sim-just`),
plus `program-bound` and the loader axiom — three. The branch replaced the
blanket assumption with a real proof and a set of NAMED residuals. The content
assumed shrank enormously while the count rose.

    master:  3   (one of them = the whole theorem)
    branch: 13 → 11 → 10, and the last move held it at 10 while moving a
                          residual OUT of the correspondence (D091: one
                          postulate deleted, one abstract-machine invariant
                          added, one theorem gained)

So **the count is not the metric** — this supersedes the older "only if the end
count goes down" gate, which is the wrong test whenever one side of the
comparison is a blanket postulate. The metric is: is each residual NAMED,
CONDITIONED on reachable states of emitted programs, and does it have a route?
That is also what `MERGE.md` actually asks for ("explainable residual by
residual").

## WHICH ARE ACTUALLY CORRESPONDENCE GAPS

Being IN `…ArchCorrectness/X86-64/` does not make a residual a correspondence
gap. The test is whether its STATEMENT relates the concrete machine to the
abstract one — read it off the signature: does it mention `X.State` /
`run-events` at all, or only `AbstractTrace` / `FlatState` / `IR`?

    genuine correspondence gaps (0)  ← ALL THREE DISCHARGED 2026-08-06
      events-running-thunk → `thunk-step`  (D090)
      events-running-ret   → `ret-step`    (D095)
      events-running-call  → `call-step`   (D098)
    No `events-running-*` postulate remains, and nothing in the cone is a model
    gap. Each closed by fixing the MACHINE rather than assuming harder: the call
    was modelled (D092), the window made one-directional and the frame cleared
    (D090), the code address made an address (D096).
      (events-running-thunk DISCHARGED 2026-08-06 — see #8)
      Both were blocked on the abstract machine not modelling the call. It does
      now (D092), so both sides of each equation describe the same transition
      and what is left is a DEFERRED PROOF: the `CompiledCorr` component
      relating the ghost `fret` to the cells the concrete `call` pushed, plus
      its ~37-site ripple in `FlatSimulation`. The concrete half of the
      transfer already exists (`FlatComposition.find-thunk-pres`).

    correspondence-located, CPU-MODEL caused (3):
      arith-sigop-contract, external-sigop-contract, conc-fuel
      (see THE CPU-MODEL ROOT below)

    obligations the correspondence CONSUMES, owned by other layers (5):
      emitted-shape-check   — codegen        (only `ir-to-trace`)
      run-meets             — abstract machine + shape table (no `X.State`)
      main-heap-moded       — frontend       (only `IR`)
      entry-size            — resource/frontend plumbing (only `ir-size`)
      emitted-thunk-guarded      — codegen (only `ir-to-trace`)
      emitted-code-addr-has-body — codegen (only `ir-to-trace`)
      ret-site-owes              — abstract machine (no `X.State`)
      ret-budget-matches         — emitter bracket (no `X.State`)
      call-site-shape            — abstract machine (no `X.State`)

    boundary axioms (2):
      stack-top-in-stack, x86-64-loader-faithful

This matters for SCOPE. A branch whose subject is the correspondence is not
finished by discharging the cheap rows — those are other layers' work that
happens to be named here. It is finished by the genuine gaps, which are also the
hardest. Of the original three: `events-running-thunk` is DISCHARGED (a
theorem); `events-running-ret` was never independent (D091 — it is blocked BY
the call); and `events-running-call`, the model gap, is CLOSED AS A MODEL GAP
by D092 — the machine performs the call now. Both survivors are ordinary
deferred proofs sharing one missing piece: the return-address component.

## Classes

- **axiom** — an honest external boundary. Permanent.
- **invariant** — a true property of the running program; a linker or static
  sizing pass could discharge it. Belongs as a PARAMETER (D087), never a
  postulate: a parameter is the hole a future proof slots into, a postulate can
  only be deleted and re-plumbed.
- **deferred proof** — provable with the machinery that exists; nobody has
  written it.
- **stub** — assumed only because something else is UNDEFINED. Not a fact about
  the world. Discharged by defining the thing, not by assuming harder.
- **model gap** — the abstract machine does not model what the concrete one
  does. No proof can bridge it; the semantics has to change first.

## The ledger

| # | residual | where | class | status / route |
|---|----------|-------|-------|----------------|
| — | `program-bound` | (was ×3 arches) | invariant | **DONE** — one parameter threaded `Certified → Compiler → ArchCorrectness → arches` |
| — | `x86-64-heap-room` | (was apex) | invariant | **DONE** — parameter; type named in `…X86-64/ResourceBounds.HeapRoom` |
| — | `entry-frame` | (was `FlatFromObs`) | — | **DONE** — parameter; each arch supplies its own |
| — | `entry-frame-base` | (was apex) | — | **DONE, DISCHARGED** — x86-64's frame IS the loader `%rsp`, so `refl` |
| 1 | `stack-top-in-stack` | `…ArchCorrectness.X86-64` | axiom-ish | the residue of the two above: the loader's `%rsp` lies in the stack region. Could fold into `stack-top`'s own postulate by giving it type `StackPointer` instead of `Word` |
| 2 | `entry-size` | `FlatFromObs` | invariant | → parameter, same pattern as `heap-room` |
| 3 | `arith-sigop-contract` | `ConcFlatSim` | **stub** | see THE CPU-MODEL ROOT below — conclusion is `arith-env-x86-64 … sym ≡ just pl`, unprovable while that function is undefined |
| 4 | `external-sigop-contract` | `ConcFlatSim` | **stub** | same root: conclusions are about `arith-env-x86-64` AND `ev-x86-64`, both undefined |
| 5 | `emitted-shape-check` | `ConcFlatSim` | deferred proof | the `FrameFreeTrace`/`SlotBudget`-mold walk over `ir-to-trace'`, `check-++` at every splice, G2 invariants as the `LabelEnv` values |
| 6 | `run-meets` | `ConcFlatSim` | deferred proof | induction on `Reachable`; entry via D074 all-tag state, step via per-instruction transfer soundness |
| 7 | `main-heap-moded` | apex | deferred proof | induction over the elaborator: building with `C.Heap` yields only `Heap` modes |
| — | `events-running-thunk` | (was `ConcFlatSim`) | — | **DONE, DISCHARGED 2026-08-06** — now the theorem `ConcFlatSim.thunk-step`. `block-step-c-thunk` (a theorem since D090) fed `lo' = lo hv ⊓ (%rsp ∸ 8b)`; its `front-lo'`/`fits` come from the new `x86-64-stack-room` PARAMETER (`ResourceBounds.StackRoom`), the exact mirror of `HeapRoom` |
| 9 | `ret-site-owes` + `ret-budget-matches` | `ConcFlatSim` | deferred proof | REPLACED `events-running-ret` 2026-08-06 (D095), now the THEOREM `ret-step` over the proven `block-step-c-ret`. Neither mentions `X.State`. (1) a reachable `c-ret` owes a return — route: static segment depth = `fret` depth + `SlotBudget` bracket neutrality; (2) the released budget IS the reservation in force — the emitter writes one `bb` twice. Both belong in the `emitted-thunk-guarded` induction. HISTORY: THE COMPONENT LANDED (D093): `CompiledCorr.ret-eq` says every ghost `fret` entry is really in memory, at its frame's window end. Three inputs left, all designed in D093 — the exact one-slot gap (as a `GapNext` conjunct in `RetAddrs`), `C.sim-ret`, and the `c-thunk`/`c-ret` bracket fact. ROUND TRIP: deleted 2026-08-06 (D091 — no reachable state fetched a `c-ret`, so its clause became `⊥` by collision with the theorem `run-no-ret`), restored the same day when D092 MODELLED THE CALL. `run-no-ret` is false and deleted, `ret-site-owes` is gone, and the route is live. No longer a model gap — what is missing is the `CompiledCorr` return-address component, preservable now that `enter-call` pins the entered frame's window END on the pushed cell |
| 10 | `call-site-shape` | `ConcFlatSim` | deferred proof | REPLACED `events-running-call` 2026-08-06 (D098), now the THEOREM `call-step`. At an emitted call the closure register holds a live heap pointer whose second cell holds a code address naming a body that exists — every conjunct is what `ir-to-trace'`'s `curry` clause arranges. No `X.State`; same class and route as the D073 dataflow disciplines. Its resource half is the `x86-64-call-room` PARAMETER. HISTORY: was THE LAST CORRESPONDENCE GAP. Blocker LOCATED (D095): `effectiveAddr s (rip+label n) ≡ idx n` is a FICTION — a code address encodes as the label NUMBER while the concrete `call` jumps to the compiled address, and `idx ℓ ≡ x86-off prog j` is false. Fix (more faithful, not less — a real linker resolves that operand): resolve `lea … (rip+label ℓ)` through `X.find-label prog (thunk ℓ)`, then `find-thunk-pres` bridges. Costs one Semantics clause, a code map through the encoding (~56 + ~37 mechanical sites), the call's block-step (it writes the pushed address, EXTENDING `RetAddrs`), and one `StackRoom`-class resource premise. WAS the model gap; CLOSED as such by D092 (2026-08-06). `flat-exec-instr instr-call-closure` now transfers control the way `call *0x8(%r12)` does — pushes `fret`/`saved-frames`, enters `enter-call`'s frame, resolves the body with `find-thunk`. The concrete side of the transfer is already proven (`FlatComposition.find-thunk-pres`); what remains is the same return-address component as #9 |
| 13 | `emitted-thunk-guarded` | `ConcFlatSim` | deferred proof | REPLACED `thunk-entry-empty` 2026-08-06 (D094), which is now the THEOREM `SegWF.seg-entry` — every way of arriving at a body entry is refuted (fall-through by this guard, jump by `find-label-sound`, return by `RetMatch`'s new call provenance, entry by position 0), leaving the call, which reserves nothing. What is left is the emitter's own statement: in an emitted trace a `c-thunk` sits at `suc q` with a `c-jmp` at `q` — the guard `ir-to-trace'` emits to stop the parent falling into the body. CODEGEN-class: only `ir-to-trace` in the type. Route: the structural induction over `ir-to-trace'` (`FrameFreeTrace`/`LabelScope` mould) — a `NoThunks`-decides-it helper collapses the clauses that emit no body entry, an append lemma handles the splices, and the one interesting adjacency (`c-jmp end ∷ c-thunk`) is inside a single literal list in the `curry` clauses |
| 11 | `conc-fuel` | apex | **stub** | asserts adequacy of `step-budget-x86-64`, an UNDEFINED postulated `ℕ → ℕ` in `…CPU.X86-64` (siblings: `ev-x86-64`, `arith-env-x86-64`). Pin `step-budget` to a definition, then prove it. NOT a resource bound — do not launder it into a parameter |
| 12 | `x86-64-loader-faithful` | apex | **axiom** | STAYS — but NARROWED 2026-08-09 (D100): it now carries `DistinctLabels x86-64 m`. Without that premise it was not merely trusted, it was FALSE for every program the emitter duplicated (`as` refuses the text, so its LHS is the trace of nothing). Same edit on the x86-32 / riscv64 twins, via the shared `AsmTraceCorrect` |
| 14 | `program-labels-distinct` | `Once.Adequacy.LabelClash` | deferred proof / codegen | NEW 2026-08-09 (D100). The apex's supply of `DistinctLabels arch m` = `AllPairs _≢_ (C.moduleLabels arch Heap false m)`, the `.L…` sibling of `DistinctSymbols`/`program-no-clash`. **Currently FALSE** — `cata-dispatch` uses the IH for its algebra trace TWICE at one label range (D099), which is exactly the defect that shipped the 61-test regression. Route: `LabelRange`'s disjoint-range argument at every splice (counter monotonicity DONE, `LabelScope` containment DONE, uniqueness next), after the cata fork is decided. SCOPE: covers the non-linear `ir-to-trace'` walk; the per-arch `compile-trace-cnt` labels are inside the range but not in the list — that walk is linear, so a `LabelRange`-shaped one-liner each |

Only #12 is permanent. #11 lives in the CPU layer, not the correspondence.
NOTHING in this cone is a model gap any more — D092 closed the last one.

RESOURCE PARAMETERS now carried (not postulates, D087): `program-bound`,
`x86-64-heap-room`, `x86-64-stack-room`, `x86-64-call-room`, `entry-frame`. All
five thread `Certified → Compiler → ArchCorrectness → the arches`.

## THE CPU-MODEL ROOT — three definitions unlock four residuals

`Once/Adequacy/CPU/X86-64.agda` postulates three FUNCTIONS that are never
defined:

    postulate
      step-budget-x86-64 : ℕ → ℕ
      ev-x86-64          : RT.EvExtractor val-x86-64
      arith-env-x86-64   : X64S.Program → RT.ArithEnv val-x86-64

Residuals #3, #4 and #11 are all conditioned on these (`env ≡ arith-env-x86-64
(compile-trace prog)`, `ev ≡ ev-x86-64`) and their CONCLUSIONS are claims about
them — `env sym ≡ just pl`, `ev sym s ≡ event-of …`, "this fuel map is
adequate". None of those is provable about a function with no definition, so all
three must be assumed. **This is not a SigOp problem and not an arith problem**;
the arith proofs themselves are postulate-free on all three arches.

The conditioning is CORRECT and must stay: it was added 2026-07-30 because over
an arbitrary `env`/`ev` the claims are refutable (`λ _ → nothing`, `λ _ _ → []`)
— the vacuity lesson. What it exposes is that the functions were never written.

So the highest-leverage move on this board is a DEFINITION task, not a proof
task:

- `arith-env-x86-64` — look up the emitted arith block by its
  `once-symbol-path` symbol in the compiled `Program`. The emitter already puts
  it there (Plan 0.20 Phase G, `arith.block.<digest>`).
- `ev-x86-64` — read the observable value out of the argument registers at a
  `call-sym`, matching abstract `event-of`.
- `step-budget-x86-64` — the event-count ↦ machine-step fuel map.

Once each reduces, the corresponding residual becomes provable rather than
assumed. `decode-x86-64` is a FOURTH undefined function there, but it is honest
toolchain-boundary work (Intel SDM byte encoding), not a correspondence gap.

## Not in this cone

- `x86-32` / `riscv64` each still postulate their whole `conc-flat-sim` plus a
  loader axiom and an opaque `entry-frame`. x86-64 is the only arch with a real
  correspondence; the other two assume it.
- `cata-correct` (`IRObsCorrectFlat`) — **FALSE AS STATED**, reclassified
  2026-08-09 (Plan 0.68 step 0). Not a deferred proof: `cata-dispatch` splices
  the algebra trace TWICE at ONE label range (`I₁ ++ at ++ (I₂ ++ at ++ I₃)`),
  and the flat machine resolves labels by a first-match scan over the whole
  trace — so the second copy's `c-jmp end` lands in the FIRST copy and the
  machine's events diverge from `evalᴰ`. This is D099's defect, and this row is
  where it actually lives; the assembler premise (D100, residual #14) is the
  downstream symptom. Refutable until the cata fork lands. Its intended
  discharge is ALSO amputated: `5088e571` deleted the ascend/value/trace thirds
  2026-06-17, leaving only descend. Rebuilding base+ascend is a project.
- `obs-correct-rest` (`IRObsCorrectFlat`) — **DELETED 2026-08-09** (Plan 0.68
  step 0). The catch-all is enumerated: 22 named obligations, one per IR
  constructor, no catch-all clause, apex green. It was hiding two independent
  kinds of falsity, neither of them visible while one postulate covered
  everything:
  * **labels** — `curry`/`case` emit control, so their obligations are false
    under a duplicate label, for the same reason `cata-correct` is;
  * **unimplemented codegen** — `Para`, `Ana`, `Hylo`, `Fuse`, `in-ν` compile to
    the EMPTY TRACE, so their obligations are refutable whenever the denotation
    emits an event. Not a proof task at all: the emitter is missing.
  A third split fell out: the effectful SigOp (`obs-correct-sigop-rest`), the
  only construct that puts anything in the observable trace, used to be assumed
  by the same postulate as `Para`'s missing codegen. See
  `plans/0.68-discharge-ir-obs-correct.md` for the scoreboard.

## THE `Window` WEAKENING (landed)

`FlatCorrespondence.Window` was BIDIRECTIONAL: `readMem … ≡ enc-maybe-at am (stk
f k)`. Since `enc-maybe-at am nothing ≡ nothing`, it also demanded the CONCRETE
cell be unmapped wherever the abstract one was unwritten. That is false the
moment a closure is applied twice at one depth — the second entry re-enters a
frame at or above the stack high-water mark (`lo` only descends), over the
previous incarnation's live data.

It is now ONE-DIRECTIONAL: a match is claimed only where the abstract cell is
WRITTEN. Consequences:

- `fresh-x86` DELETED from `sim-alloc-stack` and `block-step-alloc-stack` — the
  false premise. Callee windows are now vacuous from `fresh-abs` alone.
- …and `fresh-abs` itself is no longer a PREMISE either: `do-thunk` CLEARS the
  entered frame (`SMCore.clear-frame`), so abstract freshness holds by
  COMPUTATION. Postulating it would have been assuming something false, for the
  same reason `fresh-x86` was: a closure applied twice at one depth re-enters
  the SAME `shift-frame cf b`, which still holds the previous incarnation's
  ABSTRACT writes. The weakening and the clear are a MATCHED PAIR — neither is
  sound alone. See D090.
- `C.sim-thunk` + `block-step-c-thunk` PROVEN — previously impossible. The
  handoff's "DO NOT build it as scoped — the premise is FALSE" is now resolved,
  not worked around.
- Three lemmas DELETED rather than re-proved: `slot-empty-stop`,
  `load-indirect-stack-empty-stuck`, `load-indirect-suc-stack-empty-stuck`. Each
  said "abstract slot empty ⇒ concrete stuck", which the old statement supplied
  for free and which is FALSE — the concrete machine reads stale data. That was
  a real DIVERGENCE the bidirectional statement concealed, not a proof gap.
- Their routes are unreachable instead, by two arguments, NEITHER a postulate:
  slot reads — `site-ok` now requires a non-`e-any` claim and `MeetsSlot` refutes
  a claim at an unwritten slot (`site-slot-written`, `slot-read-written`);
  pointer reads into stack slots — heap mode admits no stack pointer at all
  (`stack-ptr-live`).

Postulate count UNCHANGED at 11: `emitted-shape-check`'s CONTENT grew (the
`site-ok` conjunct), which is exactly the shape the plan called for.

## THE ASSEMBLER BOUNDARY — what the model cannot express (D100)

`ArchSemantics.assemble : String → List Byte` is TOTAL and UNINTERPRETED. It has
no failure mode, so **no assembler or linker rejection is representable in the
model.** Everything `as`/`ld` can refuse sits inside `<arch>-loader-faithful`,
invisible — and worse, for a program the toolchain rejects that axiom is not
"trusted", it is FALSE, because its left-hand side is the behaviour of a binary
that was never produced. A `⊥`-probe cannot find any of this: the falsity is
EXTERNAL (about `as`), not internal.

Known members of the class, and where each stands:

| what the toolchain refuses | stated? | status |
|---|---|---|
| duplicate `.globl` function symbol | yes — `DistinctSymbols` | **PROVED** (`program-no-clash`) |
| duplicate `.L…` local label | yes — `DistinctLabels` (D100) | **residual #14**, currently false (D099's cata splice) |
| unresolved `.L…` reference | yes — `EmittedWF.labels-resolvable` | stated on the trace; not yet the module-level premise. Subsumes `emitted-code-addr-has-body` |
| duplicate `once_arith.block.<digest>` global | **NO** | **LIVE GAP.** `moduleSyms` lists only `once-symbol-path (cfName cf)`; the arith blocks `compileAllWithTarget` accumulates are emitted separately by `emitArithBlocks` with no dedup (`rewrite-ir`: "caller may dedup by digest" — the caller just `DL.++`s). The symbol is a pure function of the block body, so two structurally identical arith subtrees in one module define the same global twice. Route: extend `moduleSyms` to the FULL defined-symbol list and dedup by digest at the fold |
| unresolved external `once_<primitive>` (Strata) | **NO** | link-time; same shape as `labels-resolvable` one level up |
| out-of-range immediate / displacement, bad mnemonic, malformed text | **NO** | not expressible at all while `assemble` cannot fail |

The structural repair for the whole class is to give the assembler a failure
mode — `assemble : String → Maybe (List Byte)` — so that "the toolchain accepted
this text" becomes a proposition the proofs carry instead of an assumption they
cannot see. Until then, every member has to be found by hand and stated as a
separate premise, which is exactly how D100 was found (after the fact, by `as`).

### The general trap D100 exposed

**A precondition attached to a trust point stays behind when the trust point
moves.** `assemble-correct` carries `DistinctSymbols`; when `asm-sem` was DEFINED
as `exec-bytes ∘ assemble`, that field collapsed to `λ _ _ _ _ _ → refl` and its
premise became decorative. The trust moved to `loader-faithful`; the premise did
not. Whenever a postulated field becomes a definition, AUDIT ITS PREMISES — they
are now consumed by a `refl` and protect nothing.
