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

    genuine correspondence gaps (1):
      events-running-call
      (events-running-thunk DISCHARGED 2026-08-06 — see #8)
      (events-running-ret  DELETED    2026-08-06 — see #9 and D091: it was
       never an independent gap, only the call gap seen from the other end)

    correspondence-located, CPU-MODEL caused (3):
      arith-sigop-contract, external-sigop-contract, conc-fuel
      (see THE CPU-MODEL ROOT below)

    obligations the correspondence CONSUMES, owned by other layers (5):
      emitted-shape-check   — codegen        (only `ir-to-trace`)
      run-meets             — abstract machine + shape table (no `X.State`)
      main-heap-moded       — frontend       (only `IR`)
      entry-size            — resource/frontend plumbing (only `ir-size`)
      ret-site-owes         — abstract machine / call model (no `X.State`)

    boundary axioms (2):
      stack-top-in-stack, x86-64-loader-faithful

This matters for SCOPE. A branch whose subject is the correspondence is not
finished by discharging the cheap rows — those are other layers' work that
happens to be named here. It is finished by the genuine gaps, which are also the
hardest. Of the original three: `events-running-thunk` is DISCHARGED (a
theorem), `events-running-ret` turned out not to be an independent gap at all
(D091 — it is blocked BY the call, and its clause is now a theorem resting on
one abstract-machine invariant), and `events-running-call` — the model gap — is
the only one left. It is also what unblocks the return.

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
| 9 | `ret-site-owes` | `ConcFlatSim` | **model gap (call)** | REPLACED `events-running-ret` 2026-08-06 (D091). That postulate is DELETED: its clause is now the theorem `ret-step`, `⊥` by collision between this residual (a reachable `c-ret` owes a return — a call entered the body and pushed the pc, D086) and the THEOREM `run-no-ret` (`fret ≡ []` in every reachable state, because `instr-call-closure` is the identity). Two routes: (1) CFG confinement — prove no reachable pc lies in a body region, which deletes this row outright; (2) model the call, after which `run-no-ret` stops typechecking and this becomes provable from the push. NB the pair is INCONSISTENT if a `c-ret` site is ever reachable — deliberate, see D091 |
| 10 | `events-running-call` | `ConcFlatSim` | **model gap** | `exec-abstract instr-call-closure` is the IDENTITY while `call *0x8(%r12)` transfers control. The abstract machine must model the call (or codegen must inline it) before any proof exists |
| 11 | `conc-fuel` | apex | **stub** | asserts adequacy of `step-budget-x86-64`, an UNDEFINED postulated `ℕ → ℕ` in `…CPU.X86-64` (siblings: `ev-x86-64`, `arith-env-x86-64`). Pin `step-budget` to a definition, then prove it. NOT a resource bound — do not launder it into a parameter |
| 12 | `x86-64-loader-faithful` | apex | **axiom** | STAYS. Assembler + loader + printer + decoder round-trip; the boundary every verified compiler keeps |

Only #12 is permanent. #10 needs a semantics change; #11 lives in the CPU layer,
not the correspondence.

RESOURCE PARAMETERS now carried (not postulates, D087): `program-bound`,
`x86-64-heap-room`, `x86-64-stack-room`, `entry-frame`. All four thread
`Certified → Compiler → ArchCorrectness → the arches`.

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
- `cata-correct` (`IRObsCorrectFlat`) — the cata loop obligation. Its intended
  discharge (`CataNat*`) is AMPUTATED: `5088e571` deleted the ascend/value/trace
  thirds 2026-06-17, leaving only descend. Rebuilding base+ascend is a project.
- `obs-correct-rest` (`IRObsCorrectFlat`) — the non-cata IR constructors,
  deferred as one bundle.

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
