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

    correspondence-located, at the external-call boundary (1):
      external-sigop-contract (row 4; discharged by plan 0.123 R5)
      (arith-block-value DISCHARGED 2026-11-05, row 3; conc-fuel DELETED by D4a, row 11;
      see THE CPU-MODEL ROOT below)

    THE UNBOUNDED-REGISTER MODEL — NAMED 2026-08-13, CLOSED 2026-08-13 by
    plan 0.70. Kept here (rather than deleted) because the entry is what makes
    the repair auditable, and because what REMAINS is named at the end.

    The gap was: all three target semantics defined `Word = ℕ`, `add` as `_+_`
    and `sub` as TRUNCATED `_∸_`, while real registers are fixed-width and
    modular. `add` diverged only past 2⁶⁴; `sub` diverged AT SMALL VALUES
    (`3 ∸ 5 = 0` in the model, `2⁶⁴ − 2` on hardware). The correspondence was
    nevertheless TRUE, which is why nothing caught it: the ABSTRACT flat machine
    clamped identically, so both sides diverged from hardware TOGETHER.

    WHERE THE DIVERGENCE LANDED — and the reason it was the deepest kind of gap.
    An earlier draft blamed `<arch>-loader-faithful`. That was wrong and the
    truth was worse: `asm-sem` and `conc-trace` BOTH run our own `run-trace`, so
    the arithmetic cancelled and no postulate in the tree ever claimed our
    `execInstr` matches a real CPU. The theorem was conditional on a machine
    model whose fidelity was not assumed, not proved, and not stated — invisible
    to postulate-counting. D103's `lla` defect was the same class one level down.

    WHAT CLOSED IT (plan 0.70, phases A–D, all three arches):

      * ARITHMETIC INSTRUCTIONS ARE MODULAR. `add`/`sub`/`addi` compute `⊕`/`⊖`
        at the target's width — x86-32 at `Width 32`, which is what the `bits`
        parameter was for. No no-overflow precondition sits on any instruction:
        D054 makes wraparound correct, defined semantics, so a program whose
        arithmetic wraps stays covered rather than excluded.
      * IMMEDIATES ARE NORMED. An immediate field holds a machine word. This was
        not cosmetic — `⊖` is `norm (x + (modulus ∸ y))`, which truncated `∸`
        makes WRONG for `y ≥ modulus` (it collapses to `norm x`), so norming the
        operand is what keeps `⊖` on its domain.
      * ADDRESSES STAY ORDERED ℕ, under an explicit no-wrap invariant — phase
        A's decision, and CompCert's. Modular arithmetic supplies neither the
        order the layout separation needs nor the cancellation `slot-addr-inj`
        needs. So `effectiveAddr` and the implicit `%rsp` moves in
        `push`/`pop`/`call`/`ret` keep `+`/`∸` BY DESIGN. `sub rsp, n` shows both
        layers at once: the instruction is modular, and the block-step reads its
        result back as ordered ℕ through the no-borrow condition.
      * TWO DEFECTS FELL OUT, both D103-class: riscv64's `lla` wrote 0 instead of
        resolving the label, and riscv64's `li` wrote 0 for a NEGATIVE immediate
        (a real `li a0, -1` loads all-ones). Both are fixed; `step-li` now covers
        both signs instead of dodging half its domain.

    WHAT REMAINS, and it is now TRACKED rather than untracked — four parameters,
    threaded `Certified → Compiler → ArchCorrectness → X86-64 → ConcFlatSim`:

      RegRange           a register holds a value below the modulus. Becomes a
                         theorem when the register file carries its range.
      AddrNoWrap         `ret-no-wrap`, `lo-fits` — the layout stays inside the
                         address space. D087 class; a linker sizing pass
                         discharges them.
      LitFits            `tag-fits`, `lit-fits`, `float-fits` — an emitted
                         immediate fits in a machine word. NOT a linker fact:
                         D054 makes an elaborated literal in range BY
                         CONSTRUCTION, so this is the frontend's range simply not
                         threaded here yet. `float-fits` is true by construction
                         too (`primWord64ToNat`'s image is below 2⁶⁴); it is
                         assumed only because `Data.Word.Properties` states no
                         such bound.

    AND ONE ASYMMETRY LEFT IN THE MODEL: the ABSTRACT flat machine's `sv-succ`/
    `sv-pred` are still ℕ — `sv-pred` CLAMPS where the machine now wraps. The
    correspondence is true because `count-no-wrap` and `ScratchDecGuarded`
    exclude exactly the states where they would differ. Making `sv-pred` wrap
    would let `ScratchDecGuarded` be DELETED rather than discharged, and is the
    one place where "fix the abstract side first" genuinely applies, since these
    are values rather than addresses.

    (2026-10-30, plan 0.135, D363: RESOLVED BY DELETION. The seven loop instructions —
    `scratch-one`/`-zero`/`-dec`/`-load-count`, `count-zero`/`-inc`,
    `c-branch-scratch-zero` — lost their only emitters when the shape-specialised
    cata codegens were deleted, so they were removed from the abstract machine
    with every clause, lemma and hypothesis that existed only for them:
    `ScratchDecGuarded` (×3 arches), `AddrNoWrap.count-no-wrap`, `sv-succ`/
    `sv-pred`. Later the same day the three remaining retired instructions —
    `instr-loop`, `lea-indexed`, `instr-case-on-tag`, none emitted — went too,
    and with them the `Scratch`/`Count` registers (their only readers), their
    physical roles (`rbx`/`r14`, `edx`/`edi`, `s3`/`s4`), the register-tag
    invariant `FlatRegTagWF`, the `NoNested`/`NotNested` fences and the
    `FlatCorr` fields `scratch-eq`/`count-eq`. No resource hypothesis changed.)

    PHASE C STARTED 2026-08-13 — x86-64's SUBTRACTION IS NOW MODULAR. The
    semantics computes `⊖`, `step-sub-ri` says so, and all four `sub` block-steps
    bridge back to `∸` with `Once.Word.Width.⊖≡∸`. Three of them (`alloc-stack`,
    `c-thunk`, `call`) needed NO new premise: their `fits` — present since D085
    purely to tame truncated `∸` — is exactly the no-borrow condition.

    TWO NEW D087-CLASS PARAMETERS, threaded `Certified → Compiler →
    ArchCorrectness → X86-64 → ConcFlatSim` like the three rooms:

      RegRange           a register holds a value below the modulus. Trivially
                         true of any real state and NOT derivable here: `⊕`/`⊖`
                         norm their results, but `mov reg, imm n` and `lea` do
                         not. Becomes a theorem when the register file carries
                         its range.
      ScratchDecGuarded  a reachable `scratch-dec` finds a non-zero Scratch —
                         the no-borrow condition for the ONE subtraction that
                         never had one. Not a new assumption about the world:
                         `cata-nat-I₂`/`I₃` emit the branch that guarantees it,
                         so the route is the `emitted-thunk-guarded` induction.

    x86-64's ADDITION FOLLOWED, same day. `add` computes `⊕` — with NO
    no-overflow premise on the instruction, which D054 forbids outright:
    wraparound is correct, defined Once semantics, "not something the programmer
    or the compiler must prove absent", and a precondition there would be
    "exactly the narrow regime where the impossible accidentally holds". An
    earlier attempt DID balk at the range obligations and back the change out;
    that reasoning is recorded and corrected in plan 0.70 phase C.

    The obligations are real but they are LAYOUT facts, because every `add` the
    compiler emits computes an address (`rsp`, `r15`, the `rcx`/`rdi` index
    scaling) or the observable counter (`r14`) — never a user `Int`, which goes
    through the Arith backend over `Once.Word` and wraps there by design. So a
    program whose arithmetic overflows stays fully covered by the theorem.

      AddrNoWrap         a record of three, threaded as ONE parameter so the
                         four-module thread does not change as fields move:
                           ret-no-wrap    `%rsp + slots b < modulus` at `c-ret`
                           count-no-wrap  `%r14 + 1 < modulus` at `count-inc` —
                                          the one non-address site: "this run
                                          does not emit 2⁶⁴ observations"
                           lo-fits        `lo < modulus` — the stack's
                                          high-water mark is representable, the
                                          layout bound in its most basic form
                         Same D087 class and same discharge route as the three
                         rooms: a linker sizing pass.

    THE HEAP BUMP COST NOTHING: `HeapRoom` already bounds the bumped frontier by
    `lo`, so `lo-fits` discharges it outright rather than needing a site premise.
    A fourth field (`dealloc-no-wrap`) was written and DELETED —
    `instr-dealloc-stack` is unemittable, ConcFlatSim kills that route with
    `frame-op-absurd`, and a bound that is never consumed should not be assumed.
    `lea-indexed`'s `add`s were unemittable for the same reason (the
    instruction is now deleted, plan 0.135), so only THREE `add` sites are
    live — exactly the three fields.

    DIVISION NEEDED NOTHING: D055 already made `/`/`%` total on RISC-V's
    semantics, in `Once.Word` as `_/ˢ_`/`_%ˢ_` — one definition all three arches
    share, so the "align where the arches differ" work predates this phase.

    PHASE C IS DONE ON ALL THREE ARCHES (2026-08-13). riscv64 (`add`/`sub`/`addi`)
    and x86-32 (`add`/`sub`, at `Width 32`) cost NOTHING: riscv64's step lemmas
    are now stated in `⊕`/`⊖` from the start rather than stated in ℕ and
    converted, and nothing above them broke — riscv64's block-steps do not exist
    yet (plan 0.65 G2) and x86-32 has no correspondence directory. The
    conversion is in place BEFORE the proofs that would have had to be rewritten.

    WHAT C DELIBERATELY DOES NOT TOUCH, per phase A's decision (addresses are not
    values): `∸`/`+` survive at the ADDRESS sites — `effectiveAddr`, and the
    implicit `%rsp` moves inside `push`/`pop`/`call`/`ret`. Addresses stay
    ordered ℕ under a no-wrap invariant; only the ARITHMETIC INSTRUCTIONS are
    modular. `sub rsp, n` shows both layers at once: the instruction computes
    `⊖`, and the block-step reads the result back as ordered ℕ through the
    no-borrow condition. `cmp`/`test` needed nothing — they compare rather than
    subtract.

    Remaining after C: the ABSTRACT side (`sv-pred`'s clamp must become the wrap,
    or the correspondence goes false rather than the model faithful;
    `ScratchDecGuarded` is what currently excludes the case where they disagree),
    and phase D's `lit-word` seam.

    PLANNED: `plans/0.70-machine-word-is-finite.md` (written 2026-08-13). Its
    first finding is that the repair is NOT "replace ℕ with Once.Word": the
    machine word does two jobs, and they want opposite treatments. As a VALUE
    it is modular (D054). As an ADDRESS the proofs need ORDER and CANCELLATION,
    which modular arithmetic does not supply — `slot-addr-inj` cancels
    `* slot-size`, and modularly `8 * 0 ≡ 8 * 2^61`, so two distinct slots
    would share an address. Addresses therefore stay ordered `ℕ` under an
    explicit NO-WRAP region invariant (CompCert's shape), which is what today's
    proofs already assume silently.

    THEY MOVED MODULE, 2026-08-12 (plan 0.65 G1d step 2). Seven residuals that
    were declared in `X86-64.ConcFlatSim` now live in
    `Once.Adequacy.ArchCorrectness.FlatCore.RunWF`: rows 5, 6, 9 (both), 10, 13
    plus `emitted-code-addr-has-body`. NOTHING WAS ADDED OR WEAKENED — same
    seven statements, same routes; only the module column changed. The reason
    is the one the entries below already give for each of them ("no `X.State`",
    "only `ir-to-trace`"): they are facts about the ABSTRACT machine and the
    EMITTER, so riscv64 and x86-32 would otherwise each have had to declare
    their own copy and this table would have grown threefold for facts that are
    one fact. Assumed once in the core, they are discharged once for all three
    arches. `external-sigop-contract` (row 4) stays in `ConcFlatSim` — it
    quantifies over `HeapView` and the arch's runtime, so it really is per-arch
    (`arith-block-value`, row 3, was too, and is now a theorem on each).

    obligations the correspondence CONSUMES, owned by other layers (5):
      (emitted-shape-check, run-meets — GONE, D367: the first was false)
      (main-heap-moded — DONE: a theorem, `HeapModed.heap-moded`)
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
| — | `HeapRoom`/`StackRoom`/`CallRoom` ×3 arches | (was apex, 9 parameters) | invariant | **DISCHARGED 2026-11-03** (plan 0.123 A.4 step 5, D371/D372) — the emitted room checks make running out observable (`exhausted`), and the budget they re-arm (`FlatCore.Budget`) gives every spending instruction its room (`Budget.room-of`). The need's literal seam is `LitFits.room-fits` (riscv64, x86-32). |
| — | `entry-frame` | (was `FlatFromObs`) | — | **DONE** — parameter; each arch supplies its own |
| — | `entry-frame-base` | (was apex) | — | **DONE, DISCHARGED** — x86-64's frame IS the loader `%rsp`, so `refl` |
| 1 | `stack-top-in-stack` | `…ArchCorrectness.X86-64` | axiom-ish | the residue of the two above: the loader's `%rsp` lies in the stack region. Could fold into `stack-top`'s own postulate by giving it type `StackPointer` instead of `Word` |
| 2 | `entry-size` | `FlatFromObs` | invariant | → parameter, same pattern as `heap-room` |
| 3 | `arith-block-value` | (was `*/ConcFlatSim` ×3) | — | **DISCHARGED 2026-11-05 on all three arches** (plan 0.123 α′ (f3), `*/ArithBlockValue`). x86-64 first (plan 0.123 α′ (f3), `X86-64.ArithBlockValue`): the decoded argument is the block's input at its entry state — a scalar the literal in `rdi` (D392), a compound the heap words at `rdi + 8k` below the frame (`FlatLeaf.leaf-at`, `heap-eq`, the room, D387) — its `Int` leaves are words (the store invariant, D391), and the Core (`ArithSimX86-64.block-value-x86-64`, through `normalize-preserves`) gives `rax` as the SigOp's output (`FlatCore.ArithOutput`). riscv64 (`t0`, frame `8n` below `sp`) and x86-32 (`ecx`, frame `20 + 4n` below `esp`) the same way: their ArithSim layout moved from the static link layout (`InStack`/`InHeap`) to the dispatch's (inputs outside the frame, spills inside). So plan 0.67's `arith-sigop-run` is a theorem with no residual. Before: what was left of the RUN half of `arith-sigop-contract`: the VALUE in the out register. `arith-dispatch-run` (the block's `ArithRun`) is a theorem (plan 0.123 α′ (f2)) but for that field: `*/ArithFrame` proves the subroutine keeps every role register but the result's and writes memory only in its frame, each spill slot below `required-scratch` (`XInstr.SpillBound`). Which block a compiler-owned SigOp names is PROVED (`arith-sigop-lookup`, D351); `arith-sigop-run` is a theorem (plan 0.123 α′ (e)) from the arch-free frame lemma `FlatCore.SigOpFrame.sigop-arith-step`: link, halt, decode and pc from the run, the frame from the room (D387). Which payload the call runs is PROVED to be the SigOp's own block (`arith-sigop-block`: `Named` carries `BlockOf`, and one symbol is one block, `DigestInjective.block-symbol-injective`, D389). Assumed is only that THAT block's result in the out register is the encoded SigOp output. HISTORY: was `arith-sigop-run`, which hid 87 test failures after D375 (the block read its input by the old layout, D385) and was false near the frontier (the room check did not cover the block's frame, D387) and under the old dispatch model (scratch in the caller's frame, D388). HISTORY: was all of `arith-sigop-contract`, and the lookup half was false for a primitive the arith pass left bare (a float operation over a `Float` input did not link) |
| 4 | `external-sigop-contract` | `*/ConcFlatSim` ×3 | **stub** | conclusions are about `ev-<arch>` and `call-at-<arch>`, postulated in `…CPU.<arch>` (the binary's label→SigOp resolution and argument decoding). Its `env` half is a lookup now (`block-env`, plan 0.107; was `arith-env-x86-64`). **Discharged in plan 0.123 R5** (user, 2026-11-05): R5 rewrites `ev-arch`/`ret-call` to read and write by `Spec.ABI`, so a proof against today's register-based extractor would be redone there |
| — | `emitted-shape-check` | (was `FlatCore.RunWF`) | — | **GONE (D367) — it was FALSE**: `c-start` drops every claim, so `terminal ∘ ⟨ id , id ⟩` fails the check under every label environment and the postulate derived `⊥`. Its consumers' site facts are THEOREMS now, read off the program's own run, which never faults (`FlatFromObs.start-sound`, from `ir-obs-correct`) |
| — | `run-meets` | (was `FlatCore.RunWF`) | — | **GONE (D367)** with the shape checker it was stated over (`ShapeTable`, `ShapeAt` deleted) |
| 7 | `main-heap-moded` | (was apex ×3) | — | **DONE** — a theorem (`CCC.Codegen.HeapModed.heap-moded`): since plan 0.86 stage G no IR node carries a mode, so every IR is heap-moded (plan 0.87 A) |
| — | `events-running-thunk` | (was `ConcFlatSim`) | — | **DONE, DISCHARGED 2026-08-06** — now the theorem `ConcFlatSim.thunk-step`. `block-step-c-thunk` (a theorem since D090) fed `lo' = lo hv ⊓ (%rsp ∸ 8b)`; its `front-lo'`/`fits` come from the new `x86-64-stack-room` PARAMETER (`ResourceBounds.StackRoom`), the exact mirror of `HeapRoom` |
| 9 | `ret-site-owes` + `ret-budget-matches` | `FlatCore.RunWF` | deferred proof | REPLACED `events-running-ret` 2026-08-06 (D095), now the THEOREM `ret-step` over the proven `block-step-c-ret`. Neither mentions `X.State`. (1) a reachable `c-ret` owes a return — route: static segment depth = `fret` depth + `SlotBudget` bracket neutrality; (2) the released budget IS the reservation in force — the emitter writes one `bb` twice. Both belong in the `emitted-thunk-guarded` induction. HISTORY: THE COMPONENT LANDED (D093): `CompiledCorr.ret-eq` says every ghost `fret` entry is really in memory, at its frame's window end. Three inputs left, all designed in D093 — the exact one-slot gap (as a `GapNext` conjunct in `RetAddrs`), `C.sim-ret`, and the `c-thunk`/`c-ret` bracket fact. ROUND TRIP: deleted 2026-08-06 (D091 — no reachable state fetched a `c-ret`, so its clause became `⊥` by collision with the theorem `run-no-ret`), restored the same day when D092 MODELLED THE CALL. `run-no-ret` is false and deleted, `ret-site-owes` is gone, and the route is live. No longer a model gap — what is missing is the `CompiledCorr` return-address component, preservable now that `enter-call` pins the entered frame's window END on the pushed cell |
| 10 | `call-site-shape` | `FlatCore.RunWF` | deferred proof | REPLACED `events-running-call` 2026-08-06 (D098), now the THEOREM `call-step`. At an emitted call the closure register holds a live heap pointer whose second cell holds a code address naming a body that exists — every conjunct is what `ir-to-trace'`'s `curry` clause arranges. No `X.State`; same class and route as the D073 dataflow disciplines. Its resource half is the `x86-64-call-room` PARAMETER. HISTORY: was THE LAST CORRESPONDENCE GAP. Blocker LOCATED (D095): `effectiveAddr s (rip+label n) ≡ idx n` is a FICTION — a code address encodes as the label NUMBER while the concrete `call` jumps to the compiled address, and `idx ℓ ≡ x86-off prog j` is false. Fix (more faithful, not less — a real linker resolves that operand): resolve `lea … (rip+label ℓ)` through `X.find-label prog (thunk ℓ)`, then `find-thunk-pres` bridges. Costs one Semantics clause, a code map through the encoding (~56 + ~37 mechanical sites), the call's block-step (it writes the pushed address, EXTENDING `RetAddrs`), and one `StackRoom`-class resource premise. WAS the model gap; CLOSED as such by D092 (2026-08-06). `flat-exec-instr instr-call-closure` now transfers control the way `call *0x8(%r12)` does — pushes `fret`/`saved-frames`, enters `enter-call`'s frame, resolves the body with `find-thunk`. The concrete side of the transfer is already proven (`FlatComposition.find-thunk-pres`); what remains is the same return-address component as #9 |
| 13 | `emitted-thunk-guarded` | `FlatCore.RunWF` | deferred proof | REPLACED `thunk-entry-empty` 2026-08-06 (D094), which is now the THEOREM `SegWF.seg-entry` — every way of arriving at a body entry is refuted (fall-through by this guard, jump by `find-label-sound`, return by `RetMatch`'s new call provenance, entry by position 0), leaving the call, which reserves nothing. What is left is the emitter's own statement: in an emitted trace a `c-thunk` sits at `suc q` with a `c-jmp` at `q` — the guard `ir-to-trace'` emits to stop the parent falling into the body. CODEGEN-class: only `ir-to-trace` in the type. Route: the structural induction over `ir-to-trace'` (`FrameFreeTrace`/`LabelScope` mould) — a `NoThunks`-decides-it helper collapses the clauses that emit no body entry, an append lemma handles the splices, and the one interesting adjacency (`c-jmp end ∷ c-thunk`) is inside a single literal list in the `curry` clauses |
| 11 | `conc-fuel` | (was apex) | — | **DELETED (D4a, D320)**: the apex is over traces, and the binary's trace is read off the machine with no fuel (`run-trace-<arch>`), so the `step-budget-<arch>` postulates and `conc-fuel` went with the fuel. HISTORY: asserted adequacy of an undefined budget; D268 made it read the run, since no `ℕ → ℕ` could be pinned |
| 12 | `x86-64-loader-faithful` | apex | **axiom** | STAYS — but NARROWED 2026-08-09 (D100): it now carries `DistinctLabels x86-64 m`. Without that premise it was not merely trusted, it was FALSE for every program the emitter duplicated (`as` refuses the text, so its LHS is the trace of nothing). Same edit on the x86-32 / riscv64 twins, via the shared `AsmTraceCorrect` |
| 12b | `as-faithful-<arch>` | apex | **axiom — INCONSISTENT AS STATED (D272)** | `decode (assemble (print F)) ≡ just F` for every `AsmWF F` needs `print` injective on `AsmWF`; it drops `externs` (⊥ shown) and `AsmWF` admits symbols that forge text. Fix = lexical symbol validity in `AsmWF` + printed externs — part of the plan 0.107 phase-d symbol-namespace design |
| 14 | `program-labels-distinct` | `Once.Adequacy.LabelClash` | deferred proof / codegen | NEW 2026-08-09 (D100). The apex's supply of `DistinctLabels arch m` = `AllPairs _≢_ (C.moduleLabels arch Heap false m)`, the `.L…` sibling of `DistinctSymbols`/`program-no-clash`. **TRUE of the emitter as of 2026-08-11** (D101/C1 emits the algebra once, as a called body) — was FALSE while `cata-dispatch` used the IH for its algebra trace TWICE at one label range (D099), the defect that shipped the 61-test regression. Still OWED as a proof. Route: `LabelRange`'s disjoint-range argument at every splice (counter monotonicity DONE, `LabelScope` containment DONE incl. the cata's `segagree-curry` case, uniqueness next). SCOPE: covers the non-linear `ir-to-trace'` walk; the per-arch `compile-trace-cnt` labels are inside the range but not in the list — that walk is linear, so a `LabelRange`-shaped one-liner each |

Only #12 is permanent.
NOTHING in this cone is a model gap any more — D092 closed the last one.

RESOURCE PARAMETERS now carried (not postulates, D087): `program-bound`,
`x86-64-heap-room`, `x86-64-stack-room`, `x86-64-call-room`, `entry-frame`. All
five thread `Certified → Compiler → ArchCorrectness → the arches`.

## THE CPU-MODEL ROOT — closed (plan 0.67, 2026-11-05)

Three undefined functions in `Once/Adequacy/CPU/X86-64.agda` once conditioned rows #3, #4 and #11. Of them:

- `arith-env-x86-64` is DEFINED as a lookup over the image's block table (`block-env`, plan 0.107), and the
  lookup half (`arith-sigop-lookup`, D351) and the run (`arith-block-value`, row 3) are theorems on all
  three arches.
- `step-budget-x86-64` is DELETED with `conc-fuel` (D4a): the binary's trace needs no fuel.
- `ev-<arch>` and `call-at-<arch>` remain postulated: they are the binary's label→SigOp resolution and
  argument decoding at an external call. `external-sigop-contract` (row 4) is about them, and plan 0.123 R5
  defines them by `Spec.ABI` and discharges it.

`decode-x86-64` is honest toolchain-boundary work (Intel SDM byte encoding), not a correspondence gap.

## Not in this cone

- **Code the CLI runs without a theorem** (D353): not a postulate, so not a row
  here, but counted. `run-ast-dumps.sh` dumps what runs (`Once.Extract.Root.runs`)
  beside what is proved, and `formal/scripts/ast-compare.py` lists RUNS ∖ PROVED:
  each declaration declared by `formal/scripts/runs-unproved.allow` or a gap.
  Gaps today: none (D354). The Haskell side
  (`Once.CLI`, import I/O, `as`/`ld`, the Host objects) is in neither dump.
- `x86-32` / `riscv64` each still postulate their whole `conc-flat-sim` plus a
  loader axiom and an opaque `entry-frame`. x86-64 is the only arch with a real
  correspondence; the other two assume it. **No row moved on 2026-08-11, and
  that is worth saying out loud**: plan 0.69 (D102) found both of those arches'
  EMITTERS defective — x86-32's slots aliased their caller's frame, riscv64's
  bodies destroyed their own return address — and fixed them, with every
  residual here unchanged. The blanket postulates are exactly what let a broken
  emitter sit under a green tree for six weeks; x86-32's was even inconsistent
  with its own `FrameInstantiation`. Plans 0.65/0.66 replace these two rows with
  proofs, and that is the point of doing them.
- `cata-correct` (`IRObsCorrect.Cata`) — **PROVED 2026-10-31 (plan 0.135 S3, D364;
  cata M1 + M4); no postulate left.** `cata-correct` is a definition dispatching
  on the emitter's strategy: `strat-const` by `CataConst`, `strat-branching` (the
  one generic post-order walk; the nat/linear specialisations were deleted
  2026-10-30 as miscompiling) by `CataBr.Branching` over stage A's run-level
  model (`CataBr.Meaning.po-run`), the flatten loop (`CataBr.Flatten`), one fold
  round per node (`CataBr.FoldRound`, fresh argument pair per call, D1a), the
  loop by induction on the eval list (`CataBr.FoldLoop`, fills on the loop's own
  run succeed: `CataBr.FillOk`) and the exit (`CataBr.FoldExit`). History below.
- `obs-correct-In` (`IRObsCorrect.InMu`) — **was FALSE; PROVED 2026-10-31 (D366).**
  The postulate (`IRObsCorrect.Simple`) assumed `In`'s obligation at every functor
  while `In` was emitted as `mov-to-output` everywhere: at `F = K Int`/`K Float`
  with the layer in a register the result was a literal in `Output`, and at
  `K Unit` nothing at all, where `ResultPlace (μ-type F)` admits only a heap
  pointer (a refutation that uses no postulate: `IRObsCorrectF (In wf) → ⊥` at
  `K Int`, `in-reg`). Every theorem resting on it held vacuously through those
  functors. Fixed by the emitter (`MuRep`): `In` boxes an `Int`/`Float` layer
  into a fresh block and allocates one for a `Unit` layer, `out-μ` and the
  cata's call (`strat-box`) read the box; a μ value is a heap pointer at every
  functor. One machine postulate is left in the `IRObsCorrect` tree:
  `obs-correct-sigop-rest` (plan 0.88).
- (history) `cata-correct` (`IRObsCorrectFlat`) — **NO LONGER FALSE as of 2026-08-11
  (D101, C1)**; an ordinary deferred proof again. It WAS false: `cata-dispatch`
  spliced the algebra trace TWICE at ONE label range (`I₁ ++ at ++ (I₂ ++ at ++
  I₃)`), and the flat machine resolves labels by a first-match scan over the
  whole trace, so the second copy's `c-jmp end` landed in the FIRST copy and
  the machine's events diverged from `evalᴰ` (D099's defect; the assembler
  premise, residual #14, was its downstream symptom). C1 emits the algebra ONCE
  as a called body, so there is no second copy to confuse. Its discharge is
  still AMPUTATED — `5088e571` deleted the ascend/value/trace thirds 2026-06-17,
  leaving only descend; rebuilding base+ascend is a project — and C1 adds a
  call/return excursion per layer, so the discharge must also consume residuals
  #9/#10 inside the cata induction. **Note what this row could not do**: while
  it is a postulate, no theorem relates the cata's trace to the fold, which is
  why C1's first emitter shipped a cata that folded zero layers with all four
  clusters green. Only the exit tests saw it.
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
(Historical: D367 later deleted `emitted-shape-check` — it was false — and the
site facts above became theorems read off the run, which never faults.)

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

---

## Plan 0.90 additions — the `Behavior`-record producers (2026-09-12)

D179 made `Behavior` a record carrying `extends`/`bounded`/`saturates`. Three
meanings PROVE or BORROW those laws (`⟦_⟧IR` from `evalᴰ-good`; `⟦_⟧ˢ` and
`flat-trace-of` via `behavior-by`, from the compiler's own correctness
equations). Two ASSUME them, and those are the new residuals:

| # | residual | class | what discharges it |
|---|---|---|---|
| P1 | `Once.Denotation.MainMeaning.mainMeaningᵈ-pf` — the direct meaning of `main` is a prefix family | **deferred proof** | the `⟦_⟧ᶜ`/`⟦_⟧ᵢ` analogue of `evalᴰ-good`: one induction over typed derivations, `>>=T-pf` at each bind. Stated about the meaning chain, not about an arbitrary `MClo` (which would be FALSE) |
| P2 | `step-budget-<arch>-adequate` (was `RunTraceCore.run-trace-extends` / `run-trace-saturates`) — the concrete machine's trace family extends and saturates | **axiom** (CPU model) | D268: the old pair was postulated for EVERY `stepBudget` and a non-monotone budget refuted it — a postulate of ⊥ in the apex cone. Now `run-trace` takes `Adequate` as a premise and each arch postulates it for ITS budget, which reads the run (block table, code, start state). Consistent: the step count to the n-th event is such a budget. Becomes a proof when the budget is DEFINED from the program (D5) |

`bounded` is proved on both (a `take n` is at most `n` long), so neither
residual covers it.

Deleted in the same change, and worth recording as residuals that went away:
`valid-ν-wf` (a ValidAtWF constructor claiming a ν has a memory-resident layer
— false for a Kleisli ν, and unreachable anyway since Class G emits nothing for
`Ana`/`in-ν`) and `ν-layer-iso` (its inversion). `obs-correct-Out` is now
discharged by `⊥-elim (ν-input-absurd …)` — see D180.

> **RETRACTED by D189 (2026-09-12).** That last sentence is the defect. The
> `⊥-elim` discharge was sound only because the emitter produced no
> instructions for `Ana`, so no ν could ever be built to reach it. See the
> D189 row below.

### D189 — the ν suspension: one vacuous proof out, one honest obligation in

| # | residual | class | what discharges it |
|---|---|---|---|
| N1 | `obs-correct-Out` — forcing a layer | **DISCHARGED (D199)** | Was `deferred proof`; it was in fact FALSE until the emitter re-suspended (D199), and is now a proof. `apply`'s argument with the pair-packing removed: three straight-line rows, then the call, handed off to the ν's own force (`NuV.nu-force`, `IRObsCorrect.NuForce`; was `BlockRuns.coalgs`/`CoalgRuns`, deleted with the apex's `BlockRunsT`, D364). A suspension is called with the raw seed in `Input1`, where a closure is called with an `(env , arg)` pair pointer |
| N2 | `obs-correct-in-ν` — a ν built from an available layer | **DISCHARGED (D356)** | same two-cell build with an identity block: the seed IS the layer and the code returns it; a proof in `TwoCell` |

**What went the other way.** `obs-correct-Ana` left the postulate block — it is
a proof (D190's shared build plus one `CellAt`). `ν-not-resident` is gone: it
was provable, and what made it provable was the missing emitter.

**Counting honestly:** this change is *+1 postulate* (`obs-correct-Out` back,
`obs-correct-Ana` out) and *−1 false theorem*. The postulate count is not the
metric; what changed is that no proof in the tree now depends on a feature
being unimplemented.

**The gap this leaves open** is not in the ledger's usual sense: `ana` has no
concrete syntax, so no exit test can reach the ν path at all. That is why the
defect survived. Surface syntax for `ana` (and `cata`, which has the same gap)
plus an unfold exit test is the recurrence guard, tracked with D189.

### THE EMPTINESS PROBE — run it on every new residual (added 2026-09-13)

MERGE.md already carries a **vacuity** discipline: is a residual's HYPOTHESIS
reachable in emitted programs? A residual conditioned on an unreachable state
is harmless but meaningless. This is its **dual**, and it is not harmless: is
the residual's CONCLUSION inhabited at all?

A postulate whose conclusion type is EMPTY is not unproven — it is FALSE, and
everything downstream of it is unsound. That is not a hypothetical: D189's
`obs-correct-Ana` was exactly this, and `ir-obs-correct` is total over `IR`, so
the apex `CorrectCompiler` proof depended on it.

**The recipe.** For a residual concluding at `P`, in a scratch module that
imports what `P` needs:

```agda
probe : P → ⊥
probe ()            -- or: enumerate the constructors and refute each
```

If that compiles, `P` is empty and the residual is false. Cost: one file, about
a minute. The D189 instance was three lines:

```agda
refute : ResultPlace (ν-type F) m a ca v st → ⊥
refute (at-loc loc v _ _ _ _) = ν-not-resident v
refute (at-reg () _)
```

`ResultPlace` has three constructors and at a ν NONE applied: `unit-result`
needs `B ≡ Unit`; `at-loc` needs a `ValidAtWF` at `ν-type F`, which had no
constructor after `valid-ν-wf` was deleted; `at-reg` needs `FitsInRegI (ν-type
F)`, absurd.

**When it is worth running** — any residual where the answer is not obviously
"inhabited":

* the conclusion mentions a type the EMITTER never constructs (the whole
  Class-G "emitter is missing" block is this shape);
* a witness datatype lost a constructor and something downstream still concludes
  at that type — *the D180 lesson: when deleting a constructor, check the
  postulates whose CODOMAIN is that type, not just the modules that import it*;
* the conclusion is a record and one FIELD is at such a type (the emptiness
  hides one level down, which is where `obs-correct-Ana`'s was).

**What it does not catch.** A residual can be false without being empty —
Class G's `Para`/`Hylo`/`Fuse` emit `[]` while their denotations may emit
events, so their `traces-agree` half is refutable only for programs whose
denotation actually emits. That needs a witnessing program, not a probe. The
emptiness probe is the cheap half; run it first because it is nearly free.

### D191–D194 — the ν path becomes reachable, and what it cost

| # | residual | class | what discharges it |
|---|---|---|---|
| V1 | `Once.Denotation.ValueDomainLaws.bisimᵈ-to-eq` — coalgebraic extensionality at the EFFECTFUL ν | **axiom** | provable in Cubical Agda. NOT a new kind: it is `bisimS-to-eq` (plan 0.47 step 3), which the pure `νS` has carried all along. Added because `RelV (ν-type F)` is propositional equality, and `MeaningBridge`'s ana clause must equate two `anaFᵈ`s built from merely RELATED coalgebras |
| V2 | `out-app-bridge` / `OutErased.out-coh` — the ν DESTRUCTOR's erasure coherence | **deferred proof (parked, not in tree)** | `AnaErased.coerce-νin-erase-D` read backwards, after generalising the layer. `out-trace` and the whole `out-value` chain are already proved; this is the only residual, and D194's patch holds the work |

**What went the other way.** `obs-correct-Ana` left the postulate block (D189).
`ν-not-resident` is gone — it was provable, and what made it provable was the
missing emitter. `NoNu` is retracted (D191): a proven cross-stage invariant
saying the parser never produces a ν, whose whole purpose was a reliance that
had to end.

**Counting honestly across the branch:** the postulate count moved roughly
sideways. What changed is that no proof in the tree depends on a feature being
unimplemented, and the one axiom added is a standard principle the pure side
already assumed.

**The pattern worth keeping.** Four defects on this branch were one assumption
in different clothes — *a ν modelled as if its layers were already available*:
`valid-ν-wf` (a resident layer), `obs-correct-Out` (a theorem about the empty
case), `as-sum` (unfolding a ν's functor at a branch site), and
`RelV (ν-type F)` (equality of coinductive values). When a ν-shaped proof looks
easy, that is the thing to suspect.

### D188 — `obs-correct-apply` DISCHARGED; one whole-clause axiom → one invariant

`obs-correct-apply` was an axiom for the entire clause. It is now a proof
against `block-runs` (FlatFromObs; named `callee-runs` until D199 widened it to
cover ν coalgebra blocks as well as closure bodies), which is a PROGRAM-level
invariant:

| half | status |
|---|---|
| every block of the unit IS `emitted 0 l body` for the body its label was minted for | **provable** — true by construction of the emitter, by induction over `ir-to-trace'` |
| the closure a RUNTIME state holds was built by one of those `curry`s | **the real assumption** — a reachability invariant (the entry heap is empty, so it is true), needing an induction over runs |

Proved in the clause and no longer assumed: the seventeen-instruction setup and
all its `InstrWF`/`halted` obligations, its memory preservation, the two
off-pointer input residences (refuted), the closure's heap residence (refuted
for `AtStack`), the call's label resolution spelled out through `callView`'s
three levels, the callee's input witness, and the trace concatenation.

### D187 — the pair split: the third instance of one defect class

`valid-pair-wf` demanded pointers in both cells; `apply` made that refutable
(it copies the closure's env cell into the callee's argument pair, and a
`Unit` env — `main`'s — is not a pointer). `CellAt` replaces the two pointer
triples: `cell-ptr` OR `cell-inline`, one constructor covering both cells.

Reached, in order, exactly as far as the assumption had: `ShapeAt` (a mutual
`CellShapeAt`), `readTyped` (it returned `nothing` for precisely the pairs the
old witness could not describe), and `obs-correct-fst`/`-snd` (a POINTER cell
still places `at-loc`, an INLINE one `at-reg`). No new residual; no postulate
added.

### D183 / D184 — `apply`, in progress: setup proved, two witness defects fixed

`obs-correct-apply` is still a whole-clause postulate, but it is now the ONLY
one left in its class and its shape is known:

* **proved** — `ApplySetupPres.setup-mem-pres`, the sixteen instructions before
  the call (D182's three lemmas, first try);
* **fixed on the way** — D184: the closure witness was mode-POLYMORPHIC, and a
  `Stack`-resident closure makes `do-call` halt while the denotation runs the
  body. Refutable, not merely unproved. Both closure constructors now conclude
  at `Heap`, which is also exactly what the call needs to enter;
* **named, not yet stated in Agda** — the block table. `callView` already ties
  the call to the closure's code cell and `valid-closure-wf` already says what
  that cell holds and what the closure means, so the value↔label link is NOT
  missing. What is missing is that `find-thunk`'s block at that label
  implements that body. D170 removed the value's ability to carry it on
  purpose, so it enters as a program-level premise (`CalleeFaithful`, D183).

### D182 — the ten-step invariant: THREE residuals retired, none added

`inl-mem-pres`, `inr-mem-pres` and `curry-mem-pres` are GONE, replaced by the
proof `TenStepPres.mem-pres`. They were three statements of one invariant about
one ten-instruction shape; abstracting the two rows that differ (both
memory-free) makes it a single lemma. `obs-correct-inl`, `obs-correct-inr` and
`obs-correct-curry` are now postulate-free in full.

See D182 for why `derive-mem-preserved` could not serve: it bans heap writes,
while what makes this run's two heap writes invisible is their FRESHNESS — a
runtime fact about `Input1`, unstatable as a trace predicate.

### D181 — `obs-correct-curry` discharged; one residual replaces one

`obs-correct-curry` was a whole-clause postulate. It is now a proof, and what
remains is `curry-mem-pres`: the same shape as `inl-mem-pres`/`inr-mem-pres` (a
heap-allocating ten-instruction run preserves every location the caller can
name), consumed only by the `in-loc` input residence — `in-reg` and `in-unit`
are postulate-free. All three are instances of ONE unwritten generalisation;
writing it retires three residuals at once and is the obvious next reduction.
**Done — see D182 above; this paragraph is history.**

### Known-red ISLAND `Once.Category.Laws`: deleted (D347)

It and its only consumer `Once.Optimize.Correct` were superseded by the trace-level
optimizer proof (`Once.Adequacy.OptimizePreserves`, plan 0.39) and deleted.
