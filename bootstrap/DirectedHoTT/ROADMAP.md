# ROADMAP — from this POC to Once implemented in Once

> **Read this first.** This is the ONE top-level plan for `DirectedHoTT/`.
> Every other `PLAN-*.md` here is a stage of it (or historical, see §5).
> Opened 2026-10-05, after S7b step 3 hit the evaluation-cost wall
> (PLAN-BIDI §3g) and the review of the plan stack, `poc/OCP0009/` and
> the repo-level docs that followed.

## 0. The goal

This POC exists to find **the shape of dependent types in Once**: the
kernel, its metatheory, its checker and its evaluator, built so that
**Once can eventually be implemented in Once**.

- **The de Bruijn criterion** (PLAN-BIDI §0). A small, independent checker
  re-verifies any kernel term without trusting what produced it.
- **Self-hosting.** That checker, and the evaluator it runs on, are
  eventually Once programs. So every algorithm built here must be one
  Once can EXPRESS and RUN, not only one Agda can check.
- **Knot simplicity.** The Knot (the kernel described inside itself) is
  the cost centre. Kernel and metatheory changes are cheap; work that makes
  the Knot simpler is worth churn.

Repo-level context, which this POC feeds but does not depend on:
- `docs/proposals/OCP-0009-decidable-dependent-types.md`: Rungs 0–6, where
  Rung 6 is "reflect Once into Once". Its evaluator commitment (`:133-148`)
  is "determinism + totality of a big-step evaluator to canonical values;
  conv(a,b) = ⌜eval a⌝ ≟ ⌜eval b⌝ — NbE, not term rewriting".
- `bootstrap/theory/normalizer-vs-compiler-path.md`,
  `cccvm-sketch.md`, `tcb0-inspectable-vm.md`: the CCC-VM as the trusted
  bottom turtle. These are specifications and proofs only; no VM is
  implemented.
- `docs/compiler/decision-log.md` D071 (`:5016`): the linear SMCC core
  plus the QTT {0,1,ω} layer is the chosen direction.
- The POC owns its syntax: nothing here imports `normalizer.*`,
  `formal/` or `poc/OCP0009/` beyond the shared `normalizer.Syntax.Types`
  prelude.

## 1. Why the evaluator is the next centre of gravity

- Full βη rewriting in a CCC is NON-CONFLUENT (mechanised:
  `formal/Theory/Syntax/StrongCCL/CCT1/NonConfluenceWitness.agda`). Once
  therefore defines conversion by EVALUATION, which is what NbE means.
  The open question is how to evaluate well, not whether to use NbE.
- This kernel uses de Bruijn syntax with substitution. Every heavy cost
  measured here lives in that gap:
  - substitution towers (KNOT-LESSONS §7);
  - β-chains that need a cast at every step;
  - now, Agda evaluating an object-level interpreter. Every β leaves an
    unshared `subTm` tower, and the parked SigCore traversal tests OOM even
    at fuel 40.
- An **environment-based** evaluator never substitutes. A closure is a body
  paired with an environment, and a variable is a lookup.
  - Categorically this is Curien's categorical abstract machine:
    environments are products, a closure is the exponential transpose, and
    a variable is a projection.
  - So the POC's evaluator and the CCC-VM can be ONE algorithm, seen from
    the λ side and from the point-free side. That is the bridge §2 R6
    has to make precise.

## 2. The stages

Legend: ✅ done · 🟡 in progress · ⬜ planned · 🔬 research (no plan yet)

| # | stage | plan | state |
|---|---|---|---|
| R0 | **Kernel + metatheory.** Directed `Hom = ⟶*`, `Id = core(Hom)`; SR, confluence, injectivity, LR, fundamental theorem, canonicity, consistency; empty, checked trust surface | `Spec/`, `Metatheory/`, LESSONS.md | ✅ |
| R1 | **One datatype former, levitated descriptions; the Knot is EXACT.** Indexed fibred descriptions (D071–D079); the Knot's judgements faithful (F1–F5) and decoded (F6) | PLAN-LEVITATION, PLAN-FAITHFUL | ✅ (2026-10-04) |
| R2 | **Decidable checking** (S0–S6): annotated core `⊢ᴬ` decidable (CheckA), type conversion (route C), signature + δ + conservativity, untrusted bidirectional elaborator | PLAN-BIDI §3–§3f | ✅ (2026-10-02) |
| R3 | **The evaluator.** Environment-based NbE over the kernel syntax: closures, neutrals, readback, lazy δ. Untrusted first (tests, elaborator), then certified (checker, conversion) | **PLAN-EVAL** | 🟡 E0 ✅ (2026-10-05: the parked traversal tests and the whole `KD` run in ~10 s); E1 ✅ (agreement oracle with the certified evaluator, every rule); E2 next |
| R4 | **The Knot in the core** (S7): the Lib's `Sig` levitated (S7b, ✅ steps 2, 3, 5); Pw POC (step 4); then family-by-family migration | PLAN-BIDI §3g | 🟡 unblocked by R3 E0; step 4 (Pw) next |
| R5 | **Linear / QTT layer on the kernel.** Grades {0,1,ω} in the judgement, erasure, an allocation-aware evaluator. Blueprint: `poc/OCP0009/NbEPLinCore.agda`, `NbEPQTT*`, `NbEPLinQTT` (§4) | to write (PLAN-LINEAR) | 🔬 |
| R6 | **Converge with the compiler core.** Present R3's evaluator as a CAM / `Evaluable` instance over a CwF (OCP-0009's "two pillars", `:397-458`); reconcile with `formal/` and the CCC-VM; decide the TCB0 mechanism (§3, Q2) | to write | 🔬 |
| R7 | **Once in Once.** The checker (CheckA + conversion) as core programs run by the evaluator; the normalizer fixpoint `N ∘ ⌜N⌝ →* ⌜N⌝` run, not only proved | OCP-0009 Rung 6 | 🔬 |

**Order.** R3 E0–E2 unblocks R4. R4 is the large body of work and runs in
parallel with R3's certification (E3). R5 needs R3's value domain. R6 needs
R3 and R5. R7 needs all of them.

**Why R3 before R4.**
- R4's whole method is "checker by evaluation". Its migration writes Knot
  families as core programs whose tests and conversions are COMPUTED.
- The SigCore spike showed the current certified evaluator (`Algorithm/Eval`:
  substitution-based, applicative, eager δ) cannot run those programs inside
  Agda.
- Without R3 every R4 family meets the same wall.

## 3. Open questions (owner: the user unless marked)

- **Q1 — decoder form** (PLAN-BIDI §3g). Two forms:
  - select-then-map (A): what a generic program follows natively, and the
    CCC-native form, since selection is composition with a point;
  - the Lib's map-then-select (B): convertible with today's `KD`, so the
    Knot migrates family by family.
  The code is at B. ✅ Re-judged with E0 (2026-10-05): the environment
  evaluator runs B's traversals, so B's only cost is gone — B stays.
- **Q2 — the TCB0 mechanism.** Repo-level docs disagree:
  - `plans/tcb0-gap-closure.md` (2026-06-10): rule-soundness plus a trace
    verifier;
  - `bootstrap/theory/cccvm-sketch.md` and `tcb0-inspectable-vm.md`: an
    inspected VM that runs `eval`.
  Not needed before R6; record, don't decide.
- **Q3 — R6's dependent bridge.** Dependent types in a point-free setting
  need a categorical presentation of dependency: a CwF, comprehension
  category or contextual category. OCP-0009 names the CwF as the structural
  pillar. No design exists for this kernel's formers (Hom/Id/tr/ap, IMu,
  Desc).
- **Q5 — references as context projections** — ✅ PARTLY DONE 2026-10-05
  (D081): the signature is a TELESCOPE and `WfSig` is context formation, so
  signatures extend across modules (the Knot is checked in segments). Still
  open: the erased `ref d b` carries its body (E4's global value table is
  the projection reading). The
  compiler (branch `plan-0.91-program-facts`, its D071) decided that an
  internal definition reference is a PROJECTION from the definition
  context Γ (the DTT global signature): `⟦ref x⟧Γ = Γ(x)` IS δ. This kernel's
  erased `ref d b` instead carries its body (S5 route B, "δ by erasure").
  The environment evaluator makes the categorical reading concrete: a
  GLOBAL environment of entry values, so `ref d` is a projection evaluated
  once. That is E4 (sharing) and the shape R6 should adopt. Not blocking.
- **Housekeeping — decision-log numbering diverged.** `D071`–`D079` mean
  different things here (OCP-0009 levitation) and on the compiler branch
  (D071 = references as projections, …, up to D272 there). D080 here is the
  evaluator. Reconcile the numbering when the branches meet.
- **Q4 — totality without fuel** (PLAN-BIDI `:983`, old PLAN-NF Phase 2).
  The certified evaluator should become total by the LR's normalization
  (`wnorm`), not by fuel. Owner: PLAN-EVAL E3.

## 4. What `poc/OCP0009/` contributes

`poc/OCP0009/` is an archive. It is not built, and about 125 modules import
`normalizer.*`. It contributes SPECIFICATIONS and ORACLES to re-derive on
this POC's syntax, never code to import.

| asset | where | used by |
|---|---|---|
| Semantic NbE: values by recursion on the type, neutrals, readback; the η-long `Normal` invariant; `≈β-complete` | `NbEPF`, `NbEKF`, `NbEPNormal`, `NbEPComplete` | R3 (shape of `Val`/`Ne`/`quote`) |
| F3: deciding conversion by NbE forces TYPED NbE (Ω loops) | `FINDINGS.md:47` | R3 E3 (why the certified evaluator needs the LR) |
| P1/P2: funext-free pointwise substitution; well-scoped, untyped raw syntax is the sweet spot | `FINDINGS.md:69-97` | R3 (environments are well-scoped, values untyped) |
| `NbEPLinCore.agda`: 779 lines, no imports, `--safe`. Cost-instrumented value domain `⟦A ⇒ B⟧C = ⟦A⟧C → ⟦B⟧C × ℕ`; `dyn-linear` (dup-free code allocates nothing); codata liveness | `NbEPLinCore`, `NbEPLinDyn:350` | R5 (the blueprint) |
| The four static-vs-dynamic divergences (case overcounts, closure creation free, closure cost per application, cata undercounts), each `refl` | `NbEPLinDyn:31-45` | R5 test oracles |
| QTT: usage-indexed runtime context makes 𝟘-erasure definitional; "context addition is tensor splitting" | `NbEPQTTEraseTm`, `NbEPLinQTT:107` | R5 |
| Programs with known results: gcd facts, `div 0`, System T nested-natrec Ackermann | `NbEPDirDBExamplesGcdAgda:168-179`, `…GcdLib:141`, `…DivC:230`, `…AckKernel` | R3 E1 tests |

Not transferable:
- the SN/LR/Takahashi stack (already re-done here);
- DTTChMF (postulated);
- the `lexrec`/`amrec` machinery;
- the PERF numbers, which are type-check times, not runtime.

## 5. Document map

**Live:**
- `ROADMAP.md` (this file): top level.
- `PLAN-BIDI.md`: R2 (done) and R4 (S7).
- `PLAN-EVAL.md`: R3.
- `LESSONS.md`, `KNOT-LESSONS.md`, `PERF.md`: rules, which stay valid.
- `TODO.md`: a checklist, subordinate to the plans.
- The newest `HANDOFF-*.md`: session state.
- `docs/compiler/decision-log.md`: decisions D071+ (OCP-0009 entries). The
  evaluator design is D080.

**Done, kept as records:**
- PLAN-LEVITATION (R1);
- PLAN-FAITHFUL (R1);
- PLAN-INDEXED, PLAN-JUDGEMENT (pre-levitation; their Knot was deleted);
- SPIKE-LEVITATION, SPIKE-NATRECM.

**Historical.** Their open items target deleted code, so do not resume
them without re-deriving against the levitated kernel:
- PLAN-NF (superseded by PLAN-BIDI S7a and PLAN-EVAL);
- PLAN-RENAMING;
- PLAN-FORDING-INDICES;
- SIMPLIFY-KNOT (its §3 evaluator and §8.2 checker are done elsewhere).

**Attempt logs:** `*-ATTEMPTS.md`, `LIFTS.md`.

## 6. Claims, and their status

The pitch for "better than Agda/Coq/Lean" must stay honest. Each claim
below is either measured here or a conjecture.

| claim | status |
|---|---|
| Transport/`ap` compute by case on codes; canonicity holds | ✅ proved (`Metatheory/Canonicity`) |
| Determinism of evaluation replaces confluence for deciding conversion | ✅ for the CCC core (OCP-0009 POC-0); here confluence is proved anyway |
| Dup-free code allocates nothing at runtime | ✅ for the linear core (`NbEPLinDyn.dyn-linear`); ⬜ for this kernel (R5) |
| One evaluator serves both conversion checking and running programs | 🔬 R3 + R6. It is the design target, not yet true: the CCC-VM is point-free and simply typed, this kernel is de Bruijn and dependent |
| No substitution in the runtime | 🔬 true of an environment evaluator by construction (R3); a conjecture for the whole pipeline until R6 |
| The normalizer certifies itself by its fixpoint | 🔬 proved for the CCC normalizer (`bootstrap/theory/fixpoint-correctness.md`); nothing for the dependent kernel |
