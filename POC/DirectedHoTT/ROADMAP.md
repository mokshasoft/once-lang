# ROADMAP — from this POC to Once implemented in Once

> **Read this first.** This is the ONE top-level plan for `DirectedHoTT/`.
> Every other `PLAN-*.md` here is a stage of it (or historical, see §5).
> Opened 2026-10-05, after S7b step 3 hit the evaluation-cost wall
> (PLAN-BIDI §3g) and the review of the plan stack, `POC/OCP0009/` and
> the repo-level docs that followed.
> **Revised 2026-11-26** after the rebase onto master: master's core
> judgment is GRADED (usage and effect, with subsumption), so R5 is the
> shape of the kernel's judgment, not a layer added later. See R5, the
> Order and §7 (what the POC and master give each other).

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
- Master's core: `formal/Once/Spec/Core/Typing.agda`, the judgment
  `Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π` (usage `0 ≤ 1 ≤ ω`, effect `pure ≤ act ≤ eff`,
  `formal/Once/Spec/Grade.agda`). Plans 0.146 + 0.157 (branch
  `0.146-linear-core-4`) compile every program through a linear core from
  that judgment's graded derivations; D468 (proposed) says the dependent
  kernel extends that judgment (D231).
- The POC owns its syntax: nothing here imports `normalizer.*`,
  `formal/` or `POC/OCP0009/`. The prelude it used from
  `normalizer.Syntax.Types` is copied into `DirectedHoTT/Prelude.agda`.

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
| R1 | **One datatype former, levitated descriptions; the Knot is EXACT.** Indexed fibred descriptions (D490–D498); the Knot's judgements faithful (F1–F5) and decoded (F6) | PLAN-LEVITATION, PLAN-FAITHFUL | ✅ (2026-10-04) |
| R2 | **Decidable checking** (S0–S6): annotated core `⊢ᴬ` decidable (CheckA), type conversion (route C), signature + δ + conservativity, untrusted bidirectional elaborator | PLAN-BIDI §3–§3f | ✅ (2026-10-02) |
| R3 | **The evaluator.** Environment-based NbE over the kernel syntax: closures, neutrals, readback, lazy δ. Untrusted first (tests, elaborator), then certified (checker, conversion) | **PLAN-EVAL** | 🟡 E0 ✅ (2026-10-05: the parked traversal tests and the whole `KD` run in ~10 s); E1 ✅ (agreement oracle with the certified evaluator, every rule); ★ E3 soundness PROVED for terms and types (`nbe-sound`, `nbeᵀ-sound`, 2026-10-06); conversion DECIDED by NbE and used by CheckA (`ConvNbE`); ✅ the checker's cost at the Knot's scale FOUND by profiling, not the stuck-signature hypothesis (PLAN-EVAL §2f: `lvl` recomputed the context length, `lvlAt`/`idEnvAt` fix it; CheckA's `decTo` compares syntax before normalising): Pw sort 0 73 s → 19.5 s, full Pw segment OOM → 144 s / 4.8 GB. E4 TRIGGERED 2026-10-07 (reference evaluation ~38% of PwCore after the readback fixes) → ✅ **PLAN-REF** (closed 2026-10-12): references as projections, in the KERNEL (D501) — ✅ K1–K6 green, every layer; full sweep ALL GREEN (288 modules, 2026-10-11) after the compile regression was traced to instance COPIES of signature-free definitions (`SD` opaque; `Spec.Base` no longer re-exported by the instances: Gcd.LeEq 1057 → 10 s). ✅ K4's internal image of `Spec/SigWf` with faithfulness (`SigWfAgree`) and `𝒮 ⊑ᴰ (𝒮 ▸ᴷ e)` (2026-10-12). Re-exports of non-parameterised modules by parameterised ones are a lint ERROR (2026-10-12); splitting signature-free DATA out is ⏸ until two instances meet. Step 5 measured: cost-NEUTRAL at PwCore (49.4M unfoldings vs 49.0M, 81 s) once the value table is indexed by LEVEL; E4's predicted ~38% saving was a misattribution (force/eval run for every value). |
| R4 | **The Knot in the core** (S7): the Lib's `Sig` levitated (S7b, ✅ steps 2, 3, 5); Pw POC (step 4); then family-by-family migration | PLAN-BIDI §3g | 🟡 Pw POC: P1/P2 done (`Examples/SigMeth`, the core `methAt`; the core traversal IS the Knot's `wk`, `NbETravAgree`); P3 done (`Examples/PwCore`: `#PwD` ≡ the Knot's `PwF.DF`, `NbEPwAgree`); ★ P4 done 2026-10-06 (`Knot/PwCore`: the Knot's `⌜Pw⌝` IS a `ref` to the core entries, `El-⌜Pw⌝` by `nbe-sound`; `gen-judge.py` `CORE_CODE`; sweep ALL GREEN, 273 modules); 🟡 P5: measured (the planned line comparison counted GENERATED output; the Lib route's human input is the 5-line `PWRULES`), PwCore 146 s / 4.9 GB → 49.0M unfoldings / ~3.4 GB (`EraName`, readback length once); the rest is PLAN-REF; ★ P6 done 2026-10-13: the four side conditions (StkA, StkC, Flat, NNC) are core entries, one SigExtend segment per family over a shared index (`Examples/Preds*`, frame in `Examples/KnotFrame`, Knot side in `Knot/CoreRef`); `Knot/Preds`' codes are refs; `NbEPredsAgree` checks all four; a family is 1–3 lines of rows. Lesson: never read the Knot at the CONCRETE core (imports alone 81 s / 5 GB vs 8 s at a parameter). 2026-10-20/11-26: P6 item 7 (generated segments, `Knot/PwCore`); JudgeConGen 95.4G / 89 s → 70.6G / 66 s by per-level `okT⁽k⁾` and `N⁽k⁾-β` lemmas (tuning of the generated layer the generic `⊢inst` deletes; no more of it). Sweep ALL GREEN, 299 modules cold; the Knot 1488 s of ~3400 s. ⏸ Next family migration waits for R5's judgment (HANDOFF-2026-11-26) |
| R5 | **The graded dependent judgment.** `Γ ⊢[ Ψ ] t ∷ A ! π`, both of master's grade axes: usage `0 ≤ 1 ≤ ω` (types and indices checked at 0, Π carries the argument's usage) and effect `pure ≤ act ≤ eff` (what a type may depend on; conversion evaluates only pure terms), subsumption on both, and master's law 0 ⇒ pure. Decide ν/`unfold`/`iter` (codata) in or beside the dependent kernel, and the signature reference's form (§7). Through Spec, Metatheory, NbE, CheckA; then erasure and an allocation-aware evaluator. Target: `formal/Once/Spec/Grade.agda`, `Spec/Core/Typing.agda`. Blueprint for the simple-typed part: `POC/OCP0009/NbEPQTT*`, `NbEPLinQTT`, `NbEPLinCore` (§4) | to write (PLAN-GRADED) | 🔬 next |
| R6 | **Converge with the compiler core.** The target is concrete now: master's graded `Spec.Core` `Tm` (the dependent kernel "lands by adding formers here, never by introducing a second syntax"), which L1 passes and the bridge `Lq` into the linear core already consume. Present R3's evaluator as a CAM / `Evaluable` instance over a CwF (OCP-0009's "two pillars", `:397-458`; Q3); decide the TCB0 mechanism (§3, Q2) | to write | 🔬 |
| R7 | **Once in Once.** The checker (CheckA + conversion) as core programs run by the evaluator; the normalizer fixpoint `N ∘ ⌜N⌝ →* ⌜N⌝` run, not only proved | OCP-0009 Rung 6 | 🔬 |

**Order (revised 2026-11-26).** R0–R3 are done (except Q4). R5 comes
BEFORE the rest of R4: the Knot encodes every rule of the judgment, and
grades change every rule, so families migrated on the ungraded judgment
would be migrated twice. Kernel changes are cheap, the Knot is not.
1. R5 on the kernel (Spec, Metatheory, NbE, CheckA).
2. One R4 family as a pilot on the graded judgment, through the generic
   `⊢inst`; measure what grades cost in the Knot.
3. The rest of R4 (generated lines toward zero, every Knot module under
   10 s), then the object-level `prog` exhibit.
4. R6, against master's graded `Tm`. R7 needs all of them.

Ready to start migrating into master: the definition (R5) is settled and
agreed with master's grades, the Knot is written in the core rather than
generated, and one real metatheorem is proved in the language at an
acceptable cost.

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
- **Q5 — references as context projections** — ✅ DONE 2026-10-11 (D501, **PLAN-REF**, decided 2026-10-07): the kernel's `ref d` carries no body; δ projects from the signature, NbE reads a shared value table. The history below is kept for the reasoning. ✅ PARTLY DONE 2026-10-05
  (D500): the signature is a TELESCOPE and `WfSig` is context formation, so
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
- **Housekeeping — decision-log numbering diverged.** ✅ RESOLVED 2026-11-26:
  the POC line's D071–D082 collided with the compiler's D071+ (D071 there =
  references as projections). On the rebase onto master the POC entries were
  renumbered D490–D501 (old number + 419; each entry says what it was), and
  the compiler's numbers are unchanged. D499 here is the evaluator.
- **Q4 — totality without fuel** (PLAN-BIDI `:983`, old PLAN-NF Phase 2).
  The certified evaluator should become total by the LR's normalization
  (`wnorm`), not by fuel. Owner: PLAN-EVAL E3.

## 4. What `POC/OCP0009/` contributes

`POC/OCP0009/` is an archive. It is not built, and about 125 modules import
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
- `PLAN-REF.md`: R3 E4 — references as projections in the kernel (D501).
- `LESSONS.md`, `KNOT-LESSONS.md`, `PERF.md`: rules, which stay valid.
- `TODO.md`: a checklist, subordinate to the plans.
- The newest `HANDOFF-*.md` (2026-11-26): session state.
- `INPUT-DATA-AND-STRUCTURES.md`: what master's plan 0.147 asks of this
  kernel (§7).
- `MASTER-DT-ABSTRACTIONS.md` (2026-11-27): each difference from master, which
  abstraction is better and which way it moves; the erasure stance (§0).
- `docs/compiler/decision-log.md`: decisions D490–D501 (OCP-0009 entries). The
  evaluator design is D499.

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

## 7. The POC and master shape each other

Neither line is the truth. Where they differ, the mathematics decides,
and the answer may be a third design; agreement is evidence, not the
justification. The two must stay mergeable, so each difference is a
recorded decision.

**What master gives the POC:**
- **The grades and subsumption** (`⊢sub-use`, `⊢sub-eff`): one judgment
  that serves programs (the linear core reads usage; effects separate
  values from servers) and proofs (0 is erasure; pure is what types may
  mention). The POC takes them as R5.
- **The linear core** (plans 0.146/0.157): `NoLeak`, and a value owned once
  (`NoCopy`). The POC's runtime claim "dup-free code allocates nothing" (§6)
  should be stated against this core, not re-proved on a second one.
- **Codata and servers** (ν, `unfold`, `iter`) as core formers. The POC
  has none, and plan 0.147 §5 assumed none in the kernel: a decision for R5.

**What the POC gives master:**
- **A principled, proved Spec**: SR, confluence, canonicity and consistency
  of a dependent kernel; conversion decided by NbE proved sound; a de Bruijn
  checker (CheckA) that re-verifies untrusted elaboration.
- **Bidirectional checking as an implementation proved against a
  declarative core** (PLAN-BIDI S0–S6): master already took this shape
  (D231: the Spec is a core calculus, checking is proved against it).
- **Signature references as projections** (D501, master's D071 agrees).
  Still differing: master's `ref` is typed from a schema with no δ, ours
  unfolds by δ. Master's nominal and `abstract` declarations need δ
  scoped by segment (plan 0.147 §5).
- **One datatype former over levitated descriptions** (R1). What that would
  buy master, separated honestly:
  - *Already on master in first-order form.* `Spec/Polynomial`'s codes
    (`K`, `Id`, `⊕`, `⊗`) are a description grammar with one μ and one
    fold. The proof saving of "one former, one fold rule" is mostly
    banked there already.
  - *What indexing adds.* GADTs and indexed families with erased indices
    through the same former, not a new one. Plan 0.147 §4 postpones exactly
    these to dependent types. Master's G1 (nested types, "the plan's
    largest proof patch") and G3 (mutual types by Bekić) are designed as a
    fragment of `Desc`. Keeping master's functor grammar a literal fragment
    of the POC's `Desc` is the cheap way to keep the two mergeable.
  - *What levitation proper (descriptions as terms) adds.* Generic
    programs written once in the language: equality, order, show,
    serialization, `map`. These would let plan 0.147's "derived structure,
    laws proved once generically in Agda" move into Once. ⚠ The POC does
    NOT deliver this yet: `Desc` stays primitive with no eliminator
    (PLAN-LEVITATION, reopened and resolved 2026-10-04), and the Knot's
    traversals recurse on the signature instead. Infinitary `dπ` (G2) is
    not spiked.
  - *Compiled code.* Levitation is neutral at best on its own. A
    description graded 0 is static, so the layout can be read from it
    (one tag word, plan 0.138), and a generic program at a known
    description must be specialised by L1 inlining to match hand-written
    code. A description used at runtime is interpretive overhead. The
    speed-up is the linear core's, not levitation's.

