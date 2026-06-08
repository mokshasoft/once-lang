# Normalizer vs Compiler: Which Ranzow Fixpoint to Build

Companion to [tcb0-inspectable-vm.md](./tcb0-inspectable-vm.md),
[cccvm-sketch.md](./cccvm-sketch.md), and
[fixpoint-correctness.md](./fixpoint-correctness.md).

## The question

Toward a formally verified Once compiler with **no trust in source code**,
should we build a **normalizer** with the CCC-VM structure, or a **compiler**
with the CCC-VM structure? And since observing a normalizer's fixpoint requires
*running* it — which seems to need a compiler — why not skip the normalizer and
observe the *compiler's* self-reproduction fixpoint instead?

This note records the reasoning and the chosen path.

## Two fixpoints, not one

These are different animals:

1. **Ranzow normalizer fixpoint** — `N ∘ ⌜N⌝ →* ⌜N⌝`. **Correctness-bearing.**
   The leverage (unique normal forms + transparency + encoding-completeness,
   `fixpoint-correctness.md` Appendix A) lets "correct on one input — its own
   encoding" bootstrap to "correct on all inputs." This is a *theorem about CCC
   normalization*, not a generic property of self-referential programs.

2. **Reflexive compiler fixpoint** — "the binary runs its own source and
   reproduces the exact binary." **Reproducibility only.** Not correctness-
   bearing on its own: Thompson's trusting-trust compiler is precisely a binary
   that perfectly reproduces itself while being malicious. A buggy compiler can
   be a perfect fixpoint of its own source.

So a compiler inherits the Ranzow leverage **only on the part of it that is CCC
normalization**. Skipping the normalizer and building only the compiler skips
the one mechanism that delivers correctness *without trust in source*.

## Why "we need a compiler to run the normalizer" dissolves

The motivation for skipping the normalizer was: observing its fixpoint means
*running* it, and running seems to need a compiler. The inspectable CCC-VM is an
**interpreter**, not a compiler (`cccvm-sketch.md §1, §7`):

- **Runtime = the tiny inspected VM** (~few hundred instructions, 4-point byte
  audit), trusted by human inspection.
- **N = a CCC term**, just data fed to the VM. Not trusted — *certified* by the
  observed run.
- The fixpoint check is `eval(N ∘ ⌜N⌝, UNIT) == eval(⌜N⌝, UNIT)` — value
  equality, not a compile step.

No compiler is needed to observe the fixpoint. The VM is the bottom turtle that
runs N; the compiler is built *on top*, later.

## The precise reason normalizer and compiler diverge — and converge

Subtle point, easy to get wrong. There are two senses of "the front-end is CCC":

1. **The front-end is a CCC morphism** — `F : SourceCode → CCCCode`, everything
   it does is data-to-data rewriting expressible with CCC operations. **This is
   true.** The front-end *is* CCC in this sense.

2. **The front-end's self-application is its own correctness spec** — the
   condition that actually grants the Ranzow leverage. **This is stronger and
   different.**

The fixpoint `T ∘ ⌜T⌝ →* ⌜T⌝` is correctness-bearing only because, for a
normalizer, that equation *is the correctness spec instantiated at `t = N`*. It
works due to a coincidence:

- N's input type = N's output type (both are CCC-term codes),
- `⌜N⌝` is already a normal form (`fixpoint-correctness.md` Lemma 3.1),
- `nf(N) = N`.

So "applied to its own code, reproduces its own code" *is* "correct at point N."

For a translator whose **source encoding ≠ target encoding**, `⌜C⌝` (C-as-a-
morphism, encoded) is **not** the same object as `compile(source_of_C)`.
Therefore `C ∘ ⌜C⌝ →* ⌜C⌝` is no longer an instance of the correctness spec — it
degrades into the Thompson/bootstrapping *self-reproduction* equation.

> The divergence is **not** "the front-end isn't CCC." It is "source-encoding ≠
> target-encoding, so self-application stops being spec-at-a-point."

This tells us how to make them **re-converge**:

- If Once surface syntax is encoded in the **same `Code` μ-type** (extended with
  sugar constructors), then desugaring is an *endo*-rewrite `Code → Code`. Source
  and target encodings coincide, and the whole pipeline becomes **one rewrite
  system with one genuine fixpoint** — the "everything rewrites to CCC" picture.
- The only piece that stays outside is raw byte-level parsing (`bytes → tree`).
  It is still a CCC morphism (a cata over the byte list), but it is verified by
  **round-trip** (`parse ∘ print = id`), not by a normal-form fixpoint.

This is the conservative-extension condition of `fixpoint-correctness.md §6.4`,
made precise: keep Once a sugar layer over the core `Code` type and the compiler
*is* a normalizer.

## The evaluator framing sidesteps the confluence blocker

Where the normalizer proof is actually stuck: full βη **confluence** at CCT1
(`plans/cct1-confluence-dicosmo.md`). Hardin 1989 shows classical techniques
fail on this rule set; the Di Cosmo factorisation has three remaining
obligations and no existing mechanisation. The `(curry h) ∘ id` critical pair is
the characteristic obstacle.

The evaluator move in `cccvm-sketch.md` is the escape hatch:

- A term-**rewriter** needs **confluence + SN** of the βη rules → the Di Cosmo
  quagmire.
- A big-step **evaluator** to canonical values is a **deterministic function** —
  confluence is automatic (a function has one output). "Unique normal form"
  becomes "unique value," free from determinism. What remains is
  **totality/termination** = the CCC strong-normalization result, which we
  *already have* (Tait reducibility candidates; only confluence was stuck).

So the evaluator framing **keeps the SN proof and drops the confluence
obligation entirely.**

Honest caveat: the `fixpoint ⟹ correctness` leverage (transparency +
encoding-completeness, Appendix A) still must hold and is *not* yet formalized;
the Agda has only the canonicity fragment (`RanzowFixpoint/Correctness.agda`).
That argument is cleaner in a deterministic-evaluator setting and never touches
the Di Cosmo critical pairs.

## Does proving full βη CCC-rewrite confluence help? — No, and it is not provable

Earlier drafts of this note called confluence "the linchpin." That was wrong.
The **full βη rule set as defined is non-confluent**, so there is nothing to
prove — and the bootstrap does not need it.

**Counter-witness** (mechanised, zero postulates, in
`formal/Theory/Syntax/StrongCCL/CCT1/NonConfluenceWitness.agda` — `¬confluent`):

```
t = curry (apply ∘ ⟨ fst ∘ fst , snd ⟩) ∘ snd
  Path 1 (∘-congˡ + curry-η):     t → fst ∘ snd                              -- βη-NF
  Path 2 (curry-compose + assoc…): t →* curry (apply ∘ ⟨ fst ∘ (snd ∘ fst), snd ⟩) -- βη-NF
```

Two **distinct** βη-NFs. They are equationally equal, but joining them needs to
re-associate `fst ∘ (snd ∘ fst)` into `(fst ∘ snd) ∘ fst` to expose curry-η's
rigid `f ∘ fst` shape — and `assoc` is one-directional, so they cannot be joined
by directed rewriting. The root cause: `∘` is a syntactic constructor with a
one-way `assoc`, while `curry-η` demands a fixed association. λ-calculus and the
classical *restricted* subsystems (Hardin 𝒟, the β-fragment) dodge this; the full
combinator βη set does not. This is why Newman (`local-confluent-rest` is *false*,
not just unproven), Hindley-Rosen, and Di Cosmo (`NFClosed` fails) all stalled on
the same obstruction.

> Repo tension to resolve: the April session concluded "non-confluent, do not
> re-attempt Di Cosmo," but the June commits pivoted *back* to Di Cosmo, tracking
> the `(curry h) ∘ id` pair rather than the `curry-η`/`curry-compose` witness
> above (which it does not address). Mechanising the counter-witness (April's
> open-decision #1) would settle this.

What the bootstrap actually needs instead:

- **A canonical-form decision procedure.** Either the **evaluator** (determinism
  *replaces* confluence — a function has one output), or the **confluent core**
  (Curien1985 β-fragment, *already proven* in
  `Theory.Syntax.Curien1985.CCT1.Diamond`) for decidable conversion and a
  well-defined normalizer-to-core-NF fixpoint.
- **Optimizer soundness** for the η/structural rules — per-pass `≈βη`-preservation
  (equational reasoning; `≈βη` stays consistent via STLC translation despite being
  non-confluent as directed rewriting). No global confluence required.

So the `confluence` hypothesis of `fixpoint-is-canonical` /
`fixpoint-is-unique` (`RanzowFixpoint/Correctness.agda`, `…/Correctness/CCT4.agda`)
is discharged by the **core** relation or sidestepped by the evaluator's
determinism — never by full-set confluence.

| | foundation | confluence | front-end | check |
|---|---|---|---|---|
| **Evaluator** (chosen) | deterministic big-step VM | not needed (determinism) | stratified / round-trip | value equality |
| **Confluent-core rewriter** | Curien β-fragment (proven) + ≈βη passes | core only (have it) | desugaring endo-rewrite | core-NF identity |
| **Full-βη unified rewriter** | — | **impossible (non-confluent)** | — | — |

**Decision: drop the full-βη confluence pursuit.** It is a design mismatch —
directed rewriting where equational reasoning is the right tool. Keep the proven
β-fragment core for conversion, use `≈βη`-preserving passes for the optimizer, and
build the evaluator route for the bootstrap foundation.

## Chosen path

**Layer 0 — foundation ("no trust in source"):**

- Tiny **evaluator** CCC-VM; bytes pass the 4-point audit (closure /
  faithfulness / isolation / memory-safety). Trusted by inspection.
- Fixpoint theorem in **evaluator form**: determinism + totality (SN, already
  have) + transparency + encoding-completeness ⟹ fixpoint implies correct. Pure
  math, refereeable / machine-checked, **no confluence obligation**. The
  canonicity/uniqueness fragment is mechanised (zero postulates) in
  `Theory.RanzowFixpoint.EvalCorrectness` over the `Theory.Syntax.Evaluable`
  carrier — determinism alone gives canonicity; totality gives a defined
  canonical value. The full "fixpoint ⟹ correct on all inputs" jump is in
  `Theory.RanzowFixpoint.EvalFullCorrectness` (zero postulates): rather than the
  rewriting version's single monolithic Established postulate, it **decomposes**
  the gap into the two halves of Appendix A — `encoding-completeness` (A.4/A.5)
  and `transparency` (A.3) — joined by a **constructive** assembly proof through
  an explicit branch-wise-correctness certificate. Remaining depth: `transparency`
  is the standard **NbE adequacy** lemma (ADHS 2001; Balat–Di Cosmo–Fiore 2004) —
  re-based from "folklore" onto a published, provable result, to be discharged by
  the concrete VM's adequacy proof; `encoding-completeness` is largely definitional
  (⌜N⌝ exposes every branch).
- Certify N by running `eval(N ∘ ⌜N⌝) == eval(⌜N⌝)` on the VM.

**Layer 1+ — the Once compiler, stratified on the trusted core:**

- Front-end (surface Once → CCC term) written *as CCC terms*, run/checked by the
  trusted Layer-0 core. Keep Once a conservative sugar over the core `Code` type
  so desugaring is an endo-rewrite (path back to a single fixpoint).
- Raw parsing (`bytes → tree`) verified by round-trip, not by fixpoint.
- The reflexive compiler self-fixpoint ("binary reproduces itself from its own
  source") is worth doing **later, as a complementary integrity / anti-trusting-
  trust check** — not as the source of correctness.

## Termination, totality, productivity — three things, don't conflate

Once uses **only structured recursion** (`cata`/`ana`, no general `fix`). "We
don't care about termination, we care about totality + productivity" is the
[total functional programming](https://en.wikipedia.org/wiki/Total_functional_programming)
discipline, and it is exactly the right framing — but "termination" is doing
triple duty, so pin the three notions down:

1. **Object-level totality** — every closed Once program of *inductive* type
   evaluates to a finite value in finite time. Consumers (`cata`) guarantee it.
2. **Object-level productivity** — for *coinductive* output (`ana`: streams,
   infinite trees) every finite *observation* is produced in finite time. The
   coinductive analogue of totality.
3. **Meta-level strong normalization (SN)** — the *normalizer's own* reduction
   halts. This is the hypothesis the Ranzow theorem and decidable conversion
   reference.

With `cata`/`ana` as the only recursion combinators, (1) and (2) hold **by
construction** (consequences of the initial-algebra / final-coalgebra universal
properties), not as checked side-conditions.

**What this changes — the evaluator route, decisively in our favour.** Map the
two routes' requirements:

| route | needs | supplied by structured recursion? |
|---|---|---|
| term-rewriter | **confluence** + SN | SN ✓ (= totality); **confluence ✗** |
| evaluator / NbE | **determinism** + totality/productivity | determinism ✓ (free); totality/productivity ✓ |

Totality + productivity is *precisely the evaluator's missing premise*: it is what
turns "determinism replaces confluence" into a **total** function that yields a
defined canonical form for every input.

**What it does *not* change.** Totality/SN does **not** give confluence — SN with
non-local-confluence is consistent (Newman's missing hypothesis; the mechanised
`NonConfluenceWitness` is an instance). Non-confluence is *structural* (rule
overlaps), independent of whether programs terminate. Likewise **fold/build
fusion** and **`cata`-uniqueness** are non-confluent as directed rewrites
regardless of totality. The resolution is to **never orient them as rewrites**:
the evaluator computes only with the `cata`-β rule; fusion/uniqueness hold in the
model (NbE) or become `≈`-preserving optimizer passes. So structured recursion +
evaluator sidesteps their non-confluence entirely.

**Reassurance for the bootstrap.** Productivity / bisimulation-equality on
infinite values matters only for Once's *runtime over user coinductive data*
(`ana`, CCT4) — **not** for the TCB0 fixpoint check. The check operates on
**encodings**: `Code = μ TermF` is *inductive*, and `⌜N⌝`, `N ∘ ⌜N⌝` are finite
term trees. There, totality ⟹ the evaluator terminates, and equality stays a
finite structural tree-walk (the CCC-VM sketch's `equal` suffices). The
foundation lives at CCT3 (inductive, finite); coinduction is downstream.

The slogan: *the discipline that makes Once well-behaved as a language
(totality + productivity) is exactly the discipline that makes its normalizer
well-defined as an evaluator.*

## Concrete assets, and where the two evaluator-route gaps actually close

A survey of the existing tree (so this is reuse, not greenfield):

- `bootstrap/normalizer/` (51 files, builds): a concrete normalizer that already
  proves the Ranzow fixpoint on its own encoding (`fixpoint-from-noredex`), with a
  15-way dispatch, an evaluator, `NormalizerSpec`/`SatisfiesSpec`, and uniqueness —
  but in the **rewriting** paradigm, resting on `Axioms/` postulates. Its reduction
  has **two-way `assoc`**, so it dodges `NonConfluenceWitness` (the two stuck NFs
  re-associate and join) at the cost of normalization: `strong-normalization` is
  **false**, mechanised in `normalizer.Theory.WeakNormalizationFails`
  (`weak-normalization-fails`; a 3-way projection composition loops under
  `assoc-l`/`assoc-r`). This is the **dual** of the formal side — one-way assoc → SN
  holds, confluence fails; two-way → confluence salvageable, SN fails. Each rewriting
  development sacrifices one of {confluence, termination} and postulates it back; the
  evaluator route (determinism + totality) needs neither.
- `formal/Theory/Models/StrongCCL3/`: a concrete erased `encode` (tag00–15) with
  **`encode-is-nf` proven** (`NormalForm.agda`) and the typed layer's **type-recovery
  faithfulness** (`Typed/Faithful`). Full term-level faithfulness is **still open**:
  the erased encoding loses a composition's middle type, so
  `encode g ≡ encode h → g ≡ h` is not provable at the erased layer alone.

**Where the two `EvalFullCorrectness` gaps close.** Both `encoding-completeness` and
`transparency` are stated over the evaluator's `_⇓_` (`encVal`, `encode-⇓`, the
branch-exercise, NbE adequacy). They are therefore discharged **by the concrete
evaluator, not before it** — there is no sound way to close them while `_⇓_` is
abstract. (Term-level faithfulness is a *rewriting*-track `EncodingInductive` field,
not required by the evaluator theorems, and is independently open.) So the honest
next step for the evaluator route is the concrete `Evaluable` instance itself —
reusing `bootstrap/normalizer`'s evaluator + dispatch as the blueprint and
`StrongCCL3`'s `encode` / `encode-is-nf`.

## Bottom line

Build the **evaluator CCC-VM + certified normalizer core first** — that is where
the correctness leverage lives and where "no trust in source" is achievable.
Do **not** build "only the compiler": its self-reproduction fixpoint is
reproducibility, not correctness (Thompson). The compiler is a stratified
consumer of the trusted core. Keep Once as conservative sugar so that normalizer
and compiler re-converge over the **confluent core** (Curien β-fragment) with
η handled by **expansion / NbE** — *not* by chasing full-βη confluence, which is
impossible (mechanised in `NonConfluenceWitness`).
