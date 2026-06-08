# Plan: concrete Evaluable instance → discharge the evaluator-route gaps

## STATUS (2026-06-08): foundation mechanised end-to-end (postulate-free)

Modules 1–7 + capstone are DONE, all building under `bootstrap/check.sh`:
- `Once`: `SelfEncoding` + `EvalCorrectness`/`EvalFullCorrectness`
  re-parameterised over it, modules named (`Fixpoint`/`Canonical`,
  `FullFixpoint`/`Laws`/`Theorem`).
- `bootstrap`: `depend: Once`; `normalizer.Theory.Eval.Instance`
  (`NormSE`, `NormEv`, determinism + totality FREE, canonicity);
  `…Eval.RefoldFixpoint` (cata-reflection ⟹ the refold normalizer
  `cata TermF In` has the Ranzow fixpoint, fed through the formal
  canonicity theorem); `…Eval.RefoldFullCorrectness` (correct on ALL
  inputs for spec = id).

Zero postulates anywhere in the chain; NO confluence and NO
strong-normalization obligation — the evaluator route's whole point.

CAVEAT: the witness N = refold is DENOTATIONALLY THE IDENTITY (spec = id),
so the result is degenerate-but-real. The genuinely meaningful normalizer
needs module 8 below.

Recurring Agda note: wherever the candidate term sits only under the
non-injective `eval`, the unifier can't recover it — pass it explicitly
(`determinism {t = …}`, `mkFixpoint {N} …`), or prove the conclusion
directly instead of instantiating a hypothesis-bearing module (the
function-based `_⇓_` trips function-eta otherwise).

## Remaining (the real work)
- **Module 8 — adequacy / faithfulness on encodings (HARD KERNEL).** Needed
  to lift denotational results to the actual syntactic normal form, and to
  use a non-trivial N. Hits the SAME composition-middle-type obstruction as
  the erased encoding's faithfulness (see normalizer-vs-compiler-path.md):
  `eval (encode (id{A})) = eval (encode (id{B}))`, so the erased model is
  not faithful — this needs the typed two-layer encoding. Genuine
  multi-session NbE-adequacy work; principled but large.
- A real dispatch normalizer (not the refold) instantiated through the
  full chain, once module 8 exists.

---


Goal: instantiate the abstract evaluator-form theorems
(`Theory.RanzowFixpoint.EvalCorrectness` / `EvalFullCorrectness`) with a
*concrete* evaluator, discharging `determinism`, `totality`, `encVal`,
`encode-⇓`, `encoding-completeness`, and `transparency` — i.e. turning the
fixpoint⟹correctness chain into a postulate-free concrete theorem.

## Two structural facts that shape everything (verified 2026-06-08)

1. **The model needs first-order functor codes.** A total denotational
   model (`⟦_⟧T : Ty → Set`, `Fix`, `cata-Set`) is definable ONLY when
   `μ` ranges over a first-order `Func` universe (`Id`/`K`/`⊕`/`⊗`).
   - `bootstrap/normalizer` syntax: `μ_ : Func → Ty` ✓ — model exists.
   - `formal StrongCCL.CCT3`: `μ : (Ty → Ty) → Ty` ✗ — meta-level functor,
     cannot be folded; **cannot host an evaluator**. (Same reason the
     formal RF discharges used a *trivial* encoding.)
   ⇒ The instantiation target is the **normalizer's Func-based syntax**.

2. **The libs are disjoint.** `Once` (formal, abstract theorems; depends
   on stdlib) and `bootstrap` (model + `eval` + `encode` + normalizer;
   depends on NOTHING, own prelude) do not import each other.
   ⇒ An architecture decision is required (below) before wiring.

## Architecture decision — RESOLVED: (B) + SelfEncoding re-parameterization

Chosen: **(B)** `bootstrap` depends on `Once` (no duplication, forced inline),
made possible by re-parameterizing the two eval modules over the minimal
`Theory.RanzowFixpoint.SelfEncoding` record (Obj/Hom/∘/Unit/Code/encode) instead
of the full higher-order-`μ` `CCT3Structure` (which bootstrap's first-order `Func`
syntax cannot fill). `fromCCT3` adapts existing `CCT3Structure`+`EncodingScheme`
users for free. Done + typechecks. Remaining for B: `bootstrap` `depend: Once`
+ build wiring; then rewrite the instance modules against the formal theorems.

Original options (for the record):

Where do the abstract evaluator-form theorems meet the concrete model?

- **(A) Relocate the tiny abstract modules into `bootstrap`.** `Evaluable`,
  `EvalCorrectness`, `EvalFullCorrectness`, plus the minimal slice of
  `CCT3Structure`/`EncodingScheme` they use, rewritten against bootstrap's
  own prelude (~150 lines total, stdlib-free). Keeps `bootstrap`
  self-contained; small duplication of stable abstract content.
  *Recommended* — lowest coupling, no risk to existing builds.
- **(B) `bootstrap` depends on `Once`.** Import the abstract modules
  directly; pulls stdlib into bootstrap and couples the libs.
- **(C) Build a `Func`-based CCT3 syntax inside `Once`.** Port the
  normalizer's syntax+model+encode into formal. Most duplication; only
  worth it if formal must stay the single source of truth.

## Module status & plan

Target lib per the decision above (assume (A): all in `bootstrap`).

| # | Module | Status | Reuses | Work |
|---|--------|--------|--------|------|
| 1 | model (`⟦_⟧T`, `Fix`, `cata-Set`, coherence) | **EXISTS** | `Testing/Evaluator.agda` | none (reuse) |
| 2 | term interp (`eval : Term A B → ⟦A⟧T→⟦B⟧T`) | **EXISTS** | `Testing/Evaluator.agda` | none (reuse) |
| 3 | abstract theorems in-lib (`Evaluable`/`EvalCorrectness`/`EvalFullCorrectness` + minimal `CCT3Structure`/`EncodingScheme`) | TODO | `Once` originals | relocate vs prelude (~150) |
| 4 | `Evaluable` instance + `determinism` + `totality` | TODO | `eval` | **free** (`refl`; `eval t , refl`) (~50) |
| 5 | `encVal`/`encode-⇓` | TODO | `Encoding.encode`, `eval` | **free** (`refl`) (~30) |
| 6 | `CCT3Structure` + `EncodingScheme` for the normalizer syntax | TODO | normalizer syntax | structural (~100) |
| 7 | concrete normalizer `N = cata step` | partial (`normalizer = cata In`; real dispatch in `TCB0/`) | `Dispatch`/`Rebuild` | choose trivial vs real |
| 8 | **adequacy on encodings** (`eval(encode x) ≡ eval(encode y) → encode x ≡ encode y`) | TODO | `encode` structure, `encode-is-nf` | **HARD KERNEL** — but first-order (no ⇒/η), so far smaller than full NbE reify |
| 9 | `encoding-completeness` discharge | TODO | blueprint `NormalizerSpec`/`SatisfiesSpec` | moderate |
| 10 | `transparency` discharge (input induction + `cata-Set`) | TODO | blueprint `SelfFixpoint`/`NoRedex` | moderate |
| 11 | assembly → concrete `fixpoint-implies-correctness` | TODO | 4,5,9,10 + abstract | ~50 |

## Positivity (`NO_POSITIVITY_CHECK`)

The pragma in `Testing/Evaluator.agda` is an artifact of the *generic*
model (a `K`-embedded `⇒`-over-`μ` puts `Fix` left of an arrow). It is NOT
intrinsic: `Code = μ TermF` is strictly positive (`TermF` has no arrows).

Options, cleanest first:
- **Restrict the model to strictly-positive functors actually used** (the
  `Func` universe has no arrow constructor; monomorphise / avoid `K` of
  `⇒`-over-`μ`). Removes the pragma, keeps determinism/totality free.
- Operational closure model (closures as data) — sound, VM-faithful, but
  `totality` becomes a real SN proof; closure equality needs bisimulation.

**Bisimulation does NOT fix positivity** (it is an equality notion; a
relation cannot legitimise a non-positive *type*). Bisimulation is the
right equality for *closure* values (operational model) and *coinductive
ν* values (CCT4) — neither appears in the bootstrap fixpoint check, which
compares first-order `Code` data with plain `≡`.

## The hard kernel (#8) is smaller than ADHS

Adequacy is needed only *on encodings*, which are first-order `Code` data
(`Fix TermF`, no `⇒`/η). So `⟦encode x⟧` mirrors `x`'s code as a `Fix`
value and injectivity is a structural argument — it sidesteps the
sum-η / function-η difficulty that makes full NbE adequacy hard. This is
the cccvm-sketch insight: the check is a first-order value tree-walk.

## Ordering

1. Decide architecture (A/B/C).
2. Land 3–6 (relocate abstract + Evaluable instance + encVal): a compiling
   skeleton that concretely discharges `EvalCorrectness` (determinism +
   totality + canonicity) against the real `eval`. **Milestone, low risk.**
3. Pick N (#7), then the hard work: #8 (kernel), #9, #10, assembly #11.

## Caveats to keep honest

- The denotational model assumes its `Set`-interpretation (with the
  positivity treatment above). The eventual *inspectable VM* is
  operational; this model is for *proving* the theorem.
- `bootstrap/normalizer`'s existing fixpoint dev rests on FALSE axioms
  (`strong-normalization` — see `WeakNormalizationFails`; and
  confluence-via-triangle). This evaluator-route instance must NOT import
  `Axioms/`; it replaces them with determinism + totality.
