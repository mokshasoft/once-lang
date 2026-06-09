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

UPDATE (2026-06-08, cont.): obligation (1) — a REAL normalizer — is now
done, NOT degenerate:
- `…Eval.CataTerminates`: structural cata terminates, no pragma (totality
  is rigorous, not just `{-# TERMINATING #-}`-asserted).
- `…Eval.EvalSound`: `eval` respects reduction (`t ⟶ u ⟹ ∀x. eval t x ≡
  eval u x`), all 25 rule cases; one axiom (funext, for `⟶-curry`).
- `…Eval.RealNormalizerFixpoint`: the REAL `normalize = cata TermF
  normalize-step` has the denotational Ranzow fixpoint — its constructive,
  axiom-free syntactic fixpoint (TCB0 `fixpoint-from-noredex`) lifted via
  eval-soundness, fed through the formal canonicity theorem. Plus
  `normalize-correct-on-noredex`: denotationally correct on the whole
  class of already-normal inputs.

So the refold modules are the toy; the real normalizer is the genuine
witness. Trust: zero confluence, zero SN, no false postulates; one clean
axiom (funext) + the model's pre-existing pragmas (both dischargeable /
avoidable, see CataTerminates).

Recurring Agda note: wherever the candidate term sits only under the
non-injective `eval`, the unifier can't recover it — pass it explicitly
(`determinism {t = …}`, `mkFixpoint {N} …`), or prove the conclusion
directly instead of instantiating a hypothesis-bearing module (the
function-based `_⇓_` trips function-eta otherwise).

## Remaining (the real work) — now just ONE deep kernel

UPDATE (2026-06-09): transparency-kernel FEASIBILITY PROBE done.
`…Eval.HandlerCorrectness` proves the denotational correctness of the one
NON-TRIVIAL constructor of `normalize-step` — the comp handler — on both
implemented redexes:
- `handle-comp-id-left` / `handle-comp-correct-on-id-left`: `id ∘ g ⟶ g`,
  schematically and on real `encode`-images.
- `handle-comp-correct-on-id-right`: `f ∘ id ⟶ f` (exercises the second
  `check-g-handler` dispatch tier; concrete non-`id` left child).
All hold by `refl` — the `is-id`/`Out`/`distrib`/`caseWithCtx` cascade
computes in the model with no stuck redex. NO axioms, NO postulates (not
even funext). Confirms `eval` of a step branch "does the right thing on
that tag"; the path to all 15 constructors is mechanical for the rebuild
handlers and the same shape for the rewriting ones.

UPDATE (2026-06-09, cont.): transparency-kernel ASSEMBLY started.
`…Eval.StepTransparency` wires the per-constructor facts into the recursive
`normalize = cata TermF normalize-step` structure. All `refl`, axiom-free:
- `normalize-unfold` — the CRUX: `eval normalize (fix x) ≡ eval normalize-step
  (coherence⁻¹ TermF _ (fmap-Set TermF (eval normalize) x))` (cata-Set's
  computation rule + η for `eval`). This is the hook every constructor
  result plugs into.
- `normalize-comp` — specialisation: `eval normalize (comp-code c₁ c₂) ≡
  eval handle-comp (eval normalize c₁ , eval normalize c₂)`.
- `normalize-id-left` — FIRST transparency result PAST the NoRedex class:
  `eval normalize (comp-code (id-code A) c₂) ≡ eval normalize c₂` for
  ARBITRARY c₂ (the `id ∘ h ⟶ h` rewrite carried through the model on
  non-normal subterms; RealNormalizerFixpoint only had already-normal ones).
- Rebuild sweep: `normalize-fst` (leaf fixpoint), `normalize-pair` /
  `normalize-case` (recursive CONGRUENCES — the reusable inductive-step
  lemmas). The other 11 rebuild positions are the same one-liner.

UPDATE (2026-06-09, cont.): the COMP CASE of transparency is now CLOSED and
VERIFIED (both modules genuinely typecheck; interfaces re-emitted under
`bootstrap/check.sh`, exit 0):
- `HandlerCorrectness.handle-comp-trichotomy` — the COMPLETE case analysis
  of `handle-comp` on an arbitrary value pair, `is-id` decisions discharged
  internally: `(≡ v₂) ⊎ (≡ v₁) ⊎ (≡ rebuilt comp)`. This subsumes the
  `f ∘ id` redex the previous round could NOT reach as `refl` — it is now
  carried by the `is-id-correct` case split inside the lemma, on ARBITRARY
  normalized children.
- `StepTransparency.normalize-comp-complete` — lifts that trichotomy up to
  the comp-code via `normalize-comp`: `normalize (comp-code c₁ c₂)` always
  lands in exactly one of {right, left, rebuilt-congruence}. NO hypotheses,
  NO axioms.

MEMORY/TOOLING NOTE (standing rule for this dev): these proofs OOM-killed
agda (4.9–7+ GB) until rewritten WITHOUT `with`. `with e` forces agda to
normalise the whole goal, re-expanding the giant `eval handle-comp` /
`eval normalize` normal forms several times. RULE: avoid `with` on anything
mentioning `eval …`; instead LIFT the case analysis into a top-level
`private` helper that abstracts the giant term behind a plain variable `r`
(+ a `refl` witness) and PATTERN-MATCHES the small decision `⊎` (see
`tri-aux`, `ncc-lift`). `bootstrap/check.sh` now runs agda in a 5.5G/2G
cgroup scope (claude survives any OOM via oom_score_adj) and LOUDLY reports
signal-kills (exit 137) — trust the interface timestamp / real exit code,
never a wrapper's exit 0.

UPDATE (2026-06-09, cont.): the structural RECURSOR is now BUILT and
VERIFIED — `…Eval.FixInduction` (exit 0, no pragma):
- `induct : ∀ F (P : Fix F → Set) → (∀ x → All-rec F F P x → P (fix x)) →
  ∀ c → P c` — the proof-level mirror of CataTerminates' `cata`/`map-cata`,
  a mutual structural descent (`induct` peels `fix x ↦ x`; `induct-map`
  recurses on the functor CODE until `Id`, where it calls `induct` on a
  strictly-smaller sub-`Fix`). Termination accepted WITHOUT pragma.
- `All-rec F G P y` — the induction hypotheses at the recursive (`Id`)
  positions of one functor layer; `⊤` at `K` (constant) positions.

So structural induction over `Fix TermF` is rigorous and reusable.

UPDATE (2026-06-09, cont.): denotational IDEMPOTENCE is now DONE and
VERIFIED — `…Eval.Idempotence.idempotent` (exit 0, interface emitted):

    idempotent : ∀ c → eval normalize (eval normalize c) ≡ eval normalize c

i.e. `normalize`'s output is always a normal form (a normalize-fixpoint).
Proved by `induct TermF Idem idem-step`, the FIRST real application of the
structural recursor. Structure:
- `handle-comp-normal` — the CRUX, with-free: `handle-comp` of two
  normalize-fixpoints is itself a normalize-fixpoint (all three trichotomy
  branches land on an already-normal term; the rebuild branch re-normalises
  to itself via `normalize-comp` + children-normal + the rebuild spec).
- `comp-idem` — the comp position, from idempotence on both children.
- `idem-step` — 15 clauses (one per TermF position): every NON-comp handler
  is a plain rebuild (verified in Handlers: `rebuild-k`, incl. cata/curry),
  so leaves are `refl` and the recursive rebuilds close by `cong`/`cong₂`
  over the IHs; comp delegates to `comp-idem`.
Confirmed all-rebuild-except-comp by reading `TCB0/Normalizer/Handlers`.

UPDATE (2026-06-09, cont.): the SPEC `nf` is now DEFINED and VERIFIED —
`…Eval.NfSpec.nf : Term A B → Term A B` (exit 0, total, no pragma). It is
STRUCTURAL id-elimination (congruence everywhere; sole rewrite = id-comp
collapse via `comp-nf`), mirroring `normalize-step` EXACTLY — NOT the full
`_⟶_` (the β/drop rules are excluded). Detecting `id` in a Term arg trips
Agda coverage unification on the rich indices (Out/cata), so it routes
through a value-level `IsId?` detector (no `with`).

SCOPE DECISION (recorded): the bootstrap normalizer stays id-elimination-
ONLY. Rationale: its purpose is a correct/total normalizer WITH the Ranzow
fixpoint (transparency), not an optimizer; drop rewrites (dead-code elim)
are never needed for that. Per origin/heap-only-pivot-2 Plan 0.39, Once's
real correctness is SigOp-TRACE correctness and value-level proofs are
effect-blind — but ONLY drop rewrites can drop a SigOp. id-elimination is
trace-transparent (`id∘f=f`, `f∘id=f` preserve `obs` by construction), so a
VALUE-LEVEL `nf` is sound here and value-correctness ⟹ trace-correctness.
If the normalizer ever takes on drop rewrites, the spec must become
trace-aware (`obs`) — flagged in NfSpec's header.

UPDATE (2026-06-09, cont.): the ADEQUACY / faithfulness WALL is CROSSED and
VERIFIED — `…Eval.Adequacy.adequacy` (exit 0, postulate-free, with-free):

    adequacy : ∀ g → eval normalize (code-of g) ≡ code-of (nf g)
             (code-of g = eval (encode g) tt : Fix TermF)

The code-level normalizer on ⌜g⌝ yields the code of ⌜nf g⌝ — the NON-
degenerate transparency content (spec = nf, not the trivial spec = id).
Structure:
- encode→code commutation is DEFINITIONAL (refl), so the induction on the
  Term g mirrors idem-step: leaves refl, recursive rebuilds close by
  cong/cong₂ over the IH, comp via `comp-adequacy`.
- `idView` / `comp-adequacy` — the encode-faithfulness of id-detection:
  `is-id (code-of t) ⟺ IsId? t` (encode maps id→inj₁ id-code, every other
  constructor→inj₂…), aligning handle-comp's code trichotomy with comp-nf.
  Subtlety: `isId? x ≡ yes-id` is ill-typed for general x (yes-id forces the
  type eq), so all yes-id reasoning is done inside `caux` where `idView`
  refines the term to `id`; `comp-elim` is public for the no-id rewrites.

This is the semantic core of `RanzowFixpoint.EvalFullCorrectness.Correct nf
normalize`.

UPDATE (2026-06-09, cont.): CAPSTONE LANDED — `…Eval.NormalizeFullCorrectness`
(exit 0):

    normalize-correct-all :
      ∀ g → (normalize ∘ encode g) ⇓ᵈ mkVal (eval (encode (nf g)))

This IS `RanzowFixpoint.EvalFullCorrectness.Correct nf normalize` (N =
normalize, encVal g = mkVal (eval (encode g))) — full correctness on ALL
inputs for the REAL normalizer with spec = nf, NON-degenerate. Proof =
`adequacy` lifted via ⊤/function eta (`cong (λ z → λ _ → z)`, exactly as
RefoldFullCorrectness), plus a one-line `toStd` transporting the bootstrap-
prelude `_≡_` (adequacy) to the stdlib `_≡_` that the abstract `_⇓ᵈ_` uses.
Postulate-free; NO confluence, NO strong normalization.

The evaluator-route transparency obligation is DISCHARGED non-degenerately.
(The optional `EvalFullCorrectness.Theorem` MODULE instantiation is the same
eval-eta unifier story as Instance/RefoldFullCorrectness — the conclusion and
its type here are identical to that theorem's output, proved directly.)

--safe STATUS (2026-06-09): the 7 evaluator-route proof modules use NO
postulates/pragmas (verified). The chain is NOT yet `--safe`-buildable, blocked
ONLY by `Testing/Evaluator.agda`'s 3 model pragmas. QUICK WIN DONE: `eq-Term`'s
`{-# TERMINATING #-}` removed — the mutual eq-Term/eq-TermFS/eq-TyFuncCode
recursion is structural and Agda accepts it pragma-free. REMAINING (substantive,
one batch): (a) `cata-Set`'s `{-# TERMINATING #-}` — the pragma-free mutual
`cata`/`map-cata` form EXISTS (CataTerminates / FixInduction.induct) but swapping
it changes the model's REDUCTION, breaking the `fmap-Set`-stated `refl` proofs in
RefoldFixpoint / EvalSound / StepTransparency.normalize-unfold (unused) — so all
those must be restated via `map-cata`; (b) `Fix`'s `NO_POSITIVITY_CHECK` — restrict
the model to the strictly-positive `Func` universe (no `K` of an arrow), the real
work. (a)+(b) together, not piecemeal, since both touch the model's core.

Obligations (1) real normalizer + totality are DONE (above). What remains:

- **Full correctness on ALL inputs (transparency with spec = nf).** We have
  it on the NoRedex class (`normalize-correct-on-noredex`); the general case
  `∀ g. eval (normalize ∘ ⌜g⌝) ≡ eval ⌜nf g⌝` is the deep kernel. It needs
  an INDEPENDENT normal-form notion `nf` plus a proof connecting normalize's
  denotation to it — i.e. either the general *syntactic* correctness
  (`normalize ∘ ⌜g⌝ ⟶* ⌜nf g⌝`, which in the existing TCB0 dev rests on the
  FALSE `strong-normalization`/confluence axioms and would need redoing) or a
  *denotational* correctness proof of the `normalize-step` algebra
  per-constructor. This is the genuine NbE-adequacy content; multi-session.
- Faithfulness on encodings (the composition-middle-type wall, typed
  two-layer encoding) is the same deep kernel from the syntactic side.

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

---

## --safe HEAVEN (2026-06-09): the transparency + idempotence chains are machine-verified --safe

The evaluator-route's REAL theorems now typecheck under Agda `--safe` (clean
cache, per-module `{-# OPTIONS --safe #-}`), with NO postulates, NO
NO_POSITIVITY_CHECK, NO TERMINATING anywhere in their chains:

- `NormalizeFullCorrectness.normalize-correct-all` = `Correct nf normalize`
  (the transparency obligation) — 18 bootstrap modules + 10 formal Once-lib
  modules, all --safe.
- `Idempotence.idempotent` — via the structural recursor `FixInduction`.

The model refactor that made this possible:
- `Func` is now FIRST-ORDER (`Id/One/Kc/⊕/⊗`, Ty-independent) — so `Fix` is
  strictly positive with no pragma and coherence/coherence⁻¹ are total.
- `cata-Set` is the mutual structural `cata-Set`/`map-cata-Set` (no pragma).
- `Encoding` grammar (`TyFuncF`) grew One/Kc functor positions (10→11);
  `TermF` uses `Kc TyFuncF` (structurally identical, 15 positions).
- Flagged the 10 postulate-free formal/ abstract-tower modules `--safe`.

DISTURBED by the foundational change (NOT in the --safe target chains, to be
migrated separately if a fully-green tree is wanted):
- `CataTerminates` — now REDUNDANT (the model's `cata-Set` IS the structural
  version it used to demonstrate); migrate to One/Kc or retire.
- `RefoldFixpoint` / `RefoldFullCorrectness` — the DEGENERATE spec=id witness,
  superseded by the real transparency chain; used the old fmap-Set reduction.
- `EvalSound` (+ dependent `RealNormalizerFixpoint`) — carries the funext
  postulate, so it can never be `--safe`; the eval-soundness route.
- TCB0 syntactic `fmap-KK-id` callers (DispatchCombinators, RefoldIdempotent,
  Base*, SelfFixpoint, DispatchLemmas) — the K→One/Kc rename; mechanical.
