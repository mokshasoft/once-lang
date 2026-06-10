# Plan: Closing the gap to TCB0

**Target:** OCP-0004 (zero-software-trust verification — TCB0).
**Status:** roadmap (2026-06-10).
**Premise correction:** Agda is the EXPLORATION vehicle, NOT part of the TCB.
The end-state trust base is *mathematics + a one-time human verification of
self-evident traces*. Everything below is about moving facts we currently
hold *in Agda* onto that footing.

---

## 0. Where we are (the foundation banked)

On branch `cct1-safe-model`, machine-checked under Agda `--safe`, **no
postulates / NO_POSITIVITY / TERMINATING / confluence / SN**:

- `Adequacy.adequacy` / `NormalizeFullCorrectness.normalize-correct-all` =
  `RanzowFixpoint.Correct nf normalize` — the CCC+cata normalizer `normalize`
  computes the spec normal form `nf` on EVERY encoded input, **denotationally**
  (`eval (normalize ∘ encode g) ≡ eval (encode (nf g))`).
- `Idempotence.idempotent` — output is always a normal form.
- The MODEL itself is now pure category theory: `Fix` is a genuine
  strictly-positive inductive type, `cata-Set` terminates structurally — the
  Agda-specific "trust me"s are gone, so what Agda checked is now expressible
  in the *same* mathematics TCB0 grounds trust in.

### The strategic reframe (why this matters for TCB0)
OCP-0004's original Level-0 argument is **"fixpoint ⟹ normal form ⟹ unique ⟹
correct,"** which rests on **confluence + strong normalization** of the `_⟶_`
rewrite system. In THIS development those are axiom-laden / false
(`WeakNormalizationFails`, confluence-via-triangle; `Axioms/`). The **evaluator
route gives the same conclusion (the normalizer is correct) WITHOUT confluence
or SN** — denotationally, axiom-free. So:

> **TCB0's trace-verifier stays syntactic (`_⟶_` steps), but its *soundness*
> — "a verified trace's result is THE correct normal form" — can rest on the
> axiom-free evaluator route instead of on confluence/SN.**

That substitution is the core contribution this dev brings to OCP-0004, and it
is what the phases below operationalise.

### A trust-axiom taxonomy we must keep straight
- **`--safe` (no postulates)** = the *exploration* standard. Achieved for the
  correctness chain.
- **TCB0 "mathematics"** = a strictly LARGER, legitimate base: it MAY include
  standard mathematical principles like **funext** (a real theorem/axiom of
  mathematics), but must NOT include the *false* confluence/SN axioms.
  Consequence: `EvalSound`'s `funext` is acceptable *for TCB0* even though it
  is not `--safe`. The confluence/SN axioms are acceptable for NEITHER.

---

## 1. The TCB0 end state (from OCP-0004), precisely

Trust collapses to **math + human trace-reading**, via one mechanism:

> **Result ≡ verified trace content, NOT what software/hardware computed.**

Artifacts that must exist:
- **Trace-emitting normalization**: `CCC → (CCC , Trace)`, `Trace = [(rule,
  before, after)]`.
- **A verifier `V`** that checks a single step is a valid `_⟶_` instance —
  itself a small BCCR term (~25 primitives) with the SAME fixpoint property,
  decomposable into micro-verifiers (`V_id`, `V_pair`, `V_case`, `V_exp`,
  `V_cata`).
- **Human-readable meta-traces** + a one-time bootstrap protocol (verify `V`'s
  meta-trace by hand ≈ 1–2 h, then `V` verifies everything else).
- **Auditable `encode`** (injectivity proven; faithfulness checkable by reading
  ~50 lines).

Residual TCB at the end: (i) mathematics is consistent, (ii) `encode` is
faithful (readable), (iii) a human can read self-evident pattern matches. For a
*machine-checked-at-scale* variant, add (iv) the **C3PU** formal CPU semantics
in place of re-reading every trace by hand.

---

## 2. The gaps (concrete)

| # | Gap | From → To |
|---|-----|-----------|
| G1 | **Denotational → syntactic bridge.** Our correctness is about `eval` (morphism equality). TCB0 verifies `_⟶_` traces. | `Adequacy` (eval) + `EvalSound` (`t ⟶ u ⟹ eval t ≡ eval u`) + `encode` injectivity ⟹ "verified `⌜g⌝ ⟶* R`, `R` normal ⟹ `R = ⌜nf g⌝`". |
| G2 | **Trace machinery absent.** No trace emission, no verifier `V`. | Build `CCC → (CCC,Trace)`; build `V`/micro-verifiers as BCCR terms; prove each has the fixpoint. |
| G3 | **Human bootstrap absent.** No meta-trace format, no protocol. | Readable meta-trace renderer; the one-time human verification of `V`. |
| G4 | **RF of the *real* normalizer is not axiom-free.** `RealNormalizerFixpoint` rests on `EvalSound`'s funext (and is currently not migrated to One/Kc). | Re-establish the self-fixpoint of `normalize`; decide whether funext stays (OK for TCB0) or is avoidable. |
| G5 | **Encoding-faithfulness audit.** `encode` injectivity is proven; "matches intent" is a human read. | Consolidate injectivity + a ≤~50-line auditable `encode`/`⌜_⌝` with a written faithfulness argument. |
| G6 | **C3PU execution bridge.** `_⟶_`/`eval` are math; a running checker is silicon. | Formal CPU model; compile `V` to it; prove execution realizes `_⟶_` (so machine trace-checking is trustworthy). |
| G7 | **Remove Agda from the loop.** Today the facts live in Agda. | The human-checked `V` meta-trace re-grounds them; Agda becomes an optional independent cross-check. |

---

## 3. Phased plan

### Phase 0 — Consolidate the axiom-free foundation *(mostly done)*
- ✅ `--safe` correctness + idempotence + clean model (this branch).
- ☐ Land `cct1-safe-model` (decide: merge, or keep as the canonical model).
- ☐ Straggler hygiene: migrate/retire the One/Kc-disturbed modules
  (`CataTerminates` is now REDUNDANT — the model's `cata-Set` *is* the
  structural cata; `RefoldFixpoint`/`RefoldFullCorrectness` are the superseded
  spec=id witness; the TCB0-syntactic `fmap-KK-id` callers need the rename).
- **Exit:** one clean, `--safe`, axiom-free statement of "the CCC normalizer
  computes `nf`," with the model expressed as plain category theory.

### Phase 1 — The syntactic bridge (G1, G4)
Connect the denotational result to the `_⟶_` reduction system the trace lives
in. Pieces, all already partially present:
- `EvalSound` (soundness of `_⟶_` w.r.t. `eval`) — **migrate to One/Kc**; keep
  funext but LABEL it as a TCB0-legitimate axiom (not `--safe`). This is the
  hinge lemma: a verified trace preserves denotation.
- `encode` injectivity / canonicity (already in `Encoding.agda` + the formal
  `…EvalCorrectness` canonicity) — assemble into: *a normal `R` denotationally
  equal to `⌜nf g⌝` IS `⌜nf g⌝`*.
- **Target theorem:** `∀ g. normalize ∘ ⌜g⌝ ⟶* ⌜nf g⌝` (syntactic), proved
  from (adequacy + eval-soundness + injectivity) — NOT from confluence/SN.
- Re-establish the **self-fixpoint** `normalize ∘ ⌜normalize⌝ ⟶* ⌜normalize⌝`
  on the same axiom-free-modulo-funext footing (this is the runtime
  self-consistency witness; recall it proves well-formedness, *not*
  correctness — correctness is the ∀-g theorem above).
- **Exit:** correctness and self-consistency both stated over `_⟶*_` (traces),
  grounded in the evaluator route, with the residual axiom being funext only.

### Phase 2 — Trace machinery (G2)
- **Trace-emitting normalize:** instrument the reducer to emit `[(rule,before,
  after)]`. (Doc Approach 1/4 — the reduction step *is* the proof of
  `before ≡ after`.)
- **The verifier `V` as a BCCR term:** `V : Step → Bool` = "is this a valid
  `_⟶_` instance?", written `cata TermF verifyAlgebra` so it inherits the
  fixpoint property. Prove `V`'s own fixpoint and totality (reuse `cata`
  totality — now structural/axiom-free).
- **Micro-verifiers** `V_id/V_pair/V_case/V_exp/V_cata`, each with its own
  fixpoint, sized for ~15–20 min human checks.
- **Exit:** an executable (BCCR-term) verifier whose correctness is itself a
  fixpoint statement, plus trace output from the normalizer.

### Phase 3 — Human bootstrap (G3, G5)
- **Meta-trace renderer:** the self-evident format from OCP-0004 (highlighted
  pattern match + substitution + result, per step).
- **Encoding audit:** freeze a ≤~50-line `encode`/`⌜_⌝` (the One/Kc grammar is
  already small and first-order), with injectivity proven and a written
  "faithful to intent" paragraph.
- **The one-time protocol:** run *any* software to produce `T_V` and the
  checking meta-trace `M_V`; a human verifies `M_V`. After this, `V` is *proven
  by human-checked math*, not trusted.
- **Exit:** `V` grounded with **zero software trust**; the bootstrap protocol
  is documented and reproducible.

### Phase 4 — C3PU execution closure (G6) *(parallelizable)*
- Formal CPU semantics (the C3PU).
- Compile `V` (and the trace checker) to C3PU instructions; prove
  **execution realizes `_⟶_`** — i.e. the machine's steps correspond to the
  verified reduction rules.
- **Exit:** machine-checked trace verification is trustworthy without
  re-reading each trace by hand — the *engineering* form of "math + human
  reading," with the CPU datasheet replacing repeated human checks.

### Phase 5 — Evict Agda from the TCB (G7)
- The Phase-3 human-checked `V` meta-trace now establishes the load-bearing
  facts. Agda is retained ONLY as an independent cross-check (diverse
  double-checking), not as a trust root.
- **Exit:** TCB0. Trust = {math (incl. funext), encoding faithfulness
  (readable), human reasoning} + optionally {C3PU} for scale.

---

## 4. What each phase removes from the trust base

```
Phase 0  : removes Agda escape-hatches (NO_POSITIVITY/TERMINATING) + false confluence/SN
           from the *correctness* story → "math, modulo Agda+funext".
Phase 1  : removes confluence/SN entirely from the trace-soundness argument
           (evaluator route replaces them) → residual axiom = funext.
Phase 2-3: removes Agda-the-checker → V + human-checked meta-trace.
Phase 4  : removes "trust the CPU computed right" → read bytes / C3PU semantics.
Phase 5  : Agda fully out of the TCB.
Final TCB: mathematics (incl. funext) + encoding faithfulness + human reasoning
           (+ C3PU datasheet for the machine-checked variant).
```

---

## 5. Open questions / risks (be honest)

1. **Denotational ↔ syntactic ↔ trace coherence (G1).** The cleanest open
   question: does the trace-verifier's soundness need *only* eval-soundness +
   injectivity (our axiom-free-modulo-funext kit), or does some step still
   want a confluence-like uniqueness? Must be nailed before Phase 2 — it is the
   linchpin that lets us drop confluence/SN.
2. **funext (G4).** It is fine for TCB0 (real math) but not `--safe`. Decide
   whether to (a) accept it as a labelled TCB0 axiom, or (b) avoid it by
   restricting the trace rules to the first-order fragment (no `curry-η`
   congruence) where eval-soundness is funext-free.
3. **Two "normalizers."** The META `_⟶_` reducer (runs terms) vs the OBJECT
   `normalize` term (computes on encodings). OCP-0004's bootstrap is the former;
   our correctness is about the latter applied to encodings. Phase 1 must state
   exactly which fixpoint/trace is being verified and keep them aligned.
4. **`V` scope.** `V` must cover exactly the rules the normalizer emits (the
   15 `TermF` positions / the implemented `_⟶_` rules). Keep `V` minimal — every
   rule it checks is human-read once.
5. **C3PU readiness (G6).** Independent track; the human-trace variant (Phase 3)
   already reaches TCB0 without it. C3PU is the scale/ergonomics upgrade.

---

## 6. One-line summary

We hold an **axiom-free, machine-checked proof that the CCC normalizer is
functionally correct** — the hard mathematical core. TCB0 is reached by
(1) re-expressing that as a statement about `_⟶_` traces grounded in the
evaluator route (dropping confluence/SN), (2) building the tiny self-verifying
`V` and its human-checked bootstrap, and (3) optionally closing the execution
layer with the C3PU. Agda was the ladder; the meta-trace is the floor.
