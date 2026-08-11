# OCP-0005: Decision State & Invariant Encoding

**Author:** Jonas Claesson
**Status:** Draft
**Created:** 2026-06-09

---

## Summary

The decision log (`docs/compiler/decision-log.md`, 56 entries D001–D056) is the
project's design memory, but it is **prose** — not enforced. Decisions get
superseded, partially revised, or quietly contradicted by code, and nothing
catches the drift. This OCP proposes two things: (1) maintain a **decision
state** — a separate, *living* `decision-state.md` holding only the
currently-in-force decisions (supersessions/revisions resolved), each pointing
back to its decision-log lineage and kept current as decisions land; and (2)
**encode** those in-force decisions as compiler-enforced invariants (types,
proof obligations, or structural checks) so the compiler *cannot* silently
violate them. It also recognises a third
category — **design choices that are not proper decisions** (e.g. the
completeness-view rule below) — which are worth pinning the same way.

---

## Motivation

The log is append-only narrative; the *truth* (what's in force now) is implicit
and scattered. Concretely:

- **Supersession is in the prose, not the structure.** D043 is "superseded in
  full" by D044/D045; D032's value/morphism separation is recorded as a
  "vestige" made redundant by D046's grade. To know the current rule you must
  read the whole chain. There is no single "decision state."
- **Prose decisions are silently violable.** Nothing stops code from drifting
  from a decision. We only catch drift when a decision *happens* to coincide
  with a checked obligation. The recent value-lift work is the proof of this:
  - A `globalElem` post-pass over the elaborated `SExpr` was the wrong
    abstraction level — **completeness caught it** (the typing rule couldn't
    reference an Elaborate-level pass), forcing `globalElem → ⊢ᵍ`.
  - Per-shape `⊢ᶜ` lift rules were over-general — **completeness caught it
    again** (the premise admitted non-extractable `t-embed` refs).
  - These were caught *only because* completeness is a formal obligation. A
    prose decision ("a value is a closed global element") would not have.
- **The masquerade guard is a live example of an encoded decision.** D032's "no
  effect masquerades as pure" is *enforced* because purity is a **grade** on the
  arrow (D046) and `lift-morphism` lands only on `⇒[pure]`. That decision can't
  be violated — it's a type. Most decisions don't have this property yet.

So: encoding turns "we decided X" into "the compiler rejects ¬X."

---

## Proposal

### Phase 1 — Decision State (a living `decision-state.md`)

Produce a **separate, living document** — `docs/compiler/decision-state.md`,
beside the log — that is the *current truth*: only the decisions in force *now*,
with the supersession chain already resolved. The decision **log stays as it is**
— append-only narrative/history; the **state document is the resolved snapshot**.

**Two roles, not one source.** The log records *what happened and why* (D043 was
chosen, then superseded). `decision-state.md` records *what is true now* (the
current compose-desugaring rule), so future work reads one resolved document
instead of re-deriving the truth from the chain.

**Structure.** Each entry in `decision-state.md` is a *current rule*:

- a one-line statement of the rule as it stands today;
- **a pointer (back-link) to the decision-log entry/entries** it derives from —
  including the supersession lineage (e.g. "compose desugaring: direct `IR.∘`
  classifier route, no optimizer dependency — D044/D045, superseding D043");
- optionally, its enforcement mechanism once Phase 2 assigns one (the type /
  theorem / lint that pins it — so the state entry doubles as the index into the
  encoded invariants).

To build it initially, walk D001–D056 and classify each: **in force**,
**superseded** (→ by what), **revised** (narrowed/refined — D018 under D046's
grade), **vestige** (retracted but still load-bearing as a smaller guarantee —
D032's separation → the grade does the masquerade job). In-force + the surviving
content of revised/vestige entries become `decision-state.md` rules; superseded
ones do not (their successors do).

**Always current — the maintenance invariant.** `decision-state.md` must be
updated *in the same change* that lands a new decision or supersedes/revises an
old one. A new log entry that changes the in-force set is incomplete until the
state document reflects it. (This is itself a candidate Phase-3 design rule, and
a natural lint: "a decision-log diff that adds/supersedes a decision must touch
`decision-state.md`.")

### Phase 2 — Encode the in-force decisions

For each in-force decision, choose an **enforcement mechanism**:

1. **Type-level invariant** — make violation ill-typed. *Strongest.* Example:
   the masquerade guard (purity grade on `_⇒[_]_`); "the morphism realm is
   `zeroUsage`" (`lift-morphism`'s signature).
2. **Proof obligation** — a theorem the compiler must satisfy, so drift is a
   broken proof. Example: soundness/completeness of elaboration; "every
   well-typed value elaborates" (the `⊢ᵍ` / `gd-complete` obligation, which
   forced the right abstraction twice).
3. **Structural / lint check** — a mechanical check when types/proofs are
   overkill. Example: "SigOps stay in their namespace" (PreservesCCC);
   provenance disjointness of labels.
4. **Documentation-only** — decisions not (yet) mechanizable; record *why* and
   what would make them mechanizable.

The deliverable per decision is: the current rule + the chosen mechanism + (if
mechanized) a pointer to the type/theorem/check that enforces it.

### Phase 3 — Capture non-decision design choices

Some load-bearing choices never became numbered decisions but are exactly as
worth pinning. Seed the catalogue with the one this work surfaced:

> **The with-opacity / view rule.** In any operational function a completeness
> (or soundness) proof must *reduce through*, scrutinise a **view that bundles
> the decidable's defining equation** (`inspectLookupLocal`,
> `inspectWellFormedF`, `inspectCheckG`) — never the raw decidable behind a
> `with … in`. The raw form is opaque to the proof and tempts a postulate;
> three independently-accreted views are evidence this is a recurring invariant.
> Enforcement candidate: a lint over elaborator functions referenced by
> Completeness, flagging `with <decidable> in` without a corresponding view.

Two more surfaced by the Plan 0.36 cata-correctness work:

> **The "name must match the type's strongest claim" rule — encode the headline
> guarantee, demote lemmas to fields.** A correctness predicate must be *typed*
> as the guarantee its *name* asserts; supporting lemmas become **fields** of
> that type, so the theorem cannot be inhabited by proving only a lemma. A
> program is `Eff Unit Unit`, so its only observable is the SigOp trace —
> trace-correctness is *the* correctness and value-correctness (`ValidAtWF`) is
> its *engine*, not a peer. Encoded as `record MachineRefinesObs` with
> `traces-agree` (the mandatory trace obligation) + `value-realized` (`ValidAtWF`
> as a field). **Anti-pattern it kills:** `IRTraceCorrect` was *named* for the
> trace but *typed* as `ValidAtWF` — nothing forced name and type to agree, and
> Layer-0 purity (trace = f(value)) let the gap hide indefinitely; a names-only
> trace would even "verify" a program that exits with the *wrong* code.
> Mechanism: type-level (tier 1) + proof obligation (tier 2). Lint candidate: a
> predicate named `…Correct`/`…Trace…` whose conclusion omits the named
> observable.

> **The gated-shortcut rule — make a side condition an explicit predicate that
> gates the shortcut.** When a proof step is valid only under a side condition,
> encode the condition as a predicate the shortcut *requires*, rather than
> relying on an implicit coincidence. `EmitsNoSigOp ir` gates the value-only
> `pure-refines`: an effectful constructor (a `Cata` whose algebra contains a
> `SigOp`) *fails* the predicate, so the type-checker refuses the shortcut and
> forces the real trace proof. Anti-pattern: "these constructors all happen to
> emit nothing" relied on silently, which breaks the moment a new constructor
> violates it. Mechanism: type-level / structural.

> **The top-down named-postulate rule — state the obligation first, paper gaps
> with *named* postulates, discharge downward.** Never reconnoiter internals to
> decide whether you may state the top — that is middle-out and hides the gap.
> A named postulate keeps the tree green while the structure is locked
> (scaffold-first) and makes "what's still unproven" a grep-able list. It also
> lets the type-checker reveal the *real shape* of each discharge: stating
> `cata-correct : IRObsCorrect (Cata …)` and merely *thinking about* discharging
> `emitted-events` immediately surfaced that the cata's machine must be the
> looping `exec-flat`, not the straight-line `exec-trace` the scaffold had
> inherited — *before* any `flat-events` code was written against the wrong
> machine. The dual of the with-opacity rule: both make the proof *proceed
> through* explicit structure instead of opaque guesses. Mechanism: process +
> proof obligation.

---

## Impact

### Performance

None — this is a meta/process change to how decisions are recorded and checked,
not a runtime change.

### Expressivity

| | Before | After |
|---|--------|-------|
| **Least** | = | = |
| **Most** | = | = |

No language power changes. The gain is *confidence*, not capability.

### Formal Verification

New obligations are *features*, not costs: each encoded decision becomes a
type/theorem/check that **catches design drift**. The value-lift arc shows the
payoff — completeness, as an obligation, repeatedly forced the principled design
and killed wrong abstractions before they shipped. Encoding more decisions
extends that safety net.

---

## Trade-offs

**Gained:**
- A single source of truth (decision state) instead of an implicit chain.
- Decisions the compiler *enforces* — silent drift becomes a type error or
  broken proof.
- A home for non-decision design choices (the view rule, etc.).

**Lost:**
- Upfront effort: walking the 56-entry log, resolving lineage, and choosing +
  building an enforcement mechanism per decision.
- Some decisions resist mechanization; the honest outcome is "documentation-only
  + why," which is weaker than a type.

---

## Alternatives

- **Status quo (prose log).** Rejected: silently violable; the truth is implicit
  in the supersession chain.
- **Decision state only, no encoding.** A real improvement (clarity), but still
  prose — doesn't stop drift. Worth doing as Phase 1 regardless.
- **Encode opportunistically (no decision state).** What happens today — we
  encode a decision when it coincides with an obligation (masquerade grade,
  completeness). Misses everything that doesn't happen to be checked.

---

## Open Questions

- **Building & maintaining `decision-state.md`: manual or tooled?** The initial
  walk of 56 entries is feasible by hand. Keeping it current is the harder part —
  options: a lightweight convention (a machine-readable `Status:`/`Superseded-by:`
  field in the log so the state can be regenerated), a small generator, or a lint
  enforcing the maintenance invariant ("a log diff that changes the in-force set
  must touch `decision-state.md`"). Manual-with-a-lint is likely the cheapest
  start.
- **Encoding taxonomy granularity.** Are four mechanism classes (type / proof /
  lint / docs) the right cut? Where's the line between a proof obligation and a
  structural check?
- **What fraction is mechanizable?** Unknown until the walk. Some decisions are
  inherently judgment calls (naming, ergonomics) and stay documentation-only.
- **Relationship to OCP-0004 (zero-trust verification).** That OCP is about
  *trusting* the verification; this one is about *what* the verification should
  pin. They likely compose.

---

## Discussion

This OCP is an *idea*, not a plan — it sets direction. Once accepted, a plan can
sequence it (start with Phase 1 on the full log, then encode the clearly-typed
decisions first). The value-lift / `gd-complete` work (Plans 0.41/0.42) is the
motivating case study throughout: completeness-as-obligation forced the right
abstraction, and the with-opacity-view pattern is the first non-decision design
choice to catalogue.
