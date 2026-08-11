# OCP-0006: `Once.Spec` — One Home for the Language Definition

**Author:** Jonas Claesson
**Status:** DELIVERED (plan 0.58 closed 2026-07-13). `Once.Spec` is the
canonical, load-bearing spec door: `Once.Certified` consumes `CorrectCompiler`
through it; `Spec.Meaning` re-exports the derivation denotation `⟦_⟧ᵈ`
(ValueDomain + Behavior + Meaning + MainMeaning — no `realize`, no `evalᴰ`, no
`Surface.Expr`); `Spec.Syntax` is `RawExpr` only. `Once.IR` remains shared
vocabulary (option a). Follow-on work: plan 0.59 (oracle principality +
coverage); the Phase-2 witness postulate quartet (needs the elaborator
witness restructure). Plan file 0.58 deleted at close per its own P5
instruction — full history in git (branch `ocp-0006-once-spec`).
**Created:** 2026-06-24

---

## Summary

To reason about a Once program you need **two** things: *what you are allowed to
write* (the typing rules) and *what it means* (the denotation). Today these live
apart — the static semantics is buried under the implementation pipeline
(`Once.TypeCheck.Judgment`) and the dynamic semantics is under
`Once.Denotation.*` — with no single door. This OCP proposes a `Once.Spec`
namespace that gathers exactly the artifacts a reader must **trust and read**
(instead of the implementation) to understand the language and believe the
compiler is correct: the type grammar, the surface syntax, the typing judgment,
the denotation, and the top-level correctness statement. It is a **purely
organizational** change (re-homing + re-export), not a semantic one.

---

## Motivation

- **The two faces of the language are split across unrelated namespaces.** A
  programmer asking "can I write `compose f g` with a closure arm?" reads the
  typing rules; asking "what does `exit 13` do?" reads the denotation. The first
  is under `Once.TypeCheck` (an *implementation* package — the elaborator,
  classifier, soundness, completeness all live there too), the second under
  `Once.Denotation`. Nothing says "these two, together, *are* the language."
- **"Spec" is currently implicit.** D057 anchors correctness at a source-level
  reference semantics, and `Once.Adequacy` is already marked *DO NOT EDIT* — but
  there's no enumerated, namespaced **trust boundary**. A reviewer auditing "what
  do I have to believe?" has to know, by lore, which modules are spec and which
  are implementation. (This complements OCP-0005's *decision* state: that pins
  the in-force *decisions*; this pins the in-force *language definition*.)
- **The D063 work made the split concrete.** The morphism realm `⊢ᵐ` is a
  *typing* change (`Once.TypeCheck.Judgment`) whose whole purpose is to let the
  *meaning* (`realize`/`realize-morph` in `Once.Denotation.Realize`) be total and
  forcing. The two are one design, filed in two packages.

---

## Proposal

### What *is* spec (the trust boundary)

Criterion: a module is **spec** iff a reader must read/trust it to know *what
programs are legal* or *what they mean* — i.e. you would read it **instead of**
the implementation, and the compiler is verified *against* it.

| module(s) | role | spec? |
|---|---|---|
| `Once.Type` (+ `Once.Functor.*` type grammar) | the type/functor grammar | **yes** (alphabet) |
| `Once.Surface.Syntax` (`Expr`) | intrinsically-typed term grammar the denotation interprets | **yes** |
| `Once.TypeCheck.Raw` (`RawExpr`) | parsed concrete syntax | **yes** (programmer-facing syntax) |
| **`Once.TypeCheck.Judgment`** (`⊢ᵢ`/`⊢ᶜ`/`⊢ᵍ`/`⊢ᵐ`, `Typed`) | **static semantics** (what's well-typed) | **yes — all of it** |
| `Once.Denotation.SourceDenote` (`SD.⟦_⟧ˢ`) | **dynamic semantics** of surface terms — the source meaning (D057) | **yes** |
| `Once.Denotation.Realize` (`realize`/`realize-morph`) | derivation → meaning bridge (the elaborator-free reference) | **yes** |
| `Once.Adequacy` (`correct`) | the correctness criterion | **yes** (already *DO NOT EDIT*) |

**Answer to "a part of `Once.TypeCheck.Judgment`?"** — it is **entirely** spec:
the file is nothing but declarative typing rules + the `Typed` predicate + a
backward-compat alias. There is no non-spec part. The confusion is only that it
is *namespaced* under the implementation package `Once.TypeCheck`. So the move is
the whole module, not a slice.

### What is *not* spec (stays implementation/verification)

`Once.TypeCheck.Elaborate` (`checkElab`), `Classify`, `Soundness`,
`Completeness`; `Once.Surface.Elaborate` (`elaborate`); the parser; `Once.IR`;
codegen; the abstract machine; all simulation proofs. These are *checked against*
the spec, never trusted in its place.

### Boundary subtleties to settle (the genuinely non-obvious part)

1. **`Once.IR` and `evalᴰ`.** The *source* meaning is `SD.⟦_⟧ˢ` (surface terms) —
   that's the spec per D057. But `Once.Denotation.Realize.realize-morph` produces
   `Once.IR`, and `Once.Denotation.DenotTrace.evalᴰ` is over IR. So the meaning
   currently *touches* the IR (an implementation artifact). Options: (a) treat IR
   as a shared *vocabulary* both spec and impl import (IR is syntax, not
   implementation behaviour) and keep it outside `Once.Spec`; (b) the source
   meaning should be expressible in `SD` alone and IR contact in `realize-morph`
   is an implementation leak to remove. **Recommend (a)** — IR is a pure syntax
   tier (no machine), shared like `Once.Type`; revisit only if the meaning can be
   stated IR-free.
2. **`Raw` vs `Surface.Syntax`.** Both are "the program" at different stages.
   Include both, or only the surface one the denotation reads? Lean: include both
   (the programmer writes `Raw`; the denotation reads `Surface`).

### Proposed layout (re-home + re-export, no logic change)

```
Once.Spec                       -- umbrella; re-exports the language definition
Once.Spec.Type                  -- ← Once.Type
Once.Spec.Syntax                -- ← Once.Surface.Syntax (+ Raw)
Once.Spec.Typing                -- ← Once.TypeCheck.Judgment   (⊢ᵢ/⊢ᶜ/⊢ᵍ/⊢ᵐ)
Once.Spec.Meaning               -- ← Once.Denotation.{SourceDenote,Realize,DenotTrace}
Once.Spec.Correct               -- ← Once.Adequacy
```

Mechanically: move the module (or, lower-risk first cut, create `Once.Spec.*`
that `open … public` re-exports the existing modules), update imports, leave the
implementation packages importing `Once.Spec.*`. Dependency-feasible: `Judgment`
only needs `Classify`/`Surface.Syntax`/`IR`/`Functor.*` — none of which are
`Denotation` or the elaborator, so no cycle.

---

## Impact

### Performance

None — organizational.

### Expressivity

| | Before | After |
|---|--------|-------|
| **Least** | read 2+ packages, know lore | one `Once.Spec` door |
| **Most** | = | = (no new power) |

### Formal Verification

No proof changes. One real *gain*: the trust boundary becomes **enumerable and
namespaced** — "audit `Once.Spec.*`'s imports" is the whole review surface for
"is the meaning free of the compiler?", the same way D063/Realize already asks the
reviewer to audit one import line.

---

## Trade-offs

**Gained:**
- A single, namespaced language definition (legality + meaning) — one place to
  reason about programs.
- An explicit, auditable trust boundary (complements OCP-0005's decision state).

**Lost:**
- A module rename ripples across imports (the `TypeCheck`/`Denotation` consumers).
- Risk of the umbrella drifting if "spec" creeps (mitigate: the criterion above
  is the gate for what may enter `Once.Spec`).

---

## Status / sequencing

The deferral prerequisite (the D063 collapse — replace `t-compose-check`/
`t-case-copair-check` with `⊢ᵐ` arms, re-prove completeness, retire the two false
`*-eff-complete` postulates) **landed** via plans 0.52–0.55.

**Implemented (re-export cut, plan 0.58):** `Once.Spec` + the five leaves
(`Type`/`Syntax`/`Typing`/`Meaning`/`Correct`) exist as `open … public` re-exports
of the trusted spec modules — the enumerable, namespaced trust boundary. Boundary
calls settled: `Once.IR`/`evalᴰ` stay OUTSIDE (option a — shared syntax vocabulary);
`Once.Spec.Syntax` carries both `Raw` and `Surface.Syntax`; `Once.Spec.Correct` is the
`CorrectCompiler` criterion ONLY (proof-free; the instance + its named postulates are
not re-homed).

**Follow-up (not yet done):** make `Once.Spec` *canonical* by rewiring
implementation-package importers onto `Once.Spec.*` (high import churn) — a later plan.

### See Also

- D063 (the `⊢ᵐ` morphism realm — the work that exposed the split), D057
  (source-level reference semantics — why `SD` is the meaning), OCP-0005
  (decision state — the sibling "pin what's in force" idea), `Once.Adequacy`
  (already the *DO NOT EDIT* correctness criterion).
