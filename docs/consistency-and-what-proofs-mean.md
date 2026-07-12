# Consistency, Trust, and What a Proof Means

*A foundational note for Once, and an honest ledger of what the OCP-0009
dependent-types POC currently assumes.*

This document has two parts:

1. **Foundations** — what "consistency" means, what a proof *really* means, and
   why some conclusions are foundation-independent while others are not.
2. **Once's ledger** — every feature the OCP-0009 POC has prototyped, and its
   effect on the consistency we are assuming.

The short version: for the theorems Once actually cares about (compiler
correctness, program properties) a proof means essentially the same thing in any
sound system; the design is *very likely* consistent because every construction
is standard and modeled and the known paradox-traps are avoided; and the only
asserted-not-proven risk lives in a handful of documented `TERMINATING` /
positivity pragmas in the mechanization — not in the dependent-types machinery.

---

## Part 1 — Foundations

### 1. Consistency is *the* property

A logical system is **consistent** if it cannot prove both `P` and `¬P`. An
inconsistent system proves *everything* (`P` and `¬P` together derive any `Q`) and
is therefore worthless as a logic. So before "how expressive" or "how convenient,"
the first question about any proof system is: *is it consistent?*

### 2. Two senses of "consistent" — keep them apart

Real-world soundness needs **both** of these, and they are independent:

1. **Is the formal THEORY consistent?** A metamathematical question, answered by
   *model constructions*: exhibit a model, and the model witnesses consistency.
2. **Does the IMPLEMENTATION faithfully check that theory?** A *software*
   question — a kernel bug can accept an ill-typed term and let you prove `False`
   even when the theory is impeccable.

A perfect theory with a buggy checker is unsound; a correct checker for an
inconsistent theory is unsound. Across essentially every proof assistant, the
implementation is the weaker link, and it is **trusted, not verified**.

### 3. Can we prove consistency? Only *relatively* (Gödel's wall)

Gödel's **second incompleteness theorem**: no consistent system strong enough to
express arithmetic can prove **its own** consistency. So no system — Coq, Agda,
Lean, Once — proves `Con(itself)`; any system that did would *thereby* be
inconsistent.

What we *can* do is prove consistency in a **stronger metatheory**:

- `Con(PA)` — Gentzen, via transfinite induction to ε₀.
- `Con(CIC)` (Coq's core) — a set-theoretic model relative to **ZFC + inaccessible
  cardinals** (Werner).
- `Con(MLTT)` / `Con(cubical TT)` — set / cubical-set models.

Consistency proofs therefore always bottom out in a metatheory one *chooses to
trust* — turtles, never an absolute, self-contained proof. The reassurance is
that the metatheory needed for these type theories is modest and well-studied:
breaking it would require an inconsistency in *set theory*.

### 4. What a proof *really* means

A proof is a **derivation in a formal system**; it establishes `P` **relative to
that system's axioms and rules**. Its literal meaning is:

> *P holds in every model of this system* — equivalently, *if you grant these
> axioms (these commitments about what mathematical objects are), then P.*

The axioms encode a *choice of mathematical universe*. That is why the same
sentence can be a theorem in one system and its negation a theorem in another:
they are describing different universes (compare the parallel postulate — true in
Euclidean geometry, false in hyperbolic; both consistent).

### 5. The hard, absolute core — where Once lives

Not everything is relative. **Statements about concrete objects are absolute
across these systems:**

- *Concrete / arithmetic* statements ("17 is prime," "this program halts,"
  "`compile e` run on the machine yields `eval e`") are universally-quantified,
  per-instance-decidable facts. Every one of these systems is **arithmetically
  sound** (has a model ⇒ never proves a false arithmetic statement). Therefore no
  two sound systems can *disagree* on a concrete statement: if one proves `P` and
  another proves `¬P`, then `P` is both true and false — impossible. Sound systems
  may differ on *provability* (incompleteness), **never on the truth** of a
  concrete statement.
- The disagreements (see §6) live entirely in the **structural** layer (the nature
  of equality/types), which does not affect concrete conclusions.

This split is *the* reason a verified compiler means something
foundation-independently:

| Kind of statement | What a proof means |
|---|---|
| **Concrete / computational** (arithmetic, program behaviour, compiler correctness) | ≈ **absolute truth** — provability in any consistent sound system entails genuine truth; no consistent system disproves it. |
| **Abstract / structural** (UIP, univalence, "is equality proof-irrelevant?") | **conditional truth** — holds in *this* mathematical universe; genuinely system-relative. |

Three mechanisms make the top row a *theorem*, not an observation:

- **Soundness** — sound systems cannot contradict on concrete statements (above).
- **Conservativity / interpretability** — e.g. function extensionality is
  *conservative* over MLTT (the setoid / observational model), so it proves no new
  statements in the shared language; and when system A has a model built inside B,
  *all* of A's theorems transfer to B at once. You prove agreement **once**, at the
  meta-level, not case-by-case.
- **Computation is absolute** — a concrete statement's truth is ultimately a fact
  about *running programs* (Church–Turing-robust). A proof is a finite certificate
  that an infinite family of computational checks passes. **Canonicity** (which OTT
  and cubical have, but *postulated-funext* Agda does not) is the internal
  guarantee that a proof of a concrete statement *reduces to* that computation.

### 6. Genuine paradox vs. counterintuitive theorem

Two very different things are called "paradox":

- **Inconsistency — a real paradox.** Russell (naive set theory),
  **Girard (`Type : Type`)**, Reynolds (naive polymorphism + strong sums). A system
  with one of these is *broken*. Here systems are objectively rankable, and
  *avoiding these traps is a hard correctness constraint.*
- **Counterintuitive-but-consistent theorems.** Banach–Tarski (a *theorem* of
  ZFC + Choice), the Continuum Hypothesis (independent of ZFC). These are **not**
  inconsistencies — they are choices of universe. No system is "more correct" for
  them.

Conflating the two is the classic confusion. Only the first kind makes a system
*wrong*.

### 7. Verifying the kernel ≠ making the theory consistent

Verifying the kernel proves *"the kernel faithfully implements theory T."* That is
**worthless if T is inconsistent** — a verified kernel for an inconsistent theory
faithfully lets you prove `False`. Consistency of T is a *separate*, metamathematical
fact (T has a model) that kernel verification does not provide. You need both.

### 8. Larger systems are harder to assure consistent

Two reasons:

1. **Feature interactions.** Consistency does not compose: features that are each
   fine can be *jointly* inconsistent (impredicative `Set` + excluded middle +
   large elimination → inconsistent; sized types interacting with other features
   caused unsoundness in Agda). More features ⇒ more joint conditions to satisfy.
2. **Stronger axioms need stronger metatheories.** To prove consistency you build
   *one* model of *all* features at once; the clean core calculi have tidy models,
   but full implemented systems often lack a complete one. And a stronger axiom
   (e.g. general induction-recursion) raises the **consistency-strength bar** — you
   need a stronger, less-certain metatheory to justify it.

### 9. The trust stack, and Once's bet

Every proof rests on a stack:

1. the theory is consistent (metatheorem, relative — §3);
2. the kernel faithfully checks the theory (usually *trusted*, not verified);
3. the compiler / runtime / hardware are correct (usually just trusted).

Once attacks layer 2 two ways (both on `origin/ocp-0006-once-spec`):

- **A minimal auditable TCB** (the *de Bruijn criterion*): the trusted core is a
  ~212-line human-verified `tcb/scheme.c` + `verifier.scm` that checks reduction
  *traces* against the CCC laws; the powerful normalizer is **untrusted** and merely
  emits certificates the tiny checker validates.
- **Self-verification** (the summit): the aspiration to a *verified* rather than
  merely-trusted core.

The honest limit (Gödel again): self-verification **relocates** trust, it does not
eliminate it — verifying the verifier still needs *some* trusted base. The win is
not "trust nothing"; it is **"shrink the trusted base to something a human can
audit, and make everything above it checkable."**

---

## Part 2 — Once's ledger: POC'd features and their effect on consistency

Everything below is prototyped in Agda under `bootstrap/poc/OCP0009/`. Two
caveats frame the whole ledger:

- These are **POC modules in Agda** — they currently rely on *Agda's* consistency
  story and do **not** change Once's *shipping* kernel (the OCP-0006 core is the
  container/CCC theory *without* the stronger extensions below). So any
  TCB/strength increase here is **prospective** — what Once's core *would* commit
  to *if* it adopted the feature — not yet a change to the real compiler's trusted
  base.
- "Consistency effect" is judged against plain MLTT + inductive types as the
  baseline.

### Feature ledger

| Feature | Modules | Consistency effect | Risk |
|---|---|---|---|
| **Decidable conversion (NbE)** | `NbEK`, `NbEP`, `NbEPNat`, `NbEPRel`, `NbEPFund`, `NbEPNormal`, `NbEPComplete` (+ older `Conv`/`Sound`/`Finite`/`Decidable`/`Open`) | No new logical strength — a normalizer + its adequacy proof. | **The main residual risk lives here**: `eval`/`nf` carry `TERMINATING` pragmas (asserted, not proven; see below). |
| **CwF / dependent layer (Rung 2)** | `NbEPCwF`, `NbEPEl`, `NbEPElOTT` | Standard CwF over a total core; no new strength. Inherits the NbE's `TERMINATING` transitively (via `nf`). | Low (inherits NbE risk). |
| **Identity type `Id` + `J` (Rung 3)** | `NbEPId` | Definitional identity = decided conversion; no new strength. | Low. |
| **QTT (erasure / multiplicities)** | `NbEPQTT`, `NbEPQTTJ` | A *resource discipline* on the type system — **no logical strength added**. | None (semiring + intrinsic judgment; no pragmas). |
| **OTT (observational equality)** | `NbEPOTT`, `NbEPOTTMu`, `NbEPOTTQ`, `NbEPOTTCoind` | Adds funext + proof-irrelevance/**UIP (K)** — consistent with MLTT (setoid model), near-conservative; **incompatible with univalence** (a *choice*, not a risk). | Low. `funext` is taken as an explicit *parameter*, **not postulated** — no axiom introduced. |
| **Indexed inductive families (Rung 4)** | `NbEPIndexed` | Ordinary indexed containers — standard, modeled; no strength beyond MLTT + inductives. | None (strictly positive, no pragma). |
| **Coinduction** | `NbEPCoind`, `NbEPOTTCoind` | Guarded (copattern) coinduction — standard (M-types), consistent. **Deliberately avoids sized types** (the feature behind Agda's unsoundness history). | Low (`--guardedness`, a *safe* flag). |
| **Universe hierarchy `U₀ ⊂ U₁`** | `NbEPUnivH` | *Predicative* stratification — the standard way to **avoid Girard**. Modest per-level strength bump. | Low — a guardrail *against* paradox, not a risk. |
| **Induction-recursion (IR universe)** | `NbEPUniv`, `NbEPUnivDec` | **The one genuine strength increase.** IR is strictly stronger than MLTT (general IR reaches Mahlo-cardinal strength); it raises the consistency-strength bar. **This is where the small-core discipline ends by design.** | Elevated *strength*, but **not** a soundness risk: our instance (a Tarski universe with Π/Σ) is the *motivating, thoroughly-modeled* example of IR, and Agda implements IR as a sound **core** feature (not an unsafe flag). |
| **Summit (verified compiler in-theory)** | `NbEPSummit` | A *use* of the stack, not a new axiom. | None. |

### The escape hatches (what is asserted, not proven)

Being explicit about every place the mechanization *trusts* rather than *proves*:

1. **`TERMINATING` pragmas** on the `eval` / `nf` / `mapCata` recursion
   (`NbEP`, `NbEPComplete`, `NbEPFund`, `NbEPNormal`, `NbEPNat`, `NbEKF`, `NbE`).
   These disable Agda's termination checker for those functions. *If* one did not
   actually terminate, that would be an inconsistency (a non-terminating "total"
   function lets you build a loop and prove `False`). They mirror the structural
   NbE recursion and are discharged *in principle* by the standard SN /
   logical-relation argument — **low risk, but a trusted assertion, not a proof.**
   This is the single most important thing to eventually discharge.
2. **One `NO_POSITIVITY_CHECK`** (the Kripke `⇒` domain in `NbEKF`). Positivity
   violations *can* cause inconsistency; the specific use is a known-safe closure
   pattern, but it is an assumption.
3. **`funext` axiom** — used in the *older* conversion track (`Complete`, `Higher`,
   `Dependent`, `Universe`) as `--safe`-compatible postulate. The *principled* NbE
   and the OTT layer do **not** rely on it (OTT proves funext *definitionally*;
   `NbEPOTT.eq-irrel` takes funext as an explicit parameter rather than postulating
   it).

### `--safe`-verified (machine-checked "uses no unsafe features")

Agda's `--safe` flag *rejects* every unsafe escape hatch — `TERMINATING`,
`NO_POSITIVITY_CHECK`, `type-in-type`, meaning-affecting postulates — and a
`--safe` module may only import `--safe` modules. So a green build under `--safe`
is a **machine-checked certificate** that a module (and its whole import closure)
introduces none of them.

**The entire standalone expressibility tower now compiles under `--safe`** (10
modules, verified 2026-07-12):

| `--safe` | modules |
|---|---|
| IR universe + hierarchy | `NbEPUniv`, `NbEPUnivDec`, `NbEPUnivH` — **confirms induction-recursion is `--safe`-compatible** (a sound core feature, not an unsafe flag) |
| indexed inductive families | `NbEPIndexed` |
| OTT (equality, quotients, μ) | `NbEPOTT`, `NbEPOTTQ`, `NbEPOTTMu` |
| coinduction (guarded) | `NbEPCoind`, `NbEPOTTCoind` (`--safe --guardedness`) |
| verified compiler in-theory | `NbEPSummit` |

What **cannot** yet go `--safe` is *exactly* the set of modules importing the NbE
core (`NbEP`, `NbEPComplete`, …, and hence `NbEPCwF`/`NbEPEl`/`NbEPId`/`NbEPQTT*`),
because that core carries the `TERMINATING` pragmas. So `--safe` now draws the
consistency line **mechanically**: the dependent-types *features* are certified
unsafe-feature-free; the residual risk is confined to the NbE core's termination
assertions, precisely as this ledger claims.

### Verdict

- **The design is very likely consistent.** Every construction is a standard,
  well-studied, *modeled* one (IR is Dybjer–Setzer's motivating example; OTT has
  canonicity results; guarded coinduction, indexed containers, predicative
  hierarchies all have models), and the mechanization systematically **avoids the
  known paradox-traps**: no `type-in-type` (Girard), predicative, strictly positive
  (Reynolds), guarded-not-sized (Agda's sized-types history), total.
- **The one genuine strength increase is induction-recursion** (the IR universe) —
  flagged from the start as "the step that leaves the small-core discipline by
  design." It raises the consistency-strength requirement but is not a soundness
  *risk* in our modest instance.
- **The residual asserted-not-proven risk is the `TERMINATING` / positivity
  pragmas**, not the dependent-types features.

### Path from "very likely" to "machine-checked"

To upgrade the mechanization's own consistency guarantee:

0. **[DONE] Certify the standalone tower with `--safe`** — the 10 modules above
   now build under `--safe`, mechanically proving the dependent-types features use
   no unsafe escape hatches. This isolates the residual risk to the NbE core.
1. **Discharge the `TERMINATING` pragmas** in the NbE core — prove `eval`/`nf`
   terminate via the SN / logical-relation argument (tedious, not deep; the
   argument is standard and already sketched in the NbE adequacy modules). This is
   what would let the *conversion / CwF* track go `--safe` too. (A cheaper partial
   step: split `NbEP`'s pure `Tm` datatype into its own `--safe` module so the
   graded-judgment / elaboration modules that never touch `eval` can go `--safe`
   without waiting for the full termination proof.)
2. **Discharge or defunctionalize the `NO_POSITIVITY_CHECK`** — replace the Kripke
   `⇒` closure with a strictly-positive presentation.
3. **Keep funext out of the load-bearing path** — already true for the principled
   NbE + OTT; the older `funext`-using modules are superseded.
4. **Decide whether Once's *core* adopts IR** — this is a deliberate,
   consistency-strength-raising commitment (§8), and the point where the
   small-core-plus-desugar discipline formally ends. Until then it stays a POC
   demonstration, not a change to the shipping TCB.

---

*See also:* `docs/proposals/OCP-0009-decidable-dependent-types.md` §"Consistency &
the trust story" (the systems-comparison table: Coq / Agda / Idris 2 / Lean /
Once), and §5 of the same proposal for the expressibility comparison.
