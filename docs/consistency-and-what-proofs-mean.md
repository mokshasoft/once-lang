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
| **Decidable conversion (NbE)** | `NbEK`, `NbEP`, `NbEPNat`, `NbEPRel`, `NbEPFund`, `NbEPNormal`, `NbEPComplete` (+ older `Conv`/`Sound`/`Finite`/`Decidable`/`Open`) | No new logical strength — a normalizer + its adequacy proof. | ~~`eval`/`nf` carried `TERMINATING` pragmas~~ **discharged 2026-07-13**: the pragmas were unnecessary — Agda's size-change checker accepts the lexicographic (Tm, Val) recursion. The whole principled track is `--safe`. |
| **CwF / dependent layer (Rung 2)** | `NbEPCwF`, `NbEPEl`, `NbEPElOTT` | Standard CwF over a total core; no new strength. | None (`--safe` since 2026-07-13). |
| **Identity type `Id` + `J` (Rung 3)** | `NbEPId` | Definitional identity = decided conversion; no new strength. | Low. |
| **QTT (erasure / multiplicities)** | `NbEPQTT`, `NbEPQTTJ` | A *resource discipline* on the type system — **no logical strength added**. | None (semiring + intrinsic judgment; no pragmas). |
| **OTT (observational equality)** | `NbEPOTT`, `NbEPOTTMu`, `NbEPOTTQ`, `NbEPOTTCoind` | Adds funext + proof-irrelevance/**UIP (K)** — consistent with MLTT (setoid model), near-conservative; **incompatible with univalence** (a *choice*, not a risk). | Low. `funext` is taken as an explicit *parameter*, **not postulated** — no axiom introduced. |
| **Indexed inductive families (Rung 4)** | `NbEPIndexed` | Ordinary indexed containers — standard, modeled; no strength beyond MLTT + inductives. | None (strictly positive, no pragma). |
| **Coinduction** | `NbEPCoind`, `NbEPOTTCoind` | Guarded (copattern) coinduction — standard (M-types), consistent. **Deliberately avoids sized types** (the feature behind Agda's unsoundness history). | Low (`--guardedness`, a *safe* flag). |
| **Universe hierarchy `U₀ ⊂ U₁`** | `NbEPUnivH` | *Predicative* stratification — the standard way to **avoid Girard**. Modest per-level strength bump. | Low — a guardrail *against* paradox, not a risk. |
| **Induction-induction (II)** | `NbEPII` | Like IR, beyond plain MLTT+inductives — but modest: finitary II is constructible from indexed inductives in theory, and Agda implements it as a sound core feature. The example (intrinsic `Ctx`/`Ty`) is the future Spec/Kernel shape. | Low (`--safe`; no escape hatches). |
| **OTT internalized (observational universe)** | `NbEPOTTU` | `` `eq `` as a universe code with computed decoding — no strength beyond the IR universe it lives in; proof irrelevance definitional. | Low (`--safe`). |
| **Universe tower (ℕ-indexed)** | `NbEPUnivT` | Per-level strength bumps, uniformly (universe-operator construction) — the predicative ladder, now at every level. | Low (`--safe`; a guardrail, as with `NbEPUnivH`). |
| **Induction-recursion (IR universe)** | `NbEPUniv`, `NbEPUnivDec` | **The one genuine strength increase.** IR is strictly stronger than MLTT (general IR reaches Mahlo-cardinal strength); it raises the consistency-strength bar. **This is where the small-core discipline ends by design.** | Elevated *strength*, but **not** a soundness risk: our instance (a Tarski universe with Π/Σ) is the *motivating, thoroughly-modeled* example of IR, and Agda implements IR as a sound **core** feature (not an unsafe flag). |
| **Summit (verified compiler in-theory)** | `NbEPSummit` | A *use* of the stack, not a new axiom. | None. |

### The escape hatches (what is asserted, not proven)

Being explicit about every place the mechanization *trusts* rather than *proves*:

1. **[DISCHARGED 2026-07-13] `TERMINATING` pragmas** on the `eval` / `nf` /
   `mapCata` recursion (`NbEP`, `NbEPComplete`, `NbEPFund`, `NbEPNormal`,
   `NbEPNat`, `NbE`, `Complete`). These turned out to be **unnecessary**: removing
   every one of them typechecks. Agda's size-change termination checker accepts
   the mutual block's lexicographic (Tm, Val) descent — every call cycle either
   strictly shrinks the term (`eval → vcata → eval alg`, since `alg` is a subterm
   of `cataT F alg`) or keeps it and strictly shrinks the value
   (`vcata → mapCata → vcata`). The anticipated SN / logical-relation obligation
   never existed for this first-order fragment; the pragmas were conservatism
   from an earlier shape of the code. Termination of the whole NbE core is now
   **machine-checked**, not asserted.
2. **[DISCHARGED 2026-07-13] `NO_POSITIVITY_CHECK`** — the Kripke `⇒` domain in
   `NbEKF` used to be an inductive datatype whose closure field puts `Val`
   negatively. It is now defined by **recursion on the type** (a Tarski-style
   presheaf semantics: `Val A (X ⇒ Y) = ∀ {A'} → A' ≼ A → Val A' X → Val A' Y`
   as a `Set`-valued function), so there is no positivity question at all — and
   `eval` became structurally recursive as a bonus, so `NbEKF` compiles under
   `--safe`. **No positivity escape remains anywhere in the POC.**
3. **`funext` axiom** — postulated in the *older* conversion track (`Complete`,
   and transitively `Sound`/`Finite`/`Decidable`/`Open`/`Higher`/`Dependent`/
   `Universe`/`Transparency`). The *principled* NbE and the OTT layer do **not**
   rely on it (OTT proves funext *definitionally*; `NbEPOTT.eq-irrel` takes
   funext as an explicit parameter rather than postulating it). **As of
   2026-07-13 this is the ONLY escape hatch left anywhere in the POC**, and it
   is confined to the superseded track.

### `--safe`-verified (machine-checked "uses no unsafe features")

Agda's `--safe` flag *rejects* every unsafe escape hatch — `TERMINATING`,
`NO_POSITIVITY_CHECK`, `type-in-type`, meaning-affecting postulates — and a
`--safe` module may only import `--safe` modules. So a green build under `--safe`
is a **machine-checked certificate** that a module (and its whole import closure)
introduces none of them.

**81 of the 90 modules now compile under `--safe`** (verified 2026-07-16): the
standalone expressibility tower (10 modules, 2026-07-12), the QTT stack (step 1,
2026-07-12), the presheaf/Kripke NbE foundation (step 2, 2026-07-13), and —
after the `TERMINATING` pragmas proved unnecessary (step 3, 2026-07-13) — the
**entire principled NbE core, its adequacy proofs, and the whole dependent-types
track on top of it**:

| `--safe` | modules |
|---|---|
| NbE core + adequacy | `NbEK`, `NbEKF`, `NbEP`, `NbEPF` (one engine, full `{Unit,×,+,μ,⇒}` fragment), `NbEPTm`, `NbEPNat`, `NbEPRel`, `NbEPFund`, `NbEPNormal`, `NbEPComplete` (+ prototype `NbE`, `NbEConv`) |
| CwF / dependent layer + `Id`+`J` | `NbEPCwF`, `NbEPEl`, `NbEPId`, `NbEPElOTT` |
| QTT (syntax, semiring, judgment, erasure) | `NbEPQTT`, `NbEPQTTJ`, `NbEPQTTErase`, `NbEPQTTEraseTm` (erasing term elaboration) |
| OTT (equality, quotients, μ) | `NbEPOTT`, `NbEPOTTQ`, `NbEPOTTMu` |
| IR universe + hierarchy + ℕ-tower | `NbEPUniv`, `NbEPUnivDec`, `NbEPUnivH`, `NbEPUnivT` — **confirms induction-recursion is `--safe`-compatible** (a sound core feature, not an unsafe flag) |
| induction-induction | `NbEPII` (intrinsic `Ctx`/`Ty` + standard model) |
| OTT internalized | `NbEPOTTU` (observational universe; `n+0=n` by induction, internally), `NbEPOTTH` (heterogeneous `EQ`/`EQU`/`coe`/`coh` + dependent `Σ` transport) |
| indexed inductive families | `NbEPIndexed` |
| coinduction (guarded) | `NbEPCoind`, `NbEPOTTCoind` (`--safe --guardedness`) |
| verified compiler in-theory | `NbEPSummit` |
| positive-η surface sugar | `NbEPEta` (sum-η/μ-η as explicit model proofs) |
| directed rungs 0–2b.1 | `NbEPDir` (rewrite system as a proven Hom-category), `NbEPDirU` (`Hom` as a universe code), `NbEPDirJ` (directed J, `sym` refuted), `NbEPMon` (monoidal core: no-diagonal/no-discard/no-undo proven), `NbEPMonC` (sound decidable conversion for the free SMC) |
| SMC coherence completeness (2026-07-14) | `NbEPMonN` (type normalization), `NbEPMonP` (permutation realizations + agreement), `NbEPMonA` (Perm algebra), `NbEPMonU` (representation uniqueness), `NbEPMonR`/`NbEPMonY` (swapHead toolkit, **Yang–Baxter**), `NbEPMonI`/`NbEPMonQ` (algebra realized), `NbEPMonG`/`NbEPMonK`/`NbEPMonS`/`NbEPMonH`/`NbEPMonZ` (generator squares: Kelly unit lemmas, mirror hexagon, `nt-σ`), `NbEPMonE` (**completeness: `dec≈ : ∀ f g → Dec (f ≈m g)` — the linear core's equality is a decision procedure, a theorem of `--safe` Agda**), `NbEPMonD` (the hybrid kernel skeleton: conversion by normalization as an object-language type, closed instances checked by `refl`; the structural fragment proven a groupoid), `NbEPMonL` (the `⊸` expedition's stage L0: SMCC syntax + theory, the derivation-level bridge from the decided fragment, Set-model with β⊸/η⊸ by `refl`), `NbEPMonV` (stage L1: the signed-balance invariant — linearity survives closure; duplication, discard, and the K combinator all refuted in the closed core), `NbEPMonX` (stage L2a: extensional soundness — the logical-relations PER, the fundamental lemma, and the refutation oracle for the closed theory), `NbEPMonT` (stage L3.0: the linear-NbE world category — list worlds, element-generic permutation algebra, Day-tensor functoriality and symmetry), `NbEPMonW` (stage L3.1a: worlds realized back into syntax), `NbEPMonM` (stage L3.1b: **linear NbE** — the Day-convolution model, pending-permutation neutrals; β⊸/η⊸/structural/higher-order equalities decided by normalization, checked by `refl`), `NbEPMonB` (stage L3.2: the residualizing split monad — pair-returning neutrals; let-splits as composition; the frontier demo by `refl`), `NbEPMonJ` (stage L3.3: units crossed — **a total normalizer `NF` for the free SMCC**; what remains of the unit problem is exactly canonicity of node-emission order, the proof-net layer), `NbEPMonF` (stage L3.4a part 1: placement canonicity — the hoisting normalizer; the placement-variance equality decided, stability `NF (NF f) ≡ NF f` demonstrated), `NbEPMonO` (consolidation: pentagon/triangle/hexagon/Yang–Baxter re-derived from `complete` in one line each — the axioms are redundant given the decision procedure; the trust surface is `wire`/`≈m-sound`/`complete`), `NbEPMonIndex` (the one-stop `--safe` entry point for the whole tower) |
| decidability scaffolding | `Conv` |

The 9 modules that **cannot** go `--safe` are exactly the *superseded older
conversion track* — `Complete` (which postulates `funext`) and its importers
`Sound`, `Finite`, `Decidable`, `Open`, `Higher`, `Dependent`, `Universe`,
`Transparency`. Nothing on the principled path depends on them. So `--safe` now
draws the consistency line **mechanically**: everything load-bearing is
certified escape-hatch-free; the one remaining trusted assertion (`funext`) is
confined to legacy modules kept for the historical record.

### The consistency ladder (`NbEPCon0/1/2`, added 2026-07-13)

Gödel II says no sufficiently expressive system proves its own `Con` — but each
rung's `Con` can be a theorem *one level up*. The POC now demonstrates this
ladder explicitly, all `--safe` (so each is a theorem of Agda):

- **`NbEPCon0`** — rung 0 (CCC IR + fragment `Tm`): `¬ Term Unit Void`,
  `¬ Tm Unit Void`, and model-separation of `inl`/`inr`. These rungs are *below*
  the Gödel threshold (no internal propositions), so their consistency is
  provable outright — one-liners through the `--safe` Set-model.
- **`NbEPCon1`** — rung 1 (graded QTT calculus): `∀ ρ → ¬ (∅ ⊢[ρ] ι)` — the
  free calculus proves nothing about an abstract base type (elaborate `ι ↦ Void`,
  evaluate). Still sub-Gödel: grading is a resource discipline, not strength.
- **`NbEPCon2`** — the universe rungs: (A) the first-order `Code` universe
  cannot even *express* falsity (every code decodes to an inhabited type) — the
  expressibility/Gödel trade-off made concrete; (B) **the internal ladder**: the
  statement `` `Con₀ `` = "no uniform inhabitant of all small types" is a
  *`U₁`-code* — expressible only one level up (there is deliberately no
  `` `U₀ : U₀ ``) — and is proven at level 1 (`con₀ f = f `⊥₀`). Each level can
  state and prove the non-degeneracy of the level below; none can for itself.
- **`NbEPUnivT`** — the ladder made UNIFORM: with the full ℕ-indexed tower,
  `` `Con n `` is stated and proven at level `n+1` for every `n` as ONE
  ℕ-indexed theorem (`con : ∀ n → El (suc n) (`Con n)`) — a theorem in the
  level, not a per-level schema.
- **The top** — `Con(full tower)` is a theorem of Agda `--safe` (every model in
  this POC *is* such a proof) and — per Gödel — of nothing weaker. See §"Path
  from very likely to machine-checked" and plan §8 for the Once-in-Once moral:
  "Once+" is the same tower one universe level up, not a different language.

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
- **[UPDATE 2026-07-13] The `TERMINATING` / positivity pragmas are gone.** The
  positivity escape was discharged by a type-recursive Kripke domain, and the
  termination pragmas turned out to be unnecessary (Agda proves the descent
  itself). The only asserted-not-proven artifact left is the `funext` postulate
  in the superseded older conversion track; **everything load-bearing is
  `--safe`**.

### Path from "very likely" to "machine-checked"

To upgrade the mechanization's own consistency guarantee:

0. **[DONE] Certify the standalone tower with `--safe`** — the 10 modules above
   now build under `--safe`, mechanically proving the dependent-types features use
   no unsafe escape hatches. This isolates the residual risk to the NbE core.
1. **[DONE 2026-07-13] Discharge the `TERMINATING` pragmas** in the NbE core —
   this dissolved rather than being proven: removing every pragma typechecks, as
   Agda's size-change checker accepts the lexicographic (Tm, Val) recursion.
   The anticipated SN / logical-relation obligation does not arise for this
   first-order fragment. The conversion / CwF / `Id` / QTT-erasure track is now
   `--safe`. (The step-1 partial — splitting `Tm` into `--safe` `NbEPTm` — had
   already landed 2026-07-12.)
2. **[DONE 2026-07-13] Discharge the `NO_POSITIVITY_CHECK`** — the Kripke `⇒`
   domain in `NbEKF` is now defined by recursion on the type instead of as an
   inductive datatype; both of `NbEKF`'s pragmas fell away and it compiles under
   `--safe` (see the escape-hatch list above).
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
