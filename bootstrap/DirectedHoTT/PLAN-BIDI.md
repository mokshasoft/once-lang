# PLAN · DECIDABLE TYPE CHECKING — an annotated core, a bidirectional surface

★ Decided 2026-09-25. The goal is OCP-0009's title claim, *decidable
dependent types*, stated so that it holds of the KERNEL, not only of a
front end.

---

## 0. The criterion

Once aims at a **provable, self-hosting compiler**. That is the de Bruijn
criterion: a small, independent checker must be able to re-verify **any
kernel term** without trusting whatever produced it. Hence:

> **A kernel term, in its context, determines its type up to conversion.**
> Type checking the core is a total, syntax-directed `infer`; bidirectional
> checking belongs to the ELABORATOR that produces core terms.

That is the Coq and Lean kernel architecture. Agda's core does not meet
it (unannotated λ, motive-free eliminators), and Agda has no independent
kernel checker because of it.

## 1. ★ DECISION 1 — motives, and binder annotations, live IN THE TERM (1b)

Today `natrec`, `elim` and `ielim` keep their motive **only in the
derivation** (the `⊢lam` pattern), and `lam`/`pair` carry no domain or
family. No algorithm can type such a term without guessing the motive,
which is higher-order unification.

| option | verdict |
|---|---|
| 1a · annotated SURFACE syntax erasing to today's `RTm` | ⛔ fails §0: the kernel's own terms stay uncheckable; decidability would be a property of the front end only. Right for a SURFACE, wrong for a CORE. |
| 1b · **types in terms** — `natrec M z s n`, `lam A t`, … | ✅ **CHOSEN** |
| 1c · CODE motives — `natrec d z s n`, result `El (d[n])` | ⚠ forbids LARGE elimination: a motive landing in `U` needs a code for `U`, which does not exist. The restriction is an accident of the current single universe, not a principle. **With a universe hierarchy 1c COINCIDES with 1b** (every type is `El` of a code at some level) — so it is 1b at a fixed level, not an alternative. |

⛔ **Rejected reasons, recorded so they are not reused:** "1a leaves the
kernel untouched" (edit cost is recoverable; a formulation that fails the
criterion is not — `principledness-over-edit-cost`), and "count which
motives the examples USE" (that measures what we wrote, not what we should
support).

★ **The full consequence.** A bidirectional checker over a motive-annotated
core still cannot INFER a β-redex `app (lam t) u` — the domain is not in
the term. §0 requires every core term to check, redexes included, so the
end state is a FULLY annotated core:

| former | annotation it gains |
|---|---|
| `lam` | domain `A` |
| `pair` | family `B` |
| `natrec` | motive `M : RTy (Γ ∙)` |
| `elim` | motive `M : RTy (Γ ∙)` |
| `ielim` | two-slot motive `M` |
| `tr`, `jsub`, `ap`, `absurd`, `hrefl`, `idrefl` | already carry codes — **check each for what the RULE still takes from the derivation** (e.g. `⊢tr`'s `A`, `t`, `u`; `⊢jsub`'s `A`) |

⚠ **The expected structural cost** — the thing the spike measures. Today
`_⟶_` never reduces inside a TYPE (`⌜IMu⌝`'s `RTy ε` is closed and inert).
A motive in a term makes `_⟶_` and `_⟶ᵀ_` **mutual**: the principled
conversion compares annotations up to conversion (Coq does), so a term
needs a `ξ` rule into its annotation. Confluence, subject reduction and
the logical relation all grow a type-in-term case.

## 2. ★ DECISION 2 — a global SIGNATURE of definitions (2b)

Library lemmas (`⊢symN`, `KnotWf`, …) are proved once and reused.

| option | verdict |
|---|---|
| 2a · trusted-derivation leaves in a surface syntax | ⛔ a POC device with no counterpart in a real Once; teaches nothing transferable |
| 2b · **constants with declared types, δ-unfolding** | ✅ **CHOSEN** |
| 2c · re-check everything (a library is macro expansion) | principled only as "smallest kernel"; nested definitions grow terms exponentially |

★ **Caching IS 2b in disguise.** A cache keyed on the TERM needs term
equality to look anything up — as costly as encoding the term — and Agda
does not memoise, so the cache is explicit threaded data. A NAME is the
cheap key; the declared type is the cached result.

★★ **What makes 2b principled rather than convenient: it is CONSERVATIVE
over 2c.** δ-expanding every constant translates a 2b derivation into a 2c
one, so 2b proves exactly what 2c proves while checking each definition
once. That is a theorem to state and prove (δ-elimination), not an
assumption. Opacity (`abstract`-style constants that do not δ-unfold) is
the follow-on question.

### 2-bis. ★ DECISION 2 REFINED (2026-10-02): definitions extend the THEORY — a global signature Σ

Three candidates were weighed by the mathematics. The compiler's core (branch
`plan-0.91-program-facts`, `formal/Once/Spec/Core`) was read as evidence, not
as the answer: neither line is the truth.

- **What a definition is.** Extending a theory by `c := e : A` is an
  EXTENSION BY DEFINITIONS. It is conservative and eliminable: a model of
  `T + (c := e)` is a model of `T` with `c` forced to `⟦e⟧`, so every model
  extends uniquely. Locally, in a CwF, the context `Γ, x := e` is isomorphic
  to `Γ` via the substitution `x ↦ e`, and δ is that isomorphism acting on
  syntax.
- **(i) Constants only in the annotated layer, erased by inlining.** ⛔ Not a
  theory of definitions: they never exist in the theory, so the checker
  reasons about expanded terms. It is 2c with names on top; "check once" is
  lost exactly in conversion.
- **(iii) Definitions as context entries `Γ, x : A := e`.** A different, more
  general feature: LOCAL definitions (`let`, ζ). Reduction becomes
  context-dependent (`Γ ⊢ x ⟶ e`), so confluence, SR, the logical relation
  and SN must carry contexts through reduction. The kernel's reduction is
  context-free today. Not needed for S5; it can be added later on top of
  (ii).
- **(ii) A global signature Σ of CLOSED definitions.** ✅ CHOSEN. This is
  extension by definitions exactly, not an approximation of (iii).
  - Each entry `d : A = e` is typed in its PREFIX (acyclic).
  - `ref d` is typed from the declared type alone; `ref d ⟶ body d` (δ).
  - The bodies are closed, so δ is CONTEXT-FREE: Σ is a fixed parameter of
    the metatheory, and the existing proofs extend by one more reduction
    rule rather than a re-architecture.
  - Conservativity (δ-elimination) is substitution of closed terms, by
    induction on the telescope.

**Where dHoTT and the compiler differ, and which side should move:**

- The compiler's `ref d τ` carries a `GSub` instantiating prenex type
  variables, because its non-dependent core has no type abstraction in terms.
  In a dependent kernel polymorphism is `Π` over `U`, so a CLOSED `ref d`
  applied to codes is the principled form. When the compiler's core gains
  dependent formers, its `∀`-schemas become `Π`-types: the compiler moves.
- The compiler gives `ref` meaning through an environment, with no δ. That is
  right for a non-dependent core, where types never compute. A dependent
  kernel needs δ in conversion. Not a disagreement.
- Prefix-typed, acyclic telescopes: both, for the same reason
  (well-foundedness of δ).

**How the metatheory is obtained: ROUTE B (user, 2026-10-02).** This is a
second axis, independent of (ii)/(iii):

| | definitions PRIMITIVE (the metatheory re-proved with them) | definitions ELIMINATED (justified by unfolding) |
|---|---|---|
| (ii) global, closed | route A | ✅ **route B** — unfolding needs only weakening |
| (iii) in the context | heaviest | via substitution |

- Route B's main theorem IS the meaning of (ii). Extension by definitions
  means "eliminable": δ-expansion maps every derivation to a
  signature-free one. The kernel's metatheory (SN, LR, confluence,
  canonicity) is reused, not reopened.
- **B2: `ref` lives only in the ANNOTATED layer.** The kernel `RTm` is
  unchanged. Erasure unfolds `ref d` to its closed body, and conversion in
  `⊢ᴬ` is already on erasures (decision (c)), so δ is in conversion for
  free.
  - This is not (i): `ref d` is typed by its DECLARATION alone and each
    body is checked once, in its prefix. Only conversion sees bodies.
  - The relation is the same as lazy-δ conversion, by the conservativity
    theorem. Lazy δ inside the checker is an S7-efficiency increment,
    not a correctness one.
- ⚠ Route A is what OPAQUE definitions (no δ) would need, since there
  unfolding changes conversion. That would be an increment on top of B.
- User: *"if we find that the Knot can be heavily simplified by adding
  more increments, then we do that."*

## 3. Stages

| # | stage | state |
|---|---|---|
| S0 | `Algorithm/DecEq` (`Dec` equality, all sorts); `Algorithm/DecideConversionTyped` (term conversion, no parameters); `Algorithm/Check` slice 1 (certifying bidirectional checker, Π/Σ/U/El/Nat/Unit/Hom/Id) | ✅ `e4135b26` |
| S1 | SPIKE `natrecᴹ` inside `RTm` (branch `ocp-0009-spike-natrecM`) | ✅ done — superseded by §3c/§3d; it showed (a) needs a mutual SN theorem to be decided |
| S2 | The annotated layer (§3d): `Spec/Annotated` (`ATm`/`ATy`, ren/sub, erasure + commutation), `⊢ᴬ`, erasure-soundness | ✅ `70a8c1b2e`. Ported to the levitated kernel in PLAN-LEVITATION Stage F: `Spec/AnnotatedDesc`, and `Spec/TypingA` via `tools/genA.py` |
| S3 | The checker for `⊢ᴬ` (`Algorithm/CheckA`): certifying, STRUCTURAL (every former infers — no fuel); the term's own annotations checked with `⊢ᴬ`, all type reasoning on ERASURES (`validity`, `normTy`, `decConvᵀ`), annotated views of inferred types LIFTED from erased normal forms. Then COMPLETENESS (uniqueness of types up to conversion) | ✅ **2026-10-02: `⊢ᴬ` is DECIDABLE** (§3a). `inferᴬ`/`checkᴬ`/`checkTyᴬ` return `Dec`, certifying both the YES and the NO, for every former. |
| S4 | Decide TYPE conversion `≅ᵀ` completely — ROUTE C (§3b): ① validity + `srᵀ` (`Metatheory/Validity`) ✅; ② inversion — the existing `gen-*` sufficed ✅; ③ `normTy`/`decConvᵀ` (`Metatheory/NormTy`) ✅ — **structural, NO measure needed**: `homNF` recurses on the NORMAL ambient (`G` ⊂ `Π F G`), the created `app f↑ vz` go through the typed `wnorm`, and a `NoU` witness breaks the harmless `elNF ↔ homNF` cycle | ✅ |
| S5 | The signature: constants, δ, and the conservativity theorem — design (ii), §2-bis, route B | ✅ **2026-10-02** (§3e): `ref d` in the annotated layer, `⊢ᴬref`, δ by erasure; δ-elimination + conservativity (`Metatheory/Signature`); `CheckA` decides `ref` |
| S6 | The bidirectional SURFACE → annotated core elaborator | ✅ **2026-10-02** (§3f): `Algorithm/Surface` (generated: the annotated syntax + holes) and `Algorithm/Elab` (UNTRUSTED; re-checked by `CheckA`) |
| S7 | The Knot WRITTEN in the annotated core with signature references; its wf derivations come from `inferᴬ`, not from a generator. User, 2026-10-02: "if we have to write code to generate the Knot something is wrong". Measure against `HANDOFF-2026-09-24` §4's split | 🟡 **in progress** (§3g): machinery ✅, slice 1 (the closed core) ✅; next is the certified fast evaluator (S7a) |

## 3g. ★ S7 — THE KNOT IN THE CORE (in progress, 2026-10-02)

**Machinery (done):**
- `Algorithm/SigBuild` (n surface entries) gives `S` and `wfSig : R (WfSig S)`
  in two passes.
  - ELABORATE (untrusted) entry n over `sigAt n`, built by structural
    recursion.
  - CHECK (trusted) the result with `CheckA` over `prefix S n`, plus an
    erasure comparison (`_≟Tm_`).
  - No lemma relates the two passes. On concrete entries
    `wf = fromJust wfSig _`: nobody writes a derivation.
- `Algorithm/Surface` adds:
  - `holesTy`/`holesTm`: a kernel term with every annotation a hole, for
    terms the Lib computes;
  - `renTmˢ`/`subTmˢ`, generated.
- `Algorithm/Result`: the elaborator's failures carry a path and a reason.
  Read one off a type error with `why … ≡ "ok"`.
- Elaborator rules added for β-redexes `app (lam □ t) u`: the domain comes
  from the argument, and in checking mode the body is checked at the
  constant family. A `DIh`'s index code comes from its payload's `dpay`.

**Probes (measured):**
- `KD` (51 constructors, as computed by `SD KSig`) is re-derived by
  elaboration + `CheckA` from holes in about 10 s. This is the whole of
  `⊢KD`.
- ⛔ Big terms with their sub-definitions INLINED do not scale. `FIBM`,
  and even `MethTy (SI 2) KD FM`, run out of memory (5.5 GB cap, 215 s):
  `KD` is re-elaborated at every occurrence, and Agda's evaluation does
  not share the work.
- ⇒ **Every Knot definition is its own ENTRY, and a use is `ref d`.** This
  is "abstract the substituted terms" and "a variable is the cheapest
  position" again. Where the Lib computes a body, it computes it with
  VARIABLES for the earlier entries, and `subTmˢ` turns them into `ref`s.
  `Knot/Core`'s `CtxDᵛ` is the template.
- `⌜Ty⌝` is OPAQUE in today's Knot precisely so that two syntactic forms
  never compare it by normalisation. **A `ref` is exactly that discipline,
  built into the kernel:** a name, unfolded only on demand.

**Slice 1 (done), `Examples/Knot/Core`**, written by hand: `KD`, `Ty`,
`CtxD`, `Ctx`, `CT`, `JT`.
- `wf = fromJust wfSig _` checks in **56 s, 1.3 GB**.
- It replaces `⊢KD`, `⊢⌜Ty⌝`, `⊢CtxD`, `⊢CT`, `⊢JT` and every
  `-sub`/`-ren` lemma of these entries (`subTmᴬ σ (ref d) = ref d` by
  definition).

**S7a — next: the certified FAST evaluator.**
- `agda-profile.sh` on `Knot/Core` counts 25.2 M unfoldings, almost all
  of it the checker evaluating PROOFS:
  - `renTm` 3.9 M, `extS` 3.7 M, `cong` 3.4 M, `extS-cong` 3.0 M,
    `subTm-cong` 2.5 M;
  - the logical relation (`relTy`, `⊩ˢ-ext`, `_,ₛ_` 1.5 M);
  - `church-rosserᵀ`.
- **Causes:**
  - `nfOf`/`decTo` with-match on `validity (erase d)`, forcing the
    derivation and every cast's equality proof;
  - `normTy`/`decConvᵀ` normalise THROUGH the SN proof.
- **The fix** is a certified fast path, PLAN-NF Phase 1:
  - a fuel-bounded evaluator over ALL of `_⟶_`/`_⟶ᵀ_` that returns the
    normal form WITH its chain (`Lib/Eval`'s design, which today covers
    only β/fst/snd);
  - `decTo`/`viewΠ`/`viewΣ` try it first. A "yes" is certified by the
    chains, with no derivation and no validity.
  - The complete procedure runs only when the fast path fails, so
    completeness is unchanged.
- That is the increment the Knot needs before its ~1000 schema entries
  (user, 2026-10-02: add increments when they simplify the Knot).

**Then, the migration recipe** (each step is one family):
- a schema becomes a CLOSED λ-entry; an instance becomes
  `app (ref d) args`;
- the kernel-level derivations still consumed downstream come from
  δ-elimination plus subject reduction: one generic `⊢inst` replaces each
  `okT…`/`⊢k…`;
- the *Agree modules stay at kernel level, on erasures.

## 3f. ★ S6 — THE ELABORATOR (done 2026-10-02)

- **Untrusted, by the de Bruijn criterion.** `Algorithm/Elab` only
  PROPOSES an annotated term. `Checked.elaborate` re-checks it with
  `CheckA` and returns CheckA's derivation. No elaborator proof is
  needed: a bug can make a term fail, never produce a false derivation.
  `Algorithm/Check` (slice 1, fuel, `RTm`) is superseded as the seed. The
  compiler's elaborator is non-dependent (combinator translation) and was
  not a usable template.
- **The surface syntax** (`Algorithm/Surface`) is generated by `genA.py`
  from the same field table as `ATm`/`ATy`. It is the annotated syntax
  plus holes `□ᵀ`/`□` and ascription `the A t`. The two cannot drift.
- **One bidirectional function**, `el Γ t (just T | nothing)`. A hole in
  an annotation position is filled from:
  - the expected type: `lam`, `pair`, `con`, `dι`/`dσ`/`dρ`, `fsuc`;
  - a premise's inferred type: `tr`/`jsub`/`ap` from the path,
    `ielim`/`dih` from the scrutinee or description, `psplit` from the
    pair, `fcase` from the `Fin`;
  - for a MOTIVE in checking mode, the CONSTANT motive. Dependent motives
    are written out.
  - A `pair` with no family falls back to the non-dependent one.
- **Types stay annotated.** Filling a hole needs an annotated type, so the
  elaborator has its own fuel-bounded weak-head evaluator on `ATm`/`ATy`:
  β, projections, `natrec`, δ through the signature's annotated bodies
  (a HINT parameter), and `El` of a code. It never goes through erasure.
- **`Examples/Elab`**, over Σ₃, all by evaluation in 4 s:
  - `lam □ᵀ (nsuc v₀)`;
  - doubling by `natrec □ᵀ` at the constant motive;
  - `pair □ᵀ □ᵀ`, `fsuc` at its bound;
  - `app (ref 0) (ref 2)` via δ;
  - `app (ref 0) unit` rejected.

## 3e. ★ S5 — THE SIGNATURE (done 2026-10-02)

- **`Spec/Signature`**: `record Sig` with fields `size`, `type : ℕ → ATy ε`
  (the declarations), and `body : ℕ → RTm ε` (the bodies, ERASED). Also
  `d <ˢ n` (an entry), `prefix S d`, and `SigOK S` (each erased body has
  its erased type in `◇`).
- **`Spec/Annotated`** (`genA.py`):
  - `ref : ℕ → ATm Γ`; renaming and substitution leave it alone.
  - Erasure is parameterised by the bodies, `module Era (δ : ℕ → RTm ε)`,
    with `⌈ ref d ⌉ = εwkTm (δ d)`. The commutation lemmas get one clause
    each (`εwkTm-ren`/`εwkTm-sub`).
- **`Spec/TypingA (S : Sig)`**: one judgment for every signature.
  `⊢ᴬref : d <ˢ size → Γ ⊢ᴬ ref d ∷ εwkTyᴬ (type d)`. `⊢ᴬconv` on
  erasures now includes δ.
- **`Metatheory/Erasure (S) (ok : SigOK S)`** is δ-ELIMINATION. Its new
  case is the body, weakened by `sub-lemma` from `◇`.
- **`Metatheory/Signature`**:
  - `WfSig`: each entry has an annotated body typed over its PREFIX that
    erases to `body d`.
  - `wf→ok` by induction on the entries: each one is erased by `Erasure`
    over its prefix.
  - `consistencyˢ`: CONSERVATIVITY. Every kernel theorem holds over every
    well-formed signature.
- **`GenerationA`, `UniquenessA`, `CheckA`** are parameterised by `S` and
  each gains one `ref` clause. `CheckA` decides `d <ˢ size`, and its "no"
  is certified by `genᴬ-ref`.
- **`Examples/Signature`**:
  - A 3-entry signature: `suc′`, `N := ⌜Nat⌝`, `one : El (ref 1)`.
  - δ works inside TYPES (`zero∷N`).
  - The checker decides `app (ref 0) (ref 2) ∷ Nat` and rejects `ref 3`,
    both by evaluation in 4 s.
- ⚠ **Side effect:** erasure is no longer constructor-headed (`ref`
  erases to a body), so Agda stops inverting `⌈ _I ⌉ = ⌈ I ⌉`. Five
  helper calls (`motCtx-era`, `motCtx-wf`, `wfDF`, `wfFib`) now pin
  `I`/`D`/`i` explicitly (memory `unsolved-meta-means-missing-pin`).

## 3a. ★ S3 — COMPLETENESS: `⊢ᴬ` is DECIDABLE (plan, 2026-10-02)

The criterion (§0) is that a kernel term determines its type. `CheckA` is
CERTIFYING: a success returns the derivation, so soundness holds by
construction. Completeness is made certifying the same way, by changing
the result types:

    inferᴬ   : … → Dec (Σ A. Γ ⊢ᴬ t ∷ A)
    checkᴬ   : … → Dec (Γ ⊢ᴬ t ∷ A)
    checkTyᴬ : … → Dec (Γ ⊢tyᴬ A)

A separate theorem about the `Maybe`-returning `inferᴬ` is rejected: it
would mean reasoning about `with`-abstractions over `validity`/`normTy` on
abstract terms.

Where a "no" comes from today, and what refutes it:

| failing branch | refutation |
| --- | --- |
| a sub-check fails | GENERATION: a typing of the whole gives a typing of the part |
| `convTo`: `decConvᵀ` says no | UNIQUENESS of types up to conversion |
| `viewΠ`/`viewΣ`/`viewId` find no Π/Σ/Id | a NORMAL form convertible to Π IS a Π |
| `isFalse`/`isTrue`/`noNatC?` | already exact; `noNatC?` returns `Dec` |
| `tr` at another motive | generation: `⊢ᴬ` has exactly two `tr` rules (`⊢ᴬtrU`, `⊢ᴬtr`) |

Steps:

- **C1 — generation for `⊢ᴬ`** (`Metatheory/GenerationA`). There is one
  lemma per former, with two clauses: the rule, and `⊢ᴬconv`, which
  recurses and composes the conversion. ⊢ᴬconv is the only rule that is
  not syntax-directed, and `⊢tyᴬ` has none, so `⊢tyᴬ` needs no lemma.
  - A single `strip` lemma was considered and rejected: after a catch-all
    clause Agda cannot know that the remaining derivation is not a
    conversion, so each former would still owe that case.
- **C2 — normal forms keep their shape.** `nfOf` keeps `normTy`'s
  `IsNormalᵀ`. A normal `N ≅ᵀ Π A B` is literally a `Π` (by
  `church-rosserᵀ`: a normal form reduces only to itself), and likewise
  for Σ and Id.
- **C3 — uniqueness**, `uniqᴬ : Γ ⊢ᴬ t ∷ A → Γ ⊢ᴬ t ∷ B → ⌈A⌉ ≅ᵀ ⌈B⌉`, by
  induction on `t` through C1.
  - Most formers: the type is computed from the annotations.
  - `var`: lookup is deterministic.
  - `app`: `Π-inj` + `≅ᵀ-sub`. `fst`/`snd`: `Σ-inj`. All exist.
  - `Hom` never needs injectivity, which it lacks, because `jsub`/`tr`/`ap`
    carry their endpoints (the §1 audit).
- **C4 — the checker returns `Dec`.**
  - One combinator, `bindᴰ : Dec A → (B → A) → (A → Dec B) → Dec B`; its
    middle argument is C1's projection.
  - `convTo` uses C3, and the views use C2.
  - The non-vacuity tests' rejections become `no` proofs.
  - By former group: Π/Σ/Nat/Unit, then paths, then the levitated
    formers. Watch `CheckA`'s compile time (≈ 6 s cold).

Scope: this decides `⊢ᴬ`, the trusted judgement, not plain `⊢`; `⊢` is its
meaning (§0, §3d).

### 3a — log

- ✅ **C1** (2026-10-02) `Metatheory/GenerationA`: 40 generation lemmas
  `genᴬ-*`, one per former and two clauses each; `tr`'s two rules
  (`genᴬ-trU`, `genᴬ-tr`) are covered. Each takes any typing of the former,
  at any `Z`, to its rule's premises and `⌈ rule-type ⌉ᵀ ≅ᵀ ⌈ Z ⌉ᵀ`. It
  checks in 3 s and is in `Trust/Kernel`.
- ✅ **C2** (2026-10-02) `Metatheory/NormalShape`. `nf-stuck`: a normal
  type reduces only to itself. `nf-Π`/`nf-Σ`/`nf-Id`: a normal type
  convertible to a Π/Σ/Id is one, by `church-rosserᵀ` and `Π-/Σ-/Id-reduct`.
  `CheckA`'s `NF` now keeps `normTy`'s `IsNormalᵀ` witness instead of
  discarding it.
- ✅ **C3** (2026-10-02) `Metatheory/UniquenessA`:
  `uniqᴬ : Γ ⊢ᴬ t ∷ A → Γ ⊢ᴬ t ∷ B → ⌈ A ⌉ᵀ ≅ᵀ ⌈ B ⌉ᵀ`, one clause per
  former (38). It checks in 5 s.
  - 31 formers are one composition (`via`): their type is in the term.
  - Six recurse: `var` by `∋ᴬ-uniq`; `lam`/`pair` by `≅ᵀ-Πʳ`/`≅ᵀ-Σˡ`;
    `app`/`fst`/`snd` by `Π-inj`/`Σ-inj`, with `sub1≅` (`≅ᵀ-sub` + `sub1`)
    for the substitution.
  - `tr` dispatches on `genᴬ-tr-shape`, now in GenerationA: a `tr` is typed
    at exactly two motive shapes.
- ✅ **C4 proof of concept** (2026-10-02) `Algorithm/DecideA`:
  - `decTo`/`checkᴰ`: a target check whose "no" refutes by `uniqᴬ`.
  - `viewΠᴰ`: a Π view, or a refutation of every Π-typing by `nf-Π`; the
    shape test `isΠ?` needs one clause per `RTy` former.
  - The steps `decVar`, `decLam`, `decApp`, each taking its recursive
    calls' results as arguments.
  - The non-vacuity runs EVALUATE: `(λx.x) 0` YES, `0 0` NO (normal shape),
    `(λx.x) tt` NO (uniqueness).
  - It checks in 5 s, first time.
  - (superseded by C4, below; `DecideA` is deleted)
- ★ **DECISION (2026-10-02): `pair` carries its first type, `pair A B a b`.**
  - Found while writing the full checker: `pair` was the ONE former whose
    premise CONTEXT was not in the term. `B`'s premise lives in `Γ ▹ A`,
    and `A` is `a`'s type, known only up to conversion.
  - Without the annotation, a "no" on `B` would need context conversion
    for `⊢ᴬ`, and no `⊢ᴬ` renaming, substitution or conversion lemma
    exists. With it, every premise context is determined by the term.
  - This is §3d's own rule (annotate what the typing takes from the
    derivation), and it is Lean's `Sigma.mk`.
  - Changes: `genA.py`'s field table, `⊢ᴬpair` (+ `Γ ⊢tyᴬ A`), `pairSᴬ A B`
    for `psplit`'s branch. `uniqᴬ`'s `pair` clause became a plain `via`.
    The old `Maybe` checker's `pair` no longer lifts `a`'s normal form.
- ✅ **C4** (2026-10-02) `Algorithm/CheckA` IS the decision procedure:
  `inferᴬ`/`checkᴬ`/`checkTyᴬ : … → Dec …`.
  - `bind` takes, with each sub-decision, the generation projection that
    turns a typing of the whole into one of the part.
  - Of the 38 `inferᴬ` clauses, 32 regular ones were derived one to one
    from the `Maybe` clauses. `var`, `lam`, `app` (`appStep`, uniqueness +
    `Π-inj` for the argument), `fst`/`snd` (`viewΣ`) and `tr` are written
    by hand.
  - `tr` dispatches on the three-way view `trShape`, whose `none` case
    carries the refutation. It is built with an inspect-style helper:
    `with … in` needs Agda's builtin equality, and this project uses its
    own `_≡_`. A catch-all clause could not refute.
  - `decNoNatC` is complete by induction on the witness (`noNatC?-complete`).
  - `checkTyᴬ`'s "no" inverts the one `⊢tyᴬ` rule.
  - The runs evaluate YES and NO. The new rejections: `fst 0` (no Σ view)
    and a `tr` at an untypable motive.
  - `CheckA` checks in 11 s (7 s before). `viewId`/`IdV` and `nf-Id` were
    dead (`jsub` carries its endpoints) and are deleted, as is the POC
    module `DecideA`.
## 3b. ★ DECISION 3 — S4 by ROUTE C: normalise types BECAUSE they are well-typed

Found on the `natrecᴹ` spike (`SPIKE-NATRECM.md` §3, 2026-09-25). Type
normalisation is structural for every former EXCEPT one rule:

    Hom (Π A B) f g ⟶ᵀ Π A (Hom B (app (renTm vs f) (var vz)) (app (renTm vs g) (var vz)))

It CREATES terms. For an ill-typed "junk" `f` (a non-λ value) the
application is stuck — genuinely SN — but the untyped JM predicate has no
row for it, so an untyped structural `SNᵀ` is not closed under normal forms.

| route | verdict |
|---|---|
| A · make untyped SN treat "application of a non-λ value" as neutral | sound, cheapest; unlocks NOTHING beyond S4 |
| B · a local predicate inside `SNᵀ` only | ⛔ a patch — the same fact known at types, denied at terms |
| C · **normalise types via typing** — validity, SR for types, inversion, recursion on a measure | ✅ **CHOSEN** |

★ **Why C, recorded because the cost argument points the other way:**
1. **Its prerequisites are owed anyway.** Validity, SR for types and
   inversion are what S3's `infer` (well-formed results — slice 1 re-checks
   every inferred domain without it), S3 completeness (uniqueness of types)
   and S6's elaborator need.
2. **It is the η foundation.** G4 (2026-08-04) kept the kernel β-only
   *because* η "would force a typed-conversion re-foundation" (untyped η +
   surjective pairing is not confluent — Klop). C is that re-foundation's
   first step. It does NOT reopen G4; it makes the re-evaluation "at the
   welding" start from typed infrastructure. η is the largest use-site lever
   identified: `f ≡ λx. f x`, surjective pairing, unit-η definitional.

⚠ **Validity is UP TO CONVERSION (V2)**, not a choice of convenience:
`⊢conv` has no `⊢ty B` premise, so the plain statement is FALSE
(`El (fst (pair ⌜base⌝ junk))` is convertible to `base` but ill-formed).
V1 — adding the premise, as Abel–Öhman–Vezzosi do — is a separate kernel
decision touching every `⊢conv` in Lib and the Knot; not taken.

★ **A homotopy-inspired alternative, recorded for the axes question.** The
difficulty exists only because `Hom` COMPUTES at `Π` (directed funext as a
TYPE reduction). Simplicial type theory (Riehl–Shulman) presents
`hom_A(x,y)` as an extension type over a directed interval `Δ¹`, where
`hom` at `Π` is argument-swapping between terms — types never grow, and
type normalisation is structural. A kernel redesign; not now.

★ **S4 OUTCOME (2026-09-25).** Route C was costed as "validity + SR +
inversion + a measure". The measure was NOT needed: recursing on the
NORMAL ambient is structural, and typing makes the terms `Hom-Π` creates
normalisable by `wnorm`. That is the transferable lesson — the same move
as `wnᵀ` in route A, made sound by typing instead of by extending the
untyped SN predicate. Decidable conversion now covers the WHOLE kernel:
`decide-≅` (terms) + `decConvᵀ` (types).

## 3c. ★ DECISION 4 — annotations are irrelevant to conversion (c)

Found while bringing S4 onto the `natrecᴹ` spike (2026-09-25).

| option | conversion on a motive | deciding conversion needs |
|---|---|---|
| (a1) reduction enters motives | up to `≅ᵀ` | a MUTUAL term+type SN theorem — S4 (route C) derives type SN FROM term SN, and (a) makes term SN depend on type SN |
| (d) motives inert, compared by `≅ᵀ` | up to `≅ᵀ` | ⛔ the SAME mutual theorem, for TERMINATION of the comparison: substitution/duplication nests motives arbitrarily deep (`(λx. natrecᴹ (El x) …) u`, iterated by a `natrec`), so no size or depth measure decreases |
| **(c) annotations irrelevant** | **ignored — conversion compares erasures** | **nothing new**: the existing term SN, then compare erasures |

★ **Grounds, and not edit cost:** (1) annotations exist so a kernel term's
TYPE is recoverable (§0) — they are typing data, not computational content,
and irrelevance says exactly that; (2) the metatheory is LAYERED — terms
normalise without reference to types, then types (S4), then conversion;
(3) the equality is strictly COARSER (a superset) — nothing typable before
stops being typable.

⚠ **Obligations it creates:** subject reduction and uniqueness of types
under the coarser conversion; the logical relation must respect "same
erasure". Proved FIRST, before anything builds on (c).

⚠ **Correction recorded:** (d) was recommended once on the claim that it
removes the cycle. It removes it from NORMALISATION only; the DECISION
procedure still needs the mutual theorem. (a1) is not a planned follow-up —
it returns only if equality should ever distinguish annotations.

## 3d. ★ DECISION 5 — (c) is implemented as a SEPARATE ANNOTATED LAYER

The kernel the checker checks is an ANNOTATED syntax `ATm`/`ATy` with its
own syntax-directed judgment `⊢ᴬ`; its MEANING is erasure to today's `RTm`,
whose metatheory is already proven:

    ⌈_⌉ : ATm → RTm          erasure-soundness : Γ ⊢ᴬ t ∷ A → ⌈Γ⌉ ⊢ ⌈t⌉ ∷ ⌈A⌉
    conversion in ⊢ᴬ  :=  conversion of erasures   (decision (c))

★ **Why this and not annotations inside `RTm`:** it states (c)
STRUCTURALLY — the computational calculus has no annotations because they
carry no computation; the typing layer has them because they carry typing.
Putting them in `RTm` would force every metatheorem (LR, confluence, SR,
canonicity) to re-prove that they are irrelevant. Consistency, SN and
canonicity TRANSFER through erasure; conversion is decided by `decide-≅` /
`decConvᵀ` unchanged.

⚠ **Correction recorded:** this is the SHAPE of option 1a, rejected in §1
for failing the de Bruijn criterion. That rejection conflated WHERE
annotations live with WHICH judgment is trusted: here the trusted judgment
is the annotated, decidable `⊢ᴬ`, and plain `⊢` is its semantics — §0 holds.

Annotations `ATm` carries (each is what `⊢` takes from the derivation):
`lam A`, `pair A B` (A added 2026-10-02, §3a), `natrec M`, `con D`, `elim M`, `icon D I i`, `ielim I M`,
and — the §1 AUDIT's finding, made while writing the checker — `jsub A t u`,
`tr A t u`, `ap cA t u`: these took their ambient and ENDPOINTS from the
derivation, and a checker cannot recover them (`Hom` computes away at
`U`/`Π`/`Nat`, and a recovered endpoint has no annotated derivation).
⬜ Descriptions (`Desc`/`IDesc`) stay erased-level for now: their
well-formedness premises are the `⊢`-level ones — an annotated description
layer is a follow-up before `⊢ᴬ` is fully decidable.

## 3e. ★ DECISION 6 (pending adoption) — descriptions are FUNCTORS: "A-math"

Found while giving the annotated checker the inductive formers
(2026-09-25). `IConWf` puts the FIXED POINT `IMu D I j` into its own
telescope (`iwf-ρ`). The declarative judgment tolerates it (it never needs
the context well-formed); the certifying checker cannot — its conversion
engine must prove `⊢ctx`, which needs `IDescWf D`, the thing being
checked. A hidden invariant exposed by an algorithm, like the annotation
audit.

★ **The mathematics:** an indexed description is a code for a STRICTLY
POSITIVE FUNCTOR `F : (I → Type) → (I → Type)`; `IMu D` is its initial
algebra. Well-formedness is a property of `F`, checked with the recursive
positions typed by an ABSTRACT FAMILY `X : Π I U` — never the fixed point.
Positivity is STRUCTURAL (recursive positions exist only via `iρ`), not a
side check — unlike Coq's inductive-as-assumption + syntactic positivity.

★ **The model already IS this** (read from the code, not the record):
`ILift C … P` is the constructor's functor applied to an abstract predicate
`P`; `ikp-ρ`/`iki-ρ` carry nothing; the fixed point is tied ONLY in
`IMuMem`. Only the SYNTAX lags. §9.2 put `IMu D I j` in the telescope for
EXPRESSIVITY (a recursive index may name earlier fields) — A-math keeps it
(the family is applied to the same `j`). No recorded decision rejects it.

★ **SPIKE — `bootstrap/tmp/AMathSpike.agda`, GREEN:**
- Q-shape: `IConWfˣ` does not mention `D` at all; `PairIx`'s description
  ports almost verbatim (only a recursive field's TYPE changes). Carried
  terms live in the constructor's `X`-free scope and reach the telescope by
  a renaming `ρ` — positivity is SYNTACTIC; `X` at the ROOT keeps every
  carried index unchanged.
- Q-check: `telWf` — EVERY context the judgment visits is well-formed from
  `◇ ⊢ty I` alone. **The checker's circularity is gone.**
- Q-use (syntactic): `TySub.iihTy-wf` ports (`iihTy-wfˣ`) with
  `X := λj. ⌜IMu⌝ D I j`; cost = ONE conversion (β, then decode) per
  recursive field.
- Q-use (semantic) + termination: `relX` builds the `X` entry's
  interpretation DIRECTLY from `idi` (as `fund`'s `⊢⌜IMu⌝` case does) — no
  recursion into `fund`, so the recorded "fund-mutual helpers cannot be
  parameterized" trap does not arise; `relRec` is one `sem-conv`.

⚠ **It must REPLACE `iwf-ρ`, not sit beside it:** bridging new → old needs
`IDescWf D` to type `X`'s instance — the circle again.

⬜ **Adoption cost** (from the model read): the telescope gains a root slot
(carried through `ρ`); `ipayTy`/`iihTy`/`iihs`/`isingle`/`imeth*`
consumers restated over `(σ, τ)` as `iihTy-wfˣ` is; `fund`'s `iihsSem`
uses `relX`/`relRec`; `Examples/PairIx`, `DepIx`, and the Knot's
description rows are rewritten; `Spec/TypingA`'s annotated twin follows.

## 4. Open questions, recorded not answered

- **A universe hierarchy.** Needed for large elimination under code
  motives, and for `U : U`-free typing of `U` itself. Independent of this
  plan but interacts with §1's 1b/1c equivalence.
- ~~**Conversion on annotations.**~~ ✅ **DECIDED 2026-09-25: (c) —
  annotations are IRRELEVANT to conversion** (conversion compares erasures;
  domain-free PTS, Barthe–Sørensen). See §3c.
- **Fuel.** `Algorithm/Check` and `Lib/Eval` take fuel. `snorm` makes a
  fuel-free normaliser derivable (`PLAN-NF` Phase 2); a kernel `infer`
  should not ultimately depend on fuel.

## 5. Evidence and pointers

- `snorm`/`wnorm`/`dec-conv-typed`: `Metatheory/Fundamental.agda:2008-2030`.
- Constructor injectivity and `church-rosserᵀ`: `Metatheory/Injectivity.agda`.
- Inversion lemmas `gen-*`: `Metatheory/SubjectReduction.agda:496-983`.
- Clash lemmas for rejection branches: `poc/OCP0009/NbEPDirDBCanon.agda`.
- The Knot's wf burden by constructor: `iwf-κ` 823, `⊢⌜IMu⌝` 755,
  `icw-ford`/`icw-imu` 360 each, `⊢var` 3 101 (RedWfA+B, TyRedWf, Wf).
