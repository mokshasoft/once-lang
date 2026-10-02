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

## 3. Stages

| # | stage | state |
|---|---|---|
| S0 | `Algorithm/DecEq` (`Dec` equality, all sorts); `Algorithm/DecideConversionTyped` (term conversion, no parameters); `Algorithm/Check` slice 1 (certifying bidirectional checker, Π/Σ/U/El/Nat/Unit/Hom/Id) | ✅ `e4135b26` |
| S1 | SPIKE `natrecᴹ` inside `RTm` (branch `ocp-0009-spike-natrecM`) | ✅ done — superseded by §3c/§3d; it showed (a) needs a mutual SN theorem to be decided |
| S2 | The annotated layer (§3d): `Spec/Annotated` (`ATm`/`ATy`, ren/sub, erasure + commutation), `⊢ᴬ`, erasure-soundness | ✅ `70a8c1b2e`. Ported to the levitated kernel in PLAN-LEVITATION Stage F: `Spec/AnnotatedDesc`, and `Spec/TypingA` via `tools/genA.py` |
| S3 | The checker for `⊢ᴬ` (`Algorithm/CheckA`): certifying, STRUCTURAL (every former infers — no fuel); the term's own annotations checked with `⊢ᴬ`, all type reasoning on ERASURES (`validity`, `normTy`, `decConvᵀ`), annotated views of inferred types LIFTED from erased normal forms. Then COMPLETENESS (uniqueness of types up to conversion) | 🟡 **next**. SOUNDNESS covers EVERY former, the levitated inductive ones included (`con`, `ielim`, `dih`, `dpay`, `⌜IMu⌝`, `dι`/`dσ`/`dρ`). `tr` is accepted only at `⌜Hom⌝` motives. ⬜ COMPLETENESS (audited 2026-10-02) |
| S4 | Decide TYPE conversion `≅ᵀ` completely — ROUTE C (§3b): ① validity + `srᵀ` (`Metatheory/Validity`) ✅; ② inversion — the existing `gen-*` sufficed ✅; ③ `normTy`/`decConvᵀ` (`Metatheory/NormTy`) ✅ — **structural, NO measure needed**: `homNF` recurses on the NORMAL ambient (`G` ⊂ `Π F G`), the created `app f↑ vz` go through the typed `wnorm`, and a `NoU` witness breaks the harmless `elNF ↔ homNF` cycle | ✅ |
| S5 | The signature: constants, δ, and the conservativity theorem | ⬜ |
| S6 | The bidirectional SURFACE → annotated core elaborator. `Algorithm/Check`'s slice 1 is its seed; the Once compiler's `formal/Once/TypeCheck` is the shape template | ⬜ |
| S7 | The Knot WRITTEN in the annotated core with signature references; its wf derivations come from `inferᴬ`, not from a generator. User, 2026-10-02: "if we have to write code to generate the Knot something is wrong". Measure against `HANDOFF-2026-09-24` §4's split | ⬜ |

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
`lam A`, `pair B`, `natrec M`, `con D`, `elim M`, `icon D I i`, `ielim I M`,
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
