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
| S1 | **SPIKE: `natrecᴹ M z s n`, ADDITIVE** — alongside `natrec`, the way indexed descriptions were brought up. Measure the cascade through reduction, substitution, confluence, SR, LR. | ⬜ **next** |
| S2 | Decide from S1: annotate in place, former by former (`natrec`, `elim`, `ielim`, `lam`, `pair`, then the §1 audit of the code-carrying formers); delete the unannotated forms | ⬜ |
| S3 | Core `infer : Γ → t → Maybe (Σ A (Γ ⊢ t ∷ A))` — certifying, so sound by construction. Then COMPLETENESS: needs uniqueness of types up to conversion (absent today) | ⬜ |
| S4 | Decide TYPE conversion `≅ᵀ` completely — ROUTE C (§3b): ① validity + `srᵀ` (`Metatheory/Validity`) ✅; ② inversion — the existing `gen-*` sufficed ✅; ③ `normTy`/`decConvᵀ` (`Metatheory/NormTy`) ✅ — **structural, NO measure needed**: `homNF` recurses on the NORMAL ambient (`G` ⊂ `Π F G`), the created `app f↑ vz` go through the typed `wnorm`, and a `NoU` witness breaks the harmless `elNF ↔ homNF` cycle | ✅ |
| S5 | The signature: constants, δ, and the conservativity theorem | ⬜ |
| S6 | The bidirectional SURFACE → annotated core elaborator. `Algorithm/Check`'s slice 1 is its seed; the Once compiler's `formal/Once/TypeCheck` is the shape template | ⬜ |
| S7 | The Knot: `gen-knot.py` emits core terms + signature references and asks `infer` for the wf derivations; measure against `HANDOFF-2026-09-24` §4's split | ⬜ |

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

## 4. Open questions, recorded not answered

- **A universe hierarchy.** Needed for large elimination under code
  motives, and for `U : U`-free typing of `U` itself. Independent of this
  plan but interacts with §1's 1b/1c equivalence.
- **Conversion on annotations.** Compare up to `≅ᵀ` (principled, costs the
  mutual reduction) vs ignore them in conversion (cheap, but two
  convertible-motive `natrec`s would then be inconvertible). S1 should
  measure the first before anyone reaches for the second.
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
