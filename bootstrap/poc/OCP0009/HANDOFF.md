# OCP-0009 · Handoff — dependent types for Once (dHoTT path)

Branch `ocp-0009-poc0-nbe`. All modules `--safe`. Verify any module from
`bootstrap/` with `./check.sh poc/OCP0009/<Module>.agda`. Companion docs:
`FINDINGS.md` (design conclusions + proof patterns), `PATHS.md` (per-module
table + two-paths write-up). **This file is the cold-start state and — its main
job — WHAT'S LEFT before the POC is finalized.**

--------------------------------------------------------------------------
## 1. The design decision (unchanged — the punchline)

**Add dependent types to Once as a CARTESIAN dependent type theory with the
IDENTITY TYPE = the reduction relation.**

- **Kernel**: syntactic, cartesian Π/Σ, substitution strict *by construction*.
- **Definitional equality**: `core(Hom)`, decided by **NbE**.
- **Identity type**: the *directed* `Hom a b := a ⟶* b`, with **directed `J`**
  and **`no-sym`** — for reasoning about IRREVERSIBLE transformations (optimizer
  passes literally *are* `⟶*`).
- **`Id = core(Hom)`**: the invertible part of the directed `Hom` (inter-
  reducibility) IS convertibility = definitional equality = what NbE decides.
  One primitive gives both the directed `Hom` (pass/irreversibility reasoning)
  and its symmetric groupoid core (equational reasoning + typechecking).
- **Linearity is OPT-IN** (Fox comonoid layer, Path 1); QTT is secondary.

**Why not the functor-category directed CwF as kernel?** Its Π is only
**lax-stable** (Beck–Chevalley fails). Ruled out as kernel; survives as the
**consistency MODEL** (strictified). This was the central design risk — and it
is now **confirmed dissolved by the syntactic presentation** (see §2, F2).

--------------------------------------------------------------------------
## 2. Current state — the design arc is BUILT and VALIDATED (dHoTT-15…24)

The whole recommendation is demonstrated end-to-end, all `--safe`, all
zero-axiom (funext only ever *threaded*, never assumed). Detail: `PATHS.md`
table; conclusions: `FINDINGS.md`. In brief:

- **Strict kernel** (`NbEPDirKernel` 15): `Id = Hom`, subst = precomposition,
  the coherence laws ARE reductions (F1: "strict substitution" and "Id = Hom"
  are one relation), groupoid `Core`, `core→≋`.
- **Strict de Bruijn substitution** (`NbEPDirDB` 16): genuine variables, the
  four fusion lemmas + category laws as propositional `≡` **on the nose**,
  funext-free (P1).
- **Directed optimizer correctness** (`NbEPDirPass` 17, `NbEPDirDBPass` 19):
  passes ARE inhabitants of `Id`; correctness transports covariantly; passes
  survive instantiation (`pass-stable = Id-sub`); irreversibility ⇒ *why
  directed* (F4).
- **Sound symmetric core** (`NbEPDirDBCore` 18): `Core` + a denotational STLC
  model with `⟶ ⊆ ≋`, giving `core → ≋`.
- **★ THE EXPERIMENT** (`NbEPDirDBPi` 20): dependent Π/Σ, substitution **strictly
  stable** — `(Π A B)[σ] ≡ Π (A[σ])(B[σ↑])` is DEFINITIONAL. The lax-Π /
  Beck–Chevalley obstruction is **dissolved by syntax** (F2). The design's
  central bet: **CONFIRMED**.
- **Intrinsic typing + conversion** (`NbEPDirDBType` 21): the raw dependent
  syntax is a CHECKED kernel — `_⊢_∷_` with `⊢var`/`⊢lam`/dependent `⊢app`/
  **`⊢conv`**; conversion `_≅ᵀ_` = the R-S-T closure = `core(Hom)` operational.
- **Metatheory, honest depths** (22–24): (i) NbE-decides FORCES intrinsic typing
  (`NbEPDirDBNorm`, Ω self-reduces — F3); (iii) η fattens the core
  (`NbEPDirDBEta`); (ii) reduction & conversion are substitution-stable
  (`NbEPDirDBSR`) — the confluence-free half of subject reduction.
- **★ Well-behavedness proven** (25–28): **CONFLUENCE** (`NbEPDirDBConf`),
  **Π-INJECTIVITY** (`NbEPDirDBInj`, via type-level confluence), **SUBJECT
  REDUCTION** (`NbEPDirDBSubj`, `sr`/`sr*`), and the **directed identity type**
  over the kernel terms (`NbEPDirDBIdJ`, directed `J`/`no-sym`). The kernel is a
  well-behaved, type-safe (preservation) dependent type theory. All zero-axiom.

**No blocks discovered.** No impossibility, no undiscovered obstruction. The
path is unblocked; what remains is known, well-scoped metatheory (§3).

--------------------------------------------------------------------------
## 3. WHAT'S LEFT before the POC is finalized

**"Finalized" =** a machine-checked dependent type theory realizing §1: Π/Σ
**and the directed identity type**, `Id = core(Hom)` conversion **decided by
NbE**, with **subject reduction** and decidable typechecking — a system you
could point at and say "this is how Once does dependent types."

Progress (dHoTT-25…28): **[B1] confluence — DONE** (`NbEPDirDBConf`), **[B2]
subject reduction — DONE** (`NbEPDirDBInj` Π-injectivity + `NbEPDirDBSubj` the
full typed metatheory + `sr`/`sr*`), **[A2] directed `J` — DONE**
(`NbEPDirDBIdJ`). Remaining below.

**Reassessment (important):** the old handoff called A1/A3 "completable bricks."
That was wrong. Adding constructors to the CORE `RTm`/`RTy` (Σ terms, universe)
cascades through *every* downstream module and forces **re-proving confluence
AND subject reduction** for the extended calculus. So every remaining item is
LARGE: A1/A3 are syntax-extension-with-full-metatheory-redo; C1 is research-
scale. There is no clean small continuation left.

### Tier A — now LARGE (syntax extension + metatheory redo)

- **[A1] Σ intro/elim terms (pairs).**
  - *Standalone demo* — ✅ DONE (`NbEPDirDBSig`, dHoTT-29): a fresh self-contained
    dependent Π/Σ calculus with `pair`/`fst`/`snd`, Σ-β, Σ-η, dependent typing
    (`⊢pair`/`⊢fst`/`⊢snd` with `snd`'s type depending on the projection), and a
    genuinely dependent pair worked end-to-end. Touches nothing committed; shows
    the Σ-term design.
  - *Integrated* — STILL OPEN, LARGE: to make the COMMITTED kernel's `sr`/
    confluence cover pairs, add `pair`/`fst`/`snd` + Σ-β to the shared `RTm`/`_⟶_`
    and re-prove substitution, `_⟹_`/`_⁺`/triangle (`NbEPDirDBConf`), and `sr`
    (`NbEPDirDBSubj`) with the new cases. The invasive extended-calculus pass.

- **[A2] Directed identity type — ✅ DONE (`NbEPDirDBIdJ`, dHoTT-27).** Directed
  `J⟶`/`J-tgt`, `no-sym` (refuted), `transport⟶`/`yo`, over the actual `RTm`
  kernel terms. Honest remainder: `Hom` is still the META relation `⟶*`, not an
  object-language `RTy` former with `refl : RTm` and `J` as *typing rules* —
  fully internalizing needs extending `RTy`/`RTm` (and the conversion rule to see
  `refl`). The elimination principle is settled; the syntactic former is the
  small remaining step.

- **[A3] Universe + type-formation judgment.**
  - *Standalone demo* — ✅ DONE (`NbEPDirDBUniv`, dHoTT-30): a Tarski `U` with
    codes and a decoding `El` that computes by TYPE reduction (`El (⌜Π⌝ c d) ⟶ᵀ
    Π (El c)(El d)`), dependent codes (`⌜Π⌝`'s codomain under the decoded
    domain), and terms inhabiting named types via `⊢conv`. Touches nothing.
  - *Integrated* — STILL OPEN, LARGE: replacing the committed kernel's raw `El`
    with a coded universe (+ `Γ ⊢ A type`) is the same invasive
    extend-core-and-re-prove pass as integrated A1.

### Tier B — the well-behavedness foundation — ✅ DONE (confluence + SR)

- **[B1] Confluence (Church–Rosser) — ✅ DONE (`NbEPDirDBConf`, dHoTT-25).**
  Takahashi complete-development method (parallel reduction + triangle → diamond
  → confluence), ported from `CCC._⟹_`. `confluent` and `church-rosser`
  (convertible ⇒ joinable). β only; βη-confluence (η-postponement) is a later
  refinement.

- **[B2] General subject reduction — ✅ DONE** (`NbEPDirDBInj` dHoTT-26 +
  `NbEPDirDBSubj` dHoTT-28). Π-injectivity of conversion (via type-level
  confluence), the typed renaming + substitution lemmas (`Ren⊢`/`Sub⊢`), single
  substitution (`⊢[]`), generation (`gen-lam`/`gen-app`), and **`sr`**/`sr*`.
  The β case sidesteps context conversion by converting the argument to the λ's
  domain + the result type via `Π-inj`. The kernel has subject reduction.

### Tier C — the big rock (research-scale, the design's headline mechanism)

- **[C1] Typed NbE / strong normalization over `_⊢_∷_`.** The "decided by NbE"
  half of §1. Needs **SN for well-typed terms** (reducibility / logical
  relations — Girard's method) plus a **Kripke/glueing NbE model** that reifies
  to normal forms and decides conversion (sound + complete). Known-possible
  (Abel–Öhman–Vezzosi and others machine-checked exactly this), but this is a
  formalization **project**, not a slice — the single largest remaining effort.
  *Deps:* wants B1 (confluence) and the typed setting solid (21, B2). Likely
  needs the **intrinsic** representation (F3 forces the typed setting; raw `RTm`
  has no total `nf`). *Effort:* LARGE.

### Also open (from the semantic tower — not on the finalization critical path)

- **[consistency]** Strictification (local universes) of the directed CwF, so
  the semantic model validates the strict syntactic Π. For "Once+ proving Once".
- **[Π stability special case]** For `σ` an iso / discrete fibration,
  `restrict-⇛` becomes an iso → `Π⁺` strictly stable there.
- **[compiler]** Wire `redCat` (`formal/Once/IR.agda`) through the dependent
  formers / a real pass through `transp`.

--------------------------------------------------------------------------
## 4. Recommended next step

**Tier B is fully cleared** — confluence + subject reduction proven. Combined
with dHoTT-20/21 (strict dependent Π/Σ, typing, `Id = core(Hom)`) and A2
(directed `J`), the kernel is a well-behaved, type-safe (preservation) dependent
type theory. Every remaining item is now LARGE (see the §3 reassessment):

- **[A1] Σ terms** or **[A3] universe** — each extends the core syntax and
  re-does the metatheory (substitution + confluence + SR) for the extended
  calculus. Pick whichever feature you want first; budget for the full cascade.
  A *standalone* universe demo (own tiny syntax, à la `UnivS`) is the cheaper way
  to show A3's design without touching the committed core.
- **[C1] Typed NbE / SN** — the design's headline "decided by NbE", research-
  scale (SN via logical relations + a Kripke/glueing NbE model). The single
  largest piece; needs the intrinsic/typed setting (F3).

Recommendation: if the goal is **decidable typechecking** (the design's
headline), C1 is the target — but scope it as a dedicated project, not an inline
slice. If the goal is **feature-completeness**, do A1 (Σ terms) as a deliberate
extended-calculus pass. Either way, there is no more "quick brick" — the
low-hanging metatheory is done.

--------------------------------------------------------------------------
## 5. Reference — the two towers (compact)

**Path 2 (directed / dHoTT), semantic tower (dHoTT 0–14):** over the CCC
reduction relation, a directed CwF with a full type-former suite —
`NbEPDir`/`NbEPDirU` (`Hom`, `no-way-back`), `NbEPDirJ` (directed `J`, `sym`
refuted), `NbEPDirV` (variance), `NbEPDirC`/`F` (directed cata + fusion),
`NbEPDirCwF`/`L`/`J` (directed CwF + Yoneda `J`), `NbEPDirIR` (real-IR
`NatTr`/`Fuse`/`Para`), `NbEPDirTy`/`Sig`/`Pi`/`PiG`/`Sub` (formers `×⁺`/`+⁺`/
`⇒⁺`/`Σ⁺`/`Π⁺`), `NbEPDirStab`/`TyExt` (CwF stability + the extensionality
wrapper), `NbEPDirPiSub` (**the lax-Π finding**, F2's semantic side),
`NbEPDirUniv`/`S`/`V` (universes), `NbEPDirAp` (`ap`/`transport`). Then the
**syntactic** tower this session (dHoTT 15–24) — see §2.

**Path 1 (linearization, OPT-IN memory):** `NbEPLinFox` (Fox's theorem),
`NbEPLinRec` (linear recursion), `NbEPLinPass` (cartesian→linear + soundness),
`NbEPLinLive` (coinductive leak-freedom `□◇`), `NbEPLinUse` (minimal placement).
Memory correctness = a **balance law** (one free per alloc = comonoid counit),
not a heap model.

--------------------------------------------------------------------------
## 6. Ground rules that held this whole POC

- Set-level, **no univalence, no UIP axiom** (only `--with-K` `uip` as an
  avoidable convenience). funext **threaded** as a hypothesis to stay `--safe`.
- The syntactic dependent kernel (16, 20–24) is **fully zero-axiom / funext-free**
  (F/§4 of `FINDINGS.md`).
- Transport-free where possible; structural (perms/isos) over `subst`/`rewrite`.
- The directed side has **no `sym`** anywhere — every map is covariant.
