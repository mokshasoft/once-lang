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
  - *Integrated* — ✅ DONE (dHoTT-32): `pair`/`fst`/`snd` + Σ-β are now in the
    COMMITTED kernel. Six modules extended (`NbEPDirDBPi` syntax+substitution,
    `NbEPDirDBType` Σ-β + `⊢pair`/`⊢fst`/`⊢snd`, `NbEPDirDBSR`, `NbEPDirDBConf`
    confluence re-proven with the complete-development for Σ redexes,
    `NbEPDirDBInj` Σ-injectivity, `NbEPDirDBSubj` `sr` + generation). **Confluence
    AND subject reduction now genuinely cover pairs.** All `--safe`, zero-axiom;
    the whole chain re-verified. The kernel is a type-safe dependent theory with
    BOTH Π and Σ.

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
  - *Integrated* — ✅ DONE (dHoTT-33): a Tarski `U` with codes
    (`⌜base⌝`/`⌜Π⌝`/`⌜Σ⌝`) and El-decoding (`El (⌜Π⌝ c d) ⟶ᵀ Π (El c)(El d)`) is
    now in the COMMITTED kernel. The substantive part was `NbEPDirDBInj` (type
    confluence now has El-decode REDEXES — the type complete-development
    develops them). `NbEPDirDBSubj` needed `conv-ctx` (context conversion via
    the substitution lemma) for the `ξ-⌜Π⌝ˡ` case. **Confluence AND subject
    reduction now cover the universe too.** All `--safe`, zero-axiom.

**Feature-completeness (standalone) — ✅ DONE.** The self-contained line now
carries the whole feature set: `NbEPDirDBSig` (Σ pairs, dHoTT-29), `NbEPDirDBUniv`
(universe, dHoTT-30), and the capstone `NbEPDirDBFull` (dHoTT-31) — Π + Σ + a
universe *together*, with codes decoding to `Π`/`Σ`, coded dependent pairs, and
Π/Σ composing. These DEMONSTRATE the design; the standalone demos are separate
from the committed kernel. **Σ terms (dHoTT-32) AND the universe (dHoTT-33) are
now integrated into the committed kernel** — so `sr`/confluence cover pairs and
codes. The committed kernel is a well-behaved, type-safe dependent type theory
with Π, Σ, and a universe. **C1's decision engine is DONE** (`NbEPDirDBDec`,
dHoTT-34) — decidable conversion holds *modulo normalization*. What genuinely
remains: **strong normalization** (SN, research-scale) — the one input the
decision engine consumes.

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

- **[C1] Decidable conversion via NbE.** The "decided by NbE" half of §1. Splits
  into two parts:
  - *The decision ENGINE* — ✅ DONE (`NbEPDirDBDec`, dHoTT-34): using CONFLUENCE,
    convertible normal terms are syntactically equal (`conv-normal-≡`), hence
    conversion is decidable given weak normalization + decidable NF equality
    (`dec-conv`); plus a concrete non-conversion needing no inputs (`var≇lam`).
  - *NORMALIZATION (SN)* — FRAMEWORK BUILT, general theorem still research-scale.
    - *SN framework + witnesses* — ✅ DONE (`NbEPDirDBSN`, dHoTT-35): a self-
      contained intrinsically-typed STLC with the full funext-free substitution
      calculus (renaming, parallel substitution, four fusion lemmas, `sub-comm`),
      β-reduction with `⟶-sub` (reduction survives substitution), `SN` as
      accessibility of `_⟶_` with its preservation lemma, and CONCRETE SN
      witnesses exercising the machinery on real well-typed terms (`sn-var`,
      `sn-lam-id`, and the β-redex `sn-βredex` — `(λx.x) y` is SN, contracting
      only to `y` with its ξ-reducts ruled out). `--safe`, zero-axiom.
    - *The general theorem* — STILL OPEN, research-scale. `Γ⊢A → SN t` is
      Girard–Tait reducibility (`Red` by recursion on the type, `CR1/2/3`, the
      abstraction lemma, the fundamental theorem over a reducible substitution).
      For OPEN terms this needs the KRIPKE form (`Red` quantifies over future
      renamings ⇒ closed under weakening) plus reduction-reflection and SN both
      ways under renaming — a substantial standalone formalization even for STLC.
      The UNIVERSE makes it strictly harder: `El c` decodes to `Π`/`Σ`, so types
      GROW under substitution and the reducibility predicate can't be structural
      recursion on the type (needs an induction-recursion, à la
      Abel–Öhman–Vezzosi). A formalization **project**, not a slice.

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
type theory. **Integrated A1 (Σ terms) and A3 (universe) are now DONE** — the
committed kernel has Π, Σ, and a universe. **C1's decision engine is DONE** — so
decidable conversion holds *modulo normalization*. The SN FRAMEWORK is now built
too (`NbEPDirDBSN`, dHoTT-35 — STLC substitution calculus + `SN` + `⟶-sub` +
concrete witnesses). Exactly ONE research-scale item remains:

- **[SN] The general strong-normalization theorem** — `Γ⊢A → SN t`, the one
  input `NbEPDirDBDec.dec-conv` still consumes. The framework and concrete
  witnesses are in place (dHoTT-35); what remains is the reducibility argument
  itself. Even for STLC (open terms) this is the KRIPKE logical relation (`Red`
  closed under weakening, plus reduction-reflection + SN both ways under
  renaming). The UNIVERSE makes it strictly harder — `El c` decodes → types grow
  under substitution → an induction-recursion is needed (Abel–Öhman–Vezzosi-
  style). A formalization project. Everything else in the design is built and
  machine-checked.

Recommendation: **the general SN theorem is the last piece.** It is the design's
headline made fully decidable, and the one thing `dec-conv` still assumes. The
substitution/reduction/SN scaffolding it stands on is now in `NbEPDirDBSN`; scope
the reducibility proof as a dedicated project (Kripke logical relation, then the
universe's induction-recursion) — everything the design promised is otherwise
built and machine-checked.

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
