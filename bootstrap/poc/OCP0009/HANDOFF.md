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
  - *NORMALIZATION (SN)* — ✅ PROVEN for the simply-typed core (`NbEPDirDBSN`,
    dHoTT-35); the dependent+universe extension remains research-scale.
    - *STLC strong normalization* — ✅ DONE. **`sn : Γ⊢A → SN t`** is proven in
      full for the simply-typed λ-calculus, `--safe` and ZERO axioms, by
      Girard–Tait reducibility. The build: the funext-free substitution calculus
      (`sub-comm`/`ren-comm`), β-reduction with `⟶-sub`/`⟶-ren`/`⟶-ren-inv`
      (reduction reflects through renaming), `SN` as accessibility with
      `sn-antisub` (`SN (sub σ t) → SN t`) and the closure theorems (`sn-lam`,
      `sn-neutral-app`, ★ **`sn-β-exp`** SN closed under β-expansion, `nf→SN`);
      then the KRIPKE logical relation `Red` (arrow case over future renamings ⇒
      `Red-ren` closes it under weakening), the candidate conditions `CR1`/`CR2`/
      `CR3` (mutual on the type — the crux: Girard-neutral = *not a λ*, so a
      β-redex is neutral and `CR3` applies), the abstraction lemma `abs`, and the
      fundamental theorem `fund`. This is the input the decision engine assumed,
      now discharged for the simply-typed fragment.
    - *The Π/Σ fragment (functions + products)* — ✅ DONE (`NbEPDirDBSNSig`,
      dHoTT-36). Turns the "reduces to STLC" claim into a THEOREM: without `U`/`El`,
      kernel types are term-free `base`/Π/Σ trees = simple types with functions and
      products, so **`sn : Γ⊢A → SN t`** holds there too, `--safe`/zero-axiom. Adds
      the product candidate `Red (A ×ₜ B) t = Red A (fst t) × Red B (snd t)` and the
      pair-introduction lemma `red-pair` (dual to `abs`) to the dHoTT-35 proof.
    - *The universe — TYPE-LEVEL metatheory* — ✅ DONE (`NbEPDirDBSNU`, dHoTT-37).
      The kernel's reduction SPLITS: TERM reduction has no `El` (codes reduce only
      by ξ); the genuinely-new difficulty is all in TYPE reduction, where `El`
      decodes and a type GROWS. This module closes the type side: **`snᵀ`** (type
      SN — growth terminates, by structural induction on the code since the universe
      is predicative), a direct normal-form **`nfᵀ`** (`_⟶ᵀ_` is orthogonal), and
      ★ **`dec-≅ᵀ`** (type conversion is DECIDABLE) — mirroring dHoTT-25/34 at the
      type level.
    - *The universe — TERM SN + coupled fundamental theorem* — STILL OPEN,
      research-scale. NB: term SN does NOT shortcut via erasure — the erased simple
      type is not conversion-stable (a neutral code can reduce to a real code, so
      `El(neutral)` and its reduct erase differently: `base` vs `⇒`). So term SN
      genuinely needs the COUPLED induction-recursion (Abel–Öhman–Vezzosi):
      reducibility of terms AT `El`-types, FOLLOWING the decoding, standing on the
      dHoTT-37 type-normalization. A formalization **project**, not a slice.

### Also open (from the semantic tower — not on the finalization critical path)

- **[strict CwF core]** — ✅ DONE (`NbEPDirStrict`, dHoTT-38). The transport-free
  redesign: separate DATA from LAWS so substitution is definitionally strict.
  A `Sub` is LAW-FREE functor data (`ob`/`mor`) ⇒ `_∘_` is function composition
  (`∘-idˡ`/`∘-idʳ`/`∘-assoc` all `refl`); a `Ty` is a LAW-FREE covariant family
  (`fam`/`act`) ⇒ `_[_]` is precomposition (`[]-id`/`[]-∘` `refl`); hence
  `Σ-stable`/`×-stable` are **`refl`** — no funext/uip/subst/wrapper. Same
  strictness-by-construction as the syntactic kernel (dHoTT-20), now semantic.
  UNIVERSE-PARAMETRIC (polymorphic in the fibre level) — the shape of the
  consistency tower's generic rung. Honest scope: makes the covariant-stable
  formers `refl`-stable; does NOT fix the directed `Π⁺` (genuine Beck–Chevalley).
- **[consistency tower]** — ✅ RUNG BUILT (`NbEPDirStrict`, dHoTT-38b). The
  level-parametric reflection: `U ℓ'` over Γ (`: Ty Γ (ℓ ⊔ lsuc ℓ')`) reflects the
  collection of level-`ℓ'` types as one type ONE LEVEL UP; `code`/`El` witness it;
  ★ **`El-code : El (code A) ≡ A`** is `refl` — the decode is DEFINITIONAL, the
  soundness of the reflection (`Once_n`'s types are faithfully objects at the next
  level). ★ **`ladder : El (code (U ℓ')) ≡ U ℓ'`** — the universe of one level is
  itself classified (decoding back definitionally) at the next; level-parametric,
  so `ℓ' := ℓ'₀, lsuc ℓ'₀, …` gives `Once ⊂ Once⁺ ⊂ …` from ONE construction.
  Gödel not bypassed (the reflection needs a level strictly above; the ladder
  never closes on itself — trust retreats to `Once_ω`). Honest scope: this is the
  "large" reflection universe (classifies the level below, definitional decode);
  `El`'s general `act` uses one transport (subst along a code's naturality), the
  key rule `El-code` still `refl`. A substitution-STABLE small universe is
  Hofmann–Streicher (covariant, intricate) — the remaining refinement.
- **[Π stability special case]** For `σ` an EXACT map (iso / discrete fibration),
  `restrict-⇛` becomes an iso → `Π⁺` strictly stable there. NB (dHoTT-38 finding):
  for a GENERAL `σ` this is genuine mathematics, not a coherence artifact —
  strictification does not remove it; only exactness (or definitional/strict iso)
  makes it `refl`.
- **[compiler]** Wire `redCat` (`formal/Once/IR.agda`) through the dependent
  formers / a real pass through `transp`.

--------------------------------------------------------------------------
## 4. Recommended next step

**Tier B is fully cleared** — confluence + subject reduction proven. Combined
with dHoTT-20/21 (strict dependent Π/Σ, typing, `Id = core(Hom)`) and A2
(directed `J`), the kernel is a well-behaved, type-safe (preservation) dependent
type theory. **Integrated A1 (Σ terms) and A3 (universe) are now DONE** — the
committed kernel has Π, Σ, and a universe. **C1's decision engine is DONE** — so
decidable conversion holds *modulo normalization*. **STLC strong normalization is
now PROVEN** (`NbEPDirDBSN`, dHoTT-35 — `sn : Γ⊢A → SN t` by Girard–Tait
reducibility, `--safe`, zero axioms). What remains is ONE research-scale item:

- **[SN⁺] SN for the UNIVERSE** — the SOLE remaining SN frontier. STLC SN
  (dHoTT-35) and the Π/Σ fragment with products (dHoTT-36, `sn` proven for
  functions+products = the kernel WITHOUT the universe) are both machine-checked.
  What is left is exactly the universe: `El c` decodes → types grow under
  substitution → the reducibility predicate needs an induction-recursion
  (Abel–Öhman–Vezzosi-style) rather than structural recursion on the type. This is
  what `NbEPDirDBDec.dec-conv` consumes to become an unconditional decision
  procedure for the *full* kernel. Everything else in the design is built and
  machine-checked.

Recommendation: **the universe SN is the last piece**, and it is a dedicated
formalization project (the induction-recursion for the universe), not a slice. The
reducibility proofs in `NbEPDirDBSN` (STLC) and `NbEPDirDBSNSig` (adding products)
are the reusable template — the candidate conditions, the Kripke closure, the
intro lemmas (`abs`/`red-pair`), and the fundamental-theorem shape all carry over;
only the universe's type-growth needs the IR upgrade. Everything the design
promised is otherwise built and machine-checked.

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
