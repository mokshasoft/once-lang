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

**No blocks discovered.** No impossibility, no undiscovered obstruction. The
path is unblocked; what remains is known, well-scoped metatheory (§3).

--------------------------------------------------------------------------
## 3. WHAT'S LEFT before the POC is finalized

**"Finalized" =** a machine-checked dependent type theory realizing §1: Π/Σ
**and the directed identity type**, `Id = core(Hom)` conversion **decided by
NbE**, with **subject reduction** and decidable typechecking — a system you
could point at and say "this is how Once does dependent types."

Six remaining items. Ordered within each tier by dependency; effort is a rough
sense of scale, not a promise.

### Tier A — completable bricks (each a focused session, low risk)

- **[A1] Σ intro/elim terms (pairs).** Add `pair`/`fst`/`snd` to `RTm`, extend
  substitution (mechanical — the mutual pattern is set in dHoTT-20), typing
  rules, Σ-β and Σ-η. *Deps:* none. *Unblocks:* exercising `Σ'` and Σ-η
  (currently `NbEPDirDBEta` only has Π-η). *Effort:* small.

- **[A2] Internalize the DIRECTED IDENTITY TYPE in the kernel.** Add `Id`/`Hom`
  as a type former in `RTy` (an identity type between terms), with `refl`
  introduction and **directed `J`** elimination as rules in `_⊢_∷_`, connected to
  the reduction `Hom`. This is the distinctively **dHoTT** piece — currently the
  directed `J` lives only in the *semantic* tower (`NbEPDirJ`/`NbEPDirCwFJ`), not
  over the syntactic dependent kernel. *Deps:* none hard (directed `J` is
  structural recursion on `⟶*` chains — done before at dHoTT-1). *Effort:*
  moderate. *Note:* this makes the theory genuinely directed-HoTT rather than a
  standard Π/Σ theory with a reduction-based conversion.

- **[A3] Universe + type-formation judgment.** `U`/coding, `El : Tm U → Ty`
  (replacing the raw `El`), and `Γ ⊢ A type` well-formedness. *Deps:* none hard.
  *Effort:* moderate. *For:* a "complete" system (metatheory wants type
  formation; `UnivS`/`UnivV` in the tower are the semantic precedents).

### Tier B — the gateway metatheorem (moderate, standard, precedent in repo)

- **[B1] Confluence (Church–Rosser).** Tait–Martin-Löf parallel reduction +
  diamond, then confluence of `⟶*`. **Precedent lives in this repo**:
  `normalizer.Syntax.CCC` already has `_⟹_` + the diamond property for the
  point-free side — port the technique. β first (standard, ~Takahashi); βη is
  more delicate (η-postponement). *Deps:* none. *Unblocks:* → **Π-injectivity of
  conversion** (`Π A B ≅ Π A' B' → A ≅ A' × B ≅ B'`, since Π-headed types have no
  top-level redex) → general subject reduction; also de-risks B2/typed NbE.
  *Effort:* moderate, well-scoped, LOW RISK.

- **[B2] General subject reduction.** With confluence (B1) in hand: invert
  `⊢ lam t ∷ Π A B` through `⊢conv` via Π-injectivity, plus the **typed
  substitution lemma** (typed parallel substitution preserves typing — its
  confluence-free ingredients, `⟶-sub`/`≅ᵀ-sub`, are already proven in
  `NbEPDirDBSR`). *Deps:* B1. *Effort:* moderate, after B1.

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

**Take on [B1] Confluence.** Rationale:

1. **Highest leverage among completable items.** It converts the dHoTT-24
   "confluence-free half of subject reduction" into a real path to *full* SR,
   and yields **Π-injectivity of conversion** as a corollary — turning the one
   honestly-scoped ceiling into a completed theorem.
2. **Standard method with repo precedent.** Parallel reduction + diamond, and
   `normalizer.Syntax.CCC._⟹_` already does it for the sibling calculus — port,
   don't invent. LOW RISK, genuinely finishable in a focused session (unlike C1).
3. **Prerequisite you want in hand before the big rock.** Typed NbE (C1) is much
   smoother with confluence established; starting C1 cold is the wrong order.

**Alternative, if the priority is dHoTT-distinctiveness over metatheory
completion:** take [A2] (internalize the directed identity type). That is the
piece that makes this genuinely *directed*-HoTT rather than a standard dependent
theory, it is moderate and self-contained, and the machinery (directed `J` on
`⟶*` chains) is already proven semantically. Confluence (B1) is the better
*type-theory-finalization* move; A2 is the better *design-identity* move. Both
are right; B1 first is the recommendation.

Do **not** start [C1] cold — sequence B1 → B2 → (A2/A3) → C1.

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
