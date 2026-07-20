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

Progress this push (dHoTT-25…27): **[B1] confluence — DONE**, **[B2] Π-
injectivity — DONE** (the blocker; full SR assembly remains, see below),
**[A2] directed `J` over the kernel terms — DONE**. Remaining below.

### Tier A — completable bricks (each a focused session, low risk)

- **[A1] Σ intro/elim terms (pairs).** Add `pair`/`fst`/`snd` to `RTm`, extend
  substitution (mechanical — the mutual pattern is set in dHoTT-20), typing
  rules, Σ-β and Σ-η. *Deps:* none. *Unblocks:* exercising `Σ'` and Σ-η
  (currently `NbEPDirDBEta` only has Π-η). *Effort:* small. **STILL OPEN.**

- **[A2] Directed identity type — ✅ DONE (`NbEPDirDBIdJ`, dHoTT-27).** Directed
  `J⟶`/`J-tgt`, `no-sym` (refuted), `transport⟶`/`yo`, over the actual `RTm`
  kernel terms. Honest remainder: `Hom` is still the META relation `⟶*`, not an
  object-language `RTy` former with `refl : RTm` and `J` as *typing rules* —
  fully internalizing needs extending `RTy`/`RTm` (and the conversion rule to see
  `refl`). The elimination principle is settled; the syntactic former is the
  small remaining step.

- **[A3] Universe + type-formation judgment.** `U`/coding, `El : Tm U → Ty`
  (replacing the raw `El`), and `Γ ⊢ A type` well-formedness. *Deps:* none hard,
  but **requires extending the core `RTy`/`RTm` syntax** (cascades to importers)
  or a parallel extended calculus. *Effort:* moderate–disruptive. *For:* a
  "complete" system (`UnivS`/`UnivV` in the tower are the semantic precedents).
  **STILL OPEN.**

### Tier B — the gateway metatheorem (DONE: confluence + Π-injectivity)

- **[B1] Confluence (Church–Rosser) — ✅ DONE (`NbEPDirDBConf`, dHoTT-25).**
  Takahashi complete-development method (parallel reduction + triangle → diamond
  → confluence), ported from `CCC._⟹_`. `confluent` and `church-rosser`
  (convertible ⇒ joinable). β only; βη-confluence (η-postponement) is a later
  refinement.

- **[B2] General subject reduction — blocker DONE, assembly OPEN.** Π-INJECTIVITY
  of conversion is proven (`NbEPDirDBInj`, dHoTT-26, via type-level confluence) —
  the exact obstruction dHoTT-24 scoped. What remains for *full* SR is the
  **standard typed metatheory**, all confluence-free now: (a) the typed
  substitution lemma (typed renaming + substitution preserve typing — needs a
  `⊢ˢ`/`Ren⊢` judgment, the ext-lemmas, and type-level `sub-comm`/`wk-cancel`);
  (b) generation/inversion lemmas through `⊢conv` (using `Π-inj`); (c) context
  conversion (typing respects `≅ᵀ` in the context). This is ~350–450 lines of
  mechanical, low-insight proof — deferred here, precisely identified. *Effort:*
  moderate–large but routine. **ASSEMBLY OPEN.**

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

B1 (confluence), the B2 blocker (Π-injectivity), and A2 (directed `J`) are DONE.
The natural next move is **complete [B2] — the subject-reduction assembly.**
Rationale:

1. **It finishes a whole metatheorem, now unobstructed.** Π-injectivity is in
   hand; the rest (typed renaming + substitution lemma, generation lemmas,
   context conversion) is confluence-free and reuses `NbEPDirDBSR`'s
   substitution-stability. Routine, not research.
2. **Ordering.** SR + confluence is the well-behavedness foundation you want
   solid before the typed-NbE big rock (C1). Do SR, then a quick [A1] (Σ terms,
   small), and leave [A3] (universe — needs syntax extension) and [C1] (typed
   NbE / SN via logical relations — research-scale) as the two named large
   pieces.

Do **not** start [C1] cold — sequence: finish B2 → A1 → A3 → C1.

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
