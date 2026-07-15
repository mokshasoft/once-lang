# HANDOFF — OCP-0009 dependent-types POC

**Branch:** `ocp-0009-poc0-nbe`  **Working tree:** clean.
**Vehicle:** Agda, IR-only, under `bootstrap/poc/OCP0009/`. Compiler untouched.
**Build one module:** `bootstrap/check.sh poc/OCP0009/<Module>.agda` (→ EXIT 0).

## TL;DR of state

- **81 modules, all green** (72 of them `--safe`). **START AT
  `NbEPMonIndex.agda`** for the monoidal/linear tower — one `--safe`
  entry point re-exporting the headline theorems (`dec≈`, `complete`,
  `nf`, the axiom re-derivations, the closed-core theory + `bal` +
  `soundE`, and the total placement-canonical normalizer `NF`), with
  the reading guide in its header. `NbEPMonO` shows the Mac Lane
  axioms + Yang–Baxter re-derived from `complete` in one line each.
  The full expressibility tower is built and
  machine-checked: decidable conversion (NbE) → CwF/dependent layer → `Id`+`J` →
  **QTT** (semiring + graded judgment + IR elaboration) → **OTT** (funext-by-def,
  proof-irrelevance, `Eq`/`coe`, μ, quotients, bisim-at-ν) → **IR universe**
  (+ hardened decidable eq + hierarchy `U₀⊂U₁`) → **native indexed inductives** →
  **coinduction** (guarded) → **summit** (verified compiler in-theory).
- **Every §5-table row is now demonstrated** (see `plans/…-poc.md` §5).
- **The `--safe` campaign is COMPLETE (2026-07-13)** — the entire principled
  NbE core + adequacy + CwF + `Id` + QTT + OTT + IR + indexed + coinduction +
  summit. Zero `TERMINATING`, zero `NO_POSITIVITY_CHECK` anywhere. The 9
  non-safe modules are exactly the superseded older conversion track, tainted
  by `Complete`'s `funext` postulate (kept as historical record; nothing
  load-bearing imports them).
- **The FULL-fragment NbE + erasing QTT elaboration are BUILT (2026-07-13):**
  `NbEPF` — ONE engine for `{Unit,×,+,μ,⇒}` (`NbEP`+`NbEKF` merged; possible
  precisely because §2 excludes positive η; η-long products became a datatype
  shape — no `Normal` predicate; recursion-inside-a-closure decided by `nf`),
  and `NbEPQTTEraseTm` — the erasing TERM elaboration (usage-masked runtime
  context makes the `𝟘`-strengthening lemma definitional; `⌊K⌋ ≡ curry snd ≡
  ⌊idₗ⌋`; erased-argument irrelevance on OPEN terms decided by `NbEPF.nf`).
  Both `--safe`. This closes `NbEPQTTJ`'s documented "Next" and §5's QTT row
  end-to-end.
- **The former §5 "honest gaps" are ALL CLOSED (2026-07-13):** `NbEPUnivT`
  (ℕ-indexed universe tower via the universe-operator construction, + the
  UNIFORM Gödel ladder `con : ∀ n → El (suc n) (`Con n)`), `NbEPII`
  (induction-induction: intrinsic `Ctx`/`Ty` + standard model — the future
  Spec/Kernel shape), `NbEPOTTU` (OTT INTERNALIZED: `` `eq `` as a universe
  code with computed decoding; internal funext + proof-irrelevance
  definitional; **the `Open.agda` residual `n+0=n` proven by induction as an
  object-language `Id` inhabitant**). All three `--safe`. Then **`NbEPOTTH`
  (2026-07-13): the HETEROGENEOUS layer — `EQ` across types, `EQU` as
  evidence, `coe`/`coh` + full refl/sym/trans suite, dependent `Σ` codes
  (respect-bundled families), dependent-tuple transport along `n+0` by
  `refl`.** Remaining depth: the full setoid universe (Π in the
  heterogeneous layer), conversion for the extended universes inside Once's
  own NbE.
- **The consistency ladder is BUILT (2026-07-13, plan §8):** `NbEPCon0`
  (`¬ Term Unit Void` + non-degeneracy, via the `--safe` Set-model),
  `NbEPCon1` (graded QTT calculus proves nothing about an abstract base:
  elaborate `ι ↦ Void`), `NbEPCon2` (the first-order `Code` universe cannot
  even express falsity; and the internal Gödel ladder at `NbEPUnivH`'s
  `U₀ ⊂ U₁` — `` `Con₀ `` statable and provable only at level 1). All three
  `--safe`. `NbEPUnivH` gained empty codes `` `⊥₀ ``/`` `⊥₁ ``. See the
  consistency ledger's "The consistency ladder" section and plan §8 (incl. the
  Once-in-Once moral: "Once+" = same tower, one universe level up).
- **Docs are current:** `plans/ocp-0009-decidable-conversion-poc.md` (module map §1,
  reframing §6, OCP-0006 relationship §7), `docs/proposals/OCP-0009-…md`
  (Rung status notes + "Consistency & the trust story" section + systems table),
  and `docs/consistency-and-what-proofs-mean.md` (foundations + POC consistency
  ledger + `--safe` status).

## THE `--safe` TASK: **DONE** (steps 1 → 2 → 3 all complete)

Goal was: strengthen the consistency guarantee by compiling under `--safe` (which
rejects every unsafe escape hatch: `TERMINATING`, `NO_POSITIVITY_CHECK`,
`type-in-type`, meaning-affecting postulates). A `--safe` module may only import
`--safe` modules. All three steps of the user's plan are done; **the next work is
the "Other open items" section below.**

### Step 1 — DONE (commits `d00790ee`, `06c88010`)
- Flipped the 10 standalone tower modules to `--safe` (they never touch the NbE
  core): `NbEPUniv/Dec/H`, `NbEPIndexed`, `NbEPOTT/Q/Mu`, `NbEPCoind`,
  `NbEPOTTCoind`, `NbEPSummit`.
- Split the pure `Tm` syntax out of `NbEP` into new `--safe` module **`NbEPTm`**
  (`NbEP` re-exports it publicly → all downstream imports unchanged). This let the
  QTT stack go `--safe`: **`NbEPTm`, `NbEPQTT`, `NbEPQTTJ`** are now `--safe`; the
  one `nf`-tied theorem was split into **`NbEPQTTErase`** (stays non-safe).

### Step 2 — DONE (2026-07-13): `NO_POSITIVITY_CHECK` discharged, `NbEKF` is `--safe`
- The handoff plan suggested defunctionalizing the Kripke closure into a code+env
  datatype; the fix that landed is strictly better: `Val` is now defined by
  **recursion on the type** (Tarski-style presheaf semantics),
  `Val A (X ⇒ Y) = ∀ {A'} → A' ≼ A → Val A' X → Val A' Y` as a `Set`-valued
  function. No datatype → no positivity question at all — and unlike
  defunctionalization (which would route `vapp` back through `eval`), `eval`
  became structurally recursive on `Tm` and reflect/reify on the type, so the
  `TERMINATING` pragma fell away too. `Ne` stays a first-order, strictly positive
  datatype (`nApp` stores an already-reified `C.Term`).
- `NbEK` (the presheaf foundation `NbEKF` imports) was already pragma-free; it
  just got the `--safe` flag. Both β/η examples in `NbEKF` still hold by `refl`.
- **`NO_POSITIVITY_CHECK` no longer occurs anywhere in the POC.** The only
  remaining escape hatch, everywhere, is `TERMINATING` (step 3's target).

### Step 3 — DONE (2026-07-13): the `TERMINATING` pragmas were UNNECESSARY
- The anticipated research-grade SN proof **dissolved**: removing every
  `TERMINATING` pragma (`NbEP`, `NbEPNat`, `NbEPFund`, `NbEPNormal`,
  `NbEPComplete`, `NbE`, `Complete`) simply **typechecks**. Agda's size-change
  termination checker accepts the mutual `eval/vcase/vcata/mapCata/nf` block's
  lexicographic (Tm, Val) descent: every call cycle either strictly shrinks the
  term (`eval (cataT F a) → vcata → eval a` — `a` is a subterm) or keeps the
  term and strictly shrinks the value (`vcata (vIn w) → mapCata w → vcata w′`,
  `w′ ⊆ w`). The pragmas were conservatism from an earlier shape of the code,
  never re-tried. (Lesson recorded: before proving termination, try deleting
  the pragma.)
- With the pragmas gone, 13 more modules were flagged `--safe` and all pass:
  `NbEP`, `NbEPNat`, `NbEPRel`, `NbEPFund`, `NbEPNormal`, `NbEPComplete`,
  `NbEPCwF`, `NbEPEl`, `NbEPId`, `NbEPElOTT`, `NbEPQTTErase`, `NbE`, `NbEConv`.
- The audit the old note asked for was done first: `NbEPCwF`/`NbEPEl`/`NbEPId`
  genuinely use `nf` (15/27/5 uses) and `NbEPElOTT` uses `eval` — no cheap
  re-pointing was possible; it just turned out not to be needed.
- **Remaining non-safe (9, all by design):** `Complete` (real `funext`
  postulate) and its importers `Sound`, `Finite`, `Decidable`, `Open`,
  `Higher`, `Dependent`, `Universe`, `Transparency` — the superseded older
  conversion track. Making these `--safe` would mean rebuilding them on the
  principled track (or on OTT's definitional funext); of questionable value
  since they're kept as historical record.

## Other open items (now THE open items), from plan §4/§6

1. **OTT internalization** — OTT `eq` is currently a model-level construction over
   the denotational `⟦_⟧`; wire it in as Once's *object-language* identity type
   with its own computation (the "make it native" gap; OTT-the-theory supports it).
2. **Wire to the real Once IR / OCP-0006** (`origin/ocp-0006-once-spec`) — the §7
   analysis pinpointed the targets: OCP-0009's decidable conversion discharges the
   compiler's **postulated `formal/Once/Optimizer/Normal.agda`** (6 postulates),
   and our `Mult` semiring matches the compiler's **"QTT enforcement: Not started"**
   (`docs/formal/core/what-is-proven.md`). This is "demonstrated the power → ship
   the power."
3. **Decide whether Once's core adopts IR** — the IR universe (`NbEPUniv`) is the
   one genuine consistency-strength increase (flagged everywhere); adopting it into
   the shipping core is a deliberate, TCB-raising commitment. Currently POC-only.
4. **Optional refinements — ALL DONE (2026-07-13):** `⌜_⌝`-faithfulness note
   closed earlier; `sum-η`/`μ-η` sugar → `NbEPEta`; ℕ-indexed tower →
   `NbEPUnivT`. **Plan §4's checklist is now fully done or user-excluded**
   (excluded: compiler wiring, spec split — POC boundary). **Heterogeneous
   `coe`/`coh` + dependent `Σ` codes: DONE (`NbEPOTTH`, 2026-07-13)** — full
   suite (refl/sym/trans/coe/coh over `EQU`-as-data, respect-bundled Σ
   families), dependent-tuple transport along `n+0` computing by `refl`.
   Remaining depth: the full SETOID UNIVERSE (Π codes in the heterogeneous
   layer — function values bundled with respect proofs; the failure analysis
   for raw functions is in `NbEPOTTH`'s header) and conversion for the
   extended universes inside Once's own NbE.
5. **The directed research POC (intentions recorded in plan §10):** dHoTT
   internalization — `Hom` as an OBJECT-language type former with variance,
   directed transport, and decidable directed conversion (exists in no
   system; the make-or-break is decidability, as it was for equality).
   Rungs 0–2a are DONE (2026-07-13): `NbEPDir` (meta-level Hom-category),
   `NbEPDirU` (Hom as a universe code, irreversibility internal), `NbEPDirJ`
   (**the eliminator settled: Hom is a directed identity type — J in three
   forms, sym refuted, transport = J + step-covariance, universe-valued
   motives**), `NbEPMon` (monoidal core — no-diagonal/no-discard/no-undo
   proven: linearity as semantics, in-core directedness), `NbEPMonC`
   (**rung 2b part 1: the linear `Conv` — the full SMC theory `_≈m_` as
   data, the leaf-path WIRING normal form, per-axiom soundness with
   pentagon/triangle/hexagon by `refl`, decidable `conv?`, and
   `conv-refutes`**). **RUNG 2b PART 1 COMPLETED 2026-07-14: SMC
   COHERENCE COMPLETENESS IS PROVEN** — `dec≈ : ∀ f g → Dec (f ≈m g)`
   in `NbEPMonE`, all `--safe`. The staged climb (plan §10):
   `NbEPMonN` (type normalization, Beylin–Dybjer accumulator) →
   `NbEPMonP` (Ins/Perm realizations + agreement `wire∘permM ≡ applyP`)
   → `NbEPMonA` (Perm algebra: ⊙P/padP/bswap) → `NbEPMonU`
   (representation uniqueness `applyP-inj`) → `NbEPMonR`/`NbEPMonY`
   (swapHead toolkit + **Yang–Baxter**) → `NbEPMonI`/`NbEPMonQ`
   (algebra realized: push-real/⊙P-real/nt-perm-nat) →
   `NbEPMonG`/`NbEPMonK`/`NbEPMonS`/`NbEPMonH`/`NbEPMonZ` (generator
   squares: nt-α/ρ/ƛ, Kelly K2–K5′, mirror hexagon + σ-block, **nt-σ
   the bswap square**) → `NbEPMonE` (pOf, keySq, canon, completeness,
   `dec≈`). **Then `NbEPMonD` (2026-07-14): THE TWO TOWERS MEET — the
   rung-3 hybrid skeleton**: conversion by normalization
   (`f ≈m g ⟺ nf f ≡ nf g`), the structural fragment proven a groupoid
   (`invS`, so `≈m` = the symmetric equality axis; directedness =
   `NbEPMon`'s transition axis), and the kernel universe with
   `` `shom ``/`` `conv `` codes — conversion AS A TYPE decoded to
   normal-form identity: hexagon instances check by literal `refl`,
   transport across convertible programs computes away. **Agreed
   ordering (2026-07-14): hybrid skeleton ✓ → `⊸`/proof nets (the next
   research climb) → re-instantiate the skeleton over the extended
   core.** The `⊸` expedition's stage L0 is DONE (2026-07-14,
   `NbEPMonL`: CTy/CTm with `Λc`/`evc`, the SMCC theory `_≈c_` with
   β⊸/η⊸, the bridge `embE : f ≈m g → embT f ≈c embT g`, Set-model
   with β/η by `refl`). Stage L1 DONE (`NbEPMonV`: the signed-balance
   invariant `bal` — linearity survives closure; `no-dupC`/
   `no-discardC`/`no-dup⊸`/**`no-weakenC` (the K combinator refuted
   in-core)**). Stage L2a DONE (`NbEPMonX`: extensional soundness —
   the `Ext` PER, the fundamental lemma, `soundE` with every axiom
   case a one-liner by η, and `no-σc-id`: the refutation oracle for
   the closed theory; decidability explicitly NOT claimed). Remaining:
   L2b optional (the Kelly–Mac Lane pairing as a first-order
   invariant; NOT complete at units — the triple-unit obstruction),
   **L3 (linear NbE — THE frontier climb)**: the FULL DERIVATION is
   recorded in plan §10 (Day-convolution model over the decided base;
   generic reflection by type decomposition; the frontier located at
   ⊗/I-to-the-right-of-⊸-in-negative-position). Stages L3.0–L3.1 DONE
   (`NbEPMonT`: the world category; `NbEPMonW`: worlds realized back
   into syntax; `NbEPMonM`: **LINEAR NbE RUNS** — the Day-convolution
   model, evalV as repartition arithmetic, reify/reflect on
   right-purity witnesses, pending-permutation neutrals so equal
   values reify IDENTICALLY; β⊸/η⊸/structural/higher-order demos all
   by `refl`). Stage L3.2 DONE (`NbEPMonB`: the
   residualizing split monad — pair-returning neutrals; let = 
   composition; all L3.1 demos re-decided + the frontier demo
   `Λ((σ∘σ)∘ev) ≡ id` at `ι₁ ⊸ (ι₁⊗ι₂)`, by `refl`). Stage L3.3 DONE
   (`NbEPMonJ`, 2026-07-15: the `usI` node — units crossed, the
   `Good`/`GoodR` witnesses dissolve, **`NF : CTm A B → CTm A B` is
   TOTAL on the free SMCC**; seven demos by `refl` incl. both unit
   crossings). Stage L3.4a part 1 DONE
   (`NbEPMonF`, 2026-07-15: PLACEMENT CANONICITY — atoms Sp'd, absorb
   a uniform join, hoisting reify; the u3-class equality now by
   `refl`; stability demos `NF (NF f) ≡ NF f`). REMAINING ON L3:
   **L3.4a part 2** — same-boundary node ORDER (adjacent-swap sort by
   consumed positions) and λ-boundary commutation; **L3.4b adequacy — THE CLIMB IS UNDERWAY** (staged A1–A4 in plan
   §10; user decision 2026-07-15: adequacy before consolidation).
   A1 DONE (`NbEPMonAdq1`: iso backbone — chain kit, `mult-inv-l/r`,
   `join-split`/`split-join`). A2 DONE (`NbEPMonAdq2`, first-try
   green: the full homomorphism layer — swapHeadC-nat/invol, F2C/GC,
   pentagon corollaries, M-reductions, **YBC**, ins-swap-realC,
   pid-realC, push-realC, **⊙P-realC** — verbatim ports of R/Y/I/Q;
   element-genericity held perfectly). NEXT: **A2b — the pad/swap
   realizations** (NEW derivations, the G/K/S/Z analogues over list
   worlds; statements recorded in plan §10: padˡ/padʳ-real,
   insˡ/insEnd-real, bswapW-real — derive on paper first, expect
   lighter than their nt-* counterparts). Then A3 (RSp + Sp-combinator
   splice lemmas, consuming A2/A2b) and A4 (R, fundamental lemma,
   completeness `f ≈c NF f`). Rung 3 proper (variance judgments,
   directed univalence) — gated on the linear/monoidal core decision
   (§7 route (a)).
6. **At POC→real transition (intentions recorded in plan §9):** break the DT
   kernel out as a SPEC layer — `Spec/IR` (unoriented equations + one boring
   model) + `Spec/Kernel` (typing/equality judgments as pure data) + proven
   elaboration bridge; restate the Con theorems syntactically over the spec'd
   judgment; retire `normalizer/Axioms/*` (16 confluence-type postulates) via
   the evaluator route. Do NOT freeze while OTT internalization / IR adoption
   are open; a draft `Spec/Kernel` earlier is cheap and clarifying.

## Where to look

- **Roadmap + module map:** `plans/ocp-0009-decidable-conversion-poc.md` (§1 map,
  §5 systems table, §6 foundations-first order, §7 OCP-0006 relationship).
- **Proposal:** `docs/proposals/OCP-0009-decidable-dependent-types.md` (Rung
  status notes; "Consistency & the trust story").
- **Consistency/trust reference + POC ledger:**
  `docs/consistency-and-what-proofs-mean.md`.
- **The NbE core:** `NbEP` (eval/nf), `NbEPRel`/`NbEPFund`/`NbEPNormal`
  (adequacy scaffolding) — all `--safe`.

## Verify everything still green (sweep)

```bash
for f in bootstrap/poc/OCP0009/*.agda; do
  bootstrap/check.sh "poc/OCP0009/$(basename "$f")" >/dev/null 2>&1 \
    && echo "ok  $(basename "$f")" || echo "FAIL $(basename "$f")"
done
```

*(This handoff is a working note; commit it or not as you prefer.)*
