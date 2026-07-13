# HANDOFF — OCP-0009 dependent-types POC

**Branch:** `ocp-0009-poc0-nbe`  **Working tree:** clean.
**Vehicle:** Agda, IR-only, under `bootstrap/poc/OCP0009/`. Compiler untouched.
**Build one module:** `bootstrap/check.sh poc/OCP0009/<Module>.agda` (→ EXIT 0).

## TL;DR of state

- **41 modules, all green** (32 of them `--safe`). The full expressibility tower is built and
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
4. **Optional refinements:** `⌜_⌝`-faithfulness note already closed; `sum-η`/`μ-η`
   as surface sugar (plan §3.A); universe hierarchy → ℕ-indexed ∞ tower.

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
