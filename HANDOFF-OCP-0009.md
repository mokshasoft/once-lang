# HANDOFF — OCP-0009 dependent-types POC

**Branch:** `ocp-0009-poc0-nbe`  **Last commit:** `06c88010`  **Working tree:** clean.
**Vehicle:** Agda, IR-only, under `bootstrap/poc/OCP0009/`. Compiler untouched.
**Build one module:** `bootstrap/check.sh poc/OCP0009/<Module>.agda` (→ EXIT 0).

## TL;DR of state

- **38 modules, all green.** The full expressibility tower is built and
  machine-checked: decidable conversion (NbE) → CwF/dependent layer → `Id`+`J` →
  **QTT** (semiring + graded judgment + IR elaboration) → **OTT** (funext-by-def,
  proof-irrelevance, `Eq`/`coe`, μ, quotients, bisim-at-ν) → **IR universe**
  (+ hardened decidable eq + hierarchy `U₀⊂U₁`) → **native indexed inductives** →
  **coinduction** (guarded) → **summit** (verified compiler in-theory).
- **Every §5-table row is now demonstrated** (see `plans/…-poc.md` §5).
- **Docs are current:** `plans/ocp-0009-decidable-conversion-poc.md` (module map §1,
  reframing §6, OCP-0006 relationship §7), `docs/proposals/OCP-0009-…md`
  (Rung status notes + "Consistency & the trust story" section + systems table),
  and `docs/consistency-and-what-proofs-mean.md` (foundations + POC consistency
  ledger + `--safe` status).

## THE IMMEDIATE IN-PROGRESS TASK: get everything under `--safe`

Goal: strengthen the consistency guarantee by compiling under `--safe` (which
rejects every unsafe escape hatch: `TERMINATING`, `NO_POSITIVITY_CHECK`,
`type-in-type`, meaning-affecting postulates). A `--safe` module may only import
`--safe` modules. Doing steps **1 → 2 → 3 in order** (user's plan). Steps 1 and 2
are done; **step 3 is what remains.**

### Step 1 — DONE (commits `d00790ee`, `06c88010`)
- Flipped the 10 standalone tower modules to `--safe` (they never touch the NbE
  core): `NbEPUniv/Dec/H`, `NbEPIndexed`, `NbEPOTT/Q/Mu`, `NbEPCoind`,
  `NbEPOTTCoind`, `NbEPSummit`.
- Split the pure `Tm` syntax out of `NbEP` into new `--safe` module **`NbEPTm`**
  (`NbEP` re-exports it publicly → all downstream imports unchanged). This let the
  QTT stack go `--safe`: **`NbEPTm`, `NbEPQTT`, `NbEPQTTJ`** are now `--safe`; the
  one `nf`-tied theorem was split into **`NbEPQTTErase`** (stays non-safe).
- **Currently `--safe` (16):** `Conv`, `NbEK`, `NbEKF`, `NbEPTm`, `NbEPUniv`,
  `NbEPUnivDec`, `NbEPUnivH`, `NbEPIndexed`, `NbEPOTT`, `NbEPOTTQ`, `NbEPOTTMu`,
  `NbEPOTTCoind`, `NbEPCoind`, `NbEPSummit`, `NbEPQTT`, `NbEPQTTJ`.
- **Modules with REAL unsafe pragmas** (the blockers): `NbEP`, `NbEPComplete`,
  `NbEPFund`, `NbEPNormal`, `NbEPNat`, `NbE`, `Complete` (all `TERMINATING` on
  `eval`/`nf`-style recursion).
  (`NbEPTm`/`NbEPQTTErase` only MENTION "TERMINATING" in comments — they're clean.)

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

### Step 3 — TODO (THE PRIZE): discharge the `TERMINATING` pragmas on `eval`/`nf`
- The `TERMINATING` pragma sits on the mutual `eval/vcase/vcata/mapCata/nf` block
  in `NbEP.agda` (and is mirrored in `NbEPComplete`, `NbEPFund`, `NbEPNormal`,
  `NbEPNat`, `NbE`, `Complete` — each re-does an eval-shaped recursion).
- Agda can't see structural termination because the recursion is over
  `Tm` + `Val` together and `mapCata`/`vcata` recurse on the functor `F` and the
  value simultaneously. **This is the standard NbE termination obligation** =
  Strong Normalization / a logical-relation (reducibility) argument. The plan calls
  it "tedious, not deep"; the adequacy scaffolding already exists in `NbEPRel`
  (the inductive logical relation `≈V`), `NbEPFund` (`eval-cong` fundamental
  theorem), `NbEPNormal` (the `Normal` η-long predicate). The proof strategy:
  define a well-founded measure or a reducibility predicate that eval respects, and
  turn each `TERMINATING` function into a structurally/well-founded-recursive one
  (e.g. via a fuel-free accessibility argument or a sized-types-free
  logical-relation `eval` that returns a proof of reducibility).
- This is the genuine research-grade chunk. Completing it (a) removes the last
  unsafe escape hatch, bringing the **entire conversion + CwF + Id + QTT-erasure
  track under `--safe`**, and (b) turns "very likely consistent" into
  "machine-checked, escape-hatch-free" for the whole POC.
- Cheaper partial credit along the way: any module that imports the NbE core only
  for `Tm`-data (not `eval`/`nf`) can already be re-pointed at `NbEPTm` and go
  `--safe` (that's exactly how the QTT split worked in step 1). Audit
  `NbEPCwF`/`NbEPEl`/`NbEPId`/`NbEPElOTT` — they genuinely use `nf`, so they need
  step 3, but double-check.

## Other open items (post-`--safe`), from plan §4/§6

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
- **The NbE core (step-3 target):** `NbEP` (eval/nf), `NbEPRel`/`NbEPFund`/
  `NbEPNormal` (adequacy scaffolding for the SN proof).

## Verify everything still green (sweep)

```bash
for f in bootstrap/poc/OCP0009/*.agda; do
  bootstrap/check.sh "poc/OCP0009/$(basename "$f")" >/dev/null 2>&1 \
    && echo "ok  $(basename "$f")" || echo "FAIL $(basename "$f")"
done
```

*(This handoff is a working note; commit it or not as you prefer.)*
