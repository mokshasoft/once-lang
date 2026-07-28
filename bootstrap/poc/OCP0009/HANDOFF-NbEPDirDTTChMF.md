# OCP-0009 · Handoff — raw-faithful M3c (`NbEPDirDTTChMF.agda`)

> ⚠ **START AT `HANDOFF-2026-07-27.md`, NOT HERE.** Two things in this document mislead if
> read cold:
> 1. This file chases **FAITHFULNESS**. dHoTT **consistency is already proven and closed**
>    in `NbEPDirDTTSem.agda` (`--safe`, zero postulates/holes). The `consistency` name
>    *inside* `NbEPDirDTTChMF.agda` is that file's local corollary, not the project result.
>    This has been confused twice; do not make it three.
> 2. §4.2–§4.2⁸ are partly SUPERSEDED. §4.2⁸'s "Option 1" recommendation is **tested and
>    FALSE** (§4.2⁹). The live findings are §4.2⁹–§4.2¹².
>
> §2's "no in-harness feedback" is also stale — background execution has no 600 s cap.

Branch `ocp-0009-poc0-nbe`. This is the focused continuation doc for the
**fuel-indexed set-model soundness** file that discharges *faithfulness* of the
genuinely-dependent Church calculus (the "#1′ raw route" of the main `HANDOFF.md`
§3). The broad design story lives in `HANDOFF.md`/`FINDINGS.md`/`PATHS.md`; this
file is ONLY about finishing `NbEPDirDTTChMF.agda`.

**Goal:** `consistency : ∀{t} → ε ⊢ t ∷ ⊥̇ → Empty`, with ZERO
axioms/postulates/holes/TERMINATING/sized-types eventually (funext threaded as a
module parameter is the one permitted assumption).

--------------------------------------------------------------------------
## 0. Files

- `NbEPDirDTTCh.agda`   — `--safe`, ZERO postulates. Syntax + core: terms/types,
  de Bruijn ren/sub + fusion, `_⊢_∷_` (Church-style `⊢lam` carries the domain wf),
  OPEs `_⊑[_]_`, `ren⊨`/`ren⊢`, `⊨-unique`, `⊢-unique`. Cached (`.agdai`).
- `NbEPDirDTTChSub.agda` — `--safe`, ZERO postulates. `SubW` (singleW/extW),
  `sub-⊨`/`sub-⊢`, coherences `subTy-comm`/`subTy-extS-wk`/`subTy-single-wk`, `wk⊢`.
- `NbEPDirDTTChMF.agda` — **the WIP file** (`--prop --termination-depth=3`, NOT
  `--safe` due to postulates + threaded funext). One big mutual block:
  `CI/TI/MI/TI-irr/⇓/wkTI/subTI/nat-TI/nat-MI/sub-TI/sub-MI/MI-irr` + the coe/uip
  machinery. ~1240 lines.

--------------------------------------------------------------------------
## 1. State (working tree, uncommitted: `MI-irr ⊢app` written & type-checks)

DONE (real, verified, committed):
- Core interpreter `CI/TI/MI` (fuel-indexed, `--prop` bounds), `TI-irr`, `⇓`.
- `wkTI` (weakening naturality, via `nat-TI` at `wk⊑`), `envO`/`envO-⇓`/`envO-wk⊑`.
- **`nat-TI` COMPLETE**, **`sub-TI` COMPLETE**, **`sub-MI` COMPLETE (8/8)**.
- **`nat-MI` COMPLETE** — all 4 `nat-var-vz`/`nat-var-vs` (keep/skip × vz/vs) closed
  via the `nat-var` helper refactor (see §3).
- **`MI-irr` 5/6** — `⊢tt`/`⊢ff`/`⊢vz`/`⊢vs`/`⊢lam` closed.

DONE (WORKING TREE, **not yet committed**) — ✅ **CHECK NOW COMPLETE, 2026-07-27**:
`Cmd_load` of the working-tree file returned `agda2-goals-action '()` — an EMPTY goal list,
i.e. **ZERO holes**, zero type errors, zero termination errors. EXIT 0. Wall clock **26m13s**
(not the ~10 min §2 estimates — budget accordingly). The only residue is the §2.5 bound metas,
counted exactly: **66**. ⇒ `MI-irr` is confirmed 6/6 TOTAL and the work below is ready to commit.
- **`MI-irr` `⊢app` WRITTEN and TYPE-CHECKS** (the last hole, now closed). Offline
  batch run 2026-07-25: NO `UnsolvedInteractionMetas`, NO type errors. It's a faithful
  port of `nat-MI ⊢app` (see §3/§4.1) — renaming machinery dropped, `⇓` definitional so
  `pa`/`qc` are direct `TI-irr` (pinned), fuel split LHS=`suc(suc m)`/RHS=`suc m`, LHS
  collapse is `coe3-uip` (not `coe4`). Draft also saved at scratch
  `MF-MIirr-app-DRAFT.agda`. ⇒ **`MI-irr` is now 6/6, TOTAL.**
  - Two residual `MI-app-red`-implicit metas it first produced (the `{bw2,bB,btf,bΠ}`,
    same as `nat-MI ⊢app`'s own residuals at file lines 815/817/822) were then FIXED by
    passing those implicits explicitly on both `MI-app-red` calls. Verify on next run.

REMAINING for zero-axiom `consistency`:
1. **`subTI`** — postulated, and **BLOCKED, not merely unwritten**. ⚠ The earlier claim
   ("derivation fully mapped, now unblocked") is WRONG — see §4.2‴ (the pre/post-substitution
   bound conflict is forced by `envS`) and **§4.2⁹ (the Acc/"Option 1" fix is now tested and
   FAILS)**. `subTI` is not closable by re-plumbing the measure. Read §4.2⁹ before touching it.
2. **`funext` / `funextP`** — postulated; INTENDED to become module parameters
   (thread them, don't try to prove them). Do this LAST, once holes are gone. (§4.3)
3. **The ~63 file-wide unsolved `--prop` bound metas** — see §2.5. Needed ONLY for a
   truly batch-clean `EXIT 0`; the interactive workflow has always tolerated them.

Once 1 is defined, 2 is threaded, and 3 is filled, the file is axiom-free (modulo
funext) AND batch-clean, and `consistency` is the theorem.

--------------------------------------------------------------------------
## 2.5 ⚠ THE ~63 BATCH-MODE UNSOLVED METAS (reframe — read this)

**These are NOT downstream of any hole and NOT caused by the `⊢app` work.** Diffed
across the with-hole and without-hole offline runs: the metas at file lines 324, 427,
730–743, 804–822, 915–1012, 1024–1057 (and the `+62`-shifted tail after the new clause)
are **byte-identical** before/after closing the hole. They are a **persistent feature of
the whole file**.

WHAT THEY ARE: every one is a bare `_` in a **Prop-bound argument position** inside a
`where` block — e.g. `wkTI … (fst δ)(snd δ) _ _`, `nat-TI … (fst δ) _ _ _`,
`MI-vz-red … _ _ _`, `MI-vs-red … _ _ _ _`, `MI … (fst δ) _ _`, `envO … (fst δ) _`,
`nat-var-vz/​vs … _ _ _ _ _`. They live in `nat-var-vz`, `nat-var-vs`, `nat-MI ⊢app`,
`wkMI`, and the `MI-subst`-type sigs. The author left the sub-bounds as `_` expecting
unification to close them; Agda does NOT (it won't invent a Prop/`<` proof), so they
persist as unsolved.

WHY BATCH FAILS BUT INTERACTIVE "PASSES": `check-mf.sh` runs plain `agda --library-file
FILE`, which treats unsolved metas as an **error (nonzero exit)**. The handoff's earlier
"EXIT 0, 1 hole" was the **interactive `Cmd_load`** semantics, which merely *reports*
unsolved metas (yellow) and still returns success. Same file, same `--prop` pragma —
only the front-end's tolerance differs. So the file has, in strict terms, **never been
batch-clean**; these bounds have always been open.

TO FIX: each `_` must be replaced by an explicit bound term built from the clause's
incoming bounds (`b1`/`b2`/`bO`/`bd1`/`bd2`, or `δ`'s structure) via the size toolkit
`<+r` / `+mono<` / `sub-bnd<` / `<-inv` / `<≡` / `m≤m+n` / `n≤m+n` / `≤-trans` — exactly
the arithmetic already spelled out in the *main-body* bounds of each clause, just pushed
into the `where` helper calls. Signatures to derive against: `nat-TI`/`nat-MI`/
`nat-var-vz`/`nat-var-vs` (lines 335/377/385/391), `wkTI`, `MI`, `MI-vz-red`/`MI-vs-red`
(lines ~698/707), `envO` (333). Bounds are `szT …`/`szCon …`/`dsz …` sums `< n`/`< suc n`.

⚠ COST / METHOD: this is ~60 careful arithmetic derivations, and it is a POOR fit for
blind editing — a wrong term is a type ERROR (worse than a meta), and each offline batch
round is **~27 min** with NO in-harness feedback (600 s cap). Two realistic ways:
  - **(A) Do the §2 option-(B) MODULE SPLIT FIRST.** Breaking `wkTI←nat-TI` and
    `wkMI←nat-MI` (re-derive weakening directly) moves `nat-*`/`sub-*`/`MI-irr`/`subTI`
    into a DOWNSTREAM `.agdai`-cached module. Then filling these bounds becomes
    fast-iterable AND the compile ceiling is gone for good. This is the recommended
    enabler — it pays for itself here and for `subTI`/`funext`.
  - **(B) Grind blind in 27-min rounds.** Feasible but slow/error-prone; if taken, do it
    in small batches (one clause's `where` at a time) and dump the Agda meta types first
    (interactive `Cmd_metas`/`Cmd_all_goals` after `Cmd_load`) so each `_` is filled
    against its ACTUAL goal type, not a guessed one.
  RECOMMENDATION: (A). Don't start (B) blind without the meta-type dump.

NOTE for whoever resumes: decide whether a batch-clean `EXIT 0` is even the target, or
whether the interactive "0 real holes" is the accepted bar for this POC. If the latter,
tiers 1–2 (`subTI` + `funext`) alone finish the story and tier 3 is optional polish.

--------------------------------------------------------------------------
## 2. ⚠ THE PRACTICAL BLOCKER — read before doing anything

`NbEPDirDTTChMF.agda` type-checks in **~590–598 s**, right at the Claude Code
harness's **600 s Bash-timeout ceiling**. Measured 2026-07-25: termination check
is NOT the cost (`--no-termination-check` is also ~590 s); it's raw type-checking
of the mutual block. **Adding `MI-irr ⊢app` (~40–50 lines) will very likely push a
load over 600 s ⇒ the harness kills it and returns NO feedback.**

The block **cannot** be split into a cached module as-is: `wkTI`←`nat-TI`,
`wkMI`←`nat-MI`, and `subTI` are all referenced by the core `MI`, so
`nat-*`/`sub-*`/`MI-irr`/`subTI` are genuinely mutual with the core.

**So finish the last two pieces via ONE of:**
- **(A) Run Agda outside the harness** — a plain terminal `agda` with no 600 s cap.
  This is the fast path. Load command (from `bootstrap/poc/OCP0009`, with a
  library-file listing stdlib + `formal/Once.agda-lib` + `bootstrap/bootstrap.agda-lib`):
  ```
  F=NbEPDirDTTChMF.agda
  printf 'IOTCM "%s" None Indirect (Cmd_load "%s" [])\n' "$F" "$F" \
    | agda --interaction --library-file="$LIBF"
  ```
  (or `agda --library-file="$LIBF" "$F"` for a batch check). Write the clause,
  check here, iterate freely.
- **(B) Refactor to break `wkTI`←`nat-TI` and `wkMI`←`nat-MI`** (re-derive weakening
  DIRECTLY, not via `nat-TI` at `wk⊑`), so `nat-*`/`sub-*`/`MI-irr`/`subTI` move to a
  DOWNSTREAM module type-checked once → `.agdai` cache. Shrinks the WIP block by
  ~500 lines and makes iteration fast in-harness again. This is its own proof
  project (weakening naturality re-derivation), but it pays off for all future work.

Do NOT try to grind `⊢app` inside the 600 s harness — you will not get feedback.

--------------------------------------------------------------------------
## 3. Key techniques already used (reuse these)

- **`coe`-collapse family**: `coe-uip`/`coe2-uip`/`coe3-uip`/`coe4-uip`/`coe5-uip`
  (any two same-endpoint coe-paths of one element agree, via `uip'`). Both sides of
  a var/app equation are reduced to coe-stacks over a COMMON element, then collapsed.
- **`MI-vz-red`/`MI-vs-red`**: refl-lemmas packaging MI's `⊢vz`/`⊢vs` reductions so
  the `wkTI` proof becomes a NAMEABLE term (coe-proof metas can't be solved by coe
  injectivity). **`MI-app-red`**: same for MI's `⊢app` (= `coe(sym subTI)(f·u)`).
- **`MI-subst`**: strips the type-`subst` that `ren⊢`/`sub-⊢` put on var/app derivs.
- **`coe-π̂-gen pa qc f x'`**: distributes a coe through a π̂-function applied to an
  arg. ★ **PIN `qc`'s type explicitly** or coe-π̂-gen's `b'` leaks as an unsolved
  meta (this bit us before — `coe-π̂-app-arg` was the wrong tool and was deleted).
- **`nat-var` refactor**: casing the OPE `r`=keep/skip in a function's OWN `⊢vz`/`⊢vs`
  LHS stalls Agda's coverage checker on `⊢app` (`subTy(single u)B ≟ 𝔹`). FIX: extract
  var cases into mutually-recursive helpers that case `r` in isolation; the parent
  delegates. (This is how `nat-MI` was finished.) Also: order general-`wA` clauses
  (vz/vs/lam/app) BEFORE the `⊨𝔹`-specific tt/ff clauses.
- **`MI-irr` lam is SIMPLER than nat-MI lam**: `⇓` acts on the extended env
  definitionally, so `qc` is directly `TI-irr m wCo (⇓ρ, x)` (pinned) — no `goalenv`.

--------------------------------------------------------------------------
## 4. HOW TO DO the remaining pieces

### 4.1 `MI-irr ⊢app` — ✅ DONE this session (was the hole; structure below is what was written)

STATUS: written into the live file + scratch `MF-MIirr-app-DRAFT.agda`; type-checks
(no interaction meta, no type errors). Kept here as the record of the derivation.

Clause: `MI-irr (suc m) wA (⊢app (⊨Π wA' wB) tf tu) ρ bt' bw' bt bw`.
- `MI-app-red (suc m)` on the LHS-inner and `MI-app-red m` on the RHS give both as
  `coe (congÊl (sym subTI…)) (f · arg)`:
  - LHS = `coe (TI-irr wA) (coe (sym subTI_hi) (f_hi · arg_hi))`,
    `f_hi = MI (suc(suc m)) (⊨Π wA' wB) tf ρ`, `arg_hi = MI (suc m) wA' tu (⇓ρ)`,
    `subTI_hi = subTI (suc m) wA' wB wA tu ρ (λb→MI (suc m) wA' tu (⇓ρ) _ b) …`.
  - RHS = `coe (sym subTI_lo) (f_lo · arg_lo)`,
    `f_lo = MI (suc m) (⊨Π wA' wB) tf (⇓ρ)`, `arg_lo = MI m wA' tu (⇓ m (⇓ρ))`,
    `subTI_lo = subTI m wA' wB wA tu (⇓ρ) (λb→MI m wA' tu (⇓ m(⇓ρ)) _ b) …`.
- Relate `f_hi·arg_hi` to `f_lo·arg_lo`:
  - `f_lo = coe (congÊl (TI-irr (suc m) (⊨Π wA' wB) ρ)) f_hi`  [`MI-irr` recursion on `tf`],
  - `arg_lo = coe (congÊl (TI-irr m wA' (⇓ρ))) arg_hi`         [`MI-irr` recursion on `tu`],
  - `TI-irr(suc m)(⊨Π wA' wB)ρ = π̂-cong pa_a qc_a` with `pa_a = TI-irr m wA'(⇓ρ)`,
    `qc_a = λx→TI-irr m wB(⇓ρ,λ_→x)` (PIN it). Apply `coe-π̂-gen pa_a qc_a f_hi arg_lo`;
    `coe(sym(congÊl pa_a)) arg_lo = arg_hi` (coe-symˡ), so this yields
    `f_lo·arg_lo = coe P (f_hi·arg_hi)` for a concrete `P : Êl(TI(suc m)wB(⇓ρ,uf_hi)) ≡
    Êl(TI m wB(⇓ m(⇓ρ),uf_lo))` (a subst/coe — convert `subst`→`coe` via `subst≡coe`).
- Now BOTH sides are 2-coe stacks over `fu_hi := f_hi·arg_hi`
  (LHS: `sym subTI_hi` then `TI-irr wA`; RHS: `P` then `sym subTI_lo`), both from
  `Êl(TI(suc m)wB(⇓ρ,uf_hi))` to the goal `Êl(TI(suc m)wA(⇓ρ))`. Collapse with
  `coe-uip`/`coe2-uip` (subTI is opaque/postulated, but **coe only needs the
  endpoints** — no equation about subTI's proof is required). Then `sym (MI-app-red …)`.
- Bounds: mirror `nat-MI ⊢app`'s bound block (`q = <-inv bt`, `+mono<`/`m≤m+n`/`n≤m+n`
  with all args explicit — `+mono<` mis-infers otherwise). Template = the ~90-line
  `nat-MI ⊢app` clause, but SHORTER here (no `renTy-comm` `MI-subst`, `⇓` definitional).

--------------------------------------------------------------------------
## 4.2′ ⚠⚠ `subTI` — THE POSTULATE WAS **FALSE**.  READ THIS BEFORE ANYTHING ELSE.

**Found 2026-07-27.  `consistency` was VACUOUS until this was fixed.**

The postulate quantified over an ARBITRARY environment top:
```
(uf : (b : szT wC + szCon Δc < n) → Êl (TI n wC (⇓ n ρ) b))
→ TI (suc n) wS ρ bS ≡ TI n wB (⇓ n ρ , uf) bB
```
But `TI` READS the environment in its `⊨𝕀` clause:
`TI (suc n) (⊨𝕀 tb ⊨𝔹 wA wB) ρ b = Ifᵁ (MI n ⊨𝔹 tb (⇓ n ρ) …) … …`.
Take `C = 𝔹`, `B = 𝕀 (var vz) A₁ A₂` over `(Δc ▷ ⊨𝔹)`.  The RHS selects a different `Ifᵁ` branch
for different `uf` while the LHS is fixed ⇒ two contradictory instances ⇒ the postulate is
inhabitable only by an inconsistency, and everything downstream of it proved nothing.

**FIXED (working tree).**  All 8 call sites passed exactly `λ b → MI n wC tu (⇓ n ρ) btu b`, so the
parameter is now the BOUND `btu : dsz tu + szCon Δc < n` and the statement builds that env-top itself
(`--prop` ⇒ the choice of `btu` is irrelevant, callers pass whatever they hold).  Still a postulate,
but now a plausibly-true one.  DO NOT re-generalise it over `uf`.

### How to actually DISCHARGE it — direct mutual induction on (wS, wB)

The HANDOFF §4.2 route (`sub-TI` at `singleW wC tu`, then `TI-irr`, then `MI-irr`) **does not work**:
`sub-TI` needs the combined bound `bC : szSubW sσ + (szT wS + szCon Δc) < suc n`, i.e.
`dsz tu + (szT wS + szCon Δc) < suc n`, and MI's `⊢app` has only `dsz tu + szCon Δ < n` and
`szT wS + szCon Δ < suc n` SEPARATELY — their sum is not bounded.  Do not spend time there.

**What does work:** induct directly on the pair `(wS, wB)`, mutually with a term-level companion
`subMI` (needed only for the `⊨𝕀` condition).  The bounds close because:
- `sub-bnd< : sa < pa → pa + c < suc n → sa + c < n` DROPS one fuel level, so from
  `bS : szT wS + szCon Δc < suc n` and a structural `szT wS₁ < szT wS` you get `szT wS₁ + szCon Δc < n`.
  Same for `bB` via `szT𝕀l<`/`szT𝕀r<`/`szTΠl<`/`szTΠr<`.  Both bounds decrement structurally.
- The `⊨𝕀` case needs `dsz tb' + szCon Δc < n` for the SUBSTITUTED condition `tb'`.  That IS available:
  `wS = ⊨𝕀 tb' ⊨𝔹 wS₁ wS₂` is the wf of the POST-substitution type, and
  `szT wS = suc (dsz tb' + (szT wS₁ + szT wS₂))`, so `sub-bnd< (szT𝕀c< tb' wS₁ wS₂) bS` gives it.
  ⇒ the substitution size blow-up is already paid for by the caller's `bw`.  This is the crux, and it
  is why the direct induction closes where the `sub-TI` route does not.

Case plan (mirror `sub-TI` / `sub-TI-Π` / `sub-MI`, which are DONE and are the templates):
- `⊨𝔹` / `⊨⊥` : `refl` (TI is constant, env-independent).
- `⊨𝕀` : `Ifᵁ-cong` of (condition via `subMI` at `⊨𝔹`; note `subTI … ⊨𝔹 ⊨𝔹 … = refl` so the coe
  vanishes) and the two branches by recursion.  Template = `sub-TI`'s `𝕀` clause.
- `⊨Π` : `π̂-cong` + a `goalenv` coherence under the extended context.  Template = `sub-TI-Π`.
Estimated ~150–250 lines.  Write it in scratch and check OUTSIDE the harness; `--only-scope-checking`
(≈1.6 s) catches typos/unbound names before each ~25 min full run.

⚠ When lifting any bound arithmetic to top-level lemmas, keep Nat summands EXPLICIT — implicit ones
force Agda to invert `+` and leak unsolved metas + `UnsolvedConstraints` (measured: 66 → 99 metas).


### 4.2″ CORRECTION (loop iteration 3) — the direct induction does NOT close the Π CODOMAIN

§4.2′ above claimed the direct induction on (wS, wB) closes.  Measured in the dev stub, it closes
**𝔹, ⊥, the 𝕀 branches, and the Π DOMAIN** — all typecheck.  It does **not** close the Π codomain.

Reason: `sub-⊨ sσ (⊨Π wA wB) = ⊨Π (sub-⊨ sσ wA) (sub-⊨ (extW wA (sub-⊨ sσ wA) sσ) wB)`.
The domain stays a `singleW` substitution (so the recursive subTI call works — verified), but the
CODOMAIN's substitution is `extW wB1 wS1 (singleW wC tu)`.  subTI is stated for `single u` only, so it
cannot recurse there.  subTI must be generalised to an arbitrary `SubW` — i.e. it must BE `sub-TI`.

**What was learned that is still useful:** the combined bound
`bTU : dsz tu + (szT wB + szCon (Δc ▷ wC)) < n` over the PRE-substitution type is derivable at the
MI ⊢app call site (lemma `appTUcomb`, proven in the dev stub) and decrements via `combStep`.
Generalised to SubW that reads `szSubW sσ + (szT wA + szCon Γc) < n` — which is what `sub-TI`'s
existing `bC` should have been.  `sub-TI`'s current `bC` measures the POST-substitution `szT wS`,
which is NOT a sub-sum of anything MI holds; that is the original blocker.

⚠ REMAINING PROBLEM even after that change: the `TI-irr` step still needs `bS' : szT wS + szCon Δc < n`
while MI's ⊢app only gives `< suc n`.  subTI's statement spans fuel (suc n) on the left and n on the
right; sub-TI is same-fuel.  Bridging them needs either a tighter bS at the call site or a restatement.
THIS IS AN OPEN DESIGN QUESTION — do not assume it is mechanical.

Dev-stub checkpoints (untracked): scratchpad/Dev-base-cases-closed.agda,
Dev-iota-branches-closed.agda, Dev-pi-domain-closed.agda.  Dev stub checks in ~5 s.


### 4.2‴ PROBE RESULT — the pre-substitution bound CANNOT be adopted.  `envS` forbids it.

Probed in a dedicated stub (sub-TI / sub-TI-Π kept REAL, everything else postulated; checks in ~6 s;
saved as scratchpad/Probe-pre-subst-bound-FAILS.agda).  Switching sub-TI's
`bC : szSubW sσ + (szT wS + szCon Δc) < n`  (post-substitution)
to `bC : szSubW sσ + (szT wA + szCon Γc) < n`  (pre-substitution) fails — irreducibly.

**Why.**  Look at `envS`'s own extW clause:
```
envS n (extW {Δc = Δc} wA wSA sσ) (δ , xf) bE =
  envS n sσ δ bE' , (λ b → coe (congÊl (sub-TI n sσ wA wSA δ bS' b bE' bE)) (xf bS'))
```
`envS` passes its OWN `bE : szSubW (extW wA wSA sσ) + szCon (Δc ▷ wSA) < n` as sub-TI's `bC`.
And `szCon (Δc ▷ wSA) = szT wSA + szCon Δc`, so that bound IS
`szSubW sσ + (szT wSA + szCon Δc) < n` — literally sub-TI's post-substitution `bC`.
**The post-substitution measure is not a design choice; it is forced by envS.**  envS lives entirely
on the Δc (substituted) side and never sees Γc or szT wA, so it cannot supply a Γc-side bound.

**Consequence — this is a genuine dead end, not a gap to grind:**
- MI's ⊢app can supply ONLY the pre-substitution combined bound (`appTUcomb`, proven).
- sub-TI structurally requires the post-substitution one (forced by envS, above).
- The two are incompatible; substitution can grow types so szCon Δc ≰ szCon Γc under extW.

**Closing `consistency` therefore needs a MEASURE-LEVEL DESIGN CHANGE, not more proof-writing.**
Candidate directions (a decision for the author, not mechanical):
  (a) change `CI`/`envS` so the environment carries a bound sub-TI can consume from either side;
  (b) abandon this fuel sum for a different well-founded measure;
  (c) strengthen MI's ⊢app invariant (changes MI's signature and every clause).
Until one is chosen, `subTI` stays a postulate and **`consistency` is NOT proven**.


### 4.2⁗ SPIKE RESULT — the CORE is fuel-free; the NATURALITY layer is NOT.

Two spikes, both in-tree, both ~0.5 s:

**SpikeWF.agda — CLEAN (exit 0, `--prop` only, no pragmas, large elimination KEPT).**
CI/TI/MI are definable with **no fuel and no bounds**, and terminate STRUCTURALLY (no Acc needed).
Three changes were required:
  1. `CI` must be an INDUCTIVE-RECURSIVE datatype, not a recursive function.  As a function
     `CI (Δ ▷ wA)` must CALL `TI wA` at measure `szT wA + szCon Δ` = its own measure
     `szCon (Δ ▷ wA)` — no decrease, unorderable.  As an IR datatype it merely MENTIONS TI.
  2. Bind sub-derivations as VARIABLES, don't re-construct them.  The real file matches
     `⊨𝕀 tb ⊨𝔹 wA wB` then calls `MI … ⊨𝔹 tb …`; that `⊨𝔹` is a fresh term, not a subterm.
     Use `⊨𝕀 tb w𝔹 wA wB` + `MI w𝔹 tb …`.  Costs the reduction `TI ⊨𝔹 ρ = 𝔹̂`, recovered by a
     one-line `TI-𝔹` lemma mutual with TI.
  3. `⊢lam` must MATCH `⊨-unique wA' wA` (`with … | refl`), not transport along it — an opaque
     transport is never structurally smaller.
⇒ With fuel gone: no `⇓`, no `TI-irr`, no `MI-irr`, no coe-stacks along them, no szT/dsz/szCon
  measure, no bound towers, no `+`-inversion trap.  And `subTI`'s statement becomes BOUND-FREE:
  `TI wS ρ ≡ TI wB (ρ ∷ᴱ MI wC tu ρ)`.  (wkTI/subTI are still POSTULATED there — the spike tested
  definability + termination of the core, NOT those proofs.)

**SpikeWFNat.agda — FAILS.**  Adding envO/nat-TI/nat-MI and deriving wkTI from nat-TI reintroduces
termination failure.  Four problematic calls; the root cause is
    `TI (ren⊨ (wk⊑ Δc wC) wA₀) (ρ ∷ᴱ v)`   (in wkTI's own SIGNATURE)
`ren⊨ r wA` is a FUNCTION APPLICATION, not a subterm, so any statement of the form
`TI (ren⊨ r wA) δ ≡ …` defeats the structural checker.  **This is exactly the obstruction fuel was
introduced to solve (see SpikeFuel).**  Note the core terminated only while nat-TI/wkTI were
postulated; the moment their statements mention `TI (ren⊨ …)`, it breaks.

**ARCHITECTURAL IMPLICATION.** The core can be fuel-free ONLY IF `wkTI` does not route through
`nat-TI`.  That is HANDOFF §2 option (B) — "re-derive weakening DIRECTLY, not via nat-TI at wk⊑" —
previously filed as optional.  It is now LOAD-BEARING: it is what would let the core sit in a
fuel-free, bound-free, transport-light module, with nat-TI/nat-MI moved DOWNSTREAM (own measure,
own module, `.agdai`-cached).  Worth checking whether wkTI stated as
`(wA₀ : Δc ⊨ A) → TI (ren⊨ (wk⊑ Δc wC) wA₀) (ρ ∷ᴱ v) ≡ TI wA₀ ρ` and proven by induction on wA₀
lets `ren⊨` REDUCE at each constructor (⊨𝔹/⊨Π/⊨𝕀), recovering structurality.  UNTESTED.

⚠ METHOD NOTE (cost me a false positive): Agda does **not** termination-check `where`-bindings that
the body never uses.  A spike that parks recursive calls in unused where-blocks under `{!!}` bodies
proves NOTHING.  Route them through `force : A → B → B` (`force _ b = b`) so the body uses them, and
validate with a deliberate non-terminating control before trusting any such result.


### 4.2⁵ THREE naturality formulations tested — ALL fail.  Fuel-removal does NOT unlock consistency.

| spike | naturality formulation | result |
|---|---|---|
| SpikeWF     | nat-TI/wkTI **postulated** (core only) | **CLEAN, exit 0** |
| SpikeWFNat  | nat-TI real, stock OPE `keep r wA : … ⊑[ keep o ] (Θc ▷ ren⊨ r wA)` | fails |
| SpikeWFNat2 | renamed wf as an independent VARIABLE `wA'` instead of `ren⊨ r wA` | fails |
| SpikeWFNat3 | LOCAL OPE whose `keep'` carries the target wf as a **field** | fails |

SpikeWFNat3 DID kill the `TI (ren⊨ r wA) δ` culprit — so the `ren⊨`-in-the-index problem in
`NbEPDirDTTCh`'s OPE is real and fixable.  But it is not the only blocker.  Residual calls:
`TI wA' δ` and `envO (wk⊑' Δc wC) (ρ ∷ᴱ v)` (both from nat-TI's own statement), plus
`MI w𝔹 tb ρ` and `TI wB (ρ ∷ᴱ x)` — **and those last two are CLEAN in SpikeWF standalone.**

⇒ THE REAL FINDING: the core terminates structurally *in isolation*; merging the naturality layer
into the same mutual block destroys the ordering, including for calls that were previously fine.
So the layers must be SEPARATED — which requires `MI` not to depend on `wkTI`, i.e. HANDOFF §2
option (B) again, now confirmed as the hinge from a second direction.

**Net:** fuel-removal is a large win for the CORE (no ⇓/TI-irr/MI-irr, no bounds, bound-free subTI
statement — see §4.2⁗) but it does NOT by itself make `consistency` reachable.  A hybrid is implied:
fuel-free structural core + a downstream, separately-measured naturality module.  Whether MI can be
freed of wkTI is the open question, and it is the same question §4.2‴ and §4.2⁗ both landed on.


### 4.2⁶ HYBRID SPIKE (SpikeHybrid.agda) — fuel-free core + fuel ONLY on nat-TI.  Also fails.

Setup: CI/TI/MI/envO/wkTI fuel-free with BOUND-FREE statements; `nat-TI` alone carries fuel, its
CONCLUSION still bound-free (`TI wA' δ ≡ TI wA (envO r δ)`), callers supplying fuel from their own
argument's measure (`szT wA₀ < suc (szT wA₀)`) rather than an external budget.

**Result: nat-TI's own fuel recursion IS accepted** — nat-TI does NOT appear in the failing set.
The failing functions are `TI, MI, wkTI, envO`, on this cycle:

    MI  --(⊢vz/⊢vs)-->  wkTI  --(proof uses nat-TI, whose conclusion mentions envO)-->  envO
        --(keep clause coerces along nat-TI, whose type mentions TI (ren⊨ r wA))-->  TI  -->  MI

No argument decreases anywhere around it.  Putting fuel on nat-TI does not help because the cycle
does not run through nat-TI's RECURSION — it runs through nat-TI's TYPE (which mentions envO and
TI (ren⊨ …)) and back into TI/MI.

**CONCLUSION for the whole line of investigation (§4.2⁗ / 4.2⁵ / 4.2⁶):**
A measure is required on the ENTIRE TI/MI/envO/wkTI cycle — which is exactly what the current fuel
design provides.  Fuel is NOT removable while `MI` depends on `wkTI` and `wkTI` is derived from
`nat-TI`.  The single change that would unlock it is HANDOFF §2 option (B): prove `wkTI` DIRECTLY,
without nat-TI/envO.  Every route tried this session converges on that one item:
  - §4.2‴  envS forces the post-substitution measure          → need MI free of the envS route
  - §4.2⁗  ren⊨ in the OPE index defeats structurality        → need wkTI free of nat-TI
  - §4.2⁵  merging naturality into the core block breaks it   → need the layers separated
  - §4.2⁶  fuel on nat-TI alone does not cut the cycle        → need wkTI free of nat-TI
⚠ UNTESTED and the obvious next spike: can `wkTI` be proven by induction on wA₀ alone?  The ⊨Π case
needs weakening UNDER a binder, which is what pushed the original design to OPEs — so this may need
a "weakening by an arbitrary context suffix" formulation that is structural where OPEs are not.


### 4.2⁷ SpikeSyn — recursion on the type SYNTAX.  Fails, but tells us WHY fuel is NECESSARY.

Idea: §4.2⁗ blamed `ren⊨ r wA` (opaque on DERIVATIONS).  `renTy ⌜o⌝ A` on SYNTAX does reduce
structurally, so state nat-TI with `A : Ty Γ` explicit and recurse on it.

Result: still fails, but the obstruction MOVED, and the new one is informative:

    nat-TI's CONCLUSION mentions  envO r δ.
    Recursing under a Π binder instantiates it at  envO (keep r wD) (δ ∷ᴱ x)
    — envO applied to a strictly LARGER OPE.

So as the type SHRINKS (A → B), the OPE GROWS (r → keep r wD) and the environment grows with it.
envO recurses on the OPE; nat-TI recurses on the syntax.  Neither order works alone and Agda's
structural checker cannot combine them.

**⇒ A NUMERIC MEASURE ON THE NATURALITY LAYER IS NECESSARY, NOT INCIDENTAL.**  This is a lexicographic
(type ↓, OPE ↑) situation; a Nat measure can express it, structural recursion cannot.  The original
fuel decision (SpikeFuel) was CORRECT for this layer.

**SETTLED ARCHITECTURE (from §4.2⁗ + §4.2⁶ + this):**
  - core CI/TI/MI: fuel-free and structural — PROVEN (SpikeWF.agda, exit 0, 𝕀 kept).
  - naturality envO/nat-TI/nat-MI: REQUIRES a measure — now shown necessary, not a design accident.
  - therefore the two MUST be separate mutual blocks / modules.
  - the ONLY thing preventing that split is `MI`'s ⊢vz/⊢vs dependence on `wkTI`.

That single edge is now the whole problem.  Note §4.2⁷ also rules out the "prove wkTI directly by
induction on wA₀" idea: its ⊨Π case needs wC inserted BELOW the binder, i.e. arbitrary-position
insertion, i.e. OPEs — so it inherits exactly this obstruction.


### 4.2⁸ OPTION 1 (Acc + bound-free wrappers) — SOLVES subTI stateability, NOT the wkTI cycle.

Risks pre-cleared in scratchpad/AccRisk.agda (exit 0):
  - `accIrr : ∀ {n}(a b : Acc n) → a ≡ b` is PROVABLE via funext (already threaded).  ✓
  - `wfAcc n = acc (go n)` — top clause does NOT match n, so it REDUCES on open terms.  ✓
  - open-term `f (suc n) ≡ suc (f n)` by plain `refl` FAILS (accessibility proofs differ), but is
    recovered in ONE LINE: `cong (λ a → suc (f-aux n a)) (accIrr _ _)`.  ⇒ each `*-red` lemma goes
    from `= refl` to a one-line accIrr cong.  Bounded, mechanical cost.  ✓
  - ⚠ Acc's order must be **Set**-valued, not Prop (SplitInProp: cannot split a Prop into Set).
    Fine — the wrapper always supplies canonical `wfAcc`, so definitional bound-irrelevance is no
    longer needed at the type level.  This means `--prop` is not required for the BOUNDS any more.

SpikeAcc.agda (in-tree):
  - with `wkTI` POSTULATED (bound-free): whole block CI/TI/MI/envO/nat-TI/nat-TI-aux TERMINATES,
    control-validated (an injected non-decreasing self-call IS caught).  ✓
  - with `wkTI` REAL (derived from nat-TI): FAILS with the §4.2⁶ cycle, verbatim —
    `MI → wkTI → (nat-TI's TYPE mentions envO) → envO → (…mentions TI (ren⊨ r wA)) → TI → MI`.
    `nat-TI-aux` is NOT in the failing set: its Acc recursion is fine.  The Acc does not help because
    the cycle runs through nat-TI's TYPE, not its recursion.

**THE TWO PROBLEMS ARE ORTHOGONAL — this is the useful decomposition:**
  (P1) subTI is unstateable because a bound sits in TI's TYPE.
       → SOLVED by Option 1 (bound-free wrappers).  Independent of P2.
  (P2) the MI→wkTI→envO→TI→MI cycle needs a measure spanning ALL of TI/MI/envO/wkTI.
       → the CURRENT fuel design already provides exactly this.  Its only mistake was P1.

**⇒ RECOMMENDED NEXT STEP (untested, but every piece is now evidenced):**
Do NOT remove the measure.  Transform the EXISTING file mechanically:
  replace `(n : Nat)` + the bound arguments on CI/TI/MI/envO/wkTI/nat-*/sub-*/subTI
  with a single INTERNAL `Acc` on the existing szT/dsz/szCon measure, and expose BOUND-FREE wrappers.
This keeps every proven proof's structure (nat-MI, sub-MI, MI-irr all survive — only bound plumbing
changes), kills the 67 bound towers / + inversion trap / ~66 §2.5 metas, and makes subTI STATEABLE,
which is the one thing that blocked it.  SpikeAcc only put Acc on nat-TI; the full transformation
puts it on the whole cycle, which is what P2 needs.

### 4.2⁹ SpikeAcc2 — OPTION 1 IS TESTED AND **DEAD**.  Do not attempt the Acc transform.

§4.2⁸ recommended the full Acc transform on the argument that "SpikeAcc only put Acc on nat-TI;
the full transformation puts it on the WHOLE cycle, which is what P2 needs."  **That claim is now
tested and FALSE.**  `SpikeAcc2.agda` (in-tree, checks in ~1 s) implements exactly the recommended
design — Acc on ALL of CI/TI/MI/envO/wkTI/nat-TI, each on its own szT/dsz/szCon measure, with
bound-free wrappers — and the termination checker rejects it.  Control validated (`bad` IS flagged).

Failing set: `TI, MI, envO, TIa, MIa, envOa, wkTIa`.  (`nat-TIa` is again NOT in it — its own Acc
recursion is fine, exactly as in SpikeAcc.)  **Two INDEPENDENT obstructions:**

**(A) NEW — the bound-free wrapper is itself a non-decreasing call inside the block.**
```
TI   wA ρ = TIa   wA ρ (wfAcc _)      -- flagged
MI wA td ρ = MIa wA td ρ (wfAcc _)    -- flagged
envO   r δ = envOa r δ (wfAcc _)      -- flagged
```
`wfAcc _` is FRESH, so it is smaller than nothing.  The wrapper cannot be moved out of the mutual
block, because `CI`'s IR constructor `_∷ᴱ_ : (ρ : CI Δ) → Êl (TI wA ρ) → CI (Δ ▷ wA)` must mention
it, and every statement mentions it.  This kills the "bound-free wrapper" mechanism as such — the
one thing Option 1 was for.  (Writing `TIa wA ρ (wfAcc _)` inline instead changes nothing: same term.)

**(B) The §4.2⁶ type-level cycle SURVIVES, untouched — third independent confirmation.**
`nat-TIa`'s CONCLUSION is `TI wA' δ ≡ TI wA (envO r δ)`, and the flagged calls are
`TI (ren⊨ r wA) δ` and `envO (wk⊑ Δc wC) (ρ ∷ᴱ v)` — **in the TYPE**.  No amount of Acc plumbing
reaches a call that lives in a signature.  §4.2⁸'s "P2 is already solved by the measure" was the
mis-diagnosis: the measure never was the issue on this edge.

**(C) Q2 confirmed as a bonus — losing `--prop` bound-irrelevance is not "mechanical".**
Acc must be Set-valued (SplitInProp), so `TIa wA ρ h1` / `TIa wA ρ h2` are no longer the SAME TERM
as they are under `--prop`.  Every place that relied on that now needs an `accIrr` bridge, and
`cong (TIa wA ρ) (accIrr …)` is a PARTIAL APPLICATION of a mutual-block function — Agda counts it
as a call (`TI wA` is flagged at the `envO-bridge`).  §4.2⁸ costed these as "a one-line accIrr cong,
bounded, mechanical cost"; they are in fact additional non-decreasing edges.  The current file's
definitional Prop-irrelevance is load-bearing, not incidental.

**⇒ NET.  Every route now converges on ONE edge: `MI`'s ⊢vz/⊢vs dependence on `wkTI`.**
  §4.2‴ envS forces the post-substitution measure   → need MI free of the envS route
  §4.2⁗ ren⊨ in the OPE index defeats structurality → need wkTI free of nat-TI
  §4.2⁵ merging naturality into the core breaks it  → need the layers separated
  §4.2⁶ fuel on nat-TI alone does not cut the cycle → need wkTI free of nat-TI
  §4.2⁷ (type ↓, OPE ↑) needs a numeric measure     → measure is necessary, not the blocker
  §4.2⁸ Acc solves P1 only                          → mis-diagnosed P2 as solved
  §4.2⁹ Acc on the WHOLE cycle still fails          → **the measure was never the issue**
`subTI` is NOT closable by re-plumbing the measure.  The only untried direction is to remove the
`MI → wkTI` edge itself — i.e. restate `CI` so `⊢vz`/`⊢vs` need NO semantic weakening lemma (store
the top value already at the weakened wf, so the variable clauses are projections).  That is a
CORE REDESIGN and is unscoped/unproven; §4.2⁷ separately rules out the easier "prove wkTI directly
by induction on wA₀" (its ⊨Π case needs arbitrary-position insertion, i.e. OPEs again).

### 4.2¹⁰ SpikeCIR — **THE EDGE IS BREAKABLE.**  Type-agnostic `MI` kills `MI → wkTI`.

`SpikeCIR.agda` (in-tree, ~0.4 s).  First positive result in this whole line.  Two redesigns:

**V1 "store the value already at the weakened wf" — REFUTED ON PAPER, do not attempt.**
The slot would need type `Êl (TI wR (ρ ∷ᴱ v))`: the constructor's own field type mentions the
constructor's own RESULT.  That is not induction-recursion (later fields may mention EARLIER
fields and the recursive function — never the result being built); it is genuine self-reference.
Storing the weakening EQUATION as a field fails identically (`TI wR (ρ ∷ᴱ v) ≡ TI wA ρ` mentions
`ρ ∷ᴱ v` too).  V1 is not a redesign that exists.

**V2 "make `MI` TYPE-AGNOSTIC" — the core CHECKS AND TERMINATES.**  `MI : Δ ⊢ t ∷ A → CI Δ → Val`
with `Val = Σ Û Êl` (plus `⊤̂` for junk).  MI's type never mentions TI.  Verified:
  - `CI` is a **PLAIN datatype** — no induction-recursion needed, because it stores untyped
    `Val`s and its constructor never mentions `TI`.
  - `TI`'s 𝕀 clause reads the condition through `asBool : Val → 𝟚` (matches the carrier,
    defaults on mismatch) — so **TI does not depend on any soundness invariant**.
  - `MI ⊢vz`/`⊢vs` are **PURE PROJECTIONS** — no coercion, no `wkTI`.  ⊢lam is definitional
    (carrier and element come from the SAME recursive call).  ⊢tt/⊢ff trivial.
  - Whole core type-checks with **NO termination errors**.

**⇒ THE PAYOFF (this is the part that matters).**  Because `CI` is untyped, `envO` is a pure list
operation — `envO (keep r wA) (δ ∷ᴱ x) = envO r δ ∷ᴱ x`, with **no nat-TI coercion**.  That is the
`envO → nat-TI` edge whose existence made the §4.2⁶ cycle `MI → wkTI → envO → TI → MI` close.
**It does not exist in V2.**  `envO`, `nat-TI`, `wkTI` all sit strictly BELOW a finished core;
`nat-TI`'s 𝔹/⊥ cases are literally `refl` (verified in-file).  The layer separation that §4.2⁵/⁶/⁷
all demanded is achieved.

**REMAINING: exactly ONE clause — `MI ⊢app`.**  Holding `MI tf ρ` and `MI tu ρ` as untyped `Val`s,
applying one to the other needs the argument at `Êl a` where `π̂ a b` is the function's carrier,
but it sits at `Êl (fst (MI tu ρ))`.  Two options, both concrete:

  (a) **Mutual soundness `MI-ty : fst (MI td ρ w) ≡ TI wA ρ w`.**  ✅ **TESTED — IT ORDERS.**
      See §4.2¹¹.
  (b) **Untyped function space `π̂ : (a : Û) → (Val → Û) → Û`, `Êl (π̂ a b) = (v : Val) → Êl (b v)`.**
      Then ⊢app is `(b (MI tu ρ) , f (MI tu ρ))` — definitionally correct, NO soundness lemma, and
      **no `subTI` either**: the result carrier is computed from the SEMANTIC argument, not from
      `subTy (single u) B`.  That would retire the actual blocker outright.
      ⚠ BLOCKED AS STATED: `Val = Σ Û Êl`, so `(Val → Û)` puts `Û` in a NEGATIVE position and
      strict positivity fails.  The escape is a Tarski-style universe of SYNTACTIC codes (closures
      over syntax) where the codomain is a code rather than a meta-level function.  That is a real
      redesign, but it is the first route that dissolves `subTI` instead of fighting it.

### 4.2¹¹ SpikeCIRa — ROUTE (a) ORDERS.  `MI ⊢app` IS CLOSED.  This is the live architecture.

`SpikeCIRa.agda` (in-tree, ~0.7 s).  Route (a) of §4.2¹⁰ implemented.  **The only TerminationIssue
reported is the `bad` CONTROL** — `TI`, `MI` and `MI-ty` all order.

Shape that works:
  - `CI` stays **PLAIN** (untyped `Val` slots).  Well-formedness is carried SEPARATELY as a
    datatype `CIwf : CI Δ → Set`, whose `_∷w_` field is `fst v ≡ TI wA ρ w` (legitimate IR — the
    later field mentions the EARLIER field `w`).
    ⚠ Do NOT bake the proof into `CI` instead: `envO`'s keep clause would then need
    `fst x ≡ TI wA (envO r δ)` from `fst x ≡ TI (ren⊨ r wA) δ`, i.e. **nat-TI**, resurrecting the
    very `envO → nat-TI` edge §4.2¹⁰ removed.  Tested and rejected on those grounds.
  - `TI`/`MI` both take the `CIwf`; `TI`'s 𝕀 clause still reads the condition via `asBool`.
  - `MI ⊢vz`/`⊢vs` remain **pure projections**; `envO` remains a **pure list operation**.
  - `MI ⊢app` is **CLOSED, no hole**, by coercing along `MI-ty` at both `tf` and `tu`.

⚠ TWO METHOD TRAPS, both cost a round here and both recur in the real file:
  1. `ex`/`ef` must be written **INLINE**, not `where`-bound.  A where-bound value whose TYPE is a
     function type becomes an auxiliary definition, and applying it (`ef ex`) counts as a CALL with
     no descent — it alone failed the whole SCC.  (The live file carries the same warning at
     ~line 1206.)  Inlining fixed it outright.
  2. The first failure listed `TI, MI` and NOT `MI-ty`; that was the SCC failing as a unit from a
     single bad call.  Do not read the failing-function list as a diagnosis — read the
     "Problematic calls" list.

**STATE OF THE ARCHITECTURE:**
  VERIFIED — the block {`TI`, `MI`, `MI-ty`} + `CIwf` orders, with `wkTI` postulated BOUND-FREE.
  OPEN (in order):
   1. **Test B** — put the REAL `wkTI`/`nat-TI` back.  `wkTI` is consumed by `MI-ty`'s ⊢vz case, so
      it is mutual with the block; `nat-TI` needs `envO` (pure ✓) and `TI`.  This is the next gate
      and it is cheap.
   2. `MI-ty`'s other five cases are holes.  ⚠ Its ⊢app case's obligation IS `subTI`:
      `TI wB (ρ ∷ᴱ (TI wA ρ w , ex)) (w ∷w refl) ≡ TI wS ρ w`.
      **`subTI` is NOT retired by route (a) — it MOVES from MI's definition into MI-ty's proof.**
      What HAS changed is decisive though: it is now stated **BOUND-FREE**, so §4.2‴'s dead end
      (envS forcing a post-substitution bound MI's ⊢app cannot supply) *cannot even be stated*.
      P1 is solved — by a different route than Option 1 attempted.  §4.2″'s separate obligation
      (the Π codomain needs generalising to an arbitrary `SubW`, i.e. subTI must BE sub-TI) is
      still real and still unproven.
   3. `consistency` itself is not attempted in any spike.

### 4.2¹² SpikeCIRb (TEST B) — the real wkTI does NOT order.  The blocker is now ONE edge: `MI → MI-ty`.

`SpikeCIRb.agda` (in-tree, ~1 s).  Real `wkTI`/`nat-TI`/`nat-MI`/`envO-wf` put back.
Control validated.  Failing set: **`TI, MI, MI-ty, wkTI`**.

**`envO-wf`, `nat-TI` and `nat-MI` are NOT in the failing set** — the naturality layer orders on
its own recursion.  The failure is entirely the feedback path.  Problematic calls trace:

    TI --(𝕀: asBool (MI tb ρ w))--> MI --(⊢app)--> MI-ty --(⊢vz)--> wkTI
       --(calls nat-TI at wk⊑, whose TYPE is `TI (ren⊨ (wk⊑ Δc wC) wA₀) …`)--> TI

`ren⊨` in the index is §4.2⁗'s obstruction verbatim, and §4.2⁷ already proved this
(type ↓, OPE ↑) situation REQUIRES a numeric measure.  So Test B failing is not a surprise —
it is the predicted outcome, now confirmed in the new architecture.

**THE USEFUL PART — the layering is one edge away from stratified.**  Nothing except `MI ⊢app`
forces a cycle.  The natural stratification is:

    Layer 1  CI, envO                      pure; no proofs        ✅ verified
    Layer 2  CIwf, TI, MI                  ⊢vz/⊢vs projections    ✅ verified (SpikeCIR)
    Layer 3  envO-wf, nat-TI, nat-MI, wkTI orders on its own      ✅ verified (this file)
    Layer 4  MI-ty, subTI                  uses wkTI              — would be downstream

The ONLY back-edge is `MI ⊢app → MI-ty` (Layer 2 reaching into Layer 4).  Remove it and the whole
thing stratifies into `.agdai`-cached modules with no cycle and no measure anywhere.

**⇒ EVERYTHING NOW REDUCES TO: can `MI ⊢app` be defined without the soundness invariant?**
That is exactly route (b) of §4.2¹⁰ — untyped function space `π̂ : (a : Û) → (Val → Û) → Û`,
`Êl (π̂ a b) = (v : Val) → Êl (b v)`, making ⊢app `(b (MI tu ρ) , f (MI tu ρ))` with no coercion.
Blocked as stated by strict positivity (`Val = Σ Û Êl` puts `Û` negative).  **The escape — and the
next thing to spike — is a Tarski-style universe of SYNTACTIC codes**, where π̂'s codomain is a
code plus an environment (a closure) rather than a meta-level function, restoring positivity.

⚠ HONEST STATUS: route (a) alone does NOT reach `consistency`.  Its cycle needs a measure, and a
measure on `TI` reintroduces P1 (bounds in every statement mentioning TI) — which is precisely
what Option 1 failed to avoid (§4.2⁹).  Route (a) is a genuine advance (P1 dissolved, layers 1-3
verified) but it is NOT sufficient on its own.  Route (b) is the load-bearing unknown.

### 4.2¹³ SpikeErase — **THE GOAL IS CLOSED**, by a route that is not on this list at all.

`SpikeErase.agda` (in-tree, **`--safe`, zero postulates, zero holes, zero TERMINATING,
0.44 s, 130 lines**) proves

```agda
consistency : ∀ {t} → ε ⊢ t ∷ ⊥̇ → Empty
```

for the raw Church calculus. Everything §4.2′–§4.2¹² fought is simply absent.

**The observation that unlocks it.** `NbEPDirDTTCh`'s `_⊢_∷_` has SIX rules —
`⊢vz ⊢vs ⊢tt ⊢ff ⊢lam ⊢app` — and **no conversion rule and no 𝕀 eliminator**. So a
syntactic type NEVER has to compute for a derivation to exist, and the carrier of a
type can be read off the type SYNTAX alone, with no environment:

```agda
⟦_⟧T : Ty Γ → Set                 -- term-BLIND
⟦ 𝕀 t A B ⟧T = ⟦ A ⟧T ⊎ ⟦ B ⟧T    -- ignores t
```

`wkTI` and `subTI` — the two obligations that consumed this entire file — become
`ren-⟦⟧` and `sub-⟦⟧`: **4-case structural inductions on the TYPE**, because ⟦_⟧T
ignores terms. No environment appears in their statements, hence no `CI`, no `envO`,
no `CIwf`, no OPE naturality, no `Û`/`Êl` (so no strict positivity, no large
elimination), no fuel, no bounds, no `--prop`. And `MI ⊢app` needs NO soundness
invariant, so **the `MI → MI-ty` back-edge of §4.2¹² does not exist.**

Layer 2 (`⟨_⟩T : (wA : Δ ⊨ A) → ⟦Δ⟧C → ⟦A⟧T → Set`, also in the file and checking) is
the honest dependency as a PREDICATE over the already-fixed carrier: at `⊨𝕀` it
demands the injection tag agree with `⟦tb⟧M γ`. Layer 2 calls Layer 1; Layer 1 never
calls Layer 2 — so the stratification §4.2¹² wanted is obtained BY CONSTRUCTION rather
than by fighting the termination checker. Its fundamental theorem is not attempted
(that would break `--safe`).

⚠ **TWO HONEST CAVEATS — read both before calling raw-M3c finished.**

1. **Layer 1 erases the dependency.** It proves consistency, not faithfulness of the
   𝕀 mechanism. Layer 2 is where that content lives, and its `wkTI`/`subTI` analogues
   are still real work — but they are implications between PREDICATES over carriers
   already fixed by Layer 1, so if they need a measure it sits on a proof and cannot
   propagate. That is exactly the P1 property §4.2⁸/§4.2⁹ tried and failed to buy.
2. **The raw calculus has no `bif`.** With no 𝕀 introduction rule and no conversion,
   nothing can be introduced at an 𝕀 type except by assumption — the 𝕀 types are
   INERT. So raw-M3c as written has no dependent content at term level to be faithful
   TO. `NbEPDirDTTSem` has `bif`; this calculus does not. **Adding `bif` to `_⊢_∷_` is
   what would make faithfulness non-trivial**, and the `⊎` carrier plus `⟨_⟩T` were
   both written to accommodate it.

**⇒ THE ERASURE BOUNDARY, stated precisely — it is `SN⁺`'s obstruction from the other
side.** Erasure WORKS here because there is no conversion rule. Erasure FAILS for the
committed kernel (`NbEPDirDBSNU`, dHoTT-37): there `⊢conv` + `El`-decoding make the
erased simple type **conversion-unstable** — a neutral code `app (lam t) u : U` can
reduce to a real code `⌜Π⌝ …`, so `El` of the redex and of its reduct erase to `base`
vs `⇒`. Same principle, opposite verdicts, and the difference is exactly the presence
of a conversion rule. **Do not attempt an erasure shortcut for term SN — it is
refuted, not merely unattempted.**

**DISPOSITION OF THIS FILE.** `NbEPDirDTTChMF.agda` is hereby an OBSTRUCTION RECORD,
not WIP. It cannot be closed `--safe` in any meaningful sense: `subTI` is postulated
and §4.2‴+§4.2⁹ show it is not closable in this architecture; the ~66 unsolved
Prop-bound metas mean it has never been batch-clean; `funext`/`funextP` remain axioms.
The theorem it existed to prove is closed elsewhere, at 130 lines instead of 1438.
See `PLAN-dHoTT-kernel.md` §5. Do not resume the grind.

--------------------------------------------------------------------------
### 4.2 `subTI` (postulate → definition) — after `MI-irr` is done
⚠ SUPERSEDED BY §4.2‴ AND §4.2⁹ — the derivation sketch below does NOT go through.  Kept for the
   bound arithmetic only.

`subTI n wC wB wS tu ρ uf bS bB : TI(suc n) wS ρ ≡ TI n wB (⇓ρ, uf)`.
Derive from the already-DONE `sub-TI` + `TI-irr` + (now-defined) `MI-irr`:
```
subTI n wC wB wS tu ρ uf bS bB =
  trans (TI-irr n wS ρ …) (sub-TI (… singleW wC tu …) wB wS (⇓ n ρ) …)
```
- `sub-TI (suc n) (singleW wC tu) wB wS ρ …` gives `TI(suc n) wS ρ ≡ TI(suc n) wB
  (envS(suc n)(singleW wC tu) ρ)` and `envS(singleW wC tu)ρ = (ρ, λb→MI(suc n) wC tu ρ)`.
- Then `TI-irr` drops the fuel to `n` and `⇓` the env; the env-top `MI(suc n)-of-u`
  vs `uf = MI n-of-u` is reconciled by **`MI-irr`** (that is the only new dependency).
- Watch the combined bound (`szSubW + (szT wS + szCon Δc) < n`, `combStep`) and the
  env coherence (a `congTI` over `envS-⇓`, both already proven). `envS`/`sub-TI`/
  `envS-⇓` are DONE — only the glue + `MI-irr` are new. The `uf`/knot was already
  dissolved (MI's `⊢app` builds arg + uf from `MI n … (⇓ρ)` directly).

### 4.3 funext — thread as a module parameter (LAST)

`funext`/`funextP` are currently `postulate`. Once holes are gone, turn the module
into `module … (funext : …) (funextP : …) where` (or thread via an explicit
record), so the file becomes axiom-free. Verify all uses still typecheck.

--------------------------------------------------------------------------
## 5. Verify / iterate

From `bootstrap/poc/OCP0009` (build a library-file `$LIBF` with the three
`.agda-lib` paths — stdlib, `formal/Once.agda-lib`, `bootstrap/bootstrap.agda-lib`):
```
F=NbEPDirDTTChMF.agda
printf 'IOTCM "%s" None Indirect (Cmd_load "%s" [])\n' "$F" "$F" \
  | agda --interaction --library-file="$LIBF"
```
Current (working tree): `MI-irr ⊢app` written & type-checks → **0 holes / 0 type errors**,
but batch still reports the ~63 pre-existing unsolved `--prop` bound metas (see §2.5).
⚠ ~10 min interactive load / ~27 min batch — see §2. Not committed yet.

**Repo rules:** NO `Claude-Session:` trailers on commits/PRs. NO sized-types (hard
ban). NO shipped `TERMINATING` pragmas. Commit each closed case; push each commit.

--------------------------------------------------------------------------
## 6. Scratchpad references (this session)

`MF-natapp-CLOSED.agda`, `MF-natMI-lam-CLOSED.agda`, `MF-subMI-COMPLETE.agda`,
`MF-natMI-vz-keep-attempt.agda` (has the pre-refactor coverage stall — superseded).
The proven `nat-MI ⊢app` clause in the live file is the best template for §4.1.
