# OCP-0009 · Handoff — raw-faithful M3c (`NbEPDirDTTChMF.agda`)

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
## 1. State (HEAD `925a0ab5`, EXIT 0, **1 hole**)

DONE (real, verified, committed):
- Core interpreter `CI/TI/MI` (fuel-indexed, `--prop` bounds), `TI-irr`, `⇓`.
- `wkTI` (weakening naturality, via `nat-TI` at `wk⊑`), `envO`/`envO-⇓`/`envO-wk⊑`.
- **`nat-TI` COMPLETE**, **`sub-TI` COMPLETE**, **`sub-MI` COMPLETE (8/8)**.
- **`nat-MI` COMPLETE** — all 4 `nat-var-vz`/`nat-var-vs` (keep/skip × vz/vs) closed
  via the `nat-var` helper refactor (see §3).
- **`MI-irr` 5/6** — `⊢tt`/`⊢ff`/`⊢vz`/`⊢vs`/`⊢lam` closed.

REMAINING postulates / holes (what's left):
1. **`MI-irr` `⊢app`** — the ONE `{!!}` hole. (§2)
2. **`subTI`** — postulated; derivation fully mapped, needs `MI-irr` first. (§4)
3. **`funext` / `funextP`** — postulated; INTENDED to become module parameters
   (thread them, don't try to prove them). Do this LAST, once holes are gone.

Once 1+2 are closed and 3 is threaded, the file is axiom-free (modulo funext) and
`consistency` is the theorem.

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

### 4.1 `MI-irr ⊢app` (the hole) — structure is fully mapped

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

### 4.2 `subTI` (postulate → definition) — after `MI-irr` is done

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
Expect `EXIT 0`, 0 errors. Current: **1 hole** (`MI-irr ⊢app`). ⚠ ~10 min/load — see §2.

**Repo rules:** NO `Claude-Session:` trailers on commits/PRs. NO sized-types (hard
ban). NO shipped `TERMINATING` pragmas. Commit each closed case; push each commit.

--------------------------------------------------------------------------
## 6. Scratchpad references (this session)

`MF-natapp-CLOSED.agda`, `MF-natMI-lam-CLOSED.agda`, `MF-subMI-COMPLETE.agda`,
`MF-natMI-vz-keep-attempt.agda` (has the pre-refactor coverage stall — superseded).
The proven `nat-MI ⊢app` clause in the live file is the best template for §4.1.
