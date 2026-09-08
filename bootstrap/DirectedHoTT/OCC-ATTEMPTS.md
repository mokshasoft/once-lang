# `occK` / `conSSK` adequacy — the attempts log

**Why this file exists.** `bootstrap/poc/OCP0009/GAP-A-ATTEMPTS.md` closed a
51-attempt proof not on attempt 52 but by tabulating the first 51 and reading
the *why it failed* column — 45–51 shared a premise nobody had stated.
`SUBTM-ATTEMPTS.md` gave `subTm` the same treatment. The adequacy rows are the
third place guesses started stacking, so they get it too.

**The rule:** an attempt that is backed out gets a row *before* the next one is
tried. ⚠ The useful column is **Why it failed**, not *What was tried* — two
attempts that fail for the same reason are one attempt.

---

## Step A — `occ` rows (`occK` agrees with `occTm`/`occTy`)

Developed in `bootstrap/tmp/OccAgreeTmp.agda` (outside the sweep root, so it
may carry holes; see `temp-module-dev-cycle`).

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 1 | statement, postulated | ✅ typechecks — the two bridges (`b2n`, `lvl`) and the tied index are expressible |
| 2 | `base` row via `Lib/IHeadRed.ihead-red` | ⚠ **unsolved metas** — the generic lemma leaves `mth` to the selection proof, which pins nothing, so every β downstream is unsolvable |
| 3 | + index/payload spelled out | ⚠ same class, now on the βs: `subTm (single u) _t = nzero` has many solutions |
| 4 | a LOCAL specialised `occ-head-red` naming `occAt k` | ✅ **rc=0** — the statement pins every downstream term. This is why `Knot/SzAgree` carries its own `head-red` |
| 5 | `El` row (one recursive field, the mutual link) | ⚠ `ielim … != fst ihs` — `fst (pair a b)` is NOT definitional; `βfst` is a REDUCTION rule |
| 6 | + project first, then peel index and scrutinee, `ihs` pinned | ✅ **rc=0** |

★★★ **ATTEMPT 4 IS THE ONE.** The generic `ihead-red` is unusable for rows: a
row body writes `step (β _ _)` with metas, and only a statement that NAMES the
row's method (`occAt k`) makes them solvable. ⇒ every generated adequacy module
needs its OWN head-red; `Lib/IHeadRed` serves the hand-written callers
(`RenRed`, `SubRed`) where the method is already concrete.

★ **AND THE IH NEEDS THREE MOVES, NOT ONE** (attempt 6): `iihs` builds the
child as `ielim KnotD (subTm (isingle i) (pair s (snd (var vz)))) ms (fst p)`,
so the peel PROJECTS (`βfst`), then fixes the child's INDEX
(`snd (pair s n)` ⇒ `n`) and its SCRUTINEE — at different depths. That is the
hazard `Knot/SzAgree`'s header names, and a wrong count lands on some *other*
field and still type-checks.

---

## Step B — `conSSK` (the `Var`-eliminator core) ⬜ OPEN

Developed in `bootstrap/tmp/ConSAgreeTmp.agda`.

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 1 | both HEAD reductions via `ihead-red` | ✅ **rc=0** — here the generic lemma DOES work, because the caller names the method itself |
| 2 | wrapper: copy `Knot/RenSpec.singleK-vs` | ⚠ **the statement is FALSE.** `conSVs` REBUILDS `Var-vsK (fst _) (fst (snd _))`; `singleVs` returns the LOWERED `x`. Copying imported `single`'s lowering into the target |
| 3 | target corrected, one `⟶*-jsubᵖ` | ⚠ nesting count: `symN a p = jsub … p (reflN a)` is ONE jsub, so `singleVs`'s three (`symN` + `predN` + outer) are not `conSVs`'s two |
| 4 | two `⟶*-jsubᵖ` + tail congruences | ⚠ inner `jsub-refl` will not fire — the ford still reads `fst (subTm …)` |
| 5 | DIAGNOSTIC: stop after the βs, prove by `done`, read both sides | ✅ printed: the four βs leave a stack of `subTm (extS (extS (extS (single …))))` that has NOT computed |

★★★ **ATTEMPTS 3 AND 4 ARE ONE ATTEMPT** — both are "the ford peel does not
reach an `idrefl`", and the peel depth was never the cause.

★★★ **AND THE COMPARISON WITH STEP A IS THE FINDING.** Step A's rows reduce
cleanly through the same four βs. The difference is *what is being
substituted into*:

| | method | β-substitutions |
|---|---|---|
| Step A (`occ`) | GENERIC — `occMethod C = lam(lam(lam(nd (ifSum (rsum C) C (var vz)))))`, and `ifSum` RECURSES ON THE CONCRETE `C` | compute away |
| Step B (`conS`) | HAND-WRITTEN — `conSVz`/`conSVs`, whose bodies are `jsub`/`symN` TRANSPORTS over projections | stay stuck |

⇒ **the blocker is not the β spine and not the peel depth — it is that a
hand-written method body is a neutral term `subTm` cannot compute through.**
Exactly `SUBTM-ATTEMPTS.md`'s verdict for `isubPay`: *"the β spine was never
the problem … it is a neutral meta-level call and `subTm` cannot compute
through it"*, whose content was a **naturality lemma**.

⬜ **NEXT FOR STEP B:** a naturality lemma for the hand-written methods —
`subTm τ (conSVs-body …) ≡ conSVs-body (subTm τ …)` — stated with the METHOD
TUPLE ABSTRACTED. Letting the concrete `conSMeths` into the statement is the
`abstract-the-substituted-terms` trap, measured 87× in `SUBTM-ATTEMPTS.md`.

---

## What this predicts for the 53 `occ` rows

★★ **52 of them should behave like Step A, and exactly ONE like Step B.**
`Knot/Occ`'s header: *"FIFTY-TWO OF THE FIFTY-THREE ROWS ARE `Lib/IOcc`'s
GENERIC FOLD … the one exception is `cVar-vz`"*, which is spliced in by hand
(`occVz`, and `occVzK` for its arity-one form).

⇒ `occK` is **more tractable than `conSSK`**, not less, despite having 53 rows
to `conSSK`'s 2: the generic rows compute, and only the spliced `cVar-vz` row
carries a hand-written body. That single row is where the LEVEL convention
lives (`eqNat k m`) and where the naturality question above will reappear.

⚠ It also means the 9-statement block's difficulty is NOT uniform: budget the
work as 52 mechanical rows + 1 genuinely hard one, not 53 equal ones.
