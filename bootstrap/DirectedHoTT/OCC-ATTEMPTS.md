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

## ★★★ THE LESSON: DON'T FIGHT THE PROOFS, FIGHT THE ABSTRACTIONS

This file's 34 attempts are one long demonstration of a single mistake and
its remedy. **The failing proof was never the problem. The definition it
was proving things about was.**

`occOp f g = lam (maxTm (app (renTm vs f) (var vz)) …)` puts the fold's
accumulator under a lambda. A fold CHAINS its accumulator, so from the
third recursive field on every goal carried an `extR` — and thirty-odd
attempts went into peels, casts, naturality lemmas and index machinery
trying to DISCHARGE that `extR`. Making `occOp` a closed combinator
applied to its arguments deleted it:

    renTm vs (occOp (occOp a b) c) ≡ occOp (occOp (w a) (w b)) (w c)   -- refl

**Nothing left to prove.** Option A (prove the commutation as a naturality
lemma) was a day of real work aimed at a self-inflicted obligation.

★ THE SAME SESSION PRODUCED THREE MORE INSTANCES OF THE SAME SHAPE:

| symptom fought | abstraction fixed instead |
|---|---|
| `⊢tr` OOM at 5.5 GB — RTS flags, collectors, caps | SPLIT THE RULE (`JWF_SUBSPLIT`); the row-chunker had bottomed out at one rule per module |
| 1540 dead import edges slowing every Judge module | the generator emitted a chain nobody read — DELETE it, not optimise it |
| the head reduction re-derived in every adequacy proof | `Lib/IHeadRed` — extract it once, 3 clients |
| an index peel needed at every row | the ROW STATEMENT pinned the index; quantify it and the peel vanishes |

★ AND THE TELL IS ALWAYS THE SAME: *the working analogue does not have
this problem.* `Knot/SzAgree` has no weakening to cancel, no index peel,
and no `extR` — because `plusTm` builds no lambda and `agree i t` takes
its index as a parameter. Every time a proof needs a step its nearest
working sibling does not, the difference is in the DEFINITIONS, and that
is where to look first.

⚠ THE COST OF NOT DOING THIS: six mechanisms proposed and refuted (12,
13, 16, and three more), each plausible, three of them reproducing the
observed boundary exactly. A mechanism that explains the symptom is not a
diagnosis. The abstraction question — *why does the working version not
need this?* — would have reached the answer on day one.

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


---

## Step A continued — the emitter (`gen_occagree`)

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 7 | emit the `aih` spine from the `KNOT` field list | ✅ reproduces the hand-proved `El`/`Π` spines |
| 8 | — diffed against the hand rows | ⚠ caught a DROPPED `⟶*-ielimⁱ` wrapper on the index peel. Generated blind, all 53 rows would have failed identically |
| 9 | emit the full row body | ✅ `cTy-El`'s generated body is textually CONTAINED in the hand-proved row |
| 10 | `n≥2` cast chain (`b2n-∨`, then `maxℕ-assoc`) | ✅ shapes match: `refl` at n=1, `b2n-∨` at n=2, trans-chain at n=3 |
| 11 | generate `cTy-Hom` (n=3), flat `βsnd » βsnd` slot peel | ⚠ slot 2 fails — the inner `snd`s reduce under `⟶*-snd` congruences. A FLAT chain type-checks at k=1 and fails at k=2 |
| 12 | + recursive `_snds` (= `gen_szagree`'s `_peelR`) | ⚠ **`extR vs x₁ != vs x₁`** — a NEW failure mode |

★★★ **ATTEMPT 12 IS THE INFORMATIVE ONE.** Reading the `ICon`s side by side:

```agda
cTy-Pi   iρ (pair sTy (snd (var vz)))                  -- field 0
          (iρ (pair sTy (nsuc (snd (var (vs vz)))))    -- field 1   ✅
cTy-Hom  iρ (pair sTy (snd (var vz)))
          (iρ (pair sTm (snd (var (vs vz))))
           (iρ (pair sTm (snd (var (vs (vs vz))))))    -- field 2   ❌
```

⇒ **the ambient index is read from `j` BINDERS IN**: field `j` names
`var (vs^j vz)`, and the substitution that resolves it is an `iext`-chain of
length `j`. So the INDEX PEEL IS POSITION-DEPENDENT, not merely
depth-dependent — `peel_ix` currently reads only the field's depth
annotation (`D` / `sucD n` / `lit` / `fld`) and so handles `j ≤ 1`.

★ That is why `Π` passed and `Hom` fails: `Π` has two recursive fields, `Hom`
three, and the break is at field 2 exactly.

⚠ AND IT EXPLAINS THE ROW BUDGET.  14 rows have 0 recursive fields, 12 have
1, 14 have 2 — all reachable with the current peel. **27 rows have ≥2 and 13
have ≥3**, so roughly a quarter of the block is blocked on this one
generalisation.

⬜ NEXT: make `peel_ix` take the field POSITION as well as its depth, and
   emit the `iext`-chain resolution for `var (vs^j vz)`.  `gen_szagree`'s
   `_fstat(r)` vs `_fstat(j)` split — the RECURSIVE index `r` and the FIELD
   index `j` counted separately — is the same distinction and is probably
   the shape to copy.


| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 13 | read the FULL error text instead of its first line | ⚠ **attempt 12's diagnosis was WRONG** — see below |

★★★ **ATTEMPT 12 WAS MISDIAGNOSED, AND THE LOG IS WHY IT WAS CAUGHT.**
Attempt 12 read `extR vs x₁ != vs x₁`, saw that `Π` (2 fields) passed and
`Hom` (3) failed, and concluded the INDEX PEEL was position-dependent —
because field `j` names `var (vs^j vz)`. That story is tidy and false:

* `iihs` EXTENDS its substitution per field —
  `iihs D ms σ (iρ j C) p = pair (ielim D (subTm σ j) ms (fst p))
                                 (iihs D ms (iext σ (fst p)) C (snd p))` —
  and `iext`'s clauses reduce on the variable pattern, so the `vs^j`
  chain COMPUTES. There is nothing position-dependent to peel.
* the error is at `Var ((Θ ∙) ∙)` — **two binders in Θ**, the ENCODING
  context, not in the row's own telescope.

⇒ **THE REAL MECHANISM.** `Lib/IOcc.occOp` WEAKENS both arguments:

```agda
occOp f g = lam (maxTm (app (renTm vs f) (var vz))
                       (app (renTm vs g) (var vz)))
```

and `renTm ρ (lam t) = lam (renTm (extR ρ) t)` (`Spec/Syntax:294`). So
chaining the accumulator — `occOp (occOp a b) c` — puts a `lam` inside a
`renTm vs` and produces `renTm (extR vs)`. That happens at EXACTLY two
levels of chaining, i.e. at the THIRD recursive field. `Π` has two fields
and one `occOp`; `Hom` has three and two.

★ SO THE BOUNDARY IS REAL AND THE EXPLANATION WAS NOT.  Both stories
predict "breaks at 3 fields", which is why the wrong one survived a whole
attempt. ⚠ The lesson is the one this file opens with: the useful column
is WHY, and a *why* that merely reproduces the observed boundary has not
been tested. Two mechanisms predicted the same symptom.

⬜ NEXT: the fix is in `Lib/IOccRed`, NOT in the emitter's peel. Either
   · state `occStep-red` so the accumulator's weakening is absorbed
     (a `renTm`-naturality step for `occOp`), or
   · give `Lib/IOcc` an `occOp` that does not weaken — but that changes
     the fold's own definition and every `⊢occOp` client, so measure
     first.
   ⚠ Do NOT build the position-dependent peel of attempt 12; it solves
     a problem that does not exist.


| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 14 | SPIKE (`tmp/OccSpike3.agda`): apply `occSum-red` to `cTy-Hom` with everything ABSTRACT — no encoding, no row, no peels | ✅ **rc=0 at THREE fields** (and at two) |

★★★ **THE SPIKE LOCATES THE FAULT, AND IT IS NOT WHERE ATTEMPT 13 SAID.**
`occSum-red` composes fine at three fields. ⇒ `Lib/IOccRed` is sound here,
and BOTH repairs attempt 13 proposed — absorbing the weakening in
`occStep-red`, or de-weakening `Lib/IOcc.occOp` — are aimed at the wrong
file. The `occOp`-weakening mechanism is REAL (`renTm ρ (lam t) =
lam (renTm (extR ρ) t)`, and two chainings do land at field 3) but it is
not what fails.

⚠⚠ **THAT IS TWICE.** Attempt 12: a mechanism that reproduced the
boundary, wrong. Attempt 13: a mechanism that is mechanically real AND
reproduces the boundary, still not the cause. ⇒ **a mechanism is not a
diagnosis until something that ISOLATES it has been run.** The spike cost
two commands and would have saved the whole of attempt 13.

★ SO THE FAULT IS IN THE ROW'S OWN CONSTRUCTION — the pinned `{ihs = …}`,
  or the slot/index peels feeding `aih-ρ`, at slot 2. That is emitter
  code, not library code, which also means the 13 three-plus-field rows
  are NOT blocked on a library question.


| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 15 | drop the `{ihs = …}` pin from the `Hom` row | ⚠ identical error ⇒ the pin is not the fault |
| 16 | DIAGNOSTIC: replace the row's tail with `done`, read both sides | ✅ printed the goal — see below |

The left-hand side after the three βs:

```
app (subTm (single ihs) (subTm (extS (single p)) (subTm (extS² (single i))
      (ifSum 𝔹 … (ilookupD KnotD tagTy-Hom) (var vz))))) (num (lvl x))
```

★ THE SUBSTITUTIONS SIT **OUTSIDE AN UNREDUCED `ifSum`**, while
`occSum-red` needs the shape `occSum true C ihs`. `ifSum` is a DEFINED
function recursing on the `ICon`, so `subTm` cannot push through it.

⬜ **HYPOTHESIS — NOT A DIAGNOSIS.** This looks like `SUBTM-ATTEMPTS.md`'s
`isubPay` wall verbatim ("a neutral meta-level call `subTm` cannot compute
through"), whose content was a NATURALITY lemma:

    ifSum-sub : subTm σ (ifSum r C ih) ≡ ifSum r C (subTm σ ih)

⚠⚠ BUT IT DOES NOT YET EXPLAIN THE BOUNDARY, and that is exactly the test
attempts 12 and 13 failed. `Π` (two fields) goes through the SAME three βs
and the SAME `ifSum`, and it PASSES. If `subTm` simply could not commute
with `ifSum`, `Π` would fail too. ⇒ something makes the two-field case
reduce where the three-field case does not, and until that is identified
this hypothesis is not established.

★ WHAT IS ESTABLISHED (attempt 14): the fault is in the ROW, not in
  `Lib/IOccRed` — `occSum-red` composes at three fields with abstract
  arguments. So whatever the mechanism, the repair is emitter-side.

⬜ NEXT DIAGNOSTIC: run the same `done` diagnostic on the PASSING `Π` row
   and diff the two printed left-hand sides. The difference between a
   case that reduces and one that does not is the actual answer, and it
   is two commands.


| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 17 | the `done` diagnostic on the PASSING `Π` row, to diff against `Hom`'s | ⚠ **structurally IDENTICAL** — same `subTm` stack outside the same unreduced `ifSum`.  ⇒ attempt 16's hypothesis is refuted: that shape is common to a passing and a failing row |
| 18 | SPIKE (`tmp/PeelSpike.agda`): the three generated SLOT PEELS on a literal tuple | ✅ rc=0 — all three, INCLUDING slot 2 |
| 19 | SPIKE (`tmp/OccSpike4.agda`): attempt 14 redone with a CONCRETE `ihs` | ✅ rc=0 at two AND three fields |

★★★ **ATTEMPT 19 MATTERS BECAUSE ATTEMPT 14 WAS NOT A FAITHFUL ISOLATION.**
14 used an ABSTRACT `ihs`; `occSum` only unfolds into the `occOp` chain when
its arguments are concrete, so 14 could not have reproduced attempt 13's
mechanism even if that mechanism were the cause. 19 supplies the concrete
`iihs …` term and STILL passes. ⇒ attempt 13 is now refuted properly, not
merely relocated.

⚠⚠ **FOUR MECHANISMS PROPOSED, FOUR REFUTED** (12 position-dependent peel ·
13 `occOp` weakening · 16 `ifSum` naturality · and 14's own scope). Every
component works in isolation:

| component | verified |
|---|---|
| slot peels 0,1,2 | ✅ spike 18 |
| `occSum-red`, abstract, 3 fields | ✅ spike 14 |
| `occSum-red`, CONCRETE ihs, 3 fields | ✅ spike 19 |
| cast chain shapes (n=1,2,3) | ✅ attempt 10 |
| the post-β goal shape | ✅ identical in passing `Π` and failing `Hom` (17) |

⇒ **THE FAULT IS IN THE COMPOSITION, AND IT IS NOT LOCATED.** Bisection has
eliminated every part; what remains is how the parts are joined — the `»`
between the head-red and `occSum-red`, or the IH TYPES in the row's own
signature.

⬜ NEXT, and NOT another mechanism: build the `Hom` row by STARTING FROM THE
   PASSING `Π` ROW and adding one field, changing one thing at a time. The
   two rows are 40 lines apart and one works; the difference is finite and
   can be bisected directly instead of hypothesised. ⚠ Do not propose a
   fifth mechanism before that diff is read — this file's record on
   mechanisms is 0 for 4.


## The `Hom` bisection (attempts 20–24)

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 20 | `cTm-app` — TWO fields, BOTH at depth `D` | ✅ **rc=0**.  Separates the two confounded variables: `Π` passes with `sTy@D, sTy@sucD`, `app` passes with `sTm@D, sTm@D` ⇒ "two fields at the same depth" is NOT the problem |
| 21 | SPIKE (`tmp/CastSpike.agda`): the n=3 CAST CHAIN standalone | ✅ rc=0 — the one component previously verified only by SHAPE |
| 22 | regenerate `Hom` cleanly (earlier splices were suspect) | ⚠ same `extR vs x₁ != vs x₁` ⇒ NOT a splice artifact |
| 23 | SPIKE 5 (`tmp/OccSpike5.agda`): `occSum-red` with `ihs` AND the result `n` both PINNED | ✅ rc=0 at three fields.  Closes spike 19's gap — 19 left `n` a meta, so Agda never had to compute the `occOp` chain |
| 24 | inspect the generated `aih` for `Hom` directly | ⚠ index peels are IDENTICAL across slots 0,1,2 — and correctly so: `σ_j (vs^j vz)` resolves to `i` at every `j`, so one `βsnd` each |

★★★ **THE BISECTION IS EXHAUSTIVE AND THE FAULT IS STILL NOT LOCATED.**

| component | isolated? | verdict |
|---|---|---|
| slot peels 0,1,2 | ✅ spike 18 | sound |
| `occSum-red`, abstract | ✅ spike 14 | sound |
| `occSum-red`, concrete `ihs` | ✅ spike 19 | sound |
| `occSum-red`, `ihs` AND `n` pinned | ✅ spike 23 | sound |
| n=3 cast chain | ✅ spike 21 | sound |
| 2 fields @ `D`+`sucD` (`Π`) | ✅ real row | passes |
| 2 fields @ `D`+`D` (`app`) | ✅ real row | passes |
| 3 fields (`Hom`) | — | **FAILS** |

⇒ every part is sound in isolation and the composition is not. The only
thing spike 23 does not do that the row does is CONSTRUCT the `AllIH`
(spike 23 receives it as a parameter). ⇒ the fault is in building the
three-deep `aih-ρ` chain, at the point where slot 2's IH proof is checked
against the child that `iihs` produces at σ-depth 2.

⬜ **NEXT — the one isolation not yet run:** build the `AllIH` for
   `cTy-Hom` standalone, with the generated peels and the three IHs as
   PARAMETERS, and no head-red, no cast, no `occSum-red`. That is the
   exact gap between spike 23 (passes) and the row (fails), and it is the
   last unbisected step.

⚠ FIVE MECHANISMS HAVE NOW BEEN PROPOSED AND REFUTED.  Do not propose a
  sixth.  Run the isolation above; if it passes, the fault is in the `»`
  join to the head-red and nowhere else, which is a two-line surface.


## ★★★ RESOLVED (attempts 25–28) — the IH must be QUANTIFIED OVER THE INDEX

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 25 | read `Knot/SzAgree`'s WORKING 3- and 5-field rows | ★ they have TWO peels, not three — **no index peel at all**, because each child is discharged by `agree _ y0`, the `_` being the index |
| 26 | restate the row with the index quantified, `occ-head-red` using `_` placeholders | ⚠ >120s then **rc=143, ZERO errors** — killed, not refuted.  `meta-standing-for-a-computation`: three `_` in a signature |
| 27 | same, every `_` spelled out | ⚠ 2s (from >120s!) — and the SAME `extR` error, so the index peel was not the cause either |
| 28 | SPIKE (`tmp/AihSpike.agda`): CONSTRUCT the `AllIH` alone — no head-red, no cast, no `occSum-red` | ⚠ then ✅ — see below |

★★★ **ATTEMPT 28 IS THE ANSWER.** Constructing the `AllIH` in isolation
reported the mismatch in plain terms:

```
i != pair (subTm (isingle i) sTy) (subTm (isingle i) (snd (var vz)))
```

**the child's index is not `i`.** `iihs` builds it as
`subTm (isingle i) (pair s (snd (var vz)))`. An IH pinned at a particular
index therefore CANNOT apply to any child. Quantifying the IH —

```agda
((i' : RTm Γ) → IHocc k (ielim KnotD i' occMethsK a) m) → …
```

— makes it apply at every child, and the 3-field `AllIH` type-checks in
**1s**.

★ AND THAT IS EXACTLY WHAT `SzAgree` DOES.  `agree i t` takes the index as
a PARAMETER, so its rows write `agree _ y0` and the `_` unifies with
whatever `iihs` produced. It never peels an index because it never needs
one to be anything in particular.

⚠⚠ **THE ROOT ERROR WAS IN THE STATEMENT, MADE ON DAY ONE.** The first
note in this file's Step A records: *"`sz`'s agreement quantifies the
INDEX universally … `occ` depends on BOTH, so the index must be TIED to
the context, not quantified away."* That is true of the FINAL theorem and
FALSE of the ROWS. Pinning the index in the row statement created the
need for an index peel, which had no counterpart in the working proof,
and every subsequent mechanism (12, 13, 16, and the peel machinery for
`D`/`sucD`/`lit`/`fld`) was investigating a self-inflicted symptom.

★ SIX MECHANISMS PROPOSED, SIX REFUTED, and the answer came from READING
  THE WORKING PROOF rather than from any of them. ⇒ before hypothesising
  about a generated proof, diff it against the nearest proof that already
  works. `gen_szagree` was 40 lines away the entire time.

⬜ CONSEQUENCES FOR THE EMITTER:
   · DELETE `peel_ix` and all the depth-annotation machinery
     (`D` / `sucD n` / `lit` / `fld`) — it exists only to serve a pinned
     index and is not needed;
   · the row body becomes `SzAgree`'s shape plus the `⟶*-appˡ` that
     `occ`'s function-valued motive requires;
   · the ROW-LEVEL statements quantify the index; the TOP-LEVEL theorem
     ties it. Those are different statements and conflating them is what
     cost this whole investigation.


## Attempts 29–31 — `peel_ix` deleted; the residue is the JOIN

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 29 | delete `peel_ix`, regenerate the `aih` (two peels, `IH _`) | ✅ spine now matches `SzAgree`'s exactly |
| 30 | full `Hom` row, `peel_ix` gone, IHs quantified | ⚠ still `extR vs x₁ != vs x₁` |
| 31 | state the `ICon` as `ilookupD KnotD tagTy-Hom` (the head-red's own form) rather than `cTy-Hom` | ⚠ no change — the `ICon` form is not it |

★★★ **THE `extR` ENTERS THROUGH THE JOIN, AND THE ASYMMETRY WITH `sz` IS
WHY.** Three configurations, and only their combination fails:

| configuration | result |
|---|---|
| build the `AllIH` alone (`tmp/AihSpike.agda`) | ✅ |
| `occSum-red` with the `AllIH` GIVEN (spike 5) | ✅ |
| both, JOINED to the head-red (`tmp/HomFinal.agda`) | ❌ |

```agda
plusTm m n = natrec n (nsuc (var vz)) m           -- sz's op: no lam, no renTm
occOp  f g = lam (maxTm (app (renTm vs f) …) …)   -- occ's op: BOTH
```

`SzAgree`'s rows never cancel a weakening because `plusTm` builds no
lambda. `occOp` does — so when the three βs COMPUTE `occSum` into an
`occOp` chain, `renTm vs` meets a `lam` and produces `renTm (extR vs)`.
Spike 5 never saw it: its `occSum` came from a TYPE, not from βs.

⇒ attempt 13's mechanism was REAL after all, but its LOCATION was wrong
  in both directions — it is not in `Lib/IOccRed` (spikes 5/19/23 clear
  it) and not in the `AllIH` (spike 28 clears that). It is in the
  head-red's OUTPUT, where the βs force `occSum` to unfold.

⬜ NEXT: the βs' target needs a weakening cancellation, the way
   `Knot/RenSpec.singleK-vz` opens with `⟶*-castᵣ (wk-single …)`.
   ⚠ This is the FIRST place `occ` needs something `sz` does not, so
   there is no row in `SzAgree` to copy — the template runs out here, and
   that is exactly why every mechanism that assumed symmetry with `sz`
   was wrong.


## ★★★ CLOSED (attempts 32–34) — `occOp` must not build a lambda

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 32 | SPIKE (`tmp/MaxFnSpike.agda`): does a CLOSED-combinator `occOp` make renaming distribute through a chained accumulator? | ✅ **`refl`** — definitionally |
| 33 | implement it: `Lib/IOcc.occOp f g = app (app maxFn f) g`, `maxFn` closed; `⊢occOp = ⊢app (⊢app ⊢maxFn da) db` | ✅ rc=0 |
| 34 | adapt `Lib/IOccRed.occStep-red` (now THREE βs) and rerun `Hom` | ✅ **rc=0 — the 3-field row passes** |

★★★ **THE FIX WAS A DEFINITION, NOT A LEMMA.**

```agda
-- was: the accumulator sits under a `lam`
occOp f g = lam (maxTm (app (renTm vs f) (var vz)) (app (renTm vs g) (var vz)))
-- now: `f`/`g` are ARGUMENTS of a closed combinator
maxFn     = lam (lam (lam (maxTm (app (var (vs (vs vz))) (var vz))
                                 (app (var (vs vz))      (var vz)))))
occOp f g = app (app maxFn f) g
```

A fold CHAINS its accumulator, so with the old definition
`renTm vs (occOp a b)` was `lam (renTm (extR vs) …)` and every goal from
the THIRD recursive field on carried an `extR` nothing could discharge.
With `maxFn` closed,

    renTm vs (occOp (occOp a b) c) ≡ occOp (occOp (w a) (w b)) (w c)

holds by `refl`. **No naturality lemma was needed — there was nothing
left to prove.** Option A (prove the commutation) would have been real
work for a problem that a better definition deletes.

⚠ TWO RESIDUES, both small and both named by Agda:
  · `occStep-red` now does THREE βs, not one;
  · the accumulator is weakened TWICE and the new child once — `acc` is
    substituted at the FIRST β so it passes under both remaining binders.
    ⇒ `Lib/Wk.sub-w²-single` for `acc`, `wk-single` for `h`.  Using one
    lemma for both is the obvious error, and the error message says so.

★ AND `Lib/ISz` NEVER MET ANY OF THIS: its `op = plusTm` builds no
  lambda, so `Knot/SzAgree` has no weakening to cancel anywhere. That is
  why six mechanisms assuming symmetry with `sz` were wrong, and why the
  template genuinely ran out here — this was the one place `occ` needed
  something `sz` does not.

★ It also improves the term-size story: `maxTm a b = plusTm a (monusTm b
  a)` mentions `a` twice, and that duplication now lives inside a CLOSED
  `Def` (shared) instead of being inlined at every application. See
  `maxtm-is-non-linear`, which predicted this cost and can now be
  updated: the linear formulation was also the correct one.

⇒ ALL FOUR ROW SHAPES NOW PASS: `base` (0 fields), `El` (1, cross-sort),
  `Π` (2, one under a binder), `app` (2, same depth), `Hom` (3).

------------------------------------------------------------------------
## 35. `agree-ty` / `agree-tm` ARE FALSE AS STATED — `occK` is not faithful

**Not an attempt that failed — a statement that cannot be proved.** Found
while generating the remaining 48 rows, by working out what each row's
children owe.

`Knot/Occ`'s header justifies the constant rows as

> `Mu D` → `0`, because `Desc` is a closed sort with no variables

`Desc` is closed **with respect to `Γ`**. It is not variable-free:

```agda
dκ : RTy ε → DCon → DCon        -- takes a CLOSED type …
leaky = Π Nat (El (var vz))     -- … and a closed type binds its OWN vars
```

`occK` compares raw **levels**, and `enVar {Γ ∙} vz = Var-vzK (num (len Γ))`,
so the `vz` bound inside `leaky` encodes to `Var-vzK (num 0)` — the same
node as a free level-0 variable of `Γ`. `occVz = eqNatTm k (fst p)` answers
1 for both.

```agda
occTy vz (Mu (dκ leaky dι ◃ dnil)) ≡ false      -- checked by refl
occK  … at level 0                  ⟶* num 1    -- by the 7 steps below
```

`tmp/OccCex.agda` checks the `refl`-decidable halves —
`occTy vz (Mu (dκ leaky dι ◃ dnil)) ≡ false` and
`enVar {ε ∙} vz ≡ Var-vzK (num 0)`. The object side is a
reduction, so it is argued, not computed: (1) every row but `cVar-vz` uses
`occMethod`, i.e. the fold at `pick = λ _ → true`, so **every `iρ` counts**;
(2) `cTy-Mu`'s one `iρ` child has sort `sDesc`; (3) `cDCon-kap`'s has sort
`sTy`; (4) that `RTy ε` contains `Var-vzK (num 0)`; (5) `occVz` matches it;
(6) `op = max`; (7) the meta side is `false`.

**Affected rows** — every one with a description-sort or `('lit', 0)` child:
`cTy-Mu`, `cTy-IMu`, `cTm-cMu`, `cTm-cIMu`, `cTm-elim`, `cTm-ielim`,
`cDesc-cons`, `cDCon-rho`, `cDCon-kap`, `cIDesc-cons`, `cICon-rho`,
`cICon-kap`. The five proved rows (`base`, `El`, `Π`, `app`, `Hom`) are
sound — they have no such child.

### ⚠ THE SIMPLIFICATION WAS THE DEFECT

`Lib/IOccRed`'s header presents the missing filter as an advantage:

> SIMPLER — `Lib/IOcc` instantiates the fold at `(λ _ → true)`, so
> `pick (rsum C) j` is ALWAYS `true`: every recursive field counts.
> None of `ISzRed`'s `sameSortAt` / `false` cases exist.

That *is* the bug. `Lib/ISzSort` kept the filter; `Lib/IOcc` dropped it and
became unfaithful. **Fight the abstraction:** the fix is `pick`, not a
cleverer proof — no proof can close a false statement.

### THE FIX  ⚠ SUPERSEDED BY §36 — the sort clause turned out unnecessary

`pick j = descendable (fst j) ∧ not (literalZero (snd j))`, where
`descendable` keeps `sTy`/`sTm`/`sVar` and drops the four description
sorts. The depth clause is what drops `IMu`'s closed `RTy ε` index type,
which `occTy` also ignores; closed children are pinned to a literal
`num 0` by their ford, while ambient ones are `snd (var vz)`, so the test
is syntactic and decidable. `pick`'s interface (`{Δ} → R → RTm Δ → 𝔹`, with
`fieldSort` already in `Lib/IFold`) needs no change.

Cost: `Lib/IOccRed.AllIH` gains the skipped-child constructor `ISzRed`
already has, so all rows carry the filter — modest churn on the five
proved rows. Skipping a depth-0 child is sound because `Var ε` is empty.

### ⚠ WHAT THIS SAYS ABOUT THE LEDGER

`occK`'s row typechecked green, and `check-formers.sh` is satisfied: the
defect is in what the program *computes*, which no type in this
development mentions. Same mechanism as
`typechecking-cannot-see-an-encoding` — and this time the adequacy lemma
is what caught it. **The faithfulness gap is doing its job.**


------------------------------------------------------------------------
## 36. FIXED — and the fix is HALF of what §35 proposed

§35 proposed a two-clause `pick`: drop the four description sorts, AND
drop children pinned to a literal depth. **The sort clause is not needed.**
A spike (`tmp/ScopeHazard.agda`) settled it, since promoted to
`Examples/Knot/PickScope` — which is the TRACKED artifact, and the one
the library comments cite:

```agda
scopeAt _ j with depthAt j
... | someℕ _ = false   -- literal depth ⇒ a FRESH scope ⇒ do not descend
... | noℕ     = true    -- mentions the ambient index ⇒ same scope
```

**Why one clause suffices.** Descending into a `Desc`/`IDesc` at the
ambient depth is harmless, because neither can *reach* a variable without
crossing a literal-pinned edge:

* `Desc` contains no `RTm` at all — only `dρ` markers and `dκ`'s
  `RTy ε`, and `⊢DCon-kapK` pins that to `num 0`.
* `IDesc`'s only variable-bearing content is inside `ICon`s, and
  `⊢IDesc-consK` pins the `ICon` child to `num 1`.

⇒ exactly **four** of the knot's 82 recursive children restart a scope,
and Agda names them:

```agda
knot-skips     : skipD KnotD ≡ 4                                    -- refl
knot-skip-rows : skipRows 0 KnotD
               ≡ rcons 10 (rcons 39 (rcons 45 (rcons 47 rnil)))     -- refl
--   10 cTy-IMu   39 cTm-cIMu   45 cDCon-kap   47 cIDesc-cons
```
Controlled: changing one index gives `45 != 44`.

### ★★★ AND THE SCOPE-INDEX REDESIGN WAS NOT NEEDED

The proposed design fix (`FUTURE.md` D′: *index by the SCOPE rather than
its LENGTH*) would have been a rewrite of `Knot/Map` and every `⊢…K`
signature. **The information was already in the depth index.** A child in
the ambient scope has an index mentioning the index VARIABLE, so it is
not a closed numeral; a scope-restarting child is pinned to a literal by
its own typing rule. `Lib/IFold.numVal` — already present, for sort tags
— is the entire test.

⚠ Do not read this as "D′ was wrong". D′ is about `wkK`, where two
DIFFERENT renamings share a type; that class is real and still open. It
is this bug that D′ does not describe.

### WHAT IT COST

| | |
|---|---|
| `Lib/IFold` | `depthAt` + `scopeAt`, ~12 lines |
| `Lib/IOcc` | one parameter changed; **typing derivations unchanged** — `⊢ifMethod` is parameterised over `pick`, as designed |
| `Lib/IOccRed` | `IHof`/`maxIf`/skipped case restored, mirroring `Lib/ISzRed` |
| the 5 proved rows | ★ **zero edits.** Their children are all ambient, so `scopeAt true j` reduces to `true`, `IHof true` is `IHocc`, `maxIf true` is `maxℕ` |

★ **The last row is the sign the abstraction was right:** a fix that is
invisible at every use site that was already correct.

### ⬜ STILL OWED

`PickScope` says WHICH children the fold skips. It does **not** say those
are exactly the ones `Spec/Variance.occTy`/`occTm` decline to recurse
into — that correspondence is what licenses adequacy, and it is
discharged row by row by `agree-ty`/`agree-tm`. The 48 remaining rows are
unblocked, not written.
