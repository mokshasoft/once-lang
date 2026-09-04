# `subTm` over the knot — the attempts log

**Why this file exists.** In `poc/OCP0009` a proof (gap A's `⊢S3s`) took
**51** attempts. What broke it was not attempt 52; it was writing the
first 51 down in a table and reading the column of *why it failed*. Every
one of attempts 45–51 turned out to share a premise nobody had stated:
*`⊢S3` gets built first and converted second.* Dropping the premise closed
it. That record is `bootstrap/poc/OCP0009/GAP-A-ATTEMPTS.md`.

`subTm` is the second place in this project where guesses started
stacking up, so it gets the same treatment. **The rule: an attempt that
is backed out gets a row before the next one is tried.** A failure that
is not written down cannot be compared with the others, and comparing
them is the entire mechanism.

⚠ The useful column is **Why it failed**, not *What was tried*. Two
attempts that fail for the same reason are one attempt.

---

## Step 1 — `⊢extNK` (the extension is type-preserving) ✅ CLOSED

Goal:

    ⊢extNK : Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ sb ∷ SubTy d n →
             Γ ⊢ extNK d n sb ∷ SubTy (nsuc d) (nsuc n)
    SubTy d n = Π (K (pair sVar d)) (K (pair sTm (renTm vs n)))

The body — `⊢lam` over `⊢app (⊢app (⊢extSK …) …) …` — was accepted early.
Everything below is about the *conversions around it*.

| # | Attempt | Result |
|---|---------|--------|
| 1 | `⊢-cast` at the result with a `wk-single` on the codomain | ⚠ moved the goal: the domain mismatch stayed, now under a `subst` |
| 2 | as 1, with the `cong` reshaped to mention the pair | ⚠ same mismatch, different display |
| 3 | `muBwd*` at the result, as used elsewhere in this file | ⚠ `muBwd*` converts an `IMu` payload; the mismatch is *outside* it, in the Π |
| 4 | `⊢conv` at the result with `red→≅ᵀ (predSndPair …)` | ⚠ `predSndPair`'s equation is not the goal's: the goal's is under a Π |

**The shared premise (all four): the body is BUILT first and CONVERTED
second.** So every attempt aimed at the *result* type — where the
offending subterm sits inside a Π domain, a position no `⊢-cast` reaches.
Once stated, the premise is obviously optional.

| # | Attempt | Result |
|---|---------|--------|
| 5 | drop it — convert the **input** `⊢wk dsb` at its source, `⊢conv` with `⟶ᵀ*-Πˡ` | ⚠ closer: domain accepted, **codomain** now mismatched — `vs x != extR vs x` |
| 6 | + `⊢-cast` on the input's codomain by `ren-w` | ⚠ closer still: the reduction's *left* endpoint is under a substitution |
| 7 | + `predSndSub` — `predSndPair` with its right endpoint moved by `wk-single` through a new `⟶*-castᵣ` | ✅ **rc=0** |

**Resolution.** At the input the type is still concrete, and it needs
**two conversions of different kinds** — which is why no single cast was
ever going to work, and why "try another cast" could not have converged:

* the **codomain** differs by a *renaming* → `ren-w`, an `≡` → `⊢-cast`;
* the **domain** differs by a *reduction* → `predSndSub`, a `⟶*` lifted
  through the Π by `⟶ᵀ*-Πˡ` → `⊢conv`.

★ **Both lifting tools already existed** — `ξ-Πˡ` in `Spec/Typing`,
`⟶ᵀ*-Πˡ` in `Metatheory/Injectivity` — proved long before this file. The
four attempts never went looking for them because, under the dropped
premise, a Π-domain congruence had nowhere to be used. **The premise did
not just block the proof; it hid the library.**

### Slips worth not repeating

* Twice the *contexts* were wrong before the *mathematics* was (`w` on
  the endpoint instead of on the pair). Write the statement at the
  context the goal prints, not the one that reads nicely.
* `⟶*-castᵣ` is carrier-generic plumbing that had no home; it is local
  in `Knot/SubMot` pending a second customer. See the two families in
  `HANDOFF-2026-08-27` §"THE PENDING GENERALISATION".

---

## Step 2 — `⊢sPick` (the ρ component) ✅ CLOSED

⚠ No attempts yet — the first thing STATING it produced was not a proof
but a **correction to the classification**, so that is the row.

| # | Attempt | Result |
|---|---------|--------|
| 0 | state `⊢sPick` over `SubIx` as it stood (`rides` carries *`s` is closed* + `smap s ⟶* s`) | ⚠ **not even well-typed.** The witness is needed of `subTm σ s`, and `s : RTm Δ` vs `subTm σ s : RTm Γ` are in different contexts |

★ **Closedness cannot cross a substitution.** `pinned-stable` relates two
substitutions and never strips one, so no amount of care with `occTm`
reaches `subTm σ s ≡ s` — the statement does not typecheck. The
classification has to carry more.

⇒ **`IsNum`.** Every riding field's sort over `KnotD` is a literal tag,
so record it as a numeral: the sort then has a **value in `ℕ`**, and a
value crosses contexts freely. `isNum-sub : subTm σ s ≡ num (numOf p)` is
a two-line induction and closedness comes out as a corollary
(`isNum-occ`) rather than being assumed. The same Fording move the knot's
own indices use, one level up.

✅ Landed, both green, and **the mask still reads `sdGiven … ≡ 3`** — the
refined classifier loses no rows. `decStable` is now indexed by the
numeral's *value* and returns a Γ-generic witness; over the knot that
cost nothing, because the six `sortMap-*` chains were already stated for
an arbitrary `Γ` and `sTy … sICon` are `num 0 … num 5` definitionally.

| # | Attempt | Result |
|---|---------|--------|
| 1 | with `IsNum` in place, state and prove `⊢sucs`, `⊢extsN`, `⊢sPick` in a new `Sub.Typing` submodule | ✅ **rc=0 first try** |

★ **First try, after four backed-out attempts on step 1 and a stated
correction on step 2.** That is the pattern the log is meant to make
visible: the expensive part was never the proof, it was finding the
premise the goal was really making. Once the classification carried the
sort's *value*, `⊢sPick` was fifteen lines with no search in them.

Two interface choices did the work, both instances of *state the equation
at the shape it has*:

* **`⊢motApp` hands over the IH already ELIMINATED.** Passing the motive
  instead would need `iinst`'s de Bruijn layout to unfold — a
  knot-specific computation `Lib` cannot do.
* **The index is taken apart into `pair s dd` at the interface.** A
  field's index *is* a pair; left whole, every use owes a `βsnd` that
  only the customer can discharge.

⬜ Remaining for the customer: discharge `⊢ext` (that is `⊢extNK`, done)
and `⊢motApp` over the knot.

## Step 3 — `⊢isubPay` ✅ CLOSED

⚠ Stating it produced a correction *again*, and this one is worse than
step 2's: it changes the **term**, not just the proof.

| # | Attempt | Result |
|---|---------|--------|
| 0 | reuse `Lib/IWk`'s κ case — a ford field is COPIED, retyped by `⊢kaComp` | ⚠ **the copy does not inhabit the target type.** Not a proof gap; the term is wrong |

★ Weakening copies a tag ford because at the shifted index the constraint
reads `fst (sh ⟨i⟩) ≡ b`, and `βfst` takes that to `fst ⟨i⟩ ≡ b` — the
witness the method already holds. The two types are **convertible**.
Under substitution the output index reads `smap (fst ⟨i⟩)`, and nothing
reduces that to `fst ⟨i⟩`: mapping the sort is what `smap` is *for*. ⇒
the witness must be **acted on**.

⇒ **`fordMap`**, a fourth module parameter, and `isubPay`'s κ clause is
no longer `pair (fst q) …`. Over the knot the action is `jsub` once more,
in the direction `sortConv` does not go: `symN` turns `fi ≡ b` around,
the motive `λ z. sortMap z ≡ b` transports to `fi`, and the base case
`sortMap b ≡ b` is the row's own stability chain read as an identity —
**the same datum `s-rides` already carries**.

Two knock-on refinements, both forced, both the *same* move as step 2:

* `SubKa` replaces `WkKa`: a tag ford's **tag must be a numeral**
  (`fordMap` is applied in `Γ` to data named in `Δ`) and must carry the
  stability witness (it is `fordMap`'s base case).
* the ford's **code is pinned to `⌜Nat⌝`** rather than left an abstract
  closed term — over an abstract code there is no motive to name. A row
  with another code falls through to `sk-clo` or to GIVEN.
* `isubPay` now threads `fst ⟨i⟩` beside the depth. The sort was never
  needed while a κ field was a copy.

✅ Landed, both green, **and the mask still reads `sdGiven … ≡ 3`** — the
refined κ classification loses no rows either. That control is now
earning its keep twice.

| # | Attempt | Result |
|---|---------|--------|
| 1 | with `SubKa`/`fordMap` in place, prove `⊢kaPick` and `⊢isubPay` | ✅ rc=0 (two scope slips, no goal moved) |

★ Same shape as step 2: once the classification carried what the goal
was actually asking for, the proof went in without search. `⊢isubPay` is
structurally `Lib/IWk`'s `⊢iwkPay` — same walk, same `payStep` casts —
with each field's component lemma swapped.

Two things it does *not* pay that `⊢iwkPay` does:

* the four index hypotheses **thread unchanged** through the recursion,
  because `iext σ u (vs x) = σ x`. No `cong`, no re-derivation per depth.
* the IH slot needs **no cast**. `⊢iwkPay` instantiates `Mot D I` and
  owes a `wk-single` round trip; `⊢sPick` takes its hypothesis at
  `iinst`, which is the shape `iihTy` hands over.

| # | Attempt | Result |
|---|---------|--------|
| 2 | `⊢fordMapK` — `jsub` along `symN`, base case from the stability chain | ✅ rc=0 |
| 3 | `⊢motAppK` — the two `⊢app`s, naively | ⚠ apps go through; the RESULT index is under four nested substitutions |
| 4 | + `⊢-cast` collapsing the tower, `⊢conv` along `βfst` under `sortMap` | ⚠ now the ARGUMENT's domain mismatches — its own tower, one rung shorter |
| 5 | + convert `dsb` **at its source** (`⟶ᵀ*-Πˡ`, `βsnd`), left endpoint moved by `⟶*-castₗ` | ✅ rc=0 |

★ **Attempt 4→5 is step 1's lesson, reused without a search.** The
argument's mismatch sits inside a Π domain; the fix was already known —
convert the input where its type is still concrete — so it cost one
attempt instead of four. That is the log paying for itself.

⚠ `sortMap` mentions its argument **twice** (`natrec s sTm (p5 s)`: the
zero branch and inside the scrutinee), so lifting a reduction through it
takes both congruences. `sortMap-red` does it in two lines.

✅ **And `Sub.Typing` is instantiated over the knot** — `open Typing
KnotD IPair SubTy subMotK ⊢extNK ⊢motAppK ⊢fordMapK` typechecks, which
is the only thing that proves the three obligations *compose*. Each was
built against a signature written in `Lib`; nothing before that line
confirmed they fit together.

## Step 4 — `⊢isubMethodK` ✅ CLOSED

| # | Attempt | Result |
|---|---------|--------|
| 0 | put it in `Lib`, beside `⊢isubPay` | ⚠ **can't.** The method's last two binders are the MOTIVE's own, and typing them needs `subMotK` to unfold — the one thing `Lib` cannot do |
| 1 | build it at the knot, `⊢subVarM`'s five-lam prologue + `⊢icon` | ✅ rc=0 (import and cast iterations only, no goal moved) |

★ What `Lib` owed was genericity in the **row**, and `⊢isubPay` delivers
that. Genericity in the **motive** was never the customer's need — so
row 0 is a correction to where the lemma lives, not to what it says.

★★ **A computed row needs no `sortConv`.** The three given rows build at
their own sort and transport; a computed row builds its `icon` at the
output index `pair (sortMap (fst ⟨i⟩)) n` directly, so the method's
result type is met on the nose.

⇒ **and that is what forced `⊢isubPay`'s τ hypotheses to be reductions.**
`τ` is `isingle (pair (sortMap (fst ⟨i⟩)) n)`, so `fst (τ vz)` and
`snd (τ vz)` are stuck projections of a literal pair — one `βfst` and one
`βsnd`, not two `refl`s. `σ` is `isingle ⟨i⟩` with `⟨i⟩` a *variable*,
and both of its hypotheses **are** `refl`. Same lesson as steps 2 and 3:
state each side at the shape it has.

Two counting traps worth keeping:

* the payload cast takes **four** renamings and the IH's **three** — a
  binder's type lives in the context *before* it, so each is weakened
  past itself as well as past everything inner.
* `subMotK-ren = refl` — the motive mentions nothing of the ambient
  context, so pushing a renaming past its two slots is the identity.
  Without that control the `iihTy` casts would carry five stacked
  `renTy (extR (extR vs))`s with nothing to cancel them.

## Step 5 — the tuple at the mask ✅ CLOSED

| # | Attempt | Result |
|---|---------|--------|
| 1 | `imethTySubK-wf`, `imethsTyFromSubK-wf`, `⊢isubMethsK`, obligations as a `data GiveOK` | ✅ rc=0 first try — but the obligations cost **53 constructors** |
| 2 | make `GiveOK` a recursive **`Set`** instead of a datatype | ✅ rc=0, and it reduces to `Pr _ (Pr _ (Pr _ OKg))` — **three** |

★ `Lib/IWk`'s tuple walks a *prefix* and stops with a caller-supplied
tail. This one is total and interleaved (rows 11, 51, 52 of 53), so the
walk cannot end early and the obligations cannot be a suffix. Computing
them from the mask is the same move as computing the mask itself, one
level up — and the caller never names a position, so a wrong `isLookup`
is a type error rather than a silently misplaced method.

## Step 6 — `subTmK` + `⊢subTmK` ✅ CLOSED

| # | Attempt | Result |
|---|---------|--------|
| 1 | `giveK` by `eqℕ`, `giveOKK`, `⊢ielim` | ⚠ `UnsolvedConstraints`, blocked on `_give` |
| 2 | pin `{give = giveK}` at the call site | ✅ rc=0 |

⚠ `GiveOK` is a **defined `Set`**, so it is not injective: `GiveOK Γ give
0 subDescK` unfolds and consumes its `give` argument, leaving nothing to
solve the meta from. That is `pin-implicits-on-defined-set-types`,
third customer — the price of attempt 2 in step 5, and worth it.

★ **`⊢ielim` needed no cast.** It lands at `iinst i x M`, and `⊢motAppK`
takes its hypothesis in exactly that shape, so the eliminator and the IH
interface meet without a round trip between them. That was not luck: it
is why `⊢sPick`'s IH hypothesis was stated at `iinst` back in step 2.

---

# Verdict

**`subTm` is built and typed.** Six steps, ~20 recorded attempts, and the
shape of the work is unmistakable in the table: **every genuinely hard
step was a correction to an interface, not a failed proof.**

| step | attempts | what actually blocked it |
|---|---|---|
| 1 `⊢extNK` | 7 | "build first, cast second" — an unstated premise |
| 2 `⊢sPick` | 2 | closedness cannot cross a substitution ⇒ `IsNum` |
| 3 `⊢isubPay` | 6 | a κ ford is not a copy ⇒ `fordMap` |
| 4 `⊢isubMethodK` | 2 | wrong module; and τ's hypotheses are reductions |
| 5 the tuple | 2 | 53 obligations vs 3 |
| 6 `subTmK` | 2 | a defined `Set` is not injective |

Once each interface said what the goal was actually asking, the
derivations went in first try — steps 2, 3, 5 and the whole of `⊢isubPay`
did exactly that. **The cost was never the proofs.**

Rows get added here as they are tried, **before** the next attempt.

* ⬜ **5.** the tuple at the mask
* ⬜ **6.** `subTmK` + `⊢subTmK`

---

## Step 7 — `nrs`'s pointwise law (`Knot/RenSpec`) ⬜ OPEN, 8 attempts

Added 2026-09-04. **This file was consulted at attempt 4 and immediately
paid**, which is the point of it — but the row is not closed, so the
attempts are recorded here rather than lost.

| # | Attempt | Result |
|---|---------|--------|
| 1 | `⟶*-castᵣ` at the final projection, `sub-w²-single` | ⚠ source unequal |
| 2 | move the descent inside the last step | ⚠ same mismatch |
| 3 | `⟶*-castₗ` — move the SOURCE, not the target | ⚠ same |
| — | **consulted this file** — step 1's four result-casts, the summary's *"a correction to an interface, not a failed proof"*, the slips list's *"write the statement at the context the goal prints"* | ★ all three name the row |
| 4 | ⇒ `sel-here≡`/`sel-there≡`: take the pair equality as a PARAMETER | ✅ **the interface WAS wrong**; failure moved to one position |
| 5 | + `Lib/Wk.towerP` — `towerA`'s sibling at de Bruijn 1 | ✅ lemma right; same position |
| 6 | probe: deliberate mismatch, PRINT the chain | ★ endpoint legible for the first time |
| 7 | state `pay≡` with its full type, not `_` | ⚠ same |
| 8 | inline the pair so `sel-here≡` can decompose it (a `Def` hides the constructor) | ⚠ same |

**What the failure is not.** Not a missing lemma: `towerP`, `sub-w²-single`
and the `≡`-taking projections all typecheck and have visibly the right
types. Not a cast at the wrong end: attempts 1–3 covered both ends.

**★ What it costs to keep guessing.** Eight attempts converging on ONE
mismatch is this file's own signature for *the model is wrong, not the
step* — step 1 says "try another cast could not have converged". ⇒ parked
deliberately, to be re-attempted from `Lib/ISubRed`, where the same two
interfaces are exercised at 53 rows and a defect has fifty siblings to be
triangulated against.

### ★★ What this row already bought

Two interface corrections, both committed, both required by `sub-agree`:

* `Lib/IMeths.sel-here≡` / `sel-there≡` — a method's payload arrives as a
  substitution chain that collapses only PROPOSITIONALLY, so a projection
  lemma may not demand a literal pair.
* `Lib/Wk.towerP` — a payload sits at de Bruijn **1** and returns the
  MIDDLE substitution's value, where `towerA`/`towerJ` sit at 2 and 3.

⚠⚠ **And `extR`/`single` never exposed either**, because their collapse
happened to be definitional. The wrong interface survived two customers
before biting — **which is exactly how `wkK` survived**. The session's
own thesis, reproduced by its own tooling.

