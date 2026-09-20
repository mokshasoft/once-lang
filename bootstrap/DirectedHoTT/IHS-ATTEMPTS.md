# `ihsK` / `iihsK` / `iextK` adequacy — the attempts log

**Why this file exists.** Three logs before it closed their proofs not on
the next attempt but by tabulating the previous ones and reading the *why
it failed* column: `poc/OCP0009/GAP-A-ATTEMPTS.md` (51 attempts),
`SUBTM-ATTEMPTS.md`, `OCC-ATTEMPTS.md` (34). `ι-ielim` landed on
2026-09-17 and put three new ⬜ OWED entries on the ledger, so the fourth
place guesses will stack gets the same treatment from the start.

**The rule:** an attempt that is backed out gets a row *before* the next
one is tried. ⚠ The useful column is **Why it failed**, not *What was
tried* — two attempts that fail for the same reason are one attempt.

---

## 0. WHAT THE THREE EARLIER LOGS SAY, BEFORE ANY ATTEMPT HERE

Read this section first. Every line is something that cost ≥4 attempts
somewhere else in this tree.

1. ★★★ **Diff against the nearest WORKING proof before hypothesising.**
   `OCC` proposed and refuted **six** mechanisms; the answer came from
   reading `SzAgree`, which was 40 lines away the whole time.
2. ★★ **A mechanism is not a diagnosis until something ISOLATES it.**
   `OCC` 12 and 13 both *reproduced the observed boundary exactly* and
   both were wrong. The spike that settled it cost two commands.
3. ★★★ **The STATEMENT is usually what is wrong, not the proof.** `OCC`'s
   root error was pinning the index in the ROW statement — made on day
   one, found at attempt 28. `SUBTM`'s verdict: *every genuinely hard
   step was a correction to an interface, not a failed proof.*
   ⇒ **row-level statements QUANTIFY the index; the top-level theorem
   ties it.** Those are different statements.
4. ★★ **Split a stuck residue into the half that REDUCES and the half
   that is merely EQUAL.** `conSSK` read one residue as one thing for
   four attempts; projections are reductions (`sel-here`), leftover
   weakenings are equalities (`sub-w²-single`).
5. ★★★ **FIGHT THE DEFINITION.** `occOp` put the fold's accumulator under
   a `lam`; ~30 attempts went into discharging the resulting `extR`, and
   a closed combinator deleted the obligation by `refl`. **Nothing left
   to prove.**
6. ★ **Every generated adequacy module needs its OWN head-red** naming
   the concrete method. `Lib/IHeadRed.ihead-red` works only where the
   caller already names the method — which, for `ihsMethsK`, it does.
7. ★ **Develop in `bootstrap/tmp/`** (measured 154×), and **pin every
   implicit on a substitution chain at once**, not a layer at a time.

---

## 1. THE DEPENDENCY CHAIN — five of the 22 OWED entries, in order

`ι-ielim` added `iihsK` and `ifieldsK`; they sit on top of three older
entries. The chain, cheapest first, with each step's REAL size:

| # | entry | shape | depends on |
|---|---|---|---|
| 1 | ✅ `ihsK` | induction on **`DCon` — 3 cases** | nothing |
| 2 | ✅ `fieldsK` | **1** `Tm-appK` congruence | 1 |
| 3 | ✅ `iextK` | composition + a β + **5 naturality lemmas** | `sub-agree` ✅ `single-Represents` ✅ `extS-Represents` ✅ |
| 4 | ✅ `iihsK` | induction on **`ICon` — 3 cases** + `nat7` | 1, 3 |
| 5 | ✅ `ifieldsK` | **1** `Tm-appK` congruence | 4 |

★★★ **`ihsK` IS A THREE-CASE INDUCTION, NOT A 53-ROW ONE**, and this is
the single most useful fact in this file. `ihsK n C D ms p` eliminates an
ENCODED `DCon`, and `Knot/Map` gives that sort exactly three
constructors:

```agda
enDCon dι        = DCon-iK
enDCon (dρ y0)   = DCon-rhoK (enDCon y0)
enDCon (dκ y0 y1)= DCon-kapK (enTy y0) (enDCon y1)
```

Rows 0–42 and 46–52 of `ihsMethsK` are junk and are **unreachable** — no
`enDCon` ever produces their tags. ⇒ the adequacy is `conSSK`'s shape (2
rows, CLOSED) and not `occK`'s (53 rows, 34 attempts). Same for `iihsK`
over `ICon`. ⚠ The ledger entry's *"SPLIT ACROSS FIVE MODULES FOR SIZE"*
is about BUILDING the program and says nothing about proving it.

★ **AND THE `dρ` ROW OWES NO OTHER ENTRY.** `ihs D ms (dρ C) p =
pair (elim D ms (fst p)) (ihs D ms C (snd p))`, and the encoding is
structural on the nose:

```agda
enTm (pair a b)      = Tm-pairK (enTm a) (enTm b)
enTm (elim D ms t)   = Tm-elimK (enDesc D) (enTm ms) (enTm t)
enTm (fst p)         = Tm-fstK (enTm p)
```

`ihsRho`'s body is `Tm-pairK (Tm-elimK …) (app⁴ …)` — the same three
nodes. There is no object-level `elim` PROGRAM to discharge, only the
encoding congruence. ⇒ step 1 is genuinely free-standing.

### The three hazards step 1 will meet, named in advance

* **the index must be QUANTIFIED in the row statement** (`OCC` 25/28) —
  `iihs` hands each child `subTm (isingle i) (pair s (snd (var vz)))`, so
  a row pinned at a particular index cannot apply to any child;
* **the IH needs three moves, not one** (`OCC` step A att. 6) — project
  (`βfst`), then fix the child's INDEX and its SCRUTINEE, at different
  depths;
* **its own head-red**, naming `ihsAt k` (`OCC` step A att. 4).

---

## 2. Step 3 — `iextK` · ATTEMPTS

Developed in `bootstrap/tmp/IextAgreeTmp.agda`.

Statement (the ledger names the route: *"VIA its factorisation
`iext σ t ≡ single t ∘ extS σ`"* — and `iextK`'s body **is** that
factorisation, spelled out):

```agda
iext-Represents : {S T Θ : Cx} {σ : Sub S T} {s : RTm Θ} (t : RTm T) →
                  Represents σ s →
                  Represents {Γ = S ∙} (iext σ t)
                             (iextK (num (len S)) (num (len T)) s (enTm t))
```

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 1 | state it, prove by `done` (the diagnostic both earlier logs open with) | ✅ **statement is well-formed and well-typed.** Agda printed the goal: `app (iextK …) ⌈vz⌉ ⟶* enTm t` — the META side COMPUTES (`iext σ t vz` ⇒ `t`), so there is no meta-level obstacle |
| 2 | the composition chain — one β, `extS-Represents`, `sub-agree`, `single-Represents`, `wk-single` — with the β's four weakened slots cancelled by a local `cong₄'`, copying `Knot/SubExt.extS-Represents`'s `cong₃'` | ⚠ **`subTm` does NOT distribute into `extNK`'s arguments.** Agda: `renTm vs (subTm (single ⌈vz⌉) (w ⌈S⌉))` vs `subTm (extS (single ⌈vz⌉)) (w (w ⌈S⌉))` — one binder deeper |

★★★ **WHY ATTEMPT 2 FAILED, AND IT IS NOT A COUNTING SLIP.** I
hand-distributed `subTm (single a)` through the body. That is legitimate
for `app`/`ielim`/`pair` — constructors — but **`extNK` and `singleK`
both build a `lam`**:

```agda
singleK n u = lam (app (singleSK (pair sVar (nsuc (w n))) (var vz)) (w u))
extNK d n σ = lam (…)
```

so the substitution goes UNDER the binder as `extS (single a)` and the
arguments are weakened twice. ⇒ pushing the β through needs
substitution-NATURALITY for each: `Knot/SubNat.extNK-sub : ExtNSub` ✅
exists, `singleK-sub` ✗ does not, and `subTmAtK` hides `subMethsK`, which
needs the tuple's substitution-stability (`Knot/SubSpec`).

⚠ **Attempts 1 and 2 are ONE attempt against the chain and TWO different
facts about it.** Row 2's content is *"a β over a `lam`-building object
program leaves a naturality obligation"* — which is `SUBTM` step 8's
verdict verbatim.

### ⬜ THE DECISION ATTEMPT 2 FORCES — and it is lesson 5, prospectively

`iextK`'s body has **`occOp`'s exact shape**:

```agda
occOp f g     = lam (maxTm (app (renTm vs f) (var vz)) …)   -- cost ~30 attempts
iextK dd n σ t= lam (subTmAtK … (singleK (w n) (w t))
                                (app (extNK (w dd) (w n) (w σ)) (var vz)))
```

arguments weakened and placed under a `lam`. `OCC` 32–34 closed that by
making the operator a CLOSED COMBINATOR applied to its arguments, after
which the commutation held by `refl` — *"no naturality lemma was needed,
there was nothing left to prove"*.

⚠⚠ **DO NOT ACT ON THIS WITHOUT THE ISOLATION** (lesson 2 — this file's
predecessors are 0 for 6 on mechanisms that merely reproduce the
symptom). The isolation is `tmp/MaxFnSpike.agda`'s analogue and costs two
commands: does a closed-combinator `iextK` make the β's residue `refl`?

⚠ And it is a DESIGN change with blast radius — `iextK` is called by
`Knot/IihsRho` and `Knot/IihsKap`, both green as of `e9293a0a`, and by
`⊢iextK`. It is a decision, not a proof step.

★ **THE CHEAPER ALTERNATIVE, and it should be priced first:** attempt 3
is not forced to go through the β at all. `Knot/SubSpec.extNK-vz` /
`extNK-vs` exist precisely because `extS-Represents` is then three lines
(`extS-Represents d h vz = extNK-vz d _ _ _`). The same split here gives
`iextK-vz` / `iextK-vs` as REDUCTION laws in `Knot/IExt`, and
`iext-Represents` becomes their packaging — `single-Represents`'s own
shape, and the record says explicitly *"the two lemmas ARE the two
clauses"*. That keeps the β bookkeeping in one place instead of at every
call site, and needs no definition change.

⬜ **NEXT: attempt 3 = `iextK-vz` as a standalone reduction law**, in
`tmp/`, copying `Knot/SubSpec.extNK-vz`'s `step (β _ _) (⟶*-castₗ (cong₂ …
(wk-single …) (wk-single …)) …)` — note that `extNK-vz` LEAVES
`subTm (single …) (w σ)` uncancelled, because the lemma it chains into is
generic in that slot. Cancel only what the next lemma PINS.


---

## 3. Steps 1 and 2 — `ihsK` and `fieldsK` ✅ **CLOSED 2026-09-17**

Developed in `bootstrap/tmp/IhsAgreeTmp.agda`, promoted to
`Examples/Knot/IhsAgree`.  **Five attempts**, and §1's predictions held:
three cases, no other ledger entry, and the index quantified.

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 1 | state it with the index QUANTIFIED, prove by `done` | ✅ well-formed and well-typed; Agda printed the three goals and the meta side COMPUTES (`ihs D ms dι p` ⇒ `unit`) |
| 2 | row `dι` — head-red at tag 43 + seven βs | ✅ **rc=0 first try, and NO CAST.** `Tm-unitK` is built from constructors and numerals, so seven substitutions leave it alone definitionally |
| 3 | row `dρ` — head-red at 44, seven βs, two `βfst`s, the IH | ⚠ `subTm (single ⌈p⌉) (subTm (extS (single ⌈ms⌉)) (w (w ⌈D⌉))) != ⌈D⌉` — the weakening tower `ConSAgree` warned about |
| 4 | + one `⟶*-castₗ` cleaning all four slots at once | ⚠ **UnsolvedMetaVariables, ZERO type errors** — the `_` in `towerJ⁵ … _` |
| 5 | pin the tower's landing value (the head-red's own `iihs` term) | ✅ **rc=0**, all three rows; `ihsK-agree` and `fieldsK-agree` followed with no further search |

★★★ **THE TOWER IS ONE RUNG PER BINDER THE SLOT PASSES UNDER**, and the
seven-lam body makes it a countdown: `p` none · `ms` `wk-single` · `D`
`sub-w²-single` · `n` `towerJ` · the IH `towerJ⁵`.  ⚠ `Knot/Ihs.⊢ihsAppK`
already pays `towerJ p ms D n` for the very same slot — **the typing side
had counted this and the proof side re-derived it.**  Read the `⊢…AppK`
lemma of a program before writing its adequacy; it is the same arithmetic.

★★ **ATTEMPT 4 IS THE ONE WORTH REMEMBERING.** It reported *unsolved
metas and not one type error* — i.e. the chain was RIGHT and only a
landing value was unnamed.  `SUBTM` step 8 found the same thing over four
rounds and concluded *"on a substitution chain, pin everything at once
rather than discovering it a layer at a time."*  Here it cost one round
because the log said so first.

★ **AND THE `dρ`/`dκ` ROWS SHARE THEIR CHILD'S INDEX**, `pair sDCon
(snd i)`.  `dκ` reaches it through `iext (isingle i) (fst p)` applied to
`var (vs vz)`, and `iext σ v (vs x) = σ x` takes that straight back to
`i` — so the two rows differ only in the projection depth of the IH
(`fst ihs` vs `fst (snd ihs)`) and in `dρ`'s `Tm-pairK` wrapper.

⇒ **NEXT:** step 3 (`iextK`) is unchanged by this — its two logged
attempts stand, and the `iextK-vz`/`iextK-vs` route in §2 is still the
one to price first.


---

## 4. Step 3 — `iextK` ✅ **CLOSED 2026-09-18** (attempts 3-4)

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 3 | build the naturality cascade FIRST, then the β law | ✅ **rc=0**, five lemmas, every one a template copy |
| 4 | `iextK-app` (the β law, generic in the variable) + `iext-Represents` | ✅ **rc=0**, and the agreement is `single-Represents`'s three lines |

★★★ **THE LEDGER'S PREDICTION WAS RIGHT AND ITS REASON WAS WRONG.** The
entry said `iextK` *"owes a factorisation lemma FIRST — the same two-step
debt `iconSK` carries"*. There was **no factorisation lemma to write**:
`iextK`'s body already IS `single t ∘ extS σ`, spelled out. What it
actually owed was the β of its **own `lam`** — `extNK` and `singleK` both
BUILD a `lam`, so the substitution goes under the binder and their
arguments are weakened twice:

    singleMethsK-sub ← extMethsK-sub    singleSK-sub ← extSK-sub
    singleK-sub      ← extNK-sub        give-sub     ← renGive-sub
    subMethsK-sub    ← renMethsK-sub    ⇒ subTmAtK-sub

⇒ **the discriminator against `iinstK` is not "composition vs not" — it
is whether the composite sits under a binder of its own.** `iinstK`
applies `subTyAtK` to arguments and consumes it immediately; `iextK`
passes `extNK …` as an argument, so it stays a `lam`.

★★ **AND THE CASCADE WAS OWED DOWNSTREAM ANYWAY.** `Knot/IihsRho` calls
`subTmAtK` inside a seven-lam body, so `subMethsK-sub` is on the path to
`iihsK` whatever route `iextK` took. **That is what decided it against
the §2 "fight the definition" option** — the isolation the log demanded
was never run, because the cheaper route turned out to produce something
step 4 needs. ⚠ Record that as the reason, not as a refutation: the
closed-combinator `iextK` may still be the better definition, and
nothing here measured it.

★ **ONE TRAP, and it is an old one:** `with eqℕ k 11 … | true` made
`true`/`false` PATTERN VARIABLES — `𝔹`'s constructors were not imported,
so `pickTm` never reduced and every branch was the same stuck term.
Agda says `PatternShadowsConstructor` and then reports the error
somewhere else. `agda-unimported-constructor-trap`, and
`Knot/SubSpec:65` imports them for exactly this reason.

⇒ **NEXT:** step 4, `iihsK` — three cases on `ICon`, needing `ihs-agree`'s
shape plus `iext-Represents` (now available) and `subTmAtK`'s agreement
for the `iρ` row's recursive index.


---

## 5. Steps 4 and 5 — `iihsK` and `ifieldsK` ✅ **CLOSED 2026-09-18**

| # | attempt | outcome / **why** |
|---|---------|-------------------|
| 1 | state it, index PINNED at `pair sICon ⌈\|Δ\|⌉`, prove by `done` | ✅ well-typed |
| 2 | row `iι` — head-red at tag 48 + seven βs | ✅ `ihs-agree`'s `dι`, one description over |
| 3 | row `iκ` — + the `iextK` call and `iext-Represents` | ⚠ `renTm vs (…tower…) != subTm (extS …) (…)` — the `iextK`-internal slots sit ONE BINDER DEEPER |
| 4 | row `iρ` — same cast shape | ⚠ same, and `subTmAtK` too (it hides `subMethsK`) |
| 5 | `nat7` + `iextK-sub`, both slots lifted out first | ⚠ **UnsolvedMetaVariables, ZERO type errors** |
| 6 | pin all eleven slots of each `nat7`, via a `where` block | ✅ **rc=0**, all three rows; the two wrappers followed |

★★★ **THE COST WAS NEITHER OF THE TWO THINGS THE LEDGER PREDICTED.** It
said `iihsK`'s adequacy is *"`ihsK`'s PLUS the commutation of `iextK` and
`subTmAtK`"*, and that was right — both were discharged first and nothing
else was owed. But the work was that **a method body which CALLS a
`lam`-building program meets all SEVEN of the βs' substitutions**, so
that program's arguments sit one binder deeper than any ambient tower
describes. `iextK` and `subTmAtK` are both such calls.

⇒ `nat7`: a seven-fold lift taking the program's own naturality as a
hypothesis. **One lemma for both**, because both are 4-ary — and with the
seven substitutions left abstract and the program a parameter, nothing
unfolds (`abstract-the-substituted-terms`).

★★ **ATTEMPT 5 IS THE THIRD TIME THIS SESSION** that *unsolved metas with
zero type errors* meant "the chain is right, pin the landing values".
`ihs-agree` attempt 4 and `subMethsK`'s cascade were the others. It is
now a reliable reading, not a guess.

★ **ON PINNING THE INDEX.** `OCC-ATTEMPTS` 28 says a pinned row index is
fatal. It is not — what is fatal is pinning to something the child cannot
be *reduced* to. `iihsRho` READS the index (`snd ⟨i⟩` is the ICon's own
depth), so quantifying it away was not available; and `cICon-rho`'s tail
sits at `pair sICon (nsuc (snd ⟨i⟩))`, which one `βsnd` under
`⟶*-ielimⁱ` takes to the IH's own form because `len (Δ ∙) = suc (len Δ)`
is DEFINITIONAL. ⇒ **the rule is "pin only what the child reduces to"**,
and `occ`'s child (`subTm (isingle i) …`) reduced to nothing.

★ `Lib/Wk` stops at `towerJ⁵` (de Bruijn 4). The `iρ` row reads the
PAYLOAD at 5 and the ambient INDEX at 6, so `tower⁶`/`tower⁷` are written
here. ⬜ They belong in `Lib/Wk`, and its own header already says the
family wants INDEXING rather than listing — that is now four entries of
evidence, not two.

★ And `Lib/Wk` already had general `cong₃`–`cong₆`. Three modules in this
chain had grown RTm-specific copies before anyone looked.

⇒ **THE `ι-ielim` CHAIN IS CLOSED**: `ihsK`, `fieldsK`, `iextK`, `iihsK`,
`ifieldsK` — five entries, 22 OWED down to 17.


---

## 6. ★★★ THE RULE THAT CHANGED THE COST — *don't prove what is already proved*

Raised by the user after `payTyK`, and it has TWO halves. Both were
costing real attempts before they were stated.

**(a) THE KERNEL.** `payTy`'s object side weakens explicitly (`wkAtK`)
where the meta does not, and I was about to prove the bridge. It was
already there: `Spec/Syntax.payTy-ren : renTy ρ (payTy D C) ≡ payTy D C`.

⇒ **before starting any adequacy, grep the kernel for the meta's own
`-ren`/`-sub`/`-cong`/`-inst` lemmas.** The survey, which cost two greps:

| meta | kernel lemmas |
|---|---|
| `payTy` | `payTy-ren`, `payTy-sub` |
| `ipayTy` | `-cong`, `-ren`, `-sub`, `-renⁱ`, `-subⁱ` — **five** |
| `atCon` / `iatCon` | `atCon-inst`, `iatCon-inst` |
| `ihTy`, `iihTy`, `methsTyFrom` | none in `Spec/` … |

★★★ …**but `Metatheory/TySub` proves them all**: `ihTy-sub`,
`methsTyFrom-sub`, `iihTy-sub`, `iatCon-sub`, `methTy-sub`,
`imethTy-sub`, `atCon-sub`, plus the `-ren` twins. Every remaining entry
of this family has its bridging lemma written already. **Search
`Metatheory/`, not only `Spec/`.**

**(b) THE PROOFS ALREADY DONE.** The second half, and the one that
actually shortened `ihTyK`: `wkTyK-sub`, `⟶*-wkTyKᵈ`, `⟶*-wkTyKᵃ` and
`nat4₂` were built for `payTyK` the day before and IMPORTED here rather
than rebuilt. `ihTyK`'s three rows then went in **first try**, against
`payTyK`'s six attempts and `lookupDK`'s thirteen.

⚠ **AND THE COUNTER-EXAMPLE IN MY OWN WORK.** I wrote the
"lift a naturality through a stack of β-substitutions" fold **four
times** — `nat7` (7-fold, 4-ary), `nat4₂`, `nat5₂`, `nat5₄` — before
noticing that `Lib/ISub:871` and `Knot/SubExt:151` already carry the same
idea as a local `unc`. And `Lib/Wk` already had general `cong₃`–`cong₆`
while three modules grew RTm-specific copies.
⇒ `nat5₂'` is now ONE `trans` over `nat4₂`: **each fold count is one line
over the previous**, which is how the family should have grown from the
start. ⬜ It still wants a single `Lib` home parameterised by arity.

★ AND THE DISCRIMINATOR FOR WHEN A BRIDGE IS NEEDED AT ALL: read the
META. `ihTy D (dρ C) q M = Σ' … (renTy vs (ihTy D C (snd q) M))` carries
`renTy vs` ITSELF, so `wkTyK-agree` lands on the answer and NO cast is
owed. `payTy` carries none, so it needed `payTy-ren`. Same family, one
has the debt and one does not, and the definition says which.


---

## 7. ⛔ THE `IhITyAgree` SPLIT — TRIED, MEASURED, **REFUTED**

`Knot/IhITyAgree` costs **3482 s (58 min)**, the most expensive module in
the tree. Its `iρ` row's cast nests `nat7 iinstK` beside `nat7₂ wkTyK`,
and `iinstK` unfolds to four nested programs. The ledger entry records
⬜ OWED: *"move the cast equalities into their own module so they are
`Def`-backed ACROSS a module boundary and elaborated once"*.

**Done, and it does not work.**

| | wall |
|---|---|
| `where`-bound inside the clauses (committed) | **3482 s** |
| extracted to `Knot/IhITyCast`, applied | **3544 s** |
| `Knot/IhITyCast` ALONE, parameters abstract | **46 s** |

★★★ **THE 46 s IS THE TRAP, AND I FELL IN IT.** I measured the extracted
module standalone, saw 46 s against 58 min, and reported a ~75×
improvement. That number is real and it means nothing: standalone, the
module's seven parameters stay ABSTRACT. At the use site `IhITyAgree`
instantiates all seven at concrete encodings, and Agda re-elaborates
exactly as before.

⇒ `half-generalization-is-worst`, verbatim: *"A generic lemma is only
generic if its argument stays ABSTRACT at the use site."* `LESSONS.md` §3
has said so since the `Lib/IFold` vs `Examples/WkFin` measurement, and
this is another instance — the abstraction bought nothing because the
caller is an enumeration over three concrete rows.

⚠ AND IT IS ALSO `verification-that-covers-less-than-it-claims`: the
timing I quoted was produced by a run that did not do the work being
claimed. **Measure the CALLER, not the definition**
(`judge-abstractions-at-the-use-site`).

★ WHAT *DID* HELP, and it is the only thing that did: `where`-binding the
three lifts rather than inlining them. Inline, the clause did not finish
in FORTY MINUTES; `where`-bound it completes at 58. That is a real
effect and it is already in the committed version.

⬜ STILL OPEN. The cost is the elaborated size of a cast that mentions
`iinstK` seven times over a seven-substitution stack, and no relocation
of that cast changes it. A fix has to make the cast SMALLER — e.g. a
`⟶*`-level route that never needs `nat7 iinstK` at all — not move it.
**Reverted; the committed version stands.**

------------------------------------------------------------------------
## §8 — THE BOOLEAN-PREMISE CLUSTER, CLOSED IN ONE SITTING (2026-09-20)

`pwK`, `stkAK`, `stkCK`, `flatK` — four ledger entries, 120 rows, and the
whole batch cost less than `iextK` alone did.  Recorded because the
TRIAGE was right in advance for once, and it is worth knowing why.

**THE TRIAGE.** §6's rule says size an entry by its METHOD BODIES.  These
four have the two properties that make an `ielim` adequacy cheap, and
they are exactly the two whose ABSENCE cost `Knot/IhITyAgree` 58 minutes:

| | `IhITyAgree` | these four |
|---|---|---|
| motive | DEPENDENT (`iinst` over a 7-substitution stack) | CONSTANT `Nat` |
| method bodies | mention the index under 7 binders | CLOSED, or the innermost binder |
| ⇒ per row | a cast needing `nat7 iinstK` | three βs and stop |

A constant motive means `iinst i t Nat` **is** `Nat`, so not one of the
120 rows carries a cast.  A closed body means the weakening tower is
ZERO RUNGS.  28 of `pw`'s 30 rows are three βs; 29 of `stkA`'s are.

⚠ AND A CONSTANT MOTIVE IS NOT SUFFICIENT — `occK` has one too, and
`Knot/OccAgree` is still the biggest generated module in the tree.  The
difference is that `occ` FOLDS its IH tuple, so every row owes the
`maxℕ`/`_∨_` reassociation `occSum-red` needs.  These four read ONE slot
or none.  ⇒ the sharp predicate is **does the row consume its IH tuple**,
not **is the motive constant**.

**WHAT THE CONTENT ACTUALLY WAS: the SELECTION.**  `Knot/Pw` and
`Knot/Stk` build segmented tuples — constant runs with explicit
overrides BETWEEN them, because the overrides sit at rows 19-22, 26 and
37-40, in the middle of 53, where no `cdTake` prefix reaches.  Reaching
row k means walking its segment, and the walk mixes two combinators that
compose DIFFERENTLY:

    methsFrom-past   crosses a constant run — a ⟶* STEP, composed with »
    sel-there        crosses an explicit slot — a CONGRUENCE, which WRAPS

⇒ `_seg_sel` in `gen-knot.py` walks a declared segment map and emits the
composition.  `pw` is five segments, `stkA` ten, `stkC` eleven, `flat`
four; the generator is identical and only the map differs.

**THE ONE ROW THAT OWED ANYTHING.**  `stkC? (⌜Hom⌝ C a b) = stkA? C` and
`flat? (⌜Hom⌝ c a b) = stkC? c` are CROSS-CALLS, not folds, so their
methods apply the callee's PROGRAM to the payload's first field.  That
body names the INDEX binder — `var (vs (vs vz))`, the OUTERMOST of the
three — so after the βs it has been weakened twice and substituted
twice: `sub-w²-single` plus `wk-single` on the payload.  A lemma that
already existed, at `Knot/LookupD`'s depth 2.

⇒ the four form a CHAIN (`stkA` → `stkC` → `flat`), not a mutual block,
which is why each is its own module and each compiles cheaply.

**METHOD.**  Every shape was proved STANDALONE in a temp module before
the generator learned to emit it — four selection shapes, three chain
shapes, then the cross-call row.  Every one went green on the FIRST
attempt, and the 120 generated rows needed a single fix (a `sel-there`
dropped in transcription).  `temp-module-dev-cycle`, and the contrast
with `lookupDK`'s thirteen attempts is the whole argument for it.

------------------------------------------------------------------------
## §9 — `pwBodyK`/`pwDefault`: SIZED, AND IT IS REUSE (2026-09-20)

Unblocked by §8: the ledger entry said `pwDefault`'s adequacy *"only
means anything relative to `pwK`'s fold — and `pwK` is itself OWED"*.
`pwK` is now discharged.

    pwBody (⌜Π⌝ γ δ)     = δ
    pwBody (⌜Hom⌝ C a b) = ⌜Hom⌝ (pwBody C) (app (w a) vz) (app (w b) vz)
    pwBody t             = renTm vs t          ← 28 of the 30 rows

★★★ THE DEFAULT ROW IS A PROOF WE ALREADY HAVE.  `pwDefault k`'s body is

    app (app (renTmK i (icon k p)) (nsuc (snd i))) (vsRenK (snd i))

and `Knot/RenTm.renTmAtK s dd m rn t = app (app (renTmK (pair s dd) t) m) rn`
— so at `i = pair sTm ⟨len Γ⟩` the row's subject IS `renTmAtK`'s, and

    Knot/RenAgreeTie.ren-agree : RepresentsR ρ r → (t : RTm Γ) →
      renTmAtK sTm ⌈Γ⌉ ⌈Δ⌉ r ⌈t⌉ ⟶* ⌈ renTm ρ t ⌉        ✅ DISCHARGED
    Knot/SubSpec.wk-Represents : RepresentsR vs (vsRenK ⌈len Γ⌉)  ✅ EXISTS

closes all 28 in one lemma.  ⇒ §6's rule again, and this is the largest
instance of it so far: 28 rows for two names.

**WHAT IS ACTUALLY OWED.**
  · the tower on the default row — `i` occurs THREE times in the body,
    but at ONE depth, so it is one `sub-w²-single` inside one `cong₂`,
    exactly `stkCHom`'s cast;
  · `snd i ⟶ ⟨len Γ⟩` by `βsnd`, under two congruences (the depth
    argument and `vsRenK`'s), before `ren-agree` applies;
  · row 20 (`pwPi`) — `pwBody (⌜Π⌝ γ δ) = δ` is a payload projection;
  · row 22 (`pwHom`) — the IH plus `⌜Hom⌝`'s two endpoint terms
    `app (w a) vz`, whose `w` is `renTm vs` AGAIN and so is `ren-agree`
    a third time.

⚠ THE INDEX MUST BE PINNED HERE, unlike §8's four: `pwDefault` READS
`snd i`, so a quantified index leaves the depth stuck.  §7's warning
(*"a row that PINNED its index could never match a child"*) does not
apply — it was about `occ`, whose children sit at DIFFERENT depths.
`⌜Hom⌝`'s three fields are all at the AMBIENT depth, so the child's
index `subTm (isingle i) (pair sTm (snd (var vz)))` REDUCES back to the
pinned form, and `⟶*-ielimⁱ` is where that happens.
