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
| 1 | `ihsK` | induction on **`DCon` — 3 cases** | nothing |
| 2 | `fieldsK` | 2 `Tm-appK` congruences | 1 |
| 3 | `iextK` | composition + a β | `sub-agree` ✅ `single-Represents` ✅ `extS-Represents` ✅ |
| 4 | `iihsK` | induction on **`ICon` — 3 cases** | 1, 3 |
| 5 | `ifieldsK` | 3 `Tm-appK` congruences | 4 |

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
