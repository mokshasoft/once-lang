# OCP-0009 — PLAN: THE JUDGEMENT LAYER

Companion to `PLAN-INDEXED.md`, which took the SYNTAX into the kernel.
This one takes the JUDGEMENTS. It is a build plan, not a spike record:
the spikes are done and §1 says what they settled, so that nothing here
is re-discovered.

Read `HANDOFF-2026-08-27.md` first for session state; read
`tools/gen-knot.py`'s header for the syntax encoding this builds on.

---

## 1. WHAT IS ESTABLISHED — do not re-spike any of this

| | question | verdict | where |
|---|---|---|---|
| a | a **dependent** index telescope (`I = Σ' (El ⌜Nat⌝) (Tm ⟨d⟩)`) | ✅ + inhabited | `Examples/DepIx` |
| b | an **index-shifting** motive, with a Forded transport | ✅ + computes | `Examples/WkFin` |
| c | it scales to a **syntax with a binder** | ✅ | `Examples/WkTm` |
| d | an **index-dependent Π** (Kripke) motive | ✅ + computes | `Examples/KripkeIx` |

Three facts from those that shape everything below:

* ★ **BINDERS DO NOT FORCE A KRIPKE MOTIVE — SUBSTITUTION DOES.**
  Weakening at the outside shifts the index uniformly, so
  `M(i,t) = Tm (suc ⟨i⟩)` suffices for `wkTm`. What needs a motive that
  is a function of the substitution is `subTy (single u)`, i.e.
  `⊢app`'s index.
* ★ **FORDING COSTS A TRANSPORT IN THE DERIVATION AND NOTHING AT
  RUNTIME.** `jsub d (symN a (idrefl ⌜Nat⌝ x)) e ⟶* e` in two steps:
  the ford witness IS an `idrefl`, so the transport evaporates.
* ★ **ONLY FAMILIES WITH COMPUTED TARGET INDICES PAY THE FORDING TAX.**
  `TmD` is ford-free (`iι` targets the ambient); `Fin`'s `fzero`/`fsuc`
  are not. Do not assume every encoded family needs transports.

## 2. WHAT IS **NOT** ESTABLISHED

⚠ Read this before quoting §1 at anyone.

* Object-level **substitution is not built**. §1d shows the kernel does
  not block it; it does not show the code exists.
* `extS` needs a **`Fin` eliminator** to case on `vz`/`vs`. That is
  `WkFin`-shaped and known to work, but is not written.
* ~~**`Ctx` is not encoded.**~~ ✅ DONE — step 0 below. ⚠ But **not as
  the 8th sort**: it is its OWN 2-row family over a bare depth,
  `Examples/Knot/CtxD`. It was the 8th sort for one day; `Negative/WkEmp`
  is what that cost.
* Reduction is tested only at **small concrete inputs**. Nothing is known
  about `ielim` reduction at knot scale.
* The **168 rows** are not written.

## 3. BUILD ORDER

### Step 0 — `Ctx`, ENCODED  ✅ **DONE 2026-08-27**

⚠ **NOT AS THE 8th SORT, WHICH IS WHAT THIS SECTION USED TO SAY.** It was
built that way first, and the first knot-wide traversal is what refuted
it. `Examples/Knot/CtxD` — 2 rows, index a BARE DEPTH, no sort tag and so
**no tag ford at all**.

| | |
|---|---|
| the family | `CtxD`, `CtxWf`, `CtxK` — hand-written, 2 rows |
| the smart constructors | `Ctx-empK` / `Ctx-extK` at an abstract `num n` |
| the adequacy map | `enCtx` / `⊢enCtx`, §6 of the same module |
| inhabited | `◇ ▹ Nat` at depth 1 |
| `KnotD` | back to **53** rows, untouched by any of this |

★★ **WHY, AND IT IS THE DESIGN OUTPUT OF THE INCREMENT.** `Ctx` is not a
sort of the syntax. The seven families in `KnotD` are one mutual
recursion in `Spec/Syntax`; `_▹_` carries an `RTy ⌊ Γ ⌋`, so `Ctx`
depends on the syntax and the syntax never depends back. **A
one-directional dependency is a STRATUM, not a member.**

★ **AND THE INDEX MEANT TWO THINGS.** `KnotD`'s second component is the
AMBIENT SCOPE a term lives in — a parameter. A context's depth is its OWN
LENGTH — a measure of the datum. Sharing one slot forced `Knot/Map` to
grow a THIRD signature shape for `⊢enCtx` (`len ⌊ u ⌋`, read off the
argument). That was recorded as an oddity; it was a symptom.

⚠⚠ **AND THE REFUTATION IS A GREEN BUILD, WHICH IS WHY IT NEEDED
BUILDING.** As sort 7, the uniform weakening motive's `◇` method holds
`snd ⟨i⟩ ≡ nzero` and would have to prove `nsuc (snd ⟨i⟩) ≡ nzero` to
rebuild itself — but `K (sCtx, 1)` is inhabited, so a DIFFERENT
constructor closes the goal. It compiled, `--safe`, trust surface empty,
and computed `⋄ ↦ ◇ ▹ Nat`. `Negative/WkEmp` is that module, kept RED.

⇒ ★★★ **AND SPLITTING MADE `wk`'s TYPE TRUE.** With `Ctx` out,
`wkK : K (s,d) → K (s, suc d)` is honest at all 53 sorts: the closed
sorts' depth is degenerate so shifting is harmless, `ICon` is genuinely
scoped, and no row has to invent anything. The fix was not a
restriction — it removed the need for one.

**What the split costs and saves, measured on the rows themselves:**

| | as sort 7 | as `CtxD` |
|---|---|---|
| fords per row | 2 (tag + depth) | **1** (depth) |
| index | `Σ' Nat Nat` | `El ⌜Nat⌝` |
| `_▹_`'s `num-ren`/`num-sub` chains | 14 | **9** |
| `⊢ixP` on the ambient, `fordFst`, `βfst` | throughout | **absent** |

★ **THE ONE THING THAT WAS UNTESTED WENT THROUGH FIRST TRY.** `_▹_`'s
`RTy` field has a TYPE in another family, so it is a κ field carrying a
`⌜IMu⌝` code (`icw-imu`, PLAN-INDEXED §12) **at an index mentioning a
BOUND field** — a combination of three separately-built things
(`Scoped.varC`, `DepIx.islamC`, `DepIx`'s ford naming `var vz`) that had
never been put together. ⚠ Fording could not do this job: it turns a
computed INDEX into a constraint, never a field's TYPE into a family.
Both mechanisms sit in `_▹_`, three lines apart.

⚠ **AND THE COVERAGE GUARD MOVED WITH IT.** `gen-knot.py`'s `verify()`
is back to one file and no longer mentions `Ctx` — not because `Ctx` is
unchecked, but because `enCtx`'s clauses check it. Agda's coverage
checker checks FUNCTIONS, so a hand-written table with a hand-written map
is already guarded; a GENERATED table with a GENERATED map is not, which
is the whole reason `verify()` exists. **Controlled**: deleting `enCtx`'s
`_▹_` clause gives `Incomplete pattern matching for enCtx`.

### Step 1 — ★ `_∋_∷_`  ⟨THE FIRST REAL JUDGEMENT, and it is reachable NOW⟩

    here  : (Γ ▹ A) ∋ vz ∷ renTy vs A
    there : Γ ∋ x ∷ A → (Γ ▹ B) ∋ vs x ∷ renTy vs A

Two constructors, and it mentions **only** `Ctx`, `Var`, `RTy` and
`renTy vs` — weakening by ONE, which `Examples/WkTm` already provides in
the `Tm` case and which needs the same treatment for `RTy`.

✅✅ **DONE 2026-08-28** — `Examples/Knot/Lookup`. Well formed AND
inhabited: `LkD`/`LkWf`, and `⊢lkVz` at `(◇ ▹ Nat) ∋ vz ∷ renTy vs Nat`.
★ The three transports EVAPORATE at a concrete index, so §1's "Fording
costs a transport in the DERIVATION and nothing at runtime" is now
exercised at a judgement rather than asserted.

★ **DO THIS BEFORE SUBSTITUTION.** It is a complete judgement, it needs
no machinery beyond what exists, and it is the smallest thing that
demonstrates a RELATION over encoded syntax. It is this increment's
`step 1a`.

⚠ **WHAT STEP 0 DID AND DID NOT UNBLOCK.** `Ctx` is now encoded, so the
index telescope is WRITABLE — ⚠ note it now mixes two families:
`Σ' Nat (Σ' (CtxK ⟨d⟩) (Σ' (K (sVar,⟨d⟩)) (K (sTy,⟨d⟩))))`. `DepIx`
already builds a telescope mixing `El ⌜Nat⌝` with an `IMu`, so this is
the same mechanism at one more component. What is still missing is
`renTy vs` as an `ielim` over the knot returning a knot element — `Examples/WkTm` does it
for a 3-constructor toy, and the knot has 55. ⚠ Per `Lib/IFold`'s result
that must be a fold COMPUTED from the description, not 55 enumerated
methods; an enumerated one is the 147s-vs-5s mistake with a syntax
codomain instead of `Nat`.

✅ **THE INDEX TELESCOPE IS BUILT AND TYPES** (`Examples/Knot/Lookup`
§1). Four components — `Σ' Nat (Σ' (CtxK ⟨d⟩) (Σ' (Var@⟨d⟩) (RTy@⟨d⟩)))`
— and it spans **two different `IMu`s**, where `DepIx` tested two
components over one. This section flagged it as the first place to look
if a telescope misbehaves; it did not.

⚠ **WHAT DID BITE IS NOT THE TELESCOPE — IT IS FORDING, AND THIS SECTION
DID NOT PRICE IT.** `here` targets `(suc m, Γ ▹ A, vz, wk A)`, so it
Fords all four components. `iwf-κ` wants each ford's code TYPED, and a
ford's two sides must sit at the SAME code — but the ambient's `Ctx`
component lives at depth `fst ⟨i⟩` while `Ctx-extK m Γ A` lives at
`nsuc m`, and those agree only by the DEPTH ford, which is
PROPOSITIONAL.

⇒ **each of the three later fords transports its RHS along the depth
ford** (`jsub (⌜IMu⌝ … ⟨-⟩) (symN … p) e` — `WkFin`'s idiom, three times
in one row). §1 said "Fording costs a transport in the DERIVATION and
nothing at runtime"; this is the first row that pays it for a **foreign
family** rather than its own index, and it pays three.

⚠⚠ **AND IT NEEDS SMART CONSTRUCTORS AT A *VARIABLE* DEPTH, WHICH DO NOT
EXIST.** `⊢Ctx-extK` and `⊢Var-vzK` are both stated at `num n` — an Agda
NUMERAL — because `Knot/Build`'s §4 rule ("the depth must be a NUMERAL")
was written for the adequacy map, whose depths are numerals. In a
constructor's telescope the depth is a bound `iκ ⌜Nat⌝` field, i.e. a
VARIABLE. ⇒ variable-depth twins are needed first. `Knot/Build`'s route
(a) (abstract depth + `wk-single` per field, chain length = the field's
position) is the known-working way; `⊢wkK` is already in this form and
needs nothing.

### Step 2 — object-level weakening for `RTy`/`RTm`, then `extS`, then `subTm`

✅ **THE MOTIVE QUESTION IS SETTLED** — see step 0. The uniform shift
`M(i,t) = K (pair (fst ⟨i⟩) (nsuc (snd ⟨i⟩)))` is honest at all 53 sorts
now that `Ctx` is not one of them. (`Negative/WkEmp` is why that sentence
needed earning.)

★ And it prices the transports: **two `jsub`s, flat, no `wk-single`** —
the index components are projections of a VARIABLE, so the
weaken-then-substitute round trip COMPUTES. ⇒ expect step 1's
three-component telescope to cost three.

✅ **AND THE PER-FIELD RULE IS SETTLED TOO** — `Examples/Knot/WkRows`,
four methods at one motive, all green. A fold into a constant motive
takes the IH at every `iρ`; a weakening does not, and `cDCon-kap` is
where that bites — its two `iρ` fields need OPPOSITE treatments.

| row | what the method does | cost |
|---|---|---|
| `cTy-Nat` ford-only | pass the tag ford through | **free** (`βfst`) |
| `cTm-lam` riding | take the IH | conversions only |
| `cDCon-kap` pinned + riding | ★ the pinned `RTy ε` takes the **ORIGINAL field**; its sibling takes the IH | — |
| `cVar-vs` depth-Forded | riding case **plus one `congS`** | one `jsub` |

**The table by shape** (measured, not estimated): 53 rows · 13 ford-only
· 77 riding recursive fields · **4** rows with a pinned-index field
(`cTy-IMu`, `cTm-cIMu`, `cDCon-kap`, `cIDesc-cons`) · **2** depth-Forded
(`cVar-vz`, `cVar-vs`).

✅✅ **AND `wkK` EXISTS** — `Examples/Knot/Wk`:
`wkK : K i → K (sh i)`, the **first function over syntax** the encoded
knot has (everything before was a measure or a constructor). 51 methods
computed by `Lib/IWk`, 2 given (the depth-Forded `Var` rows), assembled by
`⊢iwkMethsFrom` and closed by `⊢ielim`. ⚠ Nothing in it enumerates a row.

✅ **`Lib/IWk` IS BUILT** — the classification, the method and tuple
computed from it, the DECIDER, the escape hatch, **and the typing**
(`⊢iwkPay`/`⊢iwkMethod`/`⊢iwkMethsFrom`).

★★★ **And the computed method IS the hand-written one**, by `refl`, at
all three shapes `WkRows` covers without a depth ford — including
`cDCon-kap`, the row the per-field rule is about. ⇒ `WkRows` is the
library's CONTROL, which is why it was kept.

⚠ **Writing the proof found two bugs the term level could not**: the
classification was too weak (`pinned` needed CLOSEDNESS, not just
non-occurrence of the ambient — the rebuild moves every `rides` slot
too), and `iwkPay`'s `pinned` clause failed to advance the IH tuple.
Both type-checked before. See `HANDOFF-2026-08-27` §A″.

★★ The decider is what makes it generic, and it is controlled
(`Examples/Knot/WkProbe`): 12 row shapes classify, **and the two
depth-Forded rows are REFUSED rather than mis-classified**.

★★★ **AND THE ESCAPE HATCH IS STRUCTURAL, not bookkeeping.** The method
tuple is RIGHT-NESTED, so "classified rows then given rows" is just where
the nest stops: one constructor (`wkd-stop`) and one tail argument. ⇒
`decDesc` is **TOTAL**, the contract is statable without naming a row
(`wkdLen`/`wkdRest`), and a caller with nothing exceptional passes
`unit`. **Measured: `wkdLen (decDesc KnotD) ≡ 51`** — 51 computed rows
plus a 2-method tail, the split `Knot/Ctors`/`Knot/Build` already use.

⚠ **And what it costs is COVERAGE, not a restriction.** Nothing is
forbidden — any description works and the caller supplies the leftover.
Ordering only affects how much gets computed, since `decDesc` stops at
the first row it cannot classify. Measured, not assumed: `wkdLen … ≡ 51`
and `wkdRest … ≡ cVar-vz ◂ cVar-vs ◂ inil`, so for `KnotD` the stop costs
nothing.

⇒ `Lib/IWk` §7 names the three remaining obligations and what each rests
on; `HANDOFF-2026-08-27` §A″ has the state.

⚠ **THE ORDER IS FORCED, AND IT IS SHORTER THAN IT LOOKS.**
`extS σ (vs x) = renTm vs (σ x)` — weakening by ONE, not a general
renaming. ⇒ **general renaming is never needed.** The chain is

    wk (have, for `Tm`)  →  Fin eliminator  →  extS  →  subTm

with the Kripke motive of §1d at the last step:
`∀n. (Fin ⟨i⟩ → Tm n) → Tm n`, which adds a `Π` over `Nat` and a `Tm`
codomain to what `KripkeIx` already does — both ordinary.

### Step 3 — the mutual judgement block ⟨★ **GENERATE IT**⟩

⚠⚠ **MEASURED ON STEP 1: HAND-WRITING DOES NOT SCALE HERE.** `_∋_∷_`'s
TWO rows — 7 and 10 fields — cost a long session, and most of that was de
Bruijn bookkeeping reducible to one rule (field `j` sits at
`vs^(k-1-j) vz`, the ambient at `vs^k vz`). Step 3 is **~166 rows**, with
MORE bookkeeping each: four Forded components and three transports per
row.

⇒ **extend `tools/gen-knot.py` to emit judgement rows**, with
`Examples/Knot/Lookup` as the hand-written reference the generator must
reproduce — the role `Knot/Terms`/`Knot/Build` play for the syntax table.
The generator's own header already makes this argument for 53 rows: such
bookkeeping "is not work, it is a transcription error waiting to happen".
⚠ And generating the `IConWf` is what `FUTURE.md`'s off-by-one fix asks
for, so the two land together.


⚠ **IT CANNOT BE STAGED THE WAY THE SYNTAX WAS.** `ty-El` needs
`Γ ⊢ c ∷ U`, so `_⊢ty_` and `_⊢_∷_` are MUTUAL. Per §13 that is one
description over a tagged index — fine, but it means no partial landing:
`_⊢ty_` alone is not a milestone.

| | rows | needs |
|---|---|---|
| `_∋_∷_` | 2 | weakening (step 1) — ✅ DONE, `Knot/Lookup` |
| `_⊢ty_` + `_⊢_∷_` | 43 | substitution (step 2) |
| `_⟶ᵀ_`, `_≅ᵀ_` | 30 | — |
| `_⟶_` | 73 | — |
| `Canon`, `Prog` | 20 | the above |

⚠⚠ **THE TWO "—" ROWS ARE MISLEADING, AND SO WERE TWO LATER ESTIMATES OF
MINE.** Measured 2026-08-28, three times, each answer superseding the
last:

1. *"~27 rows blocked on `subTm`"* — over-reported. The scan counted any
   mention of a substitution-ish name, `renTm vs` included.
2. *"30 rows buildable now (`_⟶ᵀ_` + `_≅ᵀ_`)"* — right about
   substitution, wrong about structure. Only **15** rules genuinely need
   `subTm`: `β`, `ap-J`, `natrec-suc`, `ι-elim`, `ι-ielim`, and ten of
   `_⊢_∷_`. Eight more need weakening ONLY, which `wkK` already
   supplies. 125 need neither.
3. ★★★ **BUT THE JUDGEMENTS ARE A CHAIN**, and that is what decides it:

       ⟶      self-contained        (5 rules need `subTm`)
       ⟶ᵀ  →  ⟶                     (`ξ-Homˡ : t ⟶ t' → …`)
       ≅ᵀ  →  ⟶ᵀ  →  ⟶              (`credᵀ`)
       ∋      self-contained        ✅ done
       ⊢ty ↔ ⊢  →  ∋, ≅ᵀ, ⊢ty       (mutual, and 10 need `subTm`)

   `_⟶_` sits at the BOTTOM and five of its rules need `subTm`. A
   judgement is ONE description, so it cannot land with 68 of 73 rows.
   ⇒ **everything above `_∋_∷_` is blocked, and on ONE thing:
   object-level `subTm`.** The "—" read as "no prerequisites"; it means
   "no SUBSTITUTION prerequisite", which is not the same claim.

⇒ ★ **STEP 2 BEFORE STEP 3.** Not a judgement call — a measured
dependency. `wkK` is done; the remainder is `Fin eliminator → extS →
subTm`.

### Step 4 — `prog` object-level ⟨★★★ **THIS IS THE DOGFOODING TARGET**⟩

⚠ **SAY SO HERE, because it is scattered across four files.** "Dogfooding"
in this tree means replacing THIS POC's OWN hand-rolled measure recursion
— `prog`/`usplit`/`trS`/`ordtrS`, each threading an explicit `ℕ` bound and
a `≤` premise — with `⊢amrec`. `ARCHITECTURE.md` says that becomes
possible "the moment `RTm` is a kernel type and `sz` is definable";
`Examples/Dogfood.agda` demonstrates the recursor is derivable in the
kernel and records that the real target is blocked on INDEXED
DESCRIPTIONS, not on the WF axis.

⇒ the KNOT is the prerequisite, not the exhibit. **This step is the
exhibit**, and steps 1–3 exist to reach it.

Only now is `⊢amrec`-through-`prog` (PLAN-INDEXED §5 item 7) statable.
`Examples/AmrecIMuRec` already shows a recursing step at an `IMu`
carrier, and `Lib/ISz` supplies the measure.

---

## 4. DESIGN CONSTRAINTS TO CARRY

★★ **STATIC vs DYNAMIC IS THE AXIS TO DESIGN AROUND.** A generic lemma
is only generic **if its argument stays ABSTRACT at the use site**. This
decided four things in one session and it fails QUIETLY:

* `Lib/IFold` calls `ipayTy-wf` at an ABSTRACT `C` — correct, and it took
  `sz` from 147s to 5s.
* `Examples/WkFin` cannot: its `C` is the CONCRETE `fzeroC`, and routing
  through the same lemma leaves `subTm εsub _t = ⌜Nat⌝` unsolved. Build
  the payload ⊢ty concretely there.
* A generic lemma consumed by an ENUMERATION is the worst case of all —
  measured WORSE than either pure alternative.

Others, each of which cost a cycle:

* **The depth must be a NUMERAL.** `num : ℕ → RTm Γ` is
  context-polymorphic, which is what lets its stability lemmas be stated
  at all; an opaque `d : RTm ⌊Δ⌋` cannot have them.
* **Ford the COMPONENT, not the pair** — and both components can need it
  independently (`Var`).
* **Pin contexts.** `ty-Π`/`⊢lam`'s second argument is one binder
  deeper; left implicit those contexts are metas that never solve.
* **`⌊_⌋` is not injective** — index recursions by a `Cx`, never a `Ctx`,
  or the recursion cannot solve its own implicit.
* **`εwkTm`/`num` are DEFINED functions** and so not injective: pin their
  arguments explicitly (`pin-implicits-on-defined-set-types`, three
  sightings).
* **Regenerate, never hand-edit** the generated files, and keep the
  generator's coverage check against `Spec/Syntax` — a missing row is
  otherwise completely silent.

## 5. COST MODEL — measured, cold, on a 7.7 GB box

| | |
|---|---|
| `Knot/Wf` (53 `IConWf`) | 104s, **needs `-c`** |
| `Knot/Ctors` (51 smart ctors) | 15–21s |
| `Knot/Build` (the 2 hand-written `Var` rows) | 6s |
| `Knot/Map` (the adequacy map) | 3s |
| `Knot/CtxD` (family + Wf + map + inhabitant) | 3s |
| `Knot/Sz` (via `Lib/IFold`) | 3s |

★ **AND ±2 ROWS COST NOTHING**, measured on 08-27 while `Ctx` was
briefly sort 7: `Wf` read 99s at 55 rows against 104s at 53, and OOM'd at
80s vs 76s without `-c`. Both inside the ±12% noise floor. The driver is
a row's TELESCOPE DEPTH, not the row count — which is the number that
matters for §3, because the judgement rows are ~3× as many but no
deeper.

⚠ A "needs `-c`" header is a claim about a **shape**, not a module:
`Knot/Sz`'s was stale within minutes of being written. Re-measure when
the shape changes.

⇒ the judgement layer is ~3× the syntax knot in rows. Expect `Wf` to be
the pain point and to need splitting or `-c`; expect the MAP-equivalent
(§6) to be cheap, as it was here.

## 6. ⚠ DO NOT SKIP THE ADEQUACY MAP

`Knot/Wf` says 53 rows are well formed; `Knot/Terms` says one term
encodes. **Neither says the description IS the knot.** Measured: set
`natrec`'s step field to `sucD 1` — `Wf` still passes, `Ctors` still
passes, only `Map` fails. Whatever judgements get encoded, the same map
must be built for them, or the encoding is asserted rather than checked.

## 7. OPEN RISKS

* `_⟶_` is **73 rows indexed by TWO terms**, so its index telescope is
  the largest yet. §1a tested two components at small scale.
* `Canon`/`Prog` carry proofs of other judgements, deepening the mutual
  block.
* Nothing is known about `ielim` **reduction** at knot scale — every
  reduction result so far is at a small concrete input.

## 8. ⛔ DO NOT

* Re-spike §1. It is done and the files are cited.
* Make a RUNG generic to speed up an enumerated consumer — two attempts,
  both measured worse.
* Assume every encoded family needs Fording transports; only those with
  computed target indices do.
* Build a general RENAMING. `extS` needs weakening only.
