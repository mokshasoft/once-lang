# OCP-0009 — PLAN: THE RENAMING PARAMETER, AND THE BUG CLASS IT HIDES

Opened 2026-09-03. Read `FUTURE.md` §"CATEGORY D′ IN DETAIL" for the
defect analysis; this file is the WORK PLAN and the running BUG TALLY.

---

## §0 The finding, in one line

`Knot/Wk.wkK : K (s,d) → K (s,suc d)` is **not** `renTm vs`. It is the
identity on de Bruijn indices — the weakening that appends a fresh slot
at the OUTERMOST end. The two agree on CLOSED terms and only there.

    wkK (var vz)     = var vz          renTm vs (var vz)     = var (vs vz)
    wkK (var (vs x)) = var (vs (wkK x))

## §1 Why it happened, and why no check saw it

**The encoding DROPPED A PARAMETER THE KERNEL HAS.**

    Ren Γ Δ = Var Γ → Var Δ
    renTm   : Ren Γ Δ → RTm Γ → RTm Δ        -- ρ is a VALUE
    wkK     : RTm Γ → RTm Γ → RTm Γ          -- ρ is GONE

Both renamings have type `RTm Γ → RTm (Γ ∙)` **in the kernel too**; the
kernel is fine anyway, because ρ is an argument. `Lib/IWk` derives the
fold with ρ inlined, unnamed and unrecoverable, and its motive states
only `M(i,t) = IMu D I (sh ⟨i⟩)` — *the depth goes up by one*, which is
the entire specification and which both renamings satisfy.

⚠⚠ **AND IT COULD NOT HAVE BEEN `renTm vs`.** A tag-preserving generic
fold can only implement a renaming stable under passing a binder
(`extR ρ ≡ ρ` one depth up). The outermost insertion is the only
weakening that is; `renTm vs` becomes `renTm (extR vs)` under a `lam`.
⇒ not a slip in two rows — a statement about what `Lib/IWk` CAN produce.

⚠ **`Examples/Knot/WkRows` LOOKS like a control and is not.** It compares
the generic derivation against hand-written rows built to the SAME
INTENT: two implementations of one misconception, agreeing. A control
must compare an implementation against a SPECIFICATION.

⚠ **`Knot/WkProbe` checks the classifier CLASSIFIES**, i.e. that the
derivation applies — orthogonal to what the result means.

⚠ **`Knot/Adequacy` skips every rule that applies a wrapper**, correctly
(it would be a commutation lemma, not `refl`) — and reported all of them
as `_Undepthed`, which reads as depth bookkeeping. `wkK` takes a depth;
that is simultaneously why the depth-only index cannot tell the two
renamings apart and why every rule using it lands in the skip list. **The
coverage gap and the bug had one cause.**

## §2 What is NOT at risk, and it is checked

`Spec/` and `Metatheory/` import nothing from `Lib/` or `Examples/`
(`tools/check-trust.sh` gate 2, controlled both ways). A library defect
cannot reach consistency, canonicity or SN. ⇒ the worst case for this
class is **a true theorem about the wrong object**, never a false one.
`⊢wkK` is true, non-vacuous, and applied at real arguments.

## §3 The option that does not exist

⛔ **"Index `K` by a SCOPE rather than a LENGTH."** `Cx` is `ε | _∙` — a
unary ℕ. In this raw syntax a scope IS a length; there is no richer index
to move to. Distinguishing the two renamings BY TYPE needs terms indexed
by a context of TYPES (intrinsic syntax), which abandons the raw/typed
separation the POC rests on. Not a re-index — a different development.

⇒ so the correct-by-construction move is **not** a stronger index. It is
**restoring the kernel's own interface: pass the renaming.**

## §4 The criterion, and it is mechanical enough to apply by hand

> **Does the object-level wrapper take every argument the kernel function
> it names takes?**

Applied to all eleven wrappers, it flags EXACTLY ONE — the true positive:

| wrapper | kernel counterpart | parameter present? |
|---|---|---|
| `subTmAtK … σ t` | `subTm σ t` | ✅ σ |
| `subTyAtK … σ A` | `subTy σ A` | ✅ σ |
| `singleK n u` | `single u` | ✅ u |
| `extNK d n σ` | `extS σ` | ✅ σ |
| `nrsSubK d` | `nrs` | ✅ (nullary) |
| `εwkK s n t` | `εwkTm t` | ✅ t |
| `conSK n k` | `conS k` | ✅ k |
| `payTyK n c d` | `payTy D C` | ✅ |
| `ihTyK n c q M` | `ihTy D C q M` | ✅ (`D` vestigial, proved) |
| `ipayTyK dd c n sb d i` | `ipayTy D I σ C` | ✅ |
| `lookupDK n d k` | `lookupD D k` | ✅ |
| **`wkK i t`** | **`renTm ρ t`** | ⛔ **ρ DROPPED** |

★ A parameter that determines the answer and does not appear in the
interface is exactly where a silent disagreement lives.

## §5 And it makes the obligation CHEAP, which is why 25 lemmas stayed owed

Once a renaming is a VALUE, its specification is pointwise and two lines:

    σ-vz : app ⌈σ⌉ ⌈vz⌉   ⟶* ⌈ σ vz ⌉
    σ-vs : app ⌈σ⌉ ⌈vs x⌉ ⟶* ⌈ σ (vs x) ⌉

a β-step each, no induction. **`wkK` cannot be given that spec at all** —
it is not a function you can apply, it is a fold with the choice baked
in. ⇒ converting does not merely concentrate the freedom; it makes the
obligation dischargeable.

⚠ It is NOT correct-by-construction. `lam (Tm-varK (Var-vzK (w n)))`
typechecks at `SubTy n (nsuc n)` and is the constant-`vz` substitution.
What is bought: the freedom shrinks from a 53-row derived fold to ONE
readable line, and that line is pointwise testable.

---

## §6 THE WORK, in order

| | step | state |
|---|---|---|
| 0 | `Knot/WkSub` — `wkSubK`/`wkTyK`/`wkTmK`/`wkTyUnderK` | ✅ done |
| 0 | emitter: `renTm vs` → `wkTmK` (`⊢ap`, `hrefl-pw`, `tr-pw`) | ✅ done |
| 0 | `Knot/IhTyRho` converted | ✅ done |
| 0 | `_WRAP_LEDGER`, both-ways, 39 programs / 25 owed | ✅ done |
| **1** | **convert the remaining suspect sites** | 🟡 4 of 6 done |
| 1a | `Knot/RenMot` — the object-level `Ren` layer (`RenTy`, `extRK`, `extRNK`) | ✅ **done** — breaks the cycle |
| 1b | `renTmK ρ` over the 53 rows (`Knot/RenTm`) | ✅ **done** |
| 1c | `extVs` (#5), `pwBodyK`'s 51 defaults (#4), `wkTmK = renTmK vsRen` | ⬜ **HERE** |
| 2 | pointwise specs for `wkSubK`/`singleK`/`extNK`/`nrsSubK` | ⬜ |
| 3 | `sub-agree` — the ONE induction, discharges the family | ⬜ |
| 4 | retire `wkK` for open terms; keep it only where CLOSED, stated | ⬜ |
| 5 | then `methsTyFrom` (unblocked, mechanical) | ⬜ |

### §6.1 Step 1's sites — the audit to be CONFIRMED, not trusted

⚠⚠ **INSPECTION HAS ALREADY FAILED TWICE ON THIS EXACT QUESTION** — once
when `wkK` was written, once on 2026-09-02 when `Knot/PayTy` was audited
and pronounced sound. The table below is a HYPOTHESIS; each row is closed
by a conversion that typechecks, not by reading.

| module | uses | shape | prediction |
|---|---|---|---|
| `Knot/Lookup` | 9 | `Γ ▹ B ∋ vs x ∷ renTy vs A`, `A` a rule variable | ⚠ BUG |
| `Knot/LookupGen` | 4 | the control for the above; mirrors it | ⚠ BUG |
| `Knot/PwBody` | 3 | `Tm-appK (wkK … x) (Tm-varK (Var-vzK …))` — push under a binder | ⚠ BUG |
| `Knot/SubMot` | 2 | same push-under-a-binder shape | ⚠ BUG |
| `Knot/PayTy` | 4 | `Σ'`'s 2nd component; `payTy D C` closed | ? claimed sound |
| `Knot/IPayTyRho/Kap` | 4 | weakening the `IDesc` passenger | ? claimed sound |

⚠ The two "claimed sound" rows rest on *"an `IDesc`/`Desc` is closed in
the kernel"*. That does not immediately give *"its ENCODING has no free
variables"*: an `ICon Δ` carries index expressions with scope. **To be
settled by conversion, not by argument.**

---

## §7 BUG TALLY — kept as the conversion proceeds

Format: site · what the wrong weakening did · how it was caught.

| # | site | verdict | caught by |
|---|---|---|---|
| 1 | `gen-knot.py:_val` → `⊢ap`, `hrefl-pw`, `tr-pw` | **BUG** — `renTm vs` emitted as `wkK` | reading `WkRows` §5/§7 against `renTm vs` |
| 2 | `Knot/IhTyRho` | **BUG** — `Σ'`'s 2nd component weakens an OPEN answer (`q`, `M`) | same reading, same day |
| 3 | `Knot/PwBody.pwApp` | **BUG** — rule is `app (renTm vs s) (var vz)` (`Spec/Typing:359`), `s` a rule variable | step 1, ✅ FIXED |
| 4 | `Knot/PwBody` — `pwBodyK`'s **51 DEFAULT rows** | **BUG, STRUCTURAL** — meta `pwBody t = renTm vs t` is the default clause, and the encoding takes `Lib/IWk`'s methods for all 51 | step 1, ⬜ OPEN |
| 5 | `Knot/SubMot.extVs` | **BUG** — `extS σ (vs x) = renTm vs (σ x)` (`Spec/Syntax:335`) | step 1c, ✅ **FIXED** — needed `Knot/RenTm` first |
| 6 | `Knot/Lookup` ×2 rows + `gen_lookupgen` ×2 | **BUG** — `_∋_∷_`'s type is `renTy vs A`, `A` a bound FIELD | step 1, ✅ FIXED |

**Running: 6 sites, 5 fixed, 1 open.** Every one is `renTm vs`/`renTy vs`
in the source with `wkK` in the encoding — a single class, not six.

★ **AND TWO CHECKS FIRED ON THEIR OWN**, which is the first time anything
has caught this class without being told to look:

* `Knot/Lookup`'s **example instantiation** rejected the converted row
  until the example was converted too. The row and its consumer must name
  the same weakening. (`libraries-exercised-by-examples`, again.)
* `Knot/LookupGen`, the **generated control**, went red the moment the
  hand-written row moved and the generator had not. That is exactly what
  a control is for — and note it only works because the two sides are
  written by different emitters.

⚠ Not caught by either: #4 and #5, which are the two that are structural.

## §8 ⚠⚠ THE BLOCKER — RENAMING IS PRIOR TO SUBSTITUTION

`Knot/SubMot.extVs` cannot use `wkTmK`: `Knot/WkSub` imports `SubMot`.
That is not an accident of module layout — it is the kernel's own
layering:

    Ren Γ Δ = Var Γ → Var Δ          Spec/Syntax:273   ← FIRST
    renTm   : Ren Γ Δ → RTm Γ → RTm Δ            :281
    Sub Γ Δ = Var Γ → RTm Δ                      :330   ← SECOND
    extS σ (vs x) = renTm vs (σ x)               :335   ← uses renTm

**Renaming is defined BEFORE substitution and `extS` is defined in terms
of it.** Expressing `renTm vs` as `subTm wkSub` inverts that and closes a
cycle exactly at `extS`.

⇒ **the Sub-based fix cannot cover the whole family.** What is needed is
the layer the kernel already has and the encoding never built: an
object-level **`Ren`**, i.e. `renTmK ρ` parameterised by an
`ρ : Π (Var d) (Var m)` — `SubTy`'s twin, one level down. Then

    wkTmK   = renTmK vsRen          (and the cycle disappears)
    extSK   uses renTmK, not subTmK
    Lib/IWk = renTmK at ONE ρ, with the ρ finally named

★ That is the same conclusion as §4 — *pass the renaming* — arrived at a
second time, from the module graph instead of from the criterion.

⬜ **DECISION NEEDED before step 2:** build `renTmK ρ` (faithful to the
kernel, unblocks #4 and #5, subsumes `Lib/IWk`), or leave `extVs`/
`pwBodyK` on `wkK` with the defect recorded.

---

## §9 ARE THERE MORE LIBRARIES LIKE THIS? — audited 2026-09-03

Of the `Lib/` modules that DERIVE an object-level program, which ship
reduction lemmas about what they derive?

| library | derives | ships laws about it |
|---|---|---|
| `ISzRed` (+`ISz`/`ISzSort`/`IFold`) | the `sz` fold | ✅ `szsStep-red`, `szsTail-red` — and `Knot/SzAgree` is built on them |
| `ISub` | substitution's apparatus | 🟡 TAKES a reduction witness as a parameter (`decStable`); proves no agreement of its own |
| **`IWk`** | **the weakening fold** | ⛔ **none** — its ONLY `⟶*` is inside a comment |
| `IPay` / `IMeths` | method-tuple apparatus | n/a — these build TYPES, not programs |

★★★ **The correlation is exact, both ways.** The library that ships
reduction lemmas is the one whose encoding is the only PROVED agreement
in the development (`sz`). The library that ships none is the one that
produced the bug. One data point each way — but the mechanism is not
mysterious: **a law you cannot state is a law you will not prove.**

⇒ answer to "are there more of these?": **one**, and it is the one found.

## §10 WHERE THE LAW CAN AND CANNOT LIVE

⛔ **NOT in `Spec`.** The law is `⌈ renTm ρ t ⌉ ⟶* iwk ρ ⌈ t ⌉` — it
mentions `enTm`, the adequacy map. `Spec` does not know the Knot exists.

⛔ **NOT generically in `Lib/IWk`.** For an arbitrary `IDesc D` there is
nothing to be faithful TO: `D` *is* the syntax. The laws that ARE
statable generically — it is a fold, it preserves tags, it commutes with
constructors — are all satisfied by the buggy version.

✅ **At the Knot**, where both languages are in scope. The kernel/library
can host the SHAPE (a record whose fields are ρ, the operation, and the
law); only the Knot can fill it.

⚠ **AND YOU CANNOT ENFORCE "USE MY PRIMITIVE" FROM INSIDE THE PRIMITIVE.**
`Lib/IWk` did not misuse `renTm` — it declined to use it and wrote a new
function. The only enforcement that works is to make the thing the caller
NEEDS obtainable only in a form that carries its law.

---

## §11 THE KERNEL-LEVEL ROOT CAUSE, AND WHAT THE NORMALIZER ALREADY DOES

### §11.1 ★★★ THE DESCRIPTION LANGUAGE HAS NO BINDERS AND NO VARIABLES

    data ICon where
      iι : ICon Δ
      iρ : RTm Δ → ICon (Δ ∙) → ICon Δ    -- recursive field at index j
      iκ : RTm Δ → ICon (Δ ∙) → ICon Δ    -- non-recursive, type `El κ`

There is **no binder former and no variable position**. Binding is
encoded as DEPTH ARITHMETIC INSIDE THE INDEX TERM — `iρ (pair sTy (nsuc
(snd ⟨i⟩)))` is how the knot says *"a type one binder deeper"*. And
`Lib/IWk`'s `WkIx` classification (`rides` / `pinned`) exists solely to
**reverse-engineer that arithmetic back into binding structure**.

⇒ **that decoding step is where the choice of renaming lives, and it is
where the bug came from.** A generic fold over a description that cannot
say which fields are under binders cannot know which renaming it is
implementing — so it implements the only one that is stable under
`extR`, which is the outermost insertion, not `renTm vs`.

### §11.2 ⇒ THE KERNEL CHANGE THAT MAKES THE CLASS UNSTATABLE

Add a binder former and a variable position to the description language.
Then `renTm`/`subTm` over `IMu D I` are DERIVED ONCE, generically, in the
kernel, with their laws proved once — the scope-safe universe-of-syntaxes
result. `Lib/IWk` stops being a user-written fold, `wkK` stops being a
user function, and `WkIx` has nothing to decode, hence nothing to decode
wrongly.

⚠ COST: it changes `ICon`, therefore every row of the 53-row knot,
therefore `Lib/IWk`/`ISub`/`IPay`, therefore the generator. That is the
whole POC — a PLAN, not a patch. ★ And it is the same request as
`FUTURE.md`'s dogfooding option 2 (*generate the layer FROM the
description*), one level deeper.

### §11.3 ✅ THE CHEAP SPEC-LEVEL PIECE, worth doing regardless

`Spec` can prove what PINS a renaming: `renTm ρ` is the unique structural
map with `f ρ (var x) = var (ρ x)`. That mentions only `Spec`'s own
notions, so it belongs in `Spec` — and with it, a library claiming to
implement a renaming owes **the VARIABLE rows only**; the other 29 are
forced. This is the mechanism that keeps the law cheap.

### §11.4 ★★★ THE NORMALIZER ALREADY SOLVED THIS, ONE DIRECTORY OVER

On `origin/plan-0.76-context-indexed-composition`:

    Theory/Spec/AlgebraSpec.agda      record AlgebraSpec (alg : …) : Set₁
                                        field alg-at-id, alg-at-comp, …
    TCB0/Compiler/SatisfiesSpec.agda  the concrete algebra INHABITS it
    Theory/GeneralCorrectness/Record  record CorrectNormalizer
                                        field terminates, produces-betanf,
                                              preserves

A record whose fields are LAWS, a proof the instance satisfies them, and
the theorem derived generically from the record. **That is `RawMonad` vs
`Monad`, and it is already house style in this repository.**

★★ AND THE LAW SHAPE MATCHES WHAT THIS PLAN ARRIVED AT INDEPENDENTLY:

    alg ∘ inj-N  ⟶*  In ∘ inj-N          per position, pointwise, a REDUCTION
    app ⌈σ⌉ ⌈vz⌉ ⟶*  ⌈ σ vz ⌉            §5, the same shape

### §11.5 ⚠ DOES THE LAW-RECORD BLOW UP THE PROOF SPACE? — MEASURED: NO

`AlgebraSpec` has **15 law fields**. `SatisfiesSpec` discharges all
fifteen in **78 lines** — 5 lines each, except `alg-at-comp` at 11. Its
header says why: 14 of 15 are trivial *because the handlers ARE*
`In ∘ inj-N`. ⇒ **the cost concentrates in the positions with real
behaviour, and there are few of those.** That is the whole point of the
per-constructor pointwise shape.

### §11.6 WHAT TO CALL IT

House style already exists: a `…Spec` RECORD plus a `Satisfies…` proof.
For the discipline: **NO RAW EXPORTS** — a library may not export a
DERIVED OPERATION except through a spec record. (`Raw…` vs bundled, in
agda-stdlib's own vocabulary.)

⚠ AND IT APPLIES TO FUNCTIONS, NOT CONSTRUCTORS. A constructor is DATA:
no behaviour, nothing to get wrong, and its adequacy is `refl` — which is
exactly what `Knot/Adequacy`'s 32 checks are. The bugs live in DERIVED
FUNCTIONS. ⇒ **`Adequacy` covers the constructors, a spec record covers
the functions, and together they are everything.**

### §11.7 THE THREE HORIZONS

| | | |
|---|---|---|
| **now** | `renTmK` + the pointwise specs — closes #4 and #5 | §6 steps 1–2 |
| **small** | `renTm` uniqueness in `Spec` — future claims cost the var rows only | §11.3 |
| **large** | binders as STRUCTURE in `ICon` — the only change that removes the class | §11.2 |

---

## §12 STEP 1a LANDED — `Knot/RenMot`, and it was cheaper than feared

`RenTy`, `extRMotK`, `constMethR`, `extRVs`, the tuple, `extRK`,
`extRNK` — **327 lines**, green, and it imports `Build`/`Ctors`/`Desc`/
`Sorts`/`Tags`/`Terms`/`Wf`/`Wk` and **not `SubMot`**. ⇒ the cycle of §8
is broken: renaming now sits BELOW substitution, exactly as in `Spec`.

★★ **TWO ROWS BECAME ONE.** `extR ρ vz = vz` and the do-nothing answer is
also `vz` — a `Var` exists at every successor depth — so `cVar-vz` reuses
`constMethR` and only `cVar-vs` is real work. `Knot/SubMot` needs a
separate `extVz` because `extS`'s junk answer is `Tm-nzeroK` and its `vz`
answer is `Tm-varK (Var-vzK n)`.

★★ **AND THE `vs` ROW LOST ITS WEAKENING.** `Knot/SubMot.extVs` pays
`wkK (pair sTm n) (app σ x)` plus two β-steps, because `extS`'s answer is
a TERM one binder deeper. A renaming's answer is a `Var`, and `vs` IS the
constructor for that — `Var-vsK n (app ρ x)`, no weakening at all. ⇒ that
is not a coincidence; it is *why* renaming can be defined before
substitution, showing up as a smaller row.

★ `predSndPair`/`predSndSub` MOVED DOWN from `Knot/SubMot`, whose own
comment asked for it: *"local only because this is its first customer; a
second one moves it down."* Being below `SubMot`, the move is forced.

⬜ NEXT (1b): `renTmK ρ` over the 53 rows. `Lib/ISub` is parameterised
(`extN`, `smap`, `decStable`, `fordMap`; its `Typing` takes the
substitution TYPE and the motive), so this should be that library at
`extN = extRNK` and `smap = id` — renaming preserves sort where
substitution maps `sVar ↦ sTm`. The `var` row differs (`Tm-varK (ρ x)`
against `σ x`) and is one of the three GIVEN methods.

---

## §13 STEP 1b LANDED — `Knot/RenTm`, and `Lib/ISub` took it unchanged

**502 lines against `Knot/SubMot`'s 1439**, green, and it imports
`Build`/`Ctors`/`CtorsV`/`Desc`/`RenMot`/`Sorts`/`Tags`/`Terms`/`Wf`/`Wk`
— **not `SubMot`**. `renTmK i x = ielim KnotD i renMethsK x`, and `ρ` is
an ARGUMENT.

★★★ **THE LIBRARY INSTANTIATED WITHOUT CHANGE.** `Lib/ISub.Sub` at

    extN      = extRNK          (Knot/RenMot — and it needs no renTm)
    smap      = λ s → s         renaming PRESERVES the sort
    decStable = λ _ → just done
    fordMap   = the witness, COPIED

and `Lib/ISub.Typing` at `RenTy`/`renMotK`/`⊢extRNK`/`⊢renAppK`/
`⊢renFordMap`. Both `open`s were accepted on the first attempt. ⇒ the
library really was generic in the thing that differs, which is the first
time that has been true of a `Lib` module at a SECOND customer.

★★ **AND `smap = id` COLLAPSES EVERYTHING `sortMap` COSTS.** Measured
against `Knot/SubMot`:

| | substitution | renaming |
|---|---|---|
| stability chains | six (`sortMap-ty` … `sortMap-icon`), ~40 lines | `done` |
| `decStable` | a 7-clause decision procedure | `λ _ → just done` |
| the ford action | `fordMapK`, a `jsub`, + a 15-line typing | the witness, copied |
| `sortConv` | takes `s'` and `sortMap s ⟶* s'` | `renConv`, neither |

⚠ **AND THE `Var` ROWS DIFFER IN KIND, WHICH IS THE POINT.**
`Knot/SubMot`'s own header says that at sort `sVar` its motive targets
`K (pair (sortMap (fst ⟨i⟩)) n)` and `sortMap sVar ⟶* sTm`, so its `Var`
methods build a TERM — what substituting a variable does. A renaming
sends a variable to a VARIABLE, so here the target really is
`K (pair sVar n)`. ⇒ the ONE place the two functions genuinely differ,
and the motive is where it shows. `renVarM` differs from `subVarM` by
exactly one `Tm-varK`.

⬜ WHAT WAS COPIED RATHER THAN REUSED, and should be parameterised at a
third customer: `⊢isubMethodK`, `⊢isubMethsK`, `GiveOK`/`Pr`/`OKg`,
`imethTySubK-wf`, `imethsTyFromSubK-wf`, `payRenK`, `ihRenK` — all
`Knot/SubMot`-local and hard-wired to `subMotK`.

