# The Knot, in retrospect — what its difficulty says about the KERNEL

*Opened 2026-09-23. A retrospective, not a plan. `LESSONS.md` records how
to work; this records what the Knot's cost is EVIDENCE FOR, about the
shape of `Spec/`.*

⚠ **Read `principledness-over-edit-cost` first.** Nothing below argues
from "that would be a lot of edits". For this POC the output is a
DESIGN; rework is recoverable, a formulation that needs an axiom is not.
Redoing 45k lines to find the right abstraction is a cost, not an
objection.

---

## 1. What it cost, measured

Since 2026-06-01, on this branch:

| | commits | added | deleted | **rework** |
|---|---|---|---|---|
| kernel (`Spec/` + `Metatheory/`) | 28 | +29,968 | −2,458 | **8%** |
| Knot (`Examples/Knot/`) | **202** | +112,018 | −44,977 | **40%** |

**7× the commits, 5× the rework rate.** 45,000 lines written and then
deleted. The kernel was written nearly once and stuck; the Knot has been
torn up repeatedly.

⇒ the difficulty in this development is **not** in the metatheory. It is
in encoding the syntax as data.

---

## 2. Why — five mechanisms, each with its evidence

### 2.1 The index is `(sort, depth)`, so every invariant is ARITHMETIC

```agda
IPair = Σ' Nat Nat            -- Examples/Knot/Sorts.agda
K i   = IMu KnotD IPair i     -- an encoded term's type: sort and depth. Nothing else.
```

`PLAN-RENAMING` §3 states the consequence exactly:

> `Cx` is `ε | _∙` — a unary ℕ. **In this raw syntax a scope IS a
> length; there is no richer index to move to.**

Everything downstream follows from that one fact:

* **the weakening towers** — `wk-single`, `sub-w²-single`,
  `sub-w³-single`, `towerP`, `towerA`, `towerJ`, `towerJ⁵`, `tower⁶`,
  `tower⁷`: **eight rungs of one lemma**, one per binder depth, because
  a binder is `+1` and the proof must count;
* **the depth congruences** — `⟶*-wkTyKᵈ` is FOUR descents, because
  `wkTyK`'s depth occurs four times in its own unfolding (the index,
  `nsuc n`, and twice inside `vsRenK`'s `Var-vsK`);
* **the `natⁿ` family** — `nat4₂`, `nat5₂'`, `nat5₄`, `nat6₂`, `nat6₅`,
  `nat7`, `nat7₂`, `nat7₃`: **eight instances across six modules**, one
  per (arity × substitution-stack depth), each a transcription of the
  previous.

None of these lemmas is about the OBJECT LANGUAGE. They are all
bookkeeping for an index that counts.

### 2.2 Typing cannot see the encoding

⚠⚠ **The sharpest evidence, and it is a real defect found 2026-09-22.**
`Knot/IMethTy.imethTyK` passed the PAYLOAD binder where the spec passes
the INDEX binder:

```agda
-- program                     -- spec
isingleK (Tm-varK (Var-vzK (nsuc n)))    isingle (var (vs vz))
Tm-varK (Var-vzK (nsuc n))               var vz
```

Two *different* variables in the spec; the *same* variable twice in the
program. `⊢imethTyK` type-checked either way, because `⊢isingleK` asks
only for `Γ ⊢ i ∷ K (pair sTm n)` — sort and depth — and both variables
satisfy it. It was found by ATTEMPTING THE ADEQUACY PROOF, not by the
type checker, and it had been in the tree for weeks.

`gen-knot.py`'s own header predicted the class:

> a wrong index is invisible at the `ICon` level … it is **a
> transcription error waiting to happen, in the one place where the
> error does not look like itself**.

★ And the control tier confirms how thin the protection is: of 159
emitted judgement rows, **2 are controlled** against an independently
written version, and `enDeriv` — the adequacy map for judgements — does
not exist. Three files mention it; none defines it.

### 2.3 Raw syntax ⇒ every object-level program owes an adequacy proof

The agreement ledger is **105 object-level programs**. Each entry is one
obligation of the form *"this encoded program computes what the
meta-level function computes"* — `szsTm ⌈t⌉ ⟶* num (sz t)` and 104
siblings. That ledger exists **only because the encoding is extrinsic**:
an encoded `pwK` and the meta `pw?` are unrelated until a theorem
relates them.

⇒ 105 theorems that say "the data means what it is named".

### 2.4 Substitution is untyped, so naturality is everywhere

`Sub Γ Δ = Var Γ → RTm Δ` carries no typing. Consequently every
object-level program that builds a `lam` needs a hand-written
push-through lemma, and the family has no home:

| lemma | lives in |
|---|---|
| `wkTyK-sub` | `Knot/PayTyAgree` |
| `wkAtK-sub` | `Knot/IPayTyAgree` |
| `subTyAtK-sub` | `Knot/IhTyAgree` |
| `vsRenK-sub`, `renMethsK-sub` | `Knot/SubSpec` |
| `iconSSK-sub` | `Knot/IConSRep` |
| + 5 more written 2026-09-22 | `Knot/MethsTyAgree` |

Eleven instances of one lemma, scattered across six modules, each
written where it was first needed. ⚠ The *reason* they are needed is
always the same: `vsRenK n = lam (Var-vsK (w n) (var vz))` puts its
argument UNDER A BINDER, so a substitution crossing it is `extS`-lifted
and does not reach the argument definitionally.

### 2.5 Hand-writing, not the index, is the biggest single multiplier

| | rows | lines/row |
|---|---|---|
| `Ctors` — generated, 2-ℕ index | 53 | **25** |
| `RedRows` / `JudgeRows` — generated, RICH index | 73 / 56 | **60–83** |
| `Lookup` — **hand-written**, rich index | 2 | **365** |

A richer index costs ~2.5–3×. **Hand-writing costs ~4× on top.** And
**6 of 132 `Knot/` modules are generated** — so the tree is
overwhelmingly on the expensive side of the larger multiplier.

⚠ This one is a TOOLING lesson, not a kernel lesson, and it is the only
mechanism here that a kernel change does not touch.

---

## 3. What this points at: EXTRINSIC → INTRINSIC

**Yes — §2.1, §2.2, §2.3 and §2.4 are all the same root cause under
different names: the syntax is RAW, and typing is a separate relation.**

### 3.1 It has already been reasoned about here, twice

**(a) `poc/OCP0009/NbEPII.agda` — 117 lines, `--safe`, DONE.**

> the intrinsically-typed SYNTAX OF A DEPENDENT TYPE THEORY — contexts
> and types over them, well-formed BY CONSTRUCTION. **This is exactly
> the shape a native `Spec/Kernel` (plan §9) would take** … II is the
> natural home of *"the DT kernel as data."*

It demonstrates the induction-induction pair `Ctx`/`Ty`, variables, a
Π-chain, the SIMULTANEOUS eliminator, the standard model, and a
consistency corollary. So the shape is not speculative — it is spiked.

**(b) The Once compiler already migrated, in this repo.**
`docs/formal/guides/intrinsic-vs-extrinsic-typing.md`: the extrinsic
path's soundness proof is *"complex, has postulates"* and its hard cases
are *"structurally difficult"*; the intrinsic path's soundness is
*"trivial by construction"*, and the guide recommends deprecating the
extrinsic one. Different language (simply-typed surface), same verdict.

### 3.2 What each mechanism would become

| mechanism | under intrinsic syntax |
|---|---|
| §2.1 towers / `natⁿ` / depth congruences | the index is a CONTEXT, not a length; weakening is a context morphism, not arithmetic. The eight tower rungs and eight `natⁿ` instances are bookkeeping for a number that no longer exists |
| §2.2 wrong-variable defects | **unrepresentable** — the index binder and the payload binder have different types |
| §2.3 the 105-entry ledger | much of it collapses: "the data means what it is named" is by construction, not by theorem |
| §2.4 the `-sub` family | substitutions become typed morphisms; much naturality is definitional |
| §2.5 hand-writing | **unchanged** — orthogonal, fix with the generator |

---

## 4. What it would cost — honestly

★ **The index audit, run 2026-09-23.** All 29 term typing rules,
classified by whether the CONCLUSION's index is a constructor
application (forward) or a computed term (needs inverting):

| | count |
|---|---|
| **forward** — conclusion is a constructor or a variable | **22** |
| **computed** — conclusion contains `subTy`/`subTm` | **7** (`⊢app`, `⊢snd`, `⊢tr`, `⊢ap`, `⊢jsub`, `⊢natrec`, `⊢elim`) |

⚠ **`⊢lam` is in the FORWARD class.** I predicted it would be the
problem — `lam : Tm (Γ,A) B → Tm Γ (A ⇒ B)` looks like it must
destructure the target's type — but `Π` is a CONSTRUCTOR, so `A` and `B`
come back by injectivity, not inversion. The inversion problem is real
for ARITHMETIC indices (`suc n`), which is what the current encoding
has, and not for type indices built from constructors.

⇒ **the 267× Fording case is not hit by type-indexing.** That
measurement (`tmp/ProbeFord`: 15,998 ms vs 60 ms) is about `renTy vs A`
in `_∋_∷_` — a RENAMING in the conclusion — and it is already on the
Ford list independently of any of this.

**Known costs:**
* ~2.5–3× lines for the richer index (§2.5's table, measured);
* 7 rules with computed conclusions, of which only `⊢app` is measured
  (2.17× worst case, and `PLAN-FORDING-INDICES` §2.3 judges Fording it a
  **bad trade** because the worst case is artificial);
* re-indexing the Knot ⇒ another pass over ~50k lines;
* substitution on intrinsically-typed de Bruijn syntax is its own known
  hard problem, and this development has not spiked it;
* consistency / canonicity / SN are DONE on raw syntax. Intrinsic
  re-opens them — though the compiler's experience (§3.1b) says soundness
  gets EASIER, not harder.

**⚠ And what is NOT evidence:** `PLAN-FORDING-INDICES` §2.3 is a model of
the honesty wanted here — it labels four of its six rows
*"NONE — inferred"* and calls its own extrapolation *"the same
shape-match §2 was criticised for"*. Four of the seven computed rules
above are in exactly that position: classified by shape, never measured.

---

## 5. ★★★ THE PROBE — RUN 2026-09-23, and it does not blow up

`Examples/ScopedTy.agda` is `Examples/Scoped.agda`'s twin: the same
λ-calculus, the same two interesting constructors, indexed by CONTEXT
AND TYPE instead of by DEPTH.

| | lam+app, desc **and** Wf | module | time | memory |
|---|---|---|---|---|
| `Scoped` — depth-indexed | **22** lines | 433 | 0.68 s | 171 MB |
| `ScopedTy` — type-indexed | **96** lines | 257 | **0.42 s** | **159 MB** |

⇒ **the constructors cost 4.4× the lines, and there is NO time or memory
blowup whatever** — the type-indexed module is *faster and smaller* than
its depth-indexed baseline.

★ **The predicted structure came out exactly right**, from `Scoped`'s own
rule (*"`iι` targets the AMBIENT index, so a constructor that wants to
land elsewhere must SAY SO with an `Id` field"*):

    app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
      target IS the ambient (Γ , B)    ⇒ NO Ford.  +1 κ for A.
    lam : Tm (Γ , A) B → Tm Γ (A ⇒ B)
      target is (Γ , A ⇒ B) ≠ ambient  ⇒ ONE Ford.  +3 κ.

⇒ **one Ford across the whole language**, and Fording is the CHEAP form
(`tmp/ProbeFord`: 60 ms forded vs 15,998 ms computed). The 267× case is
not reachable from here.

### 5.0 ⚠⚠ PROBE 2 — THE FOLD, and a CORRECTION TO §2.1

`Examples/ScopedTySz` applies `Lib/ISz`'s generic fold to the
type-indexed syntax, against `Examples/ScopedSz` on the depth-indexed
one. The port was **structurally byte-for-byte identical** — only
`INat` → `I`:

| | content lines | time | memory |
|---|---|---|---|
| `ScopedSz` — depth | **22** | 0.85 s | 185 MB |
| `ScopedTySz` — type | **22** | 0.82 s | 185 MB |

⇒ **a fold over a type index costs exactly nothing extra.** `Lib/ISz`'s
claim to be *"generic in the description AND in the index type"* is now
measured rather than plausible.

★★★ **BUT CHASING THE NEXT STEP FOUND THAT §2.1 OVER-ATTRIBUTES, and
this is evidence AGAINST the case this file was building.**

§2.1 lists the weakening towers and the `natⁿ` family as consequences of
*"the index is `(sort, depth)`, so every invariant is ARITHMETIC"*.
Checked directly, they are not:

```agda
methsTyMotK = Π (…D…) (Π (…M…) (Π Nat (…)))   -- THREE motive passengers
methsTyCons = lam (lam (lam (lam (lam (lam …)))))   -- 3 standard + 3 passengers
```

The tower depth is **6 because the method has 6 binders**: three standard
(index, payload, IH tuple) plus one per MOTIVE PASSENGER. `sub-w²-single`
and `tower⁶` collapse the substitution stack those βs leave. Likewise
`nat6₅` is 6-fold (six substitutions = arity) × 5-ary (`methTyK`'s
arity). **Both families are driven by METHOD ARITY, which comes from the
motive's Π-telescope — not by the index being a number.**

⇒ a typed `methsTyFrom` would still take `D`, `M` and `j` as passengers,
still be `lam⁶`, and still owe the same towers. **Type-indexing does not
remove the two largest pain families.**

What IS index-driven, and would go:

* `⟶*-wkTyKᵈ`'s four descents — `wkTyK` mentions its DEPTH four times
  (the index, `nsuc n`, and twice inside `vsRenK`'s `Var-vsK`);
* §2.2's defect class — `K`'s index is `Σ' Nat Nat`, which cannot
  distinguish the index binder from the payload binder;
* §2.3's ledger, in part — adequacy obligations that hold by
  construction under intrinsic typing.

⇒ **the honest scorecard: B fixes §2.2 and part of §2.3, does nothing
for the towers and `natⁿ` in §2.1, and costs 4.4× on constructor lines.**
The `natⁿ`/tower problem is an ARITY problem, and its remedy is the one
`Lib/Wk` already names — index the family instead of listing it — not a
different kernel.

### 5.1 ⚠ What the probe does NOT cover

* **`var`.** `ScopedTy` omits it; `Scoped` carries it plus the whole
  forded `Fin` family. A typed `var` needs `Var Γ A`, which is
  `Knot/Lookup`'s shape — already built, already known to work, 730
  hand-written lines for 2 rows.
* **Scale.** Two constructors, not 53.
* **The folds.** Nothing here measures `sz`/`occ`/`ren`/`sub` over a
  type index, and those are where §2.1's towers live. This is the
  biggest remaining unknown and it is the one that matters most,
  because §2.1 is the mechanism the whole argument rests on.
* ⚠ The module totals are **not** apples-to-apples (different auxiliary
  families). Only the 22 → 96 figure is.

### 5.2 What it settles, and what it does not

**Settles:** a type index does not blow up. The catastrophe I argued
for — extrapolating 40× and 267× onto index richness — does not happen.
Both of those numbers are about specific failure modes (accumulating
codes; invertible computed indices), and neither is hit.

**Does not settle:** whether the Knot as a whole gets easier. That needs
the folds. But the direction of the evidence has moved: the cost is
4.4× on *constructor* lines, against §2's measured 40% rework rate and
eight tower rungs and eight `natⁿ` instances that a structural index
would delete outright.

---

## 6. The open question this file does not answer

§5 built the constructor-level probe and it came out favourable. What
remains unmeasured is **the folds** — `sz`, `occ`, `ren`, `sub` over a
type index. §2.1 says the Knot's pain is index bookkeeping in exactly
those folds, so that is where the argument must finally be tested.

⇒ the next probe, if one is wanted: `Knot/SzAgree`'s shape (a 30-row
fold, 442 lines, generated) against a type-indexed twin.

---

## 7. THE ARITY PROBLEM — diagnosis, and the move the WF axis already made

⚠ §5.0 showed the towers and `natⁿ` are ARITY, not index. This section
asks what to do about that, and the answer is a move this project has
already made ONCE, elsewhere, and won with.

### 7.1 Why arity costs anything at all

A method is `lam^n`. Applying it leaves **n stacked substitutions**, and
field `j` must be read past binders `j+1 … n` — so it arrives WEAKENED:

```agda
subTm σ₁ (subTm σ₂ (… (subTm σ_n (var (vs^(n-1) vz)))))
```

Each layer meets a `renTm vs`, and `subTm σ (renTm vs t)` **is stuck on
an abstract `t`** — it needs `wk-single`, which is an induction on the
term. ⇒ n binders cost O(n) weakening rungs (`tower⁶`, `towerJ⁵`, …) and
arity × stack-depth naturality lifts (`nat6₅`, `nat7₂`, …).

★★★ **The weakening exists ONLY because there is more than one binder.**
With one binder nothing is weakened past anything.

### 7.2 What the WF axis did differently — and it is the same shape

`Lib/Ord`, in its own words:

> `Hom Nat (nsuc k) nzero` **COMPUTES** to `base`. No fuel, no `Acc`, no
> `TERMINATING` — **the measure never appears, because the ORDER
> reduces.**

Agda/Coq/Lean do well-founded recursion through `Acc`, which does **not**
compute, so every use site fights `Acc_inv` transports. Once put the
invariant where it REDUCES, and the obligation became a conversion.

⇒ **the transferable principle: put the obligation where it COMPUTES.**

### 7.3 The same move, unmade, in the Knot

The Knot uses a **Π-telescope** for method arguments — n curried binders.
The alternative is a **Σ-telescope** — one binder over a tuple:

| | Π-telescope (today) | Σ-telescope |
|---|---|---|
| apply | n `app`s ⇒ n βs | **one** β |
| read field `j` | `var (vs^k vz)` under n substitutions, weakened | `fst (snd^j …)` |
| what that costs | `subTm σ (renTm vs t)` — **STUCK**, needs `wk-single` | `βfst`/`βsnd` — **REDUCTIONS** |
| ⇒ | the tower family, the `natⁿ` family | nothing |

Concretely: `subTm (single tup) (fst (var vz))` is `fst tup`, and
`fst ⟨i , …⟩ ⟶ i` by `βfst`. It **computes**. Nothing is weakened
because there is one binder.

⇒ this is `Hom Nat` computing, one level up: **§2.1's whole cost is
lemmas standing in for reductions that a different encoding would
perform.**

⚠ And it says where the Knot is CONVENTIONAL: curried methods are what
generic programming with descriptions does everywhere. The WF axis was
where this project departed from the field and won. **The Knot never
got that treatment.**

### 7.4 ⇒ What is missing in the KERNEL, exactly

```agda
ifields D i ms σ C m p = app (app (app m i) p) (iihs D ms σ C p)
```

**Three unary applications, fixed by `ι-ielim`.** So:

| binders | whose? | fixable where? |
|---|---|---|
| index, payload, IH tuple | **the kernel's ι-rule** | ⛔ kernel — `ifields` must pass a TUPLE |
| one per motive passenger (`D`, `M`, `j`, …) | **ours**, via `imethTy`'s Π-telescope | ✅ **library, today** |

⇒ **a library-only change already removes half the depth** — tupling the
motive passengers takes `methsTyCons` from `lam⁶` to `lam⁴`, and the
towers from six rungs to four — with NO kernel change and no re-indexing.

⇒ and the kernel change that finishes it is ONE RULE:

```agda
ifields D i ms σ C m p = app m (pair i (pair p (iihs D ms σ C p)))
```

one binder, `lam¹`, and **every field access becomes a reduction**. The
same edit to `ι-elim` for the non-indexed twin.

### 7.5 The ideal Knot, and the gap to it

Assume the Σ-telescope. An adequacy row becomes:

    head-red  ·  ONE β  ·  βfst/βsnd projections  ·  the IH

with **no cast at all** — no tower, no `natⁿ`, no `-sub` push-through for
the method machinery, no depth congruence for the argument slots.
Compare `Knot/MethsTyAgree`'s `consK-app`, which needs six βs, a
`cong₅`, `tower⁶`/`towerJ⁵`/`towerJ`/`towerA`/`towerP`, `nat6₅`,
`nat6₂` and `methTyK-sub` — **to say the same thing**.

**What is missing, in order of cost:**

1. ⬜ `imethTy`/`methTy` build a Σ-telescope instead of a Π-telescope;
   `Lib/IPay.⊢methLam` becomes `⊢methTuple`. **Library only.**
2. ⬜ `ι-ielim`/`ι-elim` pass a tuple. **Kernel, one rule each** — and
   its subject-reduction obligation is the same obligation, re-shaped.
3. ⬜ then delete: the tower family (8 rungs), the `natⁿ` family (8
   instances), and the `-sub` lemmas that exist only to cross a method's
   binders.

⚠⚠ **STATUS: PROPOSED, NOT MEASURED.** What is verified is the
diagnosis — `ifields` is three unary apps, `methsTyMotK` is a
three-passenger Π-telescope, `βfst`/`βsnd` are reductions, and the tower
family is eight rungs deep. That tupling removes the towers is an
argument, not a measurement.

⇒ **the probe: take ONE program with passengers — `methsTyFromK` is the
one just built, and its `consK-app` is the worst case — and rebuild it
with the passengers tupled.** That is step 1 alone, library-only, and it
should take `lam⁶` to `lam⁴`. If the cast shrinks as predicted, step 2
is worth its kernel edit; if it does not, this section is wrong and
cheaply so.

### 7.6 ⛔ A cross-module depth ladder does NOT test §7 — numbers void

An attempt to measure §7 by timing three modules of increasing binder
depth, cold:

| module | binders | time | RSS | lines |
|---|---|---|---|---|
| `PayTyAgree` | n=4 | 679.23 s | 600 916 KB | 288 |
| `IhTyAgree` | n=5 | **900.00 s** | **9 332 KB** | 293 |
| `MethsTyAgree` | n=6 | **319.96 s** | 673 620 KB | 443 |

⚠ **Every row is unusable, and for three independent reasons:**

1. `IhTyAgree` is `900.00 s` flat with a 9 MB RSS — that is the **timeout
   wrapper**, not Agda. The observation is CENSORED: the true value is
   "> 900 s", which is not a number.
2. n=6 is **twice as FAST as n=4**. There is no monotone trend to read.
3. These are three DIFFERENT modules — 288 / 293 / 443 lines, different
   row counts, different bodies. Binder depth is confounded with
   everything else, and the biggest module was the fastest. cf.
   `sweep-first-module-eats-the-closure`: cold ordering alone can swamp
   the effect being measured.

⇒ **this run is evidence for nothing — not for §7 and not against it**,
and it is recorded here only so the numbers are never cited as either.

★ The methodological point it does establish: **§7 cannot be tested by
comparing modules.** Binder depth is not separable from content across
the tree. The probe must be an **A/B on ONE module** — `methsTyFromK`
with its passengers curried, then tupled, same rows, same bodies, cold
both times — which is what §7.5 already specifies. Treat §7.5's wording
as binding, not as one option among several.
