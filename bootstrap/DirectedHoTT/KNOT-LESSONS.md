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
