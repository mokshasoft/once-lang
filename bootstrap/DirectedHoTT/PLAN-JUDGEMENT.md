# OCP-0009 — PLAN: THE JUDGEMENT LAYER

Companion to `PLAN-INDEXED.md`, which took the SYNTAX into the kernel.
This one takes the JUDGEMENTS. It is a build plan, not a spike record:
the spikes are done and §1 says what they settled, so that nothing here
is re-discovered.

Read `HANDOFF-2026-08-26.md` first for session state; read
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
* **`Ctx` is not encoded.** It is an 8th sort, and it is not among the 53
  — it lives in `Spec/Typing`, not `Spec/Syntax`.
* Reduction is tested only at **small concrete inputs**. Nothing is known
  about `ielim` reduction at knot scale.
* The **168 rows** are not written.

## 3. BUILD ORDER

### Step 0 — `Ctx` as the 8th sort  ⟨cheap, independent⟩

`_▹_ : (Γ : Ctx) → RTy ⌊ Γ ⌋ → Ctx`. Index it by DEPTH, as the rest of
the table is: `Ctx d → RTy d → Ctx (suc d)`. Then the `RTy` field sits at
`pair sTy ⟨d⟩` — an ordinary cross-sort field at the ambient depth, so it
costs nothing new. ⚠ `◇` Fords the depth to `0` and `_▹_` to `suc d`, so
`Ctx` is a Forded family like `Var` and pays §1's transport where its
index is consumed.

⇒ regenerate through `tools/gen-knot.py`; its coverage check must be
extended to `Spec/Typing`'s `Ctx` or it will not see the new sort.

### Step 1 — ★ `_∋_∷_`  ⟨THE FIRST REAL JUDGEMENT, and it is reachable NOW⟩

    here  : (Γ ▹ A) ∋ vz ∷ renTy vs A
    there : Γ ∋ x ∷ A → (Γ ▹ B) ∋ vs x ∷ renTy vs A

Two constructors, and it mentions **only** `Ctx`, `Var`, `RTy` and
`renTy vs` — weakening by ONE, which `Examples/WkTm` already provides in
the `Tm` case and which needs the same treatment for `RTy`.

★ **DO THIS BEFORE SUBSTITUTION.** It is a complete judgement, it needs
no machinery beyond what exists, and it is the smallest thing that
demonstrates a RELATION over encoded syntax. It is this increment's
`step 1a`.

⚠ Its index is a THREE-component dependent telescope —
`Σ' Nat (Σ' (Ctx ⟨d⟩) (Σ' (Var ⟨d⟩) (RTy ⟨d⟩)))`. §1a tested two
components; three is more of the same but is the first place to look if
it misbehaves.

### Step 2 — object-level weakening for `RTy`/`RTm`, then `extS`, then `subTm`

⚠ **THE ORDER IS FORCED, AND IT IS SHORTER THAN IT LOOKS.**
`extS σ (vs x) = renTm vs (σ x)` — weakening by ONE, not a general
renaming. ⇒ **general renaming is never needed.** The chain is

    wk (have, for `Tm`)  →  Fin eliminator  →  extS  →  subTm

with the Kripke motive of §1d at the last step:
`∀n. (Fin ⟨i⟩ → Tm n) → Tm n`, which adds a `Π` over `Nat` and a `Tm`
codomain to what `KripkeIx` already does — both ordinary.

### Step 3 — the mutual judgement block

⚠ **IT CANNOT BE STAGED THE WAY THE SYNTAX WAS.** `ty-El` needs
`Γ ⊢ c ∷ U`, so `_⊢ty_` and `_⊢_∷_` are MUTUAL. Per §13 that is one
description over a tagged index — fine, but it means no partial landing:
`_⊢ty_` alone is not a milestone.

| | rows | needs |
|---|---|---|
| `_∋_∷_` | 2 | weakening (step 1) |
| `_⊢ty_` + `_⊢_∷_` | 43 | substitution (step 2) |
| `_⟶ᵀ_`, `_≅ᵀ_` | 30 | — |
| `_⟶_` | 73 | — |
| `Canon`, `Prog` | 20 | the above |

### Step 4 — `prog` object-level

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
| `Knot/Ctors` (51 smart ctors) | 21s |
| `Knot/Map` (the adequacy map) | 4s |
| `Knot/Sz` (via `Lib/IFold`) | 3s |

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
