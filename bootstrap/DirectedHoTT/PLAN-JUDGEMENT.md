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
* ~~**`Ctx` is not encoded.**~~ ✅ DONE — step 0 below. It is the 8th
  sort, tags 7, rows 54–55, and it lives in `Spec/Typing` rather than
  `Spec/Syntax`, which is why the generator's coverage check now reads
  two files.
* Reduction is tested only at **small concrete inputs**. Nothing is known
  about `ielim` reduction at knot scale.
* The **168 rows** are not written.

## 3. BUILD ORDER

### Step 0 — `Ctx` as the 8th sort  ✅ **DONE 2026-08-27**

`Ctx d → RTy d → Ctx (suc d)`, tags 7, rows 54 and 55 — **appended last**,
so no existing tag and hence no `∈ID` position moved. Regenerated through
`tools/gen-knot.py`, whose coverage check now reads **two files** (`Ctx`
lives in `Spec/Typing`, not `Spec/Syntax`) and is controlled: deleting
`_▹_` from the table makes it report `✗ Ctx: missing ['_▹_']`.

| | |
|---|---|
| `Desc`/`Wf`/`Tags`/`Ctors`/`Map` | regenerated, all green |
| the two rows' smart constructors | `Knot/Build`, hand-written |
| the adequacy map | `enCtx`/`⊢enCtx` in `Knot/Map` |

★ **THE ROW FORMULA ABOVE WAS RIGHT; THE SENTENCE PRICING IT WAS NOT.**
`Ctx d → RTy d → Ctx (suc d)` targets `suc d`, so the `RTy` field does
**not** sit at `pair sTy ⟨d⟩` and is not "an ordinary cross-sort field at
the ambient depth": BOTH recursive fields sit at the **bound field's**
depth `m`. That is what makes `_▹_` a shape the table did not previously
have — `Var`'s rows Ford the depth with
at most ONE ordinary field beside the Ford; this one has two, and the
telescope is five slots, the deepest after `ordtr`'s six.

★★ **AND THE DEPTH-FORDED SHAPE SCALES TO FIELDS.** `⊢Ctx-extK` costs
exactly **one `kCast` and one `⊢-cast`** — every mangled form of the two
numerals comes back by `num-ren`/`num-sub`, one rung per action, exactly as
the `Var` rows do. The extra field lengthens the chains without adding a
KIND of obligation. ⇒ nothing here argues against §3 step 1's three-
component telescope.

⚠ `◇` IS AT A LITERAL INDEX AND SO COSTS NOTHING. It Fords the depth to
`0`, so its ambient is the closed `pair sCtx nzero` and both actions
compute on it — `Knot/Terms`' situation, not `Var-vsK`'s.

**Measured, cold, on the same 7.7 GB box** — the two rows are free:

| | 53 rows | 55 rows |
|---|---|---|
| `Knot/Wf`, `-A64m` | OOM at 76s | OOM at 80s |
| `Knot/Wf`, `-A64m -c` | 104s | **99s** |
| `Knot/Ctors` | 21s | 15s |
| `Knot/Build` | — | 6s |
| `Knot/Map` | 4s | 3s |

⇒ the "needs the compacting collector" marker was **re-measured and is
still right** (the plan's §5 warning about stale markers applies, and this
time the marker survived it). And +2 rows moved the number by less than the
±12% noise floor: **the cost is the SHAPE of a row, not the count.**

⚠ THE NEGATIVE CONTROL, run on the new rows and not merely on the
mechanism. `Knot/Map`'s `Ctx` clause is the ONLY place where Agda's own
`_▹_` meets the table, and it is load-bearing:

| perturbation of `⊢enCtx (Γ ▹ A)` | |
|---|---|
| swap the two recursive arguments | rejected: `enTy A != enCtx Γ` |
| depth `suc (len ⌊ Γ ⌋)` | rejected: `nsuc (num …) != num …` |

⇒ field ORDER and the DEPTH are both pinned by the map, for these rows.

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

⚠ **WHAT STEP 0 DID AND DID NOT UNBLOCK.** `Ctx` is now a sort, so the
index telescope is WRITABLE. What is still missing is `renTy vs` as an
`ielim` over the knot returning a knot element — `Examples/WkTm` does it
for a 3-constructor toy, and the knot has 55. ⚠ Per `Lib/IFold`'s result
that must be a fold COMPUTED from the description, not 55 enumerated
methods; an enumerated one is the 147s-vs-5s mistake with a syntax
codomain instead of `Nat`.

⚠ Its index is a THREE-component dependent telescope —
`Σ' Nat (Σ' (Ctx ⟨d⟩) (Σ' (Var ⟨d⟩) (RTy ⟨d⟩)))`. §1a tested two
components; three is more of the same but is the first place to look if
it misbehaves.

### Step 2 — object-level weakening for `RTy`/`RTm`, then `extS`, then `subTm`

⚠⚠ **READ `HANDOFF-2026-08-27` §A′ BEFORE STARTING.** The uniform shift
that `WkTm`/`WkFin` use works for 54 of the 55 rows and breaks at `◇` —
and the point is that it does not FAIL there, it fabricates a context and
type-checks. `◇`'s method is DEAD CODE for any traversal entered at a
syntax sort, so this is a fork (split `Ctx` out / write the junk down and
restrict the claim), not a blocker. Derived on paper, not compiled; spike
`◇` first.

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
| `Knot/Wf` (55 `IConWf`) | 99s, **needs `-c`** (re-measured 08-27) |
| `Knot/Ctors` (51 smart ctors) | 15s |
| `Knot/Build` (the 4 hand-written rows) | 6s |
| `Knot/Map` (the adequacy map) | 3s |
| `Knot/Sz` (via `Lib/IFold`) | 3s |

★ **AND +2 ROWS COST NOTHING** (53 → 55 moved `Wf` from 104s to 99s,
inside the ±12% noise floor). The driver is a row's TELESCOPE DEPTH, not
the row count — which is the number that matters for §3, because the
judgement rows are ~3× as many but no deeper.

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
