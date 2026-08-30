# Where-bound lemmas that should be lifted — a scan

**Why this file.** `Lib/IPay`'s `iatCon-wf` spike stalled for want of
"substituting by a renaming IS renaming". Its own note said *"look for
that lemma before writing one"* — and the lemma existed, in
`Lib/Wk.nrs-wTy`'s `where` block, one scope too deep for grep. Lifting it
unblocked the spike in four lines.

⇒ so the tree was scanned for the same shape. **A `where`-bound lemma is
invisible** — to grep, to a reader, and to any future search tactic.

**Method.** Every `where` clause (excluding `data`/`record`/`module`
headers), every definition in it carrying a type signature, keeping those
whose signature mentions **no variable bound by the enclosing clause** —
i.e. lemmas that are general in their own right. **295 hits**, from 1619
where-bound definitions.

---

## ★★★ The finding: a lemma in the wrong STRATUM breeds copies

`subTy (single u) (renTy vs A) ≡ A` — the type-level twin of
`wk-single` — has **six local copies**:

| file | name |
|---|---|
| `Metatheory/Fundamental.agda:166` | `wk-sub-single` |
| `Metatheory/Fundamental.agda:583` | `wk-single-ty` |
| `Metatheory/Fundamental.agda:773` | `wk-single-ty` |
| `Metatheory/SubjectReduction.agda:2173` | `wk-sub-single` |
| `Metatheory/SubjectReduction.agda:2308` | `wk-sub-single` |
| `Metatheory/Fundamental/Indexed.agda:251` | `wk-sub-single` |

⚠⚠ **And they are not carelessness.** `wk-singleTy` *does* exist, at top
level — in **`Lib/Wk`**. But `Lib` imports `Metatheory`, so
**`Metatheory` cannot see it**. Every one of those six is a module that
needed the lemma and could not reach it.

★ The TERM version `wk-single` is in `Spec/Typing:77`, below both strata,
where everyone can use it. **The type version is simply in the wrong
place.** ⇒ move `wk-singleTy` down beside `wk-single`, and six copies
collapse.

⚠ That edits `Spec/Typing` — the kernel. It *adds* a derived lemma next
to its existing twin and changes no statement, but it is a kernel file,
so it wants a deliberate nod rather than a drive-by.

---

## Other duplicates found

| lemma | copies | note |
|---|---|---|
| `subTm (extS (single y)) (w (w t)) ≡ w t` (`peel₁`/`p₁`) | **5** — `Gcd/Dvd:414`, `Gcd/IndG:205,315`, `Gcd/StepExt:488`, `Comparison/GcdIndStepConcrete:118` | it is `sub-w` then `wk-single`; `Knot/Build:467`'s `rtA` is a sixth, generalised |
| `ren-sub` / `ren-sub'` / `ren-sub''` | 5 — `Lib/Wk:195,213,225`, `AmrecT:185,200` | all instances of top-level `Lib/Wk.ren-sub` |
| `ren-subTy` | 1 — `AmrecT:170` | now top-level in `Lib/Wk`; `AmrecT` can import it |
| `+-suc : n + suc o ≡ suc (n + o)` | 2 — `Fundamental:162`, `Fundamental/Indexed:247` | standard `Nat` |
| `extR-swap` / `extS-swap` / `swap3` / `swap3s` | 4 — `SubjectReduction:999,1021,1240,1276` | one family, four `where` blocks in one file |
| `exts-wk` | 1 — `SubjectReduction:2540` | the `Lib/Wk.sub-w` statement |

⚠ **A third copy at the term level, too**: `Spec/Variance.ren-as-sub` is a
~100-line structural induction proving exactly what `Lib/Wk.ren-sub`
proves in two lines via `subTm-id`/`renTm-subTm` — and `Lib/Wk` *imports*
`ren-as-sub` while also defining `ren-sub`. Two proofs of one statement,
in the same import graph.

---

## What is safe to do now, and what is not

* ✅ **Within `Lib/` and `Examples/`** — `AmrecT`'s three copies, the five
  `peel₁`s, `Lib/Wk`'s own `ren-sub'`/`ren-sub''`. These can import the
  top-level lemma today.
* ⚠ **`Metatheory/`'s six** cannot be fixed without moving the lemma into
  `Spec/`. That is the real repair, and it is a kernel edit.
* ⬜ **`SubjectReduction`'s swap family** is four `where` blocks in one
  file; hoisting them to that file's top level costs nothing and needs no
  cross-stratum move.

## Does the `Metatheory` cleanup help steps 3 and 4? — **no**

Steps 3 and 4 build in `Examples/` and `Lib/`, both of which can already
see `Metatheory` *and* `Lib`. The six duplicates cost those modules
nothing. ⇒ **deferring it is correct**; it is hygiene, not a blocker.

## Which stratum, actually — and does it need a new one?

⚠ **The worry "don't move things into `Spec` that don't belong there" does
not apply to this particular lemma**, and it is worth being precise about
why.

    wk-singleTy T = trans (subTy-renTy T) (subTy-id T)

Both `subTy-renTy` and `subTy-id` are **already in `Spec/Syntax`**, and
the term-level twin `wk-single` is **already in `Spec/Typing:77`**. So
this is not new material entering the kernel — it is a one-line corollary
of two neighbours, sitting three strata away from both. `Spec/Syntax`
*is* the shared substitution-lemma stratum; it already holds
`subTy-renTy`, `subTy-subTy`, `subTy-cong`, `subTy-id`, `renTy-renTy`.

★ **So no new module is needed for this one.** The dependency direction
question is real but separate:

* **`Metatheory` → `Lib`?** Wrong way round. `Lib` is proof machinery
  built *on* subject reduction and the logical relation; inverting it
  would put `Sub⊢`, `⊢-cast` and friends below their own proofs.
* **A shared `Lib/…` module both can import?** The right shape *for
  lemmas that genuinely need typing derivations* and are wanted on both
  sides. ⬜ Whether any such lemma exists has **not been measured** —
  every duplicate found in this scan is purely syntactic (substitution
  and renaming equalities), and those belong in `Spec/Syntax` with their
  siblings, not in a new stratum.
* ⇒ so: **measure before building a stratum.** If the only citizens turn
  out to be syntactic, the shared module is an empty box.

## The rule this suggests

**If a `where`-bound lemma's statement mentions nothing from its clause,
hoist it** — even with one customer. The cost is a line; the cost of not
doing it was, here, a blocked generalisation and six duplicated proofs.
And place it in the **lowest** stratum that states it, or the modules
below will each write their own.
