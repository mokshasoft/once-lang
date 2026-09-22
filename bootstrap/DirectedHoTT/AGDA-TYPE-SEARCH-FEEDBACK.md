# Feedback: `--duplicate-types` / `--search-type` / `--dead-code`

*Notes from first use, 2026-09-22, against `agda 2.8.0-ccf93d7-dirty`.
Companion to `AGDA-TYPE-SEARCH-PROPOSAL.md`, which is the design this
implements. Tested on `DirectedHoTT` — ~330 modules, 933 definitions in
the largest closure exercised.*

---

## 0. Verdict

It works, it is fast enough to be an everyday tool rather than a batch
job, and **it found a duplicate that the text-based prototype
structurally could not**. Three of its design choices are better than
what the proposal asked for. The issues below are about usage guidance
and one packaging hazard, not about correctness.

| run | invocation | result | cost |
|---|---|---|---|
| 1 | `--duplicate-types` on `Examples/AmrecT` | 4 real duplicates, body sizes matching | 7.3 s / 558 MB |
| 2 | `--duplicate-types` on `Lib/Wk` | the load-bearing `cong₃`, body 5 = 5 | 1.3 s / 190 MB |
| 3 | `--search-type='subTm _ (subTm _ _) ≡ _'` on `Lib/Wk` | 9 `generalises` + 2 `instance-of`, ranked | 1.3 s / 190 MB |

★ **1.3–7.3 s on a warm closure.** The proposal worried that "re-checked
rather than reused" would make this a CI job. It does not.

---

## 1. Better than asked for

**a. Pattern-symbol frequency, printed as guidance.**

```
  Pattern symbols, and how many types in scope mention each --
  a pattern built only from common ones cannot return a short list:
    DirectedHoTT.Spec.Syntax.subTm 107 types
    normalizer.Syntax.Types._≡_   314 types
    DirectedHoTT.Spec.Syntax.RTm  543 types
```

The prototype needed an inverse-document-frequency filter to get 153
candidates down to 13, and that filter was a black box that silently
discarded true positives. Surfacing the frequencies instead of filtering
on them is strictly better: the user learns *why* their query is bad and
can fix it, and nothing is dropped.

**b. Ranking by how much of the hit the pattern accounts for**, with the
matching substitution printed per hit (`with _1 := Γ ∙, _2 := Γ, …`).
The substitution is what tells a reader *how to call* the lemma, not
merely that it exists. Nothing in the prior art (Hoogle, Loogle,
`SearchPattern`, `find_theorems`) prints it.

**c. The body-size column, and the header that explains it.** This was
the proposal's single strongest recommendation and it is implemented
with the argument attached. It is load-bearing in practice — see §2.

---

## 2. Body size is doing real work

It separates three kinds of same-type pair *at a glance*:

```
ren-wTy       AmrecT 102 | Lib.Wk 102    → real duplicate
wk-ren        RedCong 195 | TySub 102    → same name, different theorem
⊢strong-descend 7 | ⊢strong-step 136     → an ALIAS (`= ⊢strong-step`)
aSBr 72 | ihZ 118                        → same type, different function
```

⚠ The alias case is worth calling out: `Lib/Ord.⊢strong-descend` is
literally `= ⊢strong-step`. It is reported, correctly, and the 7-vs-136
gap says "alias" immediately. A reader with only the types would have
had to open the file.

---

## 3. ★ It found something the name-based prototype could not

The prototype's strongest detector was "same name in more than one
module" — exact, O(n), and it found 23 byte-identical duplicates. It is
blind, by construction, to a duplicate under a **different name**.

`--duplicate-types` found one:

```
{Γ : Cx} → RTy Γ → RTm (Γ ∙) → RTm (Γ ∙) → RTm Γ → RTy Γ
  Examples.AmrecT.aAuxB    body 11
  Examples.AmrecT.aIHTat   body 11
  Lib.Rec.aIHTat           body 11
```

and in the source:

```agda
aAuxB  A cM m n  = aAuxB'  A m (w n)  (w cM)      -- Examples/AmrecT
aIHTat A cM m μx = aIHTat' A m (w μx) (w cM)      -- Lib/Rec
```

The same function, three times, under two names — and `AmrecT` already
imports `Lib/Rec`. Same for the primed pair (`aAuxB'` 19 / `aIHTat'`
22). **This is the case that motivates typing the index rather than
hashing names**, and it is a concrete win over the prototype rather than
a hypothetical one.

---

## 4. Issues

**4.1 ⚠ Scope is the entry module's import closure — DOWNWARD only.**
This is the one thing that would mislead a new user, and it bit the
exact scenario the tool exists for.

The prototype was written because I hand-wrote `towerJ⁶` when `tower⁶`
already existed. Searching `subTm _ (subTm _ _) ≡ _` **from `Lib/Wk`**
returns the whole local family — `towerP`, `towerA`, `towerJ`,
`towerJ⁵`, `sub-w²-single`, `sub-w³-single` — and **not `tower⁶`**,
because `tower⁶` lives in `Examples/Knot/IihsAgree`, which is
*downstream* of `Lib/Wk`.

Cross-module search itself works: the same run returned hits from
`Spec/Syntax` and `Metatheory/SubjectReductionBase`. The rule is that
you see what you depend on, never what depends on you.

⇒ **the entry module must be the one you are editing**, which is highest
in the dependency order — not the library you expect the answer to live
in. The instinct is the opposite. Worth one line in `--search-type`'s
help; it converts a silent miss into a usage rule.

**4.2 No direction on kernel copies.** `cong₃` is byte-identical in
`Spec/Syntax` and `Lib/Wk`. The header's prose covers it ("a copy that
lets one part of a development avoid importing another may be carrying
an architectural invariant") but nothing says **which side** is
removable. Here the import ban is one-way — `Lib/` may import `Spec/`,
not the reverse — so the kernel copy must stay and the `Lib/Wk` copy is
the candidate. ⚠ I got that direction backwards in my own prototype's
warning on the first attempt, which is the argument for encoding it
rather than leaving it to the reader: if the tool knows the import
graph, it knows which side *can* import the other.

**4.3 `LC_ALL=en_US.utf8` fails on this box** despite `locale -a`
listing it; output dies with `commitBuffer: invalid argument (cannot
encode character '\949')` — including partway through `--help`.
`LC_ALL=C.UTF-8` plus `--transliterate` works. `run-ast-dumps.sh`
hardcodes `en_US.utf8`, so it will hit this.

**4.4 Interface sharing between binaries.** The custom build reports
version `2.8.0` and therefore shares `_build/2.8.0/` with a stock 2.8.0
agda; each invalidates the other's interfaces. There is no
`--build-dir`, so staging into a scratch tree is the only isolation —
which is exactly what `run-ast-dumps.sh` already does and says why.
Measured here: cheap (a re-check of 8 modules, 7.5 s) — but this tree
has a module that takes 58 minutes, so on the wrong module it is not
cheap. **Suggest either a `--build-dir` flag or a note in the help.**

**4.5 Minor: `_.`-qualified locals repeat.** `where`-bound helpers
(`_.ptw`, `_.bridge`) appear ~10× in one report. One of them is a real
find — `Lib/Wk._.bridge` and `Metatheory/TySub._.ptw` have the same type
*and* both body 51, i.e. a shared lemma waiting to be lifted — so
suppressing them outright would lose signal. Perhaps collapse repeats of
the same qualified name.

---

## 5. Suggestions, ranked

1. **Scope note in `--search-type`'s help** (§4.1). Highest value per
   character: it is the difference between a silent miss and a rule.
2. **Which-side-is-removable for kernel/library collisions** (§4.2),
   derived from the import graph.
3. **`--build-dir`, or a help note about interface sharing** (§4.4).
4. Collapse repeated `_.`-qualified locals (§4.5).
5. Consider surfacing `--dead-code` in the same report: a duplicate that
   is *also* unreachable is unambiguously deletable, and that subset is
   the only one safe to act on without reading. (The prototype found one
   — a lemma with the same type as its neighbour twenty lines away, never
   used.)

---

## 6. Not the tool's fault, recorded so the numbers are not misread

The cost figures above are clean, but three runs during this session
died silently and I first blamed contention. They were **my** fault: I
had three concurrent agda processes alive without realising (one moved
to the background by a timeout and assumed dead, one orphaned by
`nohup`, one intentional), on a 7 GB box. They OOM-killed each other.
Nothing in the tool contributed. Timings in §0 were taken with the box
otherwise idle.
