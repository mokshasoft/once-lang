# OCP-0009 · SCOPING THE INDUCTIVE-TYPES AXIS

*Written 2026-08-13, after the gcd three-way comparison. ⚠ NOTHING HERE IS
BUILT — this is a scope with costs estimated from MEASURED precedent, and
it should be read as a plan to argue with, not a result.*

--------------------------------------------------------------------------
## 0. WHY THIS AXIS, AND WHY NOW

Three independent threads converged on it:

1. **The dogfooding target.** `ARCHITECTURE.md`: *"`⊢amrec` applies to
   `prog`/`usplit`/`trS`/`ordtrS` VERBATIM the moment `RTm` is a kernel
   type and `sz` is definable. Nothing further is needed from the WF
   axis."*
2. **`lexrec`'s missing use site** (`WF-LIBRARY.md` D11). The canonical
   genuine example is UNIFICATION — Robinson terminates on (unsolved
   variables, term size) lexicographically and the size can *increase*
   when a variable is eliminated. Unwritable here: no term carrier.
3. **The gcd comparison.** 54% of the kernel route was arithmetic, because
   the kernel's `_+_`/`_∸_` are `natrec` terms that are stuck on open
   arguments. A term carrier is where that actually bites.

⇒ they are ONE blocker, and `ARCHITECTURE.md` already ranks it *"the real
blocker, and the highest value"*.

--------------------------------------------------------------------------
## 1. ★ THE UNIT OF COST, MEASURED

`ARCHITECTURE.md` says a new former costs *"a full nine-module cascade
(rules, classifier, SN layer, Conf development, `fund` case, Canon case —
the `ordtr` bill)"*. That bill is in git, so it is a number:

| former added | lines | modules | biggest two |
|---|---|---|---|
| `ordtr` (5 rules, no binder, no new type) | **1,914** | 12 | `LR` 757 (40%), `Conf` 431 (23%) |
| `Nat`+`nzero`+`nsuc`+`natrec` (dependent motive, binder, ι) | **2,026** | 11 | `LR` 541 (27%), `Fund` 367 (18%), `Conf` 303 (15%) |

★ **One kernel former ≈ 2,000 lines across ~12 modules, 40–60% of it in
`LR` + `Conf`.** Both data points agree, and `natrec` is the closer
analogue (it has a dependent motive, a binder and an ι-rule, as any
inductive eliminator does).

⚠ **`LR` is already 5,428 lines.** `agda-perf-is-mutual-block-size` says
compile time is dominated by the mutual block's positivity and termination
graph — so a nested induction added *there* is the main performance risk of
this axis, not the line count.

--------------------------------------------------------------------------
## 2. FOUR DESIGNS

### A — one bespoke former per datatype
One cascade (~2 kloc) **each**. ⛔ `ARCHITECTURE.md` already rejects this
shape for ordered inductives: *"one former per datatype, versus one `μ` for
all"*. ⚠ And the dogfooding target is not one small datatype — `RTm` is an
INDEXED family (`RTm : Cx → Set`) with 25 constructors.

### B — W-types
`W A B`, `sup`, `Wrec`. One cascade; every strictly-positive
NON-INDEXED inductive encodes. ⛔ **Does not reach the target**: `RTm` is
indexed by its context, which plain `W` cannot express. Also the standard
objections — the encoding's equality theory wants funext, and `sz` over an
encoding is unpleasant.

### C — a UNIVERSE OF DESCRIPTIONS (containers / `Desc`) ★ RECOMMENDED
`Desc`, `⟦_⟧`, `μ`, and one generic fold; indexed descriptions (`IDesc`)
for families. One cascade for the machinery, and then **every datatype is a
TERM, not a former** — new datatypes cost the kernel nothing.

★ This is exactly `ARCHITECTURE.md`'s own "one `μ` for all" argument,
lifted from measures to types.

★★ And it removes a job rather than adding one: **strict positivity is
enforced by the `Desc` grammar**, so the kernel never needs a positivity
checker.

⚠ Biggest single cascade of the four — the `LR` case for `μ` is a nested
induction, which is the hardest thing on the list and where it could fail.

### D — sized types
⛔ **Banned.** `no-sized-types` is a standing project decision: they infect
everything.

--------------------------------------------------------------------------
## 3. ⭐ THE FIRST MOVE — A SPIKE THAT DE-RISKS THE HARD PART

Do NOT start by touching the kernel. The whole cascade hinges on one
question, and it can be asked in isolation:

> **Can the logical relation be defined by induction on a description, and
> does the fundamental theorem's case for the generic fold go through?**

Spike it at a MINIMAL universe — `end`, `rec`, `σ` — with no indexing, no
kernel integration, and no `--safe` obligations beyond the LR itself. That
is where the 2 kloc would concentrate; everything else in the cascade is
the mechanical row-filling both measured precedents show.

⚠ **Gate the axis on that spike**, exactly as `(S,S)` gated lexrec. If the
LR case does not go through at three constructors it will not go through at
`RTm`'s twenty-five.

--------------------------------------------------------------------------
## 4. THE ACCEPTANCE TEST

From `ARCHITECTURE.md`, unchanged: a datatype former, a fold, `sz : T → Nat`
definable by that fold, and the descent `sz ⟨sub-part⟩ < sz t`.

★ **The descent is already paid for.** `sz (node l r) ⟶ suc (sz l + sz r)`,
and `sz l ≤ sz l + sz r` is `≤-plusˡ`/`+-mono` — i.e.
`NbEPDirDBLibArith*`, the 371 lines built for gcd, is *directly* what a
`sz`-based descent needs. That investment was not gcd-specific.

⚠ **And the axis may SHRINK the WF axis.** `ARCHITECTURE.md`: *"anything
expressible as a CATA needs no well-founded order at all — the fold IS the
eliminator."* Much of `prog`/`usplit`/`trS` may turn out to be folds, and
need no measure at all. That is a good outcome and should be checked
BEFORE assuming `amrec` is what unblocks them.

--------------------------------------------------------------------------
## 5. TOTALITY, PRODUCTIVITY, STRUCTURED RECURSION — where they sit

**Structural recursion** — the recursive call is on a syntactic subterm.
`natrec` is the ONLY recursion former in this kernel, and it is structural
on ℕ.

**Totality** — every function total, every term normalising. ⚠ Here it is
not *checked*, it is *structural*: there is no general fixpoint, no
`TERMINATING`, no fuel, so there is no non-terminating term to write.
`NbEPDirDBCanon`'s consistency rests on exactly that.

**⇒ what the WF axis is FOR.** It lets you write recursions that are NOT
structural (`div`, `gcd`, quicksort) by COMPILING them into structural
recursion on a bound: `aux n x (μ x ≤ n)` is structural on `n`. That is
literally what `aAuxB`/`amrec` is.

★ **Which is why D11 found what it found.** `amrec` and `lexrec` are
DERIVED terms — structural recursion in disguise — so they cannot add
definitional power, and no function can "require" them. They buy
ergonomics, not reach.

**Productivity** — the dual, for CO-inductive data: every finite
observation produced in finite time, with guarded corecursion as the
structural analogue. ⚠ **This kernel has no coinductive types at all**
(`NbEPCoind`/`NbEPOTTCoind` are separate explorations, not part of the DB
kernel), so productivity does not currently arise. If codata is ever
added it is its OWN cascade — and ⚠ **the WF axis will not help**, because
a measure establishes termination, not productivity. Guardedness does.

**How this bears on the axis.** Adding an inductive type means adding a
structural ELIMINATOR, and the ~2 kloc cascade *is* the cost of proving
that the new former preserves totality — SN, confluence, subject
reduction, canonicity. Nothing about it is bureaucracy; each module is one
half of the totality argument.

--------------------------------------------------------------------------
## 6. HONEST UNCERTAINTY

* The 2 kloc figure is from two SIMPLE formers. A description universe is a
  type former, a family of constructors, a generic eliminator AND a nested
  induction in `LR`. **2 kloc is a floor, not an estimate**; I would not be
  surprised by 2–3×.
* Whether `IDesc` is needed on day one, or whether a non-indexed `Desc`
  buys enough to be worth landing first, is undecided and worth deciding
  from the spike.
* Nothing here is measured. The gate in §3 exists so the first real number
  arrives before the commitment does.
