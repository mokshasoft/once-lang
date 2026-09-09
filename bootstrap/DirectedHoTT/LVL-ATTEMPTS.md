# `agree-var` — THE LEVEL ROWS

Companion to `OCC-ATTEMPTS.md`. That file logs `occK`'s fold plumbing;
this one logs the TWO `Var` rows, which are not plumbing — they carry the
only real mathematical content in `occK`'s adequacy.

## Why they are separate from the other 48

The 48 generated rows are the generic fold, and they went green in one
pass once `Lib/IFold.scopeAt` was in place. The `Var` rows are different
for three independent reasons, and each one bites:

1. **`cVar-vz` is not folded.** It is the ONE row spliced by
   `Lib/IMeths.methsAt` (`Knot/Occ`'s `occVz`), because its ICon has no
   `iρ` field and the generic fold would hand back `z` where the answer
   is `eqNat k m`. So `occSum-red` does not apply to it at all.
2. **Their `nat` field is the ENCODED DEPTH**, not an Agda constructor
   argument: `enVar {Γ ∙} vz = Var-vzK (num (len Γ))`. The generator
   emitted `agree-var x (vz y0) i` and Agda said *"the constructor vz
   expects 1 arguments … but has been given 2"*.
3. **They sit at indices 51/52**, past `methsAt`'s spliced prefix, so
   `methsAt-sel` does not reach them — `methsAt-past` does.

## ✅ THE STATEMENT HAD TO CHANGE — and this was found by trying

The first statement was

```agda
agree-var : (x y : Var Γ) (i : RTm Θ) → … (b2n (eqv x y))
```

**It cannot be proved.** `cVar-vs` descends from `enVar (vs y')` to
`enVar y'` where `y' : Var Γ` while `x : Var (Γ ∙)`; if `x` is `vz` it
has no counterpart in `Γ`, so the IH cannot even be stated. ⇒ quantify
the LEVEL, not a second variable:

```agda
agree-var : (k : ℕ) (y : Var Γ) (i : RTm Θ) → … (b2n (eqℕ k (lvl y)))
```

The `eqv` form is then recovered at the ONE use site (`cTm-var`) by
`eqv-lvl` below. ★ Same shape as the standing lesson that a narrow twin
shadows the general form — except here the narrow one is not merely
weaker, it is unprovable.

## ✅ THE THREE LEMMAS — all green, `tmp/LvlSpike.agda`

| | | |
|---|---|---|
| `eqNat-num` | `eqNatTm (num a) (num b) ⟶* num (b2n (eqℕ a b))` | ✅ first try |
| `lvl-bound` | `eqℕ (len Γ + m) (lvl y) ≡ false` | ✅ |
| `eqv-lvl` | `eqv x y ≡ eqℕ (lvl x) (lvl y)` — **`lvl` is injective** | ✅ |

### ⚠ `lvl-neq` ALONE DOES NOT GO THROUGH — generalise over the slack

The bound wants to be `eqℕ (len Γ) (lvl y) ≡ false`. At `y = vs y'` the
goal is about `len (Γ ∙) = suc (len Γ)` while the IH is about `len Γ`,
and nothing bridges them. Carrying a slack `m` makes the `vs` case
exactly the IH at `suc m`:

```agda
lvl-bound : (y : Var Γ) (m : ℕ) → eqℕ (len Γ + m) (lvl y) ≡ false
```

⚠ And `_+_` recurses on its FIRST argument, so `len Γ + suc m` is stuck
and stepping the slack costs a `+-suc` rewrite — the same recursion-
direction tax `Lib/NatMaxNum` already pays three times.

### ⚠ `Lib/NatEq` HAD NO REDUCTION LEMMA AT ALL

`⊢eqNat` (typing) existed; nothing said what `eqNatTm` COMPUTES. Exactly
the pattern the 2026-09-09 library audit measured across `Lib/`: 57
law-parameters, every one a typing law. `eqNat-num` is the meaning law,
and `occK`'s `cVar-vz` row is its first consumer.

## ATTEMPTS AT THE TWO ROWS

| # | attempt | outcome |
|---|---|---|
| 1 | `agree-var (x y : Var Γ)` — the obvious statement | ❌ **UNPROVABLE**, and only visible on trying to write `cVar-vs`: the IH needs `x : Var Γ` where the row has `x : Var (Γ ∙)`. Quantify the LEVEL instead |
| 2 | `sel-vs` by `methsAt-past … » step (βsnd _ _) done` | ❌ `sel 1 t = fst (snd t)`, so the `βsnd` redex is UNDER a `fst`. Agda names the position: `snd (pair _ _) != fst (snd (pair …))`. Needs `ξ-fst` |
| 3 | finish `cVar-vz` with `eqNat-num` (literal numerals) | ❌ `fst p` has passed three binders and only REDUCES to a numeral. ⚠ **And it cannot be patched at the call site** — `eqNatTm a b` mentions each argument TWICE, so no congruence rewrites one. Needed `eqNat-red` over REDUCTIONS |
| 4 | cast the substituted `fst p` with a three-`subTm` chain | ❌ **the inner two are RENAMINGS**, not substitutions — the method telescope weakens with `renTm vs`. Agda: `renTm vs (renTm vs (num n)) != subTm _ρ (num n)` |
| 5 | wrote `num-ren` to fix (4) | ⚠ **it already existed**, `Lib/NatNum:43`. Reinvented rather than grepped — the standing lesson, again |
| 6 | `methsAt-past W 0 0` with implicits inferred | ❌ unsolved `_mth`: Agda unfolds `occMethsK` and matches POINTWISE instead of as `methsAt W occAt 0 occTail`. Pin `{mth = occAt} {tl = occTail}`, as the generated rows already do |
| 7 | ✅ **`agree-var`, both rows** | `cVar-vz` via `eqNat-red` + `num-stable`; `cVar-vs` needs **no cast at all** — `lvl (vs y) = lvl y` is exactly what the fold returns |

## ⚠⚠ TWO PROCESS FAILURES, both silent, both mine

**`--allow-unsolved-metas` was on for one run** (a mangled heredoc) and
reported `rc=0` on the whole module. It was hiding **12 unsolved metas** —
every row with no recursive field, where `aih-ι`'s implicit `ihs` is
mentioned nowhere. Removing the flag found them instantly; the fix is
`{ihs = unit}`. ⇒ *a flag that suppresses an error class suppresses
exactly the class you are looking for.*

**Two `str.replace` calls silently did nothing** (whitespace drift) and I
believed the "PATCHED" print. The generated output still had the old
term. ⇒ **assert on every mechanical edit** — the same lesson as
`appends-need-absolute-paths`.

## ✅ RESULT — ALL 53 ROWS

```
agree-ty  11   agree-tm  30   agree-var  2
zero-desc  2   zero-dcon  3   zero-idesc 2      = 50 clauses
cICon-*    3   UNREACHABLE (cIDesc-cons's edge is lit(1), skipped)
```

No postulates, no `TERMINATING`, no `OPTIONS` line — default flags, so
termination and metavariable checking are both ON. The six-way mutual
recursion terminates structurally.

**Controlled twice.** Swapping a cast chain's arguments gives
`Γ ∙ != Γ`; replacing `eqv-lvl x y` with `refl` gives
`eqℕ (lvl x) (lvl y) != eqv x y`. So the injectivity theorem is
load-bearing, not decoration.
