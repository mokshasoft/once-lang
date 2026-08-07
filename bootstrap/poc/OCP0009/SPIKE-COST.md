# SPIKE-COST — why `⊢lexrec` is expensive, measured

**Date:** 2026-08-07. **Branch:** `ocp-0009-poc0-nbe`.
**Question:** the carrier-generic `⊢lexrec` blew the 5.5 GB cap. Is that
"lexicographic descent is intrinsically hard", or an encoding problem?

**Answer: neither the descent nor the derivation. It is CONTEXT DEPTH.**
Cost grows ~1.7× per context slot, *including slots nothing references*.

All numbers from `bootstrap/check.sh` (default `+RTS -A64m`), wall clock and
peak RSS, on the 7.5 GiB box, with all dependencies already built.

---

## 1. The three-way Ackermann comparison

Ackermann is the example `⊢lexrec` was built to unlock, so it is the fair
yardstick. Modules: `SpikeAckAgda1`, `SpikeAckAgda2`, `SpikeAckT`.

| # | Ackermann, how | time | RSS |
|---|---|---|---|
| A1 | **pure Agda**, its own termination checker does the lex descent | 0.24 s | 0.07 GB |
| A2 | **pure Agda**, lexicographic `Acc` on ℕ × ℕ proved BY HAND | 0.33 s | 0.11 GB |
| B | **object language**, nested `natrec` (System T), derived + kernel-checked | 0.61 s | 0.14 GB |
| C | **object language via `⊢lexrec`**, generic carrier | ≈120 s / 3.4 GB — *for one branch of four* |

Read off:

* **Proving lexicographic well-foundedness by hand costs +40%** (A2 vs A1).
  It is not hard. Agda's termination checker already does exactly this
  descent, which is the power `⊢lexrec` exists to give the object language.
* **Deriving a whole function in the object language costs ~2.5×** pure
  Agda (B vs A1). The kernel's `_⊢_∷_` is not the problem either.
* **`⊢lexrec` costs ~200× the time and ~25× the memory of B** — and that
  is *one of four branches*, in five modules.

⚠ B is NOT a replacement for `⊢lexrec`. Ackermann happens to be
structurally recursive at higher type (the outer `natrec` returns
`Nat → Nat`), so it never needed a measure. `⊢lexrec` earns its keep on
the recursions that are not — `div`, `gcd`, quicksort on a pair measure.
`SpikeAckT` is kept only as the cost baseline.

## 2. What the cost actually is: a 2×2×2 ablation

One derivation — `⊢lexZZrec1`, branch (0,0)'s first recursor argument —
held **textually identical** across every variant. Only `Γ₅`'s shape moves.
Modules `SpikeCostS1`…`SpikeCostS6`.

| variant | carrier | Γ₅ slots | step slot | time | RSS |
|---|---|---|---|---|---|
| S4 | `Nat` | 4 | `Nat` (LStepT ablated) | 8.4 s | 0.90 GB |
| S3 | `Nat` | 4 | `LStepT` | 8.5 s | 0.86 GB |
| S5 | `El ⌜Nat⌝` (CLOSED code) | 4 | `LStepT` | 12.1 s | 1.44 GB |
| S6 | `El ⌜Nat⌝` (CLOSED code) | **5** (one UNREFERENCED `U` slot) | `LStepT` | 21.6 s | 2.49 GB |
| S1 | `El (var (vs⁸ vz))` (VARIABLE) | 5 | `LStepT` | 42.5 s | 3.91 GB |
| S2 | `El (var (vs⁸ vz))` (VARIABLE) | 5 | `Nat` (LStepT ablated) | 42.4 s | 4.13 GB |

Three independent, roughly multiplicative factors (RSS):

| factor | cost |
|---|---|
| `Nat` → `El c`, i.e. a two-node binder type instead of one | ×1.67 |
| **one more context slot, referenced by nothing** | **×1.73** |
| the code goes from CLOSED to a VARIABLE (`renTy`/`subTy` stop collapsing) | ×1.57 |
| total | ×4.5 |

### 2a. `LStepT` — the biggest type in the context — costs NOTHING

S1 vs S2 and S3 vs S4: replacing the `stp : LStepT` slot (which contains
all of `REC1T` and `REC2T`) with plain `Nat` changes the cost by under 6%,
in the *wrong direction* both times, i.e. noise.

So the intuition "a `there` chain crossing `stp` embeds a copy of `LStepT`
in every stored implicit, and that is the blow-up" is **wrong**. Hoisting
the `there⁹ here` lookups into `Def`s to stop that duplication was also
tried: it buys 4.14 → 3.60 GB, 13%. Worth keeping, not the mechanism.

### 2b. Depth alone, with nothing referenced, is the mechanism

S6 differs from S5 by ONE extra `U` slot at the BOTTOM of `Γ₅`. Because it
is at the bottom, **no `there` chain in the derivation gets longer** — the
derivation text is byte-identical. Cost still goes 1.44 → 2.49 GB.

Pushed further (same derivation, extra unreferenced `U` slots at the
bottom), against the 5.5 GB cap:

| extra slots | Γ₅ slots | result |
|---|---|---|
| 0 | 5 | 21.6 s / 2.49 GB |
| 2 | 7 | **OOM** (killed at 121 s) |
| 4 | 9 | **OOM** (killed at 89 s) |
| 6 | 11 | **OOM** (killed at 704 s) |

Extrapolating ×1.73/slot from S6 predicts 7.4 GB at 7 slots — consistent.
A cubic-in-depth law fits about as well over this range; the sweep OOMs
before it can separate them. Either way the practical law is

> **~1.7× per context slot, for every derivation in that context.**

This is not a `⊢lexrec` property. It applies to any derivation in a deep
open context, and it is why the branch contexts — `Γ₅`'s 5 slots plus the
4–9 binders a branch introduces, so depth 9–14 — are so expensive.

## 3. Consequences for `⊢lexrec`

* Each `⊢lam` layer in a branch costs ~2.5–3 GB, so a recursor argument
  needs **one `⊢lam` per module**. `+RTS -c` does not save it. Branch
  (0,0) is five modules where the ℕ carrier needed one (39 s / 2.1 GB).
* The peel recipe, per layer: name the sub-term, read its expected type off
  Agda with the probe technique (put a deliberately wrong `⊢nzero` in the
  derivation slot; the `UnequalTerms` error prints the expected type in
  full), name that type too. `REC1T`/`REC2T` are split as `Π _ REC_Tbody`
  so the probed types come out as
  `subTy (extSⁱ σ) (subTy (extSʲ σ') (renTy (extRᵏ vs)ⁿ REC_Tbodyᵐ))`.

## 4. Candidate fixes, untested

Ranked by expected payoff. **None of these has been measured** — that is
the next spike, and given §2b the one to try first is the one that removes
context slots.

1. **Take `stp` out of the context.** It is only ever applied, never bound
   over. If the branch lemmas take `Γ ⊢ stp ∷ LStepT` as an Agda-level
   argument instead of reading a context variable, `Γ₅` loses a slot →
   ~1.7×. `cP`/`μ₁`/`μ₂` cannot follow: they occur inside TYPES, so as
   Agda-level `RTm`s they would need `renTm vs` weakening under every
   binder, and those do not collapse definitionally — that is the
   transport trap, and it is exactly why they are context variables.
2. **Bundle `μ₁`/`μ₂` into one `Π (El A) (Σ' Nat Nat)` slot.** Another
   slot gone, at the price of `fst`/`snd` noise at each use.
3. **State the peeled types in REDUCED form** rather than as
   `subTy`/`renTy` chains. Every `renTy`/`subTy` in a stored type is a
   `Def` application carrying two `Cx` arguments, and `Cx` is UNARY — so
   each one carries a numeral of size = context depth. This is the most
   plausible concrete mechanism behind §2b and the cheapest to test.
4. Non-unary `Cx`/`Var`. Deep kernel change; would invalidate a lot.
   Note [[lkp-computed-lookup-is-slower]]: moving type information out of
   the indices into a lookup FUNCTION was tried on 2026-08-06 and is
   slower. This is a different change, but adjacent — be suspicious.
