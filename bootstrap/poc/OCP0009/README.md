# OCP-0009 · POC-0 — Decidable conversion by the evaluator

**Goal.** Cash the load-bearing claim of OCP-0009 §6 ("The load-bearing POC"):
decide conversion of the reified IR by **evaluating both sides to a canonical
value and comparing** —

```
conv(a, b)  =  eq-val (eval a) (eval b)
```

— which is OCP-0009's *evaluator route* (Motivation → "The property, stated at the
right altitude"). **Determinism of `eval` replaces confluence:** a function has one
output, so the canonical value is unique for free. No rewriting, no confluence, no
strong-normalization-of-a-rewrite-system is used. The classical `SN + confluence`
chain — provably unavailable for full βη CCC (`NonConfluenceWitness`) — is bypassed
in a principled way.

**Compiler untouched; IR only.** Everything here consumes the existing reified IR
and its evaluator *unchanged*:

- `Term A B` — the reified BCCR IR (`normalizer.Syntax.CCC`)
- `eval : Term A B → ⟦ A ⟧T → ⟦ B ⟧T` — the total, deterministic big-step
  evaluator (`normalizer.Testing.Evaluator`)

POC-0 adds only a generic structural equality on canonical values
(`eq-val`/`eq-Fix`) and a `FirstOrder` guard. It is a separate IR→IR consumer, per
OCP-0009 §6 ("operates on the reified IR … not by touching the compiler
front-end").

## What conversion means here

The definitional equality `conv` decides is **observational (model) equality**:

```
t ≋ u   :=   ∀ x. eval t x ≡ eval u x
```

This is the *correct*, maximal, sound conversion: it validates all βη laws **and**
terminal-η (a CCC's terminal object is unique), by construction. It is strictly
**coarser** than the reduction convertibility `_≈_` (RST-closure of `_⟶_`), whose
rule set has no terminal-η — e.g. `id{Unit} ≋ terminal` but **not** `id{Unit} ≈
terminal`. So `conv`, which compares denotations, decides `_≋_`, not `_≈_`. (An
earlier draft mistakenly targeted `_≈_` and postulated a *false* canonicity lemma;
retargeting to `_≋_` both fixes that and closes the proof.)

## Files

| File | Flags | Contents |
|---|---|---|
| `Conv.agda` | `--safe`, **postulate-free** | `FirstOrder`, `eq-val`/`eq-Fix`, `conv`, and worked examples whose `refl` proofs **force `conv` to run at type-check time** |
| `Complete.agda` | funext only | `eval-sound : t ⟶ u → ∀ x. eval t x ≡ eval u x` (eval respects every rule) + `eq-val-refl`; `≈→conv` |
| `Sound.agda` | **postulate-free** | `_≋_` (+ equivalence/congruence), `eq-val-sound`, and the finalized **`conv-sound` / `conv-complete` / `conv-decides`** |
| `Finite.agda` | **postulate-free** | `FiniteFO`, `AllEq`, and **`conv-fin` / `conv-fin-decides`** — conversion on any finite first-order domain (POC-0b(i)) |
| `Decidable.agda` | **postulate-free** | **`≋-dec : … → Dec (t ≋ u)`** — the proof-carrying decidable-conversion capstone |
| `Transparency.agda` | (re-export) | status board |

## Check

```bash
for m in Conv Complete Sound Finite Decidable Higher Dependent Transparency; do bootstrap/check.sh poc/OCP0009/$m.agda; done
```

All eight exit 0. `Conv.agda`'s example block is the POC *executing*: e.g.
`conv fo-Nat (fst ∘ ⟨ zero , one ⟩) zero ≡ true` is proved by `refl`, i.e. Agda
evaluated the conversion and got `true` — the product-β equation decided purely by
running both sides, never by orienting a rewrite.

## Status against the scorecard (OCP-0009) — FINALIZED

`conv` is a **sound + complete + terminating** decision procedure for conversion
`_≋_`, on closed morphisms `Term Unit C` with first-order codomain `C`:

- **Terminating** — ✅ `conv` is a total Agda function (`Conv.agda`, `--safe`).
- **Sound** — ✅ `conv-sound : conv fo t u ≡ true → t ≋ u` (`Sound.agda`).
- **Complete** — ✅ `conv-complete : t ≋ u → conv fo t u ≡ true` (`Sound.agda`).
- ⇒ **`conv-decides`** — ✅ `conv` decides `_≋_`.

Both directions are proven with **zero postulates**. The reduction theory is related
by `≈⊆≋` (= eval-soundness), so `conv` also accepts everything `_⟶_`/`_≈_` equate
(`≈→conv`).

### Axiom inventory (whole POC)

Exactly **one**: `funext` (`Complete.agda`), used only for congruence under `curry`
in eval-soundness (the `≈⊆≋` bridge). Consistent, standard; far milder than the
*false* confluence/SN postulates the rewriting track rests on. The core decision
result `conv-decides` is **funext-free**.

### Scope (honest)

Closed morphisms (`Unit` domain — one point, so `∀ x` collapses to a single
evaluation) with first-order codomain (so value-equality is decidable without
reification). Lifting either restriction is POC-0b.

## POC-0b(i) — finite domains, by enumeration (`Finite.agda`, proven)

Lifts the domain from `Unit` to **any finite first-order type** (`FiniteFO`:
Void/Unit/×/+ — no `μ`, no `⇒`), still **sound + complete, zero postulates**:

```
conv-fin : FiniteFO A → FirstOrder C → Term A C → Term A C → Bool
conv-fin-decides : conv-fin decides _≋_ on such morphisms.
```

`conv-fin` enumerates all inhabitants of the domain and checks the equation at each.
Worked example (executes at type-check via `refl`): on `Bool₂ = Unit + Unit`,
`conv-fin … (notB ∘ notB) id ≡ true` — involutivity decided across *both* points, a
conversion POC-0's `Unit`-only `conv` could not even state.

**This maps the boundary of pure evaluation precisely:**

> Evaluation-at-points decides conversion **iff the domain is finite**. `FiniteFO`
> excludes exactly `μ` (infinite — `Nat`) and `⇒` (function) — the two cases whose
> input set is not enumerable, and therefore *precisely* where residualizing NbE /
> neutrals become necessary.

### Capstone — conversion is *Decidable* (`Decidable.agda`, proven)

```
≋-dec : FiniteFO A → FirstOrder C → (t u : Term A C) → Dec (t ≋ u)
```

The proof-carrying form: `yes p` returns a proof `p : t ≋ u`, `no ¬p` a refutation —
literally "decidable conversion" for the fragment (the OCP title, made concrete).
Zero new postulates. The closed case (POC-0) is the instance `≋-dec₀ = ≋-dec
ffo-unit`.

## POC-0b(ii) — higher-order codomains (`Higher.agda`, proven)

Lifts the *codomain* restriction: a function-valued morphism `Term A (X ⇒ Y)` is
comparable when the argument `X` is finite — check the two functions agree at every
input (`Checkable`, `conv-h`, sound+complete via **funext**). Example: two
function-valued terms `idFun ≋ negneg` (both the identity on `Bool₂`) decided by
enumerating the argument; `idFun ≢ negFun` rejected. Completes the "how far pure
evaluation reaches" story: every *hereditarily finite* type is decidable; `μ` in an
argument/domain position (an infinite input set) is the true neutrals/NbE frontier.

## POC-1 — dependent-index conversion (`Dependent.agda`, proven)

Cashes the motivating example. Addition `+` is a **real `cata`** over `Nat` in the
point-free IR (`add : Term Nat (Nat ⇒ Nat)`), and type equality `Vec m ≡ Vec n`
reduces to **the same `conv`** on the index terms — no new decision engine, exactly
OCP-0009 Rung 2's claim. Executing checks:

```
VecConv (0 + 3) 3 ≡ true    -- Vec (0+3) ≡ Vec 3   (left unit, definitional)
VecConv (3 + 0) 3 ≡ true    -- Vec (3+0) ≡ Vec 3   (right unit, cata runs)
VecConv (1 + 2) 3 ≡ true
VecConv (1 + 1) 3 ≡ false   -- correctly rejected
```

and actual conversion *proofs* `Vec-0+3≡Vec-3 : (0 + 3) ≋ 3` (the object a checker
transports along), via `conv-sound`. Scope: **closed** indices. The general
`∀ n. Vec (0+n) ≡ Vec n` (n a free variable) is open conversion on a `Nat` domain —
the `μ`-domain neutrals frontier — but the *mechanism* is identical: the checker
calls the same `conv` on indices.

## Next

1. **Neutrals / NbE (the `μ`-domain frontier).** For infinite input positions
   (domain `Nat`, argument `Nat ⇒ B`) evaluate at a single **generic (neutral)**
   input and compare symbolically — residualizing NbE. This is what makes the *open*
   `∀ n. Vec (0+n) ≡ Vec n` decidable. Standard for the simply-typed core (terminates
   by construction); known-hard sub-case is sums; recursion stays inductive-only
   (OCP-0009 §2). Same pillar: `reify`/`reflect`/`nf` deterministic, no confluence.
2. **CwF layer proper (Rung 2).** Add `Π`/`Σ` + context extension as IR constructors
   over the *same* evaluator; elaborate a named surface into the nameless core.

The through-line: each step extends *one* evaluator and re-confirms the three-
property scorecard — never a second checker (OCP-0009 §5, "The two pillars";
OCP-0004 TCB0 = one inspectable VM).
