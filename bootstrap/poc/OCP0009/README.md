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
| `Transparency.agda` | (re-export) | status board |

## Check

```bash
for m in Conv Complete Sound Finite Decidable Transparency; do bootstrap/check.sh poc/OCP0009/$m.agda; done
```

All six exit 0. `Conv.agda`'s example block is the POC *executing*: e.g.
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

## Scope (honest)

`conv` is defined for closed morphisms `Term Unit C` with **first-order** codomain
`C` (`Void`/`Unit`/`×`/`+`/`μ` — no `⇒`). This is the type-level-conversion case
Once's checker needs most: indices like `Vec n` are first-order data. Comparing
**function-valued** morphisms (`C = A ⇒ B`) needs NbE reification against a
neutral/generic argument — the one place the closed-term evaluator genuinely
extends (OCP-0009 §5, "open terms / neutrals").

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

## Next

1. **POC-0b(ii) — neutrals / NbE.** For `μ`/`⇒` domains (infinite / higher-order),
   evaluate at a single **generic (neutral)** input and compare symbolically —
   residualizing NbE (reify/reflect). Standard for the simply-typed core (terminates
   by construction); the known-hard sub-case is sums, and recursion must stay
   inductive-only (OCP-0009 §2). Same pillar: `reify`/`reflect`/`nf` are deterministic
   total functions, no confluence.
2. **POC-1 — CwF layer (Rung 2).** Add `Π`/`Σ` + context extension as new IR
   constructors over the *same* evaluator; elaborate a named surface into the
   nameless core; decide `Vec (0+n) ≡ Vec n` by this same `conv`.

The through-line: each step extends *one* evaluator and re-confirms the three-
property scorecard — never a second checker (OCP-0009 §5, "The two pillars";
OCP-0004 TCB0 = one inspectable VM).
