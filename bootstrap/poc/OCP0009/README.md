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

## Files

| File | Flags | Contents |
|---|---|---|
| `Conv.agda` | `--safe`, **postulate-free** | `FirstOrder`, `eq-val`/`eq-Fix`, `conv`, and worked examples whose `refl` proofs **force `conv` to run at type-check time** |
| `Transparency.agda` | postulates | the two adequacy obligations (`conv-complete`, `conv-sound`) stated as the explicit named holes |

## Check

```bash
bootstrap/check.sh poc/OCP0009/Conv.agda          # --safe, postulate-free, runs the examples
bootstrap/check.sh poc/OCP0009/Transparency.agda  # states the two holes
```

Both currently exit 0. `Conv.agda`'s example block is the POC *executing*: e.g.
`conv fo-Nat (fst ∘ ⟨ zero , one ⟩) zero ≡ true` is proved by `refl`, i.e. Agda
evaluated the conversion and got `true` — the product-β equation decided purely by
running both sides, never by orienting a rewrite.

## Status against the scorecard (OCP-0009)

`conv` must be a **sound + complete + terminating** decision procedure for the
chosen congruence `_≈_` (the RST-closure of `_⟶_`).

- **Terminating** — ✅ free: `conv` is a total Agda function (`Conv.agda` is `--safe`).
- **Sound / Complete** — ⏳ stated as `conv-sound` / `conv-complete` in
  `Transparency.agda`; the NbE-adequacy content, still to prove.

## Scope (honest)

`conv` is defined for closed morphisms `Term Unit C` with **first-order** codomain
`C` (`Void`/`Unit`/`×`/`+`/`μ` — no `⇒`). This is the type-level-conversion case
Once's checker needs most: indices like `Vec n` are first-order data. Comparing
**function-valued** morphisms (`C = A ⇒ B`) needs NbE reification against a
neutral/generic argument — the one place the closed-term evaluator genuinely
extends (OCP-0009 §5, "open terms / neutrals").

## Next

1. **POC-0 proof half.** Discharge `conv-complete` (induction on `_≈_`, one lemma
   per `_⟶_` rule — the tractable direction) then `conv-sound` (a logical relation
   between syntax and the value domain — the genuine transparency lemma). This also
   discharges OCP-0004's two open evaluator obligations for this fragment.
2. **POC-0b — neutrals.** Extend `eval`→reify to a residualizing (NbE) semantics so
   `conv` covers function-valued codomains and open terms. Removes the `FirstOrder`
   restriction.
3. **POC-1 — CwF layer (Rung 2).** Add `Π`/`Σ` + context extension as new IR
   constructors over the *same* evaluator; elaborate a named surface into the
   nameless core; decide `Vec (0+n) ≡ Vec n` by this same `conv`.

The through-line: each step extends *one* evaluator and re-confirms the three-
property scorecard — never a second checker (OCP-0009 §5, "The two pillars";
OCP-0004 TCB0 = one inspectable VM).
