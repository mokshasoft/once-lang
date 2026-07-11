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
| `Complete.agda` | funext only | `eval-sound` (eval respects every `⟶` rule) → **`conv-complete` proven** |
| `Sound.agda` | funext + `reify-eval` | `eq-val-sound`, reify `↑`, its section `eval-reify`, `_≈_` equivalence → **`conv-sound` derived** from the single canonicity hole |
| `Transparency.agda` | (re-export) | status board; `decides-≈` = complete + sound together |

## Check

```bash
for m in Conv Complete Sound Transparency; do bootstrap/check.sh poc/OCP0009/$m.agda; done
```

All four exit 0. `Conv.agda`'s example block is the POC *executing*: e.g.
`conv fo-Nat (fst ∘ ⟨ zero , one ⟩) zero ≡ true` is proved by `refl`, i.e. Agda
evaluated the conversion and got `true` — the product-β equation decided purely by
running both sides, never by orienting a rewrite.

## Status against the scorecard (OCP-0009)

`conv` must be a **sound + complete + terminating** decision procedure for the
chosen congruence `_≈_` (the RST-closure of `_⟶_`).

- **Terminating** — ✅ free: `conv` is a total Agda function (`Conv.agda` is `--safe`).
- **Complete** — ✅ **discharged**: `conv-complete` (`Complete.agda`), from
  `eval-sound : t ⟶ u → ∀ x. eval t x ≡ eval u x` (eval validates every reduction
  rule as a model equation), lifted to `_≈_`.
- **Sound** — ◑ **reduced to one lemma**: `conv-sound` (`Sound.agda`) is *derived*
  from canonicity `reify-eval : t ≈ ↑ (eval t tt)`. Everything else — `eq-val-sound`
  (structural equality reflects `≡`), reify `↑`, its section `eval-reify`, `_≈_` as
  an equivalence — is proven.

### Remaining postulates (whole POC)

Exactly two, both named and standard:

- **`funext`** (`Complete.agda`) — function extensionality; used only for congruence
  under `curry`. Consistent; far milder than the *false* confluence/SN postulates the
  rewriting track needs.
- **`reify-eval`** (`Sound.agda`) — canonicity: every closed first-order morphism is
  convertible to the canonical morphism of its value. This is the genuine
  NbE-adequacy / transparency content of the evaluator route, identical to the repo's
  open `EvalFullCorrectness` (`normalizer-vs-compiler-path.md`). Proof = a Tait-style
  logical relation over all types.

## Scope (honest)

`conv` is defined for closed morphisms `Term Unit C` with **first-order** codomain
`C` (`Void`/`Unit`/`×`/`+`/`μ` — no `⇒`). This is the type-level-conversion case
Once's checker needs most: indices like `Vec n` are first-order data. Comparing
**function-valued** morphisms (`C = A ⇒ B`) needs NbE reification against a
neutral/generic argument — the one place the closed-term evaluator genuinely
extends (OCP-0009 §5, "open terms / neutrals").

## Next

1. **Close `reify-eval` (canonicity).** The one remaining hole. A Tait-style logical
   relation over all types relating a closed morphism to its value; the μ-case uses
   the initial-algebra induction principle. This also discharges OCP-0004's open
   `EvalFullCorrectness` transparency obligation for this fragment. *(Paper-length;
   its own work item.)*
2. **POC-0b — neutrals.** Extend `eval`→reify to a residualizing (NbE) semantics so
   `conv` covers function-valued codomains and open terms. Removes the `FirstOrder`
   restriction.
3. **POC-1 — CwF layer (Rung 2).** Add `Π`/`Σ` + context extension as new IR
   constructors over the *same* evaluator; elaborate a named surface into the
   nameless core; decide `Vec (0+n) ≡ Vec n` by this same `conv`.

The through-line: each step extends *one* evaluator and re-confirms the three-
property scorecard — never a second checker (OCP-0009 §5, "The two pillars";
OCP-0004 TCB0 = one inspectable VM).
