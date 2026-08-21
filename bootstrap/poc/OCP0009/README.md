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
| `Higher.agda` | funext only | `Checkable`, **`conv-h`** — higher-order codomains (functions with finite args) (POC-0b(ii)) |
| `Dependent.agda` | funext only | `add`/`plus` (`cata`), **`VecConv`** — dependent-index conversion `Vec m ≡ Vec n` (POC-1) |
| `Universe.agda` | funext only | universe `U` with **`Π`/`Σ` formers** on the IR, **`TyConv`** + `Π-cong`/`Σ-cong` (POC-1b) |
| `NbE.agda` / `NbEConv.agda` | prototype | ad-hoc engine + decider ({Unit,×,+,μ}), demonstrated |
| `NbEK.agda` | **postulate-free** | **principled** NbE foundation — thinnings `_≼_`, presheaf weakening, **proven functor laws** (`wkVal-id`/`wkVal-comp`), reflect/reify |
| `Transparency.agda` | (re-export) | status board |

## Check

```bash
for m in Conv Complete Sound Finite Decidable Higher Dependent Universe Open NbE NbEConv NbEK Transparency; do bootstrap/check.sh poc/OCP0009/$m.agda; done
```

All thirteen exit 0. `Conv.agda`'s example block is the POC *executing*: e.g.
`conv fo-Nat (fst ∘ ⟨ zero , one ⟩) zero ≡ true` is proved by `refl`, i.e. Agda
evaluated the conversion and got `true` — the product-β equation decided purely by
running both sides, never by orienting a rewrite.

## Scripts

| script | what it does |
| --- | --- |
| `sweep.sh` | builds everything that is *supposed* to be green, sequentially. Reads RED/RTS classification from module headers. **Refuses to start if another agda is live** — two agda processes OOM-kill each other on this box. Read the `== ALL GREEN (N modules)` line; a refusal exits 2, which is not the same as a pass. |
| `check-formers.sh` | Agda's coverage checker checks *functions*, not *datatypes*, so a missing term former is invisible. This catches it. |
| `clean-agdai.sh` | clears Agda interfaces before a cold timing run. Interfaces live in `bootstrap/_build/<version>/agda/poc/OCP0009/`, **not** in `poc/OCP0009/.agdai/` (which is empty). Use `--deps M` to clear `M` *and its importers*; `-n` to dry-run. **Exits 2 if it clears nothing** — a silent no-op cache-clear once produced a retracted measurement, because deleting nothing looks exactly like deleting everything. |


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

## POC-1b — extend Code with a Π/Σ universe; prove type conversion (`Universe.agda`)

"Extend Code with CwF constructors and prove conversion", done as a **conservative
extension of the one IR** (not a parallel model). The CwF's *type* layer is a
Tarski-style universe `U = μ UF` built from the **existing** `Func` grammar, so
type-codes are ordinary IR data:

- **`Π`/`Σ` are IR constructors** — `piC`, `sigmaC : Term (U * U) U`, with sugar
  `Π[ A , B ]`, `Σ[ A , B ]`.
- **Type conversion is the proven `conv`** — `TyConv = conv fo-U`, inheriting
  soundness + completeness (`TyConv-decides`) with no new engine and no new axiom.
- **CwF congruence laws proven** — `Π-cong` / `Σ-cong` (formers respect conversion)
  from the already-proven `_≋_` congruences (`≋-∘`, `≋-⟨,⟩`).

Executing checks: `Π (Nat,Nat) ≡ Π (Nat,Nat)` ✓, `Π (Nat,Nat) ≢ Σ (Nat,Nat)`,
`Π (Nat,Nat) ≢ Π (Unit,Nat)`, plus a proof object `Π-nat-nat-refl`. Scope: **closed**
type-codes; a dependent *context* (a later code mentioning an earlier variable) is an
open `U`-valued morphism of `μ`-domain — the neutrals frontier. Type formation +
type conversion are here and proven; dependency-through-contexts awaits NbE.

## The neutrals frontier, correctly framed (`Open.agda`, proven)

Before building NbE, one fact must be pinned — it corrects a tempting overclaim and
fixes the engine's target:

> On **open** terms, observational equality `_≋_` (`∀ x. eval t x ≡ eval u x`)
> **strictly exceeds** definitional equality. `_≋_` on the infinite `Nat` domain is
> the whole first-order theory of the model — it contains every inductive theorem
> (`n+0=n`, commutativity, …) and is therefore **undecidable**. A checker's
> conversion is the **definitional fragment** (what reduces); NbE decides *that*, a
> proper subset. The residual is **propositional** — proven with induction / `J`,
> deliberately not by conversion.

Proven split on the smallest witness:

- `0+n≋n : plus0 ≋ id` — **definitional**, proved by `λ n → refl`. An *open*
  (`Nat`-domain) conversion that evaluation already decides (`add 0` reduces to the
  identity, so `0+n` computes to `n` under a variable `n`).
- `+F-runit : ∀ n → n +F zeroF ≡ n` — **propositional**, proved by *induction*; not
  `refl`, so no conversion checker / NbE decides it. (`+F-lunit : 0+m=m` is `refl` —
  definitional — showing the reduce-vs-induct asymmetry is `+`'s recursion argument.)

So evaluation genuinely reaches *some* open conversions, and the decidable target is
exactly the reduce-vs-induct line. The NbE **engine** (reify open terms to normal
form so the definitional subset becomes a `Bool`/`Dec` decision, not a hand-written
`refl`) is the remaining engineering — now with its correct target fixed.

## The NbE engine — sound core (`NbE.agda`, `--safe`, postulate-free)

The residualizing reify/reflect that turns the definitional subset into an
object-level normal form for **open** terms:

```
nf : Term A B → Term A B          -- normalize via a semantics with NEUTRALS
```

`reflect`/`reifyVal`/`eval-nbe`/`nf` are deterministic total functions (same pillar —
no confluence). `nf` **decides open-term definitional conversion** for the
`{Unit, ×, +}` fragment: on source `Bool₂ × Bool₂` (whose `+`-typed components keep
the source variable a genuine neutral), these are decided by `nf t ≡ nf u` (`refl`):

```
⟨ fst , snd ⟩ ≋ id                 (product η, neutrals survive)
fst ∘ ⟨ snd , fst ⟩ ≋ snd          (product β)
[ inr , inl ] ∘ inl ≋ inr          (coproduct β)
```

These are open conversions the earlier closed/finite `conv` could not state.

**Now with `μ` (inductive types).** Real `vIn` values + **cata-β** (recursion runs) +
**out-η** (`Out ∘ In = id`) + **cata/Out on a μ-neutral stays stuck** (the
inductive-only discipline, OCP-0009 §2). The subtle soundness case — `cata` meeting a
functor-position neutral — is residualized via the syntactic `fmap` (`mapCata`), so
nothing is dropped. Executing (`refl`):

```
double ∘ zero ≋ zero            (cata-β: recursion normalizes; double 0 = 0)
double ∘ one  ≋ two             (double 1 = 2)
Out ∘ In ≋ id                   (out-η, open μ term)
double ∘ id ≋ double            (cata on a μ-variable stays stuck)
```

**Scope (honest, sound within it).** Still open: **in-η** (`In ∘ Out = id`) is *not*
captured — matching `Out` under a value at a `⟦F⟧F(μF)` index needs `⟦_⟧F` to be
injective, which Agda's unifier can't invert; sound, one η-law fewer. **`⇒`**
(functions) stays **opaque** (`nOpaque` — needs a Kripke reify). Full adequacy (`nf`
sound + complete + stable) is the logical-relation obligation — **stated and
demonstrated, not postulated**. `NbE.agda` now carries a `TERMINATING` pragma (the
`eval-nbe`/`vcata`/`mapCata` knot terminates by the standard NbE argument, not
Agda-structurally), so it is no longer `--safe`.

## The engine as a decision procedure (`NbEConv.agda`)

`nf` produces normal forms; `NbEConv` compares them into an actual Bool decision —
what a type-checker calls:

```
conv-nbe : Term A B → Term A B → Bool     -- = eqTree (erase (nf t)) (erase (nf u))
```

An **open-term conversion decider** for `{Unit, ×, +, μ}`: it accepts definitional
equals *and* **rejects** non-equals (impossible to show with `refl`). Executing:

```
conv-nbe (double ∘ zero) zero ≡ true      conv-nbe (double ∘ zero) two ≡ false
conv-nbe (double ∘ one)  two  ≡ true      conv-nbe one zero            ≡ false
conv-nbe ⟨fst,snd⟩ id ≡ true              conv-nbe (fst ∘ ⟨snd,fst⟩) fst ≡ false
```

Comparison is on an untyped erasure (structure only) — faithful for same-typed normal
forms; a fully type-faithful `Dec (t ≡ u)` via `_≟Ty_`/`_≟Func_` is the refinement.

## Next

1. **`⇒` in the engine** (Kripke reify — the remaining fragment) + **in-η**.
2. **Full adequacy** — the logical relation (`nf` sound + complete + stable), which
   turns the demonstrated soundness into a theorem.
3. **CwF contexts (Rung 2 proper).** Context extension + reindexing so type-codes may
   mention earlier variables — dependent contexts, riding on the engine above.

The through-line: each step extends *one* evaluator and re-confirms the three-
property scorecard — never a second checker (OCP-0009 §5, "The two pillars";
OCP-0004 TCB0 = one inspectable VM).
