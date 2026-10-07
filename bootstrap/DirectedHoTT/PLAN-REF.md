# PLAN-REF — references are PROJECTIONS from the signature (kernel)

> Opened 2026-10-07. Stage E4 of PLAN-EVAL (R3), and the open half of
> ROADMAP Q5. Decision D082 (to record in `docs/compiler/decision-log.md`).
> Supersedes PLAN-BIDI §2-ter's "`ref` carrying its body (B1′)".

## 0. The decision, and why

**The kernel's `ref d` carries no body. Its meaning is a projection from the
signature, which is the definition context; δ unfolds that projection.**

The POC exists to find the right shape for Once's dependent kernel, its
libraries and their USE SITES. The two criteria are compile performance at a
use site and the clarity of use-site code and proofs. Both pick projections:

- **Performance.** A body-carrying `ref d b` makes every algorithm on raw
  syntax pay for the transitive closure of the bodies a term mentions, not
  for the term. Measured 2026-10-06:
  - `CheckA.decTo`'s syntactic check walked the Knot signature: ~40% of
    `Examples/PwCore` (worked around by `Algorithm/EraName`, deleted here);
  - NbE re-evaluates a body at every unfolding (`eval`/`force`/`refV`,
    ~38% after the other fixes). A value table cannot be used soundly while
    the term carries its own body (§2.6);
  - Agda itself compares two spellings of one erased body by descending
    into it: `Knot/PwCore` needed `ref d (Sig.body S d)` written exactly as
    the typing carries it, and inferred types, or >300 s / out of memory.
  With `ref d` a reference is O(1) syntax everywhere; a body is touched
  only when δ fires.
- **Clarity.** `⊢ref` loses its premise. The Knot's `kref` loses its quoted
  body (and the `cls` field kind that exists only to copy it). `EraName`,
  `fill` and the "write the body exactly so" rules disappear.
- **The mathematics.** Extension by definitions in a CwF: the signature is a
  context (D081 already made `WfSig` context formation), a reference is a
  projection, δ is the definitional isomorphism. It is the compiler's D071
  (`⟦ref x⟧Γ = Γ(x)`), so R6 has one shape to converge on.

Rejected (2026-10-07): projections only in the checker/evaluator, the kernel
keeping `ref d b` (a "by names" twin plus a bridge for every raw algorithm:
a hidden invariant at every use site); an invariant "every `ref d b` has
`b ≡ δ d`" threaded through NbE soundness (the same, inside the proofs).

**Method: the SPEC is the invariant.** `Spec/` changes first, exactly as
below; Agda then flags every module that is not in line, layer by layer.
No spikes, no compatibility layer, no old/new coexistence.

## 1. The new Spec

### 1.1 Syntax (`Spec/Syntax`)

- `ref : ∀ {Γ} → ℕ → RTm Γ`. Renaming and substitution: `ref d ↦ ref d`.
- **The kernel signature** (raw, a telescope; defined here because typing
  and reduction both need it):

  ```agda
  record KEntry : Set where       -- a declared closed type, a closed body
    field kType : RTy ε ; kBody : RTm ε
  data KTele : Set where ∅ : KTele ; _▸_ : KTele → KEntry → KTele
  record KSig : Set where field len : ℕ ; tele : KTele
  -- size, type d, body d by lookup (as Spec/Signature does today)
  ```

### 1.2 Reduction and conversion (`Spec/Typing`, parameter `Σ : KSig`)

- `δref : d <ˢ size Σ → ref {Δ} d ⟶ εwkTm (body Σ d)`.
  - The side condition is what makes reduction MONOTONE under signature
    extension (§1.4): a name beyond the signature is stuck, so every step
    under `Σ` is a step under any `Σ' ⊇ Σ`.
- Everything else is unchanged. δ still has no congruence and overlaps
  nothing.

### 1.3 Typing (`Spec/Typing`, parameters `Σ : KSig` and `n : ℕ`)

- `⊢ref : d <ˢ n → Γ ⊢ ref d ∷ εwkTy (type Σ d)`. No premise.
- `n` is the number of names a derivation may USE; reduction is always at
  `Σ`. An entry `d` is typed at `n = d` (its prefix), with the SAME
  reduction relation as every other entry. This is what lets entry
  reducibility be proved by induction on `n` with ONE logical relation
  (§2.2), with no transport between relations.
- `WfSig Σ`: for every `d <ˢ size Σ`, `◇ ⊢[Σ , d] body Σ d ∷ type Σ d`
  (and the type well-formed at `d`). Context formation, as D081.

### 1.4 Extension

`Σ ≤ Σ'` (a prefix of the telescope). Lemmas, each one induction:
`⟶`, `≅`/`≅ᵀ`, `⊢`/`⊢ty` transport along `≤` (same `n`), and `⊢[n]` to
`⊢[n']` for `n ≤ n'`. A Knot segment (`SigExtend`, D081) moves its
predecessor's results across one `≤` at the boundary; nothing else ever
transports.

Not transported: SN, the logical relation, canonicity, consistency. Adding
δ-rules can change what reduces, so these are theorems ABOUT a given
well-formed `Σ`, used at the signature where they are needed.

## 2. The metatheory pass

### 2.1 Local cases (`Metatheory/*`, parameter `Σ`)

- Renaming/substitution lemmas: `ref` is a constant.
- Confluence: δ is a root rule on a stuck atom; side condition irrelevant.
- SR (`δref` case): the body's derivation from `WfSig Σ` (at `n = d`),
  weakened by `εwk`, moved to the ambient `n` by `≤`. SR therefore takes
  `WfSig Σ` (or the `SigOK`-shaped consequence) as an argument.
- Validity, injectivity, `NormTy`, `RedCong`: follow the errors.

### 2.2 The logical relation

- The relation depends on reduction, so on `Σ` alone.
- `fund` at `n` takes an ORACLE `∀ d → d <ˢ n → ⊩ (body d) at (type d)`;
  its `⊢ref` case reads it and closes under the δ expansion.
- **Entry reducibility** `entries : WfSig Σ → ∀ n ≤ size → oracle at n`, by
  induction on `n`: entry `n` is `fund` at `n` on its own derivation, with
  the oracle for `< n` from the IH. No transport, no induction on names
  inside `fund`.
- Canonicity, consistency, SN: for every `WfSig Σ`, through `entries`.

### 2.3 Conservativity (`Metatheory/Signature`)

δ-elimination stays the MEANING of extension by definitions: unfolding every
reference maps a `Σ`-derivation to a signature-free one. It becomes a
substitution of the bodies for the names, by induction on the telescope.

## 3. Above the metatheory

- **Annotated layer.** `⌈ ref d ⌉ = ref d`. `Era` loses its body parameter.
  `Spec/Signature` (the checker's view: annotated types, erased bodies)
  becomes a view of `KSig`. `Metatheory/Erasure`'s `⊢ᴬref` case is `⊢ref`.
- **Algorithm.**
  - `DecEq`: `encTm (ref d) = node … (nat d)`.
  - `NbE`: `vref d`, forced through a VALUE TABLE: a data structure of the
    entries' values, built once and passed down (SigBuild → CheckA → NbE).
    Measured 2026-10-06 (`tmp/Share*`): Agda shares an argument thunk
    (200 uses cost one evaluation) and recomputes a function application
    (200×). Soundness: the table's entry `d` is `eval (body Σ d)`.
  - `EraName` is deleted; `decTo` compares erasures directly.
  - `CheckA`, `ConvNbE`, `Elab`, `SigBuild`: follow the errors.
- **Lib.** Generic libraries are parameterized by `Σ` (a library is checked
  once against ANY signature: conservativity, read as module structure).
- **Examples.** Each module instantiates at its segment's concrete `Σ`, so
  δ computes definitionally at use sites.
- **The Knot.** `kref ⌜d⌝`: no quoted body, the `cls` field kind deleted.
  The Knot's judgement families take the QUOTED signature as a parameter,
  mirroring `Spec`; the δ row reads the body from it. `RedAgree` /
  `TypingAgree` (faithfulness) flag every mismatch.

## 4. Order

Dependency order, each layer green before the next:

1. `Spec/` (Syntax, Typing, Variance, Annotated, Signature).
2. `Metatheory/` (local cases, SR, confluence, LR + `entries`, canonicity,
   consistency, conservativity, erasure).
3. `Algorithm/` (DecEq, NbE + table, soundness, ConvNbE, CheckA, Elab,
   SigBuild; delete EraName).
4. `Lib/`, then `Examples/` (non-Knot), then the Knot and its generators
   (`gen-judge.py`, `gen-knot.py`), then `Trust/` (`gen-trust.sh`).
5. Measure: `Examples/PwCore` and the sweep against today's numbers
   (PwCore: 49.0M unfoldings, ~3.4 GB).

Pre-flight before every sweep: `tools/check-trust.sh` and
`tools/lint-imports.py` (no Agda, seconds).

## 5. What would make this wrong

Recorded so a failure is recognised, not explained away:

- The use-site cost of the `Σ` parameter. Agda lambda-lifts module
  parameters, and a half-generalised library has been the worst case here
  before (LESSONS: half-generalization). If use sites slow down, it shows in
  the step-5 measurement, and the answer is to fix the parameterisation's
  shape, not to restore the body.
- An Agda-level identification of `body Σ d` at a concrete `Σ` that does
  not compute (a lookup that is stuck because `Σ` is not in normal form at
  the use site). Use sites instantiate concrete telescopes; `lookupE`
  computes on them.
