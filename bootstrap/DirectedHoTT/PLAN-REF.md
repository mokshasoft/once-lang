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
  record Def : Set where       -- a declared closed type, a closed body
    field kType : RTy ε ; kBody : RTm ε
  data DefTele : Set where ∅ : DefTele ; _▸_ : DefTele → Def → DefTele
  record Defs : Set where field len : ℕ ; tele : DefTele
  -- size, type d, body d by lookup (as Spec/Signature does today)
  ```

### 1.2 Reduction and conversion (`Spec/Typing`, parameter `Σ : Defs`)

- `δref : d <ˢ size Σ → ref {Δ} d ⟶ εwkTm (body Σ d)`.
  - The side condition is what makes reduction MONOTONE under signature
    extension (§1.4): a name beyond the signature is stuck, so every step
    under `Σ` is a step under any `Σ' ⊇ Σ`.
- Everything else is unchanged. δ still has no congruence and overlaps
  nothing.

### 1.3 Typing (`Spec/Typing`, parameters `Σ : Defs` and `n : ℕ`)

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
  becomes a view of `Defs`. `Metatheory/Erasure`'s `⊢ᴬref` case is `⊢ref`.
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
- **The Knot** (decided 2026-10-07; the fork resolved by principle, work
  disregarded). `kref ⌜d⌝`: no quoted body, the `cls` field kind gone. The
  DESCRIBED signature is an INDEX of the Knot's judgement families, a
  quoted signature `⌜𝒮⌝` beside the quoted variable context:
  - the signature IS a context (D081), and the Knot already indexes its
    judgements by the quoted variable context — the definition context
    gets the same treatment;
  - internalising "for all 𝒮" (Spec's meta-parameter) is a family over
    quoted signatures, so the Knot is ONE object, not a meta-family of
    Knots, one per signature;
  - it is what R7 needs: a checker in Once takes the signature as input.
  ★ REFINED (2026-10-07): a PARAMETER of the families, not an index. The
  signature is uniform across a judgement's recursive structure (every
  premise is over the same signature) — the defining property of a
  parameter. So a family over `q` is `IMu J (D q) i`: its recursive
  positions refer to the same `D q`, nothing threads `q` through premises,
  and only the δ/`⊢ref` rows and a family citing another (`⊢conv` cites
  `≅`) mention it. `λ q. IMu J (D q) i` is ONE code over all signatures
  (R7). The price: a description is no longer CLOSED but NATURAL in `q`
  (`FIBM-sub σ q : subTm σ (FIBM q) ≡ FIBM (subTm σ q)`); at every current
  use site `q = ⌜𝒮⌝` is closed, so the codes there are closed again.
  The AMBIENT signature (where the Knot's own codes live) is an Agda-level
  parameter, like Lib's. The rows: δ is `kref n ⟶ εwkK 1 j (body of ⌜𝒮⌝ at
  n)` under `n < size ⌜𝒮⌝`; `⊢ref` is `kref n : εwkK 0 j (type of ⌜𝒮⌝ at
  n)` under `n < bound`. The Knot also describes the definition context's
  FORMATION (`Spec/SigWf.WfK` over quoted signatures). Faithfulness: for
  every `𝒮`, the Knot at `⌜𝒮⌝` decodes to / encodes from Spec at `𝒮`
  (`RedAgree`/`TypingAgree` and the decoders); the generators
  (`gen-knot.py`, `gen-judge.py`) emit the new index and the module
  parameters, so the generated tree stays the generators' output.

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

## 6. Progress

### 2026-10-07 — Spec and Metatheory green (branch `plan-ref`)

- **Spec.** `ref d` has no body; `Defs` and `_<ˢ?_` in `Spec/Syntax`.
  `Spec/Typing` split three ways so each relation has exactly the
  parameters it depends on: `Spec/Base` (signature-free: substitutions,
  `Ctx`, `∋`), `Spec/Reduction 𝒮` (δ reads the body), `Spec/Typing 𝒮 n`
  (`⊢ref : d <ˢ n → …`, `EntryOK`/`SigOK`). Erasure is signature-free.
  `Spec/SigWf`: the kernel's context formation (`WfK`, each entry typed at
  its prefix).
- **Three module classes.** Reduction-level `(𝒮)`: Confluence,
  Injectivity, RedCong, the LR, `Fundamental/{Syntactic,Semantic,Indexed}`
  — ONE relation for every n, which entry reducibility needs. Typing-level
  `(𝒮)(n)`; above subject reduction `(𝒮)(n)(ok : SigOK)`. Top-level
  theorems (Canonicity, NormTy) take the single hypothesis `(wf : WfK 𝒮)`
  and derive `ok`/`refs` themselves.
- **Mixed modules split**: `TySub`, `SubjectReduction` → a `.Red` part
  (typing-free definitions, `(𝒮)`) re-exported by the original.
  `IsNormalᵀ` moved to the LR, `≅ᵀ-Πʳ`/`≅ᵀ-Σˡ` to RedCong.
- **Confluence got simpler**: the development unfolds a reference ONCE
  (`refDev`), the body not developed; a reference's only parallel reducts
  are itself and its unfolding, so the triangle needs no recursion into
  the signature.
- **The LR's `⊢ref` case reads an ORACLE** (`Fundamental/Semantic.RefsOK`);
  `Metatheory/Entries` builds it by induction along the telescope (entry
  m is `fund` at m on its own derivation, the oracle below m from the IH,
  one δ expansion). Validity's `⊢ref` case reads `okTy`: context
  formation carries type formation, as `c-▹` does.
- **Two generated structural lemmas**: `Metatheory/SigMono` (a derivation
  moves to a larger name bound) and `Metatheory/SigExt` (reduction,
  conversion and typing move along a signature extension, §1.4).
  `Metatheory/Signature.wf→K`: the checker's `WfSig S` is the kernel's
  `WfK (kernel S)` — each entry erased over its prefix, moved by `SigExt`.
  `Metatheory/SigBelow` (erasure agreement across bodies) deleted: erasure
  no longer reads bodies, and `⊢ᴬref` already bounds the names.
- **Agda module discipline** (found here, applies to every layer): each
  `open import M args` is a NEW instance, so (a) a parameterised module is
  instantiated ONCE per file (`import M args as ᴵM` + `open ᴵM …`), and
  (b) a parameterised module re-exports `public` only its own `.Red` part —
  otherwise two paths to one module make its names ambiguous.
- Reflection on a parameterised module's function needs the UNAPPLIED
  module (`FormerCensus` reads `LR₀.spine?`): the applied copy is a
  one-clause delegation.

Next: `Algorithm/` (NbE value table, CheckA on `wf→K`, SigBuild without
the `below` check), then Lib, Examples, the Knot and its generators.

### 2026-10-07 — Algorithm green

- **E4, the value table.** `Algorithm/NbE/Value` holds the values, the
  readings `⌊_⌋`, the type values, and `Tbl` (a telescope of entry values,
  `lookupT`; a name beyond the table is its own, stuck, value) — all
  table-free. `Algorithm/NbE (tbl : Tbl)` is the evaluator: `vref d`
  forces to `lookupT tbl d`. `Algorithm/NbE/TblOK (𝒮)(tbl)`: the table is
  sound — every entry closed (`TblSc`) and read as `ref d` (`TblReads`);
  the soundness stack (`NbESound`, `NbESoundTy`, `ConvNbE`, `ConvLazyNbE`)
  takes it as a parameter, and `S-forceR`/`S-rb` at a reference are one
  line each. `Algorithm/NbETable`: `mkTbl : Defs → Tbl` (entry m evaluated
  at the table of the entries before it, the prefix passed as an argument)
  and `mkTbl-ok`, along the telescope.
- **The table is SHARED.** `CheckA (S)(wfK)(tbl)(tok)` takes it as a
  parameter; `SigBuild` THREADS it along the telescope (`Stage`), each
  stage carrying `t ≡ mkTbl (kernel Sᵢ)` — `refl` at every step, because
  `mkTbl` of an extended signature unfolds to `extendAt` of the old table
  (the construction is signature-free for exactly this reason). So each
  entry is evaluated once per segment check.
- `Algorithm/Eval`: `head (ref n)` fires δ exactly on the signature's
  names (`refHead`, by `_<ˢ?_`); a reference beyond is normal (`nf-ref`,
  as `nf-app`: its head does not step). One `Dec` (the prelude's; DecEq
  re-exports it).
- `EraName` deleted: erasure keeps the name, so `decTo` compares erasures
  directly and linearly. `CheckA`'s `era-liftTm (ref d)` is `refl`.
- `SigBuild`: `EntryWf` carries the type's derivation; the `below` checks
  are gone (`⊢ᴬref` bounds the names); the kernel hypothesis is `wf→K`.

Next: Lib, then Examples, then the Knot.

### 2026-10-07 — Lib green

- No reference cases: the layer is parameters and imports only. Classes
  computed as a fixpoint over imports: 33 typing-level `(𝒮)(n)`, 20
  `(𝒮)(n)(ok)` — nearly all through `Lib/Sugar`, whose `srᵀ*` (subject
  reduction for TYPES) genuinely needs the entries typed (a type reduction
  may contain a δ step) — 8 `(𝒮)(wf)` (canonicity, the fundamental lemma),
  5 reduction-level.
- The kernel's `SigOK` is renamed `EntriesOK`: `Lib/Syn` has its own
  `SigOK` (the Knot's quoted signatures), used across Lib.
- Where a file declares its own `n`, the module parameter is `𝓃`.
- Module discipline extended to LOCAL imports (`where open import M args`):
  they open the file's one top-level instance (`open ᴵM …`).

### The Knot stage — steps

- ✅ K1. `Lib/SynFib`, `Lib/SynFam`, `Lib/SynPat`: families with a PARAMETER
  of code `P`: a row is `R q j p c` (law over `q` too); `Fib₀` takes `P`;
  `RowOK` assumes `Ξ ⊢ q ∷ El P`; `FIBM q`, `fib-β` at `q`, `FIBM-sub`
  natural in `q`; `SynFam` gives `DF q`. Parameterless families: `P =
  ⌜Unit⌝`, rows ignore `q`.
- ✅ K2. `Examples/Knot/QSig`: `⌜QSig⌝ = Σ Nat (Σ (Π Nat ⌜Ty⌝₀) (Π Nat
  ⌜Tm⌝₀))` (size, declared types, bodies — functions, so no list type is
  needed); `quoteDefs : Defs → RTm Δ` (each entry quoted, selected by a
  `natcase` chain); its typing; lookups.
- ✅ K3. Generators (`gen-knot.py`, `gen-judge.py`): rows take `q`; a family
  citing another passes `q`; module parameters (the ambient signature)
  and one instance per (module, arguments) emitted by the generators.
- ✅ K4 (δ, ⊢ref, RefCon; the SigWf image + its faithfulness, 2026-10-12). Hand rows: δ (`Knot/Ref`: `kref n ⟶ εwkK 1 j (bodies q n)` under
  `n < size q`), `⊢ref` (`Knot/RefJudge`: `kref n : εwkK 0 j (types q n)`
  under `n < bound`), `Knot/RefCon`; the internal image of `Spec/SigWf`.
- ✅ K5 (green in the 2026-10-10 sweep). Decoders and agreement at `q = ⌜𝒮⌝` (`RedDecode`, `JudgeDecodeHand`,
  `RedAgree`, `TypingAgree`): `n < size` from the `Hom Nat` premise, the
  body from `quoteTm` injectivity after the lookup computes.
- ✅ K6 (all signature examples green in the 2026-10-10 sweep). The signature-building examples (SigCore, SigMeth, PwCore, the NbE
  agreement tests) at their `kernel S`; then MEASURE (step 5 of §4) — ✅ 2026-10-12: cost-neutral after the level-indexed table (49.4M unfoldings vs 49.0M; 81 s).

### 2026-10-07 — Knot stage: K2 done, K3 underway

- **K2.** `Knot/QSig`: `⌜QSig⌝` with typed projections `sizeQ`/`typesQ`/
  `bodiesQ`. The TYPING judgement's parameter is `⌜TSig⌝ = Σ ⌜QSig⌝ Nat`,
  the signature AND the bound, as `Spec/Typing (𝒮)(n)`; its conversion
  premise passes `sigT q`. `Knot/QuoteSig`: `quoteDefs 𝒯`. A `natrec`
  chain SHIFTS the entry function at each step, so `typesQ`/`bodiesQ
  (quoteDefs 𝒯) (num d) ⟶*` the quoted entry is a one-line induction at
  every name (the kernel's default `⟨Unit∣unit⟩` past the size).
- **K3, positions.** `gen-judge` has an ambient position `QS`, mentioned
  only by `⌜⟶⌝` (RedT's premise on the lower stratum). A telescope takes the
  signature iff it cites it. A row is always `R q j p c`. Families over
  nothing (`Pw`, the side conditions) are at `unit`.
- ★ **The core is a hypothesis on the ambient signature (decided).**
  `Knot/PwCore`'s code is a reference to the core entries (P4). A reference
  is a projection from the ambient signature, so the Knot that cites the
  core is over any signature CONTAINING it:
  `(core : PwCore.Kc ⊑ᴰ 𝒮)` (`Spec/SigExtend`: same names, types and bodies
  below the core's size). Two consequences:
  - `⊢⌜Pw⌝` is `⊢ref` with no premise.
  - The conversions core ≅ Knot are decided ONCE at the concrete core by NbE
    and carried to `𝒮` by `SigExt.ext≅`.

  `tools/planref.py` gives every module importing a core citer the third
  parameter (class `C`; 33 Knot modules). The rejected alternative, a Knot
  that never cites the core with core-agreement as a separate theorem,
  reverts P4 and the direction of R4 (the Knot moving INTO the core).
- ⏸ **Follow-up: split signature-free data out of parameterised modules.**
  DEFERRED with a trigger 2026-10-12 (see that day's entry): no module
  meets two instances, so the split has no customer yet.
  - Agda datatypes are generative in their module's parameters:
    `Lib/Syn.Sig 𝒮₁ …` ≠ `Lib/Syn.Sig 𝒮₂ …`. So signature-independent
    data (`Fld`/`Shape`/`Sig`/`ShOK`/`SigOK`/`NthG`, `Lt`, `Cons`, `Tel`,
    `STm`, the Knot's `KSig`/`KOK`, …) should live in unparameterised
    modules, as `Spec/Base` does for the kernel.
  - Today every crossing between two signatures goes through raw `RTm`
    (signature-free), so nothing is blocked. The core examples instantiate
    Lib and the Knot at `∅ᴷ` (`Examples/Lib0`).

### 2026-10-08 — K3/K4 green through the constructors; K5 written; a regression to profile

- **Green** (checked in dependency order): QSig, QuoteSig, Knot/PwCore (over
  `core`, 46 s / 1.6 GB, conversions decided at the core by NbE), Ref, Red,
  RedT, Conv, ConvCon, JudgeConv, JudgeRowsTm, RefJudge, JudgeRowsGen,
  Judge, RefCon, QView, RenAgree, SubAgree, OpAgree, PredsCon, PredsAgree;
  the core examples SigCore → SigMeth → PwCore at the empty signature's
  Lib/Knot instances (136 s / 3.9 GB for the three).
- **K4** δ: `n < sizeQ q ⟹ kref n ⟶ εwkK 1 j (bodiesQ q n)`; ⊢ref:
  `n < boundT q ⟹ kref n : εwkK 0 j (typesQ (sigT q) n)` — no premise. Both
  rows as a TAIL after the side condition (`TδT`/`T⊢refT`, own law), the
  row at the sources (`T q j p c = T' q j (nameOf p) c`), constructors by
  one `mono-by`.
- **K5** (written, checking): decoders read closed derivations at the
  quoted ambient signature (`q𝒮`, typing at `t𝒮 = (q𝒮 , size)`). The side
  condition decodes by `homLt` (a closed `Hom Nat (d+1) m` at numerals is
  `d <ˢ m`: the order computes, consistency at 0) and encodes by
  `⊢below`/`⊢belowT` (`homLt⁻`: it computes to `Unit`). The typing
  family's conversion premise is at `sigT t𝒮`, a redex: the family at a
  REDUCING parameter reduces (`Lib/SynFam.DF-⟶*`, `KF-⟶ᵀ*`, by substitution
  monotonicity).
- ⚠ **Compile time: Red and RedT regressed.**
  - Rechecked one module per process, dependencies already built: Red
    561 s (P5 sweep: 12 s), RedT 175 s (11 s). The rest is in line:
    RenAgree 16 s, SubAgree 18 s, PredsCon 5.6 s, Pw/PwCore < 8 s.
  - The 3416 s / 79 s figures measured earlier were dependency chains
    rechecked in one process under memory pressure — not evidence
    (`exit-143-is-not-evidence-about-cost`; time cold or not at all).
  - Acted on regardless, as the principled form: the derived library
    arguments have ONE global spelling (`Entries.okᵂ`/`refsᵂ`,
    `Defs.size 𝒮`; `planref.py`) instead of per-module private
    abbreviations.
  - ⬜ Profile Red (`tools/agda-profile.sh`). A first profiling run was
    stopped by the session's memory guard; it is to be rerun with the
    user's go-ahead.
- **State at 2026-10-08 morning** (one module per process, deps built):
  - green through RedTConGen;
  - still to check, in order: RedTAgree ConvAgree PredsDecode Unquote
    QuoteSig PwDecode RedCompDecode RedDecodeXi RedDecode RedTDecodeXi
    RedTDecode ConvDecode JudgeConGen ConvHead Core JudgeDecodeBase
    JudgeDecodeHand LookupDecode JudgeDecodeTm JudgeDecodeTy JudgeDecode
    Exact LookupAgree Sz TypingAgree (the K5 layer, all written);
  - then K6 (the signature-building examples) and gen-trust + a sweep.
  - Driver: one `check.sh` per module in topological order (a single
    process rechecking a chain OOMs at the 5.5 G cap).
  - Two background runs were stopped by the session's memory guard;
    rerunning them needs the user's go-ahead.
- **Real regression vs the cold sweep** (`sweep-cold.log`), one module
  each: Red 148 → 561 s, RedT 40 → 175 s, RedXiConGen 58 → 870 s,
  RedCompConGen 52 → 448 s, RedTConGen ~40 → 394 s, JudgeRowsGen
  52 → 205 s, RedAgree 10 → 158 s; peaks 3.3–4.7 GB.
  - Only the families with a NON-TRIVIAL parameter code (`⌜QSig⌝`,
    `⌜TSig⌝`) regressed; the ones over `⌜Unit⌝` (Preds, Pw) did not.
  - Hypothesis to profile: `subTm σ ⌜Unit⌝` COMPUTES to `⌜Unit⌝`, while
    `subTm σ ⌜QSig⌝` is stuck on the opaque `⌜Ty⌝₀`/`⌜Tm⌝₀`. Every
    substitution or weakening of the parameter (FIBM under the method's
    binders, `wkQ`, the case modules) then goes through the `P-sub`
    casts — the context-form-mismatch pattern.
  - A principled candidate if confirmed: a parameter code that is CLOSED
    BY CONSTRUCTION. A reference (to a core entry for `⌜QSig⌝`) is closed
    under substitution definitionally (`⌜Pw⌝-sub` is `refl`), which is
    the R4 direction anyway.

### 2026-10-09/10 — K5 + K6 green; the regression explained; full sweep

- **K5 green.** All K5 modules pass (generator fixes in `gen-judge.py`/`gen-knot.py`).
  Sweep times: TypingAgree 44 s, JudgeDecode 28 s, Exact 17 s.
- **The regression is NOT the parameter `q`** (profiled, Red at `604f34c07`
  vs `plan-ref`): q-free lemmas with byte-identical text regressed 25–50×;
  `Sig.KD` unfolded 0 → 1058, SD/SI ~100 → ~6000. Cause: every file builds
  its own module instance (`open import M 𝒮 wf`), so one name reached
  through two files has two heads, syntactic equality fails, and Agda
  normalises the description under renamings. **Fix:** `SD` OPAQUE in
  `Lib/Syn` (+ `SD-def`, explicit `unfolding SD` where the code is read:
  ⊢SD, SD-sub, ⊢conSyn, SynTravM/SynFib, Knot/Sub+SubEnv, Knot/PwCore's
  byNbE). Red 540 → 175 s. The residual ~1.65× over the baseline is
  conversion overhead from module ARGUMENTS (`Defs.size`, `okᵂ`, `tag`
  as new top conversion entries) — an artefact of Agda's encoding of an
  ambient signature; accepted, not optimised, unless a module hits the
  memory ceiling. The `q`-closed-by-construction candidate (2026-10-08)
  is therefore unneeded.
- **K6 green.** SigCoreEval, NbEKDTest, NbEPwAgree, SigCoreTest,
  NbESigCoreTest, NbESigSubKnotTest, NbESigTravTest, NbETravAgree,
  SigExtendTest, Signature, Elab, NbEAgree at their `kernel S` instances
  (all 2–8 s). Two patterns were needed:
  - joining two NbE copies at a concrete code: a generic
    `byNbE t u : nfᴺ t ≡ nfᴺ u → t ≅ u` (NbEKDTest: OOM → 22 s);
  - deciding a concrete equality: a `with`-defined Boolean `differs ≡
    false` + `same`, never `IsYes`/`fromYes` (NbEPwAgree: OOM → 16 s).
- **Sweep 2026-10-10** (`sweep-planref.log`, gen-trust regenerated, lint
  clean): 279/283 green; the 4 failures were the Comparison benchmarks
  (still on unparameterised imports) and `Trust.Comparison` importing
  them — ported to the `Examples/Lib0` instances afterwards.
- ⚠ **To check:** `Gcd.LeMid` 61 → 14 872 s and `Gcd.LeEq` 4 → 1037 s in
  that sweep. LeMid followed a 143 kill and may have rebuilt the closure
  (`sweep-first-module-eats-the-closure`); re-time each alone.

### 2026-10-11 — Spec.Base no longer shared through the instances

- **The Gcd regression is real, and it is a copy.** Re-timed alone after
  deleting only their interfaces: LeEq **1057 s / 1.0 GB** (cold 4 s),
  LeMid **113 s / 4.96 GB** (cold 61 s; the sweep's 143 was the 5.5 GB cap).
  Profiled (`agda-profile.sh`): `Eq4.⊢transport`, `Eq4!.step`/`eq4`,
  `⊢MIDnr`, `⊢S3s` = 850 s of 1050, all `extS`/`renTm`/`subTm` unfoldings
  (55 M in `⊢transport` alone). Conversion heads include
  `Lib0.Inst.Spec-Typing.single`, `Lib.ArithComm._.⌊_⌋`,
  `Spec.Typing._.Base.⌊_⌋`: COPIES of signature-free `Spec.Base`
  definitions.
- **Mechanism.** `Spec.Reduction` did `open import Spec.Base public`; a
  module application copies the whole exported scope, re-exports included,
  so every `Spec.Typing 𝒮 n` instance minted its own `single`, `⌊_⌋`, `nrs`,
  … Two heads for one function, and `subTm (single x) F ≡ subTm (single′ x) F`
  is decided by evaluating the substitution. Same family as the SD fix
  (2026-10-09), one level down: open problem 4 of HANDOFF-2026-10-08 (split
  the signature-free data out of the parameterised modules), now measured.
- **Fix.** `Spec.Reduction` opens `Spec.Base` without `public`;
  `tools/base_unshare.py` (also the last pass of `planref.convert_all`, so
  the generators emit it) strips the Base names from every Typing/Reduction
  `using`/`hiding` list and opens them once, from `Spec.Base`, before the
  module header (247 files, idempotent; regeneration reproduces the tree
  byte for byte; lint 0 errors / 395 warnings as before).
- ✅ **Sweep `bootstrap/sweep-unshare.log`: ALL GREEN, 288 modules**
  (4538 s total). Against `sweep-cold.log` (pre-PLAN-REF) and the 10-08
  one-module-per-process numbers:

  | module | cold | 10-08 / 10-11 alone | un-shared sweep |
  |---|---|---|---|
  | Gcd.LeEq | 4 s | 1057 s / 1.0 GB | **10 s** |
  | Gcd.LeMid | 61 s | 113 s / 4.96 GB | **65 s** |
  | Knot.Red | 148 s | 175 s (after SD) | 986 s, see below |
  | Knot.RedT | 40 s | 175 s | 61 s |
  | Knot.RedXiConGen | 58 s | 870 s | 134 s |
  | Knot.RedCompConGen | 52 s | 448 s | 123 s |
  | Knot.RedTConGen | 28 s | 394 s | 62 s |
  | Knot.JudgeRowsGen | 52 s | 205 s | 87 s |
  | Knot.RedAgree | 10 s | 158 s | 19 s |

  The Gcd regression is gone (LeEq 2.5× of cold, inside its first-module
  noise; LeMid at cold). The Knot families keep a ~1.5–2.3× overhead over
  cold, the module-argument cost accepted on 2026-10-09/10.
- ⚠ **Knot.Red is at the memory ceiling.** In the sweep it was killed with
  143 at `-A64m` and passed on the ladder's `-A64m -c` (986 s, with another
  session's agda running alongside). Re-timed alone (deps built, no other
  agda): `-A64m` → 143 at 6m51s (scope peak 4.9 GB + 2 GB swap);
  `-A64m -c` → **285 s, 3.8 GB + 1.7 GB swap**. The 175 s after the SD fix
  was at `-A64m`, so Red got slower and bigger since 10-10, or that run
  was close to the cap already.
  - Profiled (`agda-profile.sh`, HEAP=5G; killed at the cap, snapshot at
    189 s covering ~5000 of 7358 lines): **no instance-copy blowup**. At
    most 52 k unfoldings per site (LeEq: 55 M in one), heads canonical
    (`Spec.Syntax.renTm`, `Spec.Base.⌊_⌋`); the `Red._.Tel`/`._.⌜Tm⌝`
    copies are the module's own instance, hundreds of hits. Cost is spread
    over ~16 k sites and ~1640 blocks: Red is SIZE plus the accepted
    module-argument overhead.
  - ✅ So, per `agda-oom-is-a-gc-choice`: `gen-judge.py` now gives Red the
    COMPACTING COLLECTOR header, and the sweep starts it at `-A64m -c`
    instead of losing ~7 min to a 143 first. Splitting Red is the fallback
    if it outgrows `-c`.
- **Rule:** a parameterised module never `public`-re-exports a
  non-parameterised one. A regression after a parameterisation: look in the
  profile's conversion/unfolding heads for `M._.name` / `Inst.…name`
  copies of signature-free definitions.

### 2026-10-12 — signature extension; K4's SigWf image, closed

- **`⊑ᴰ-▸ : 𝒮 ⊑ᴰ (𝒮 ▸ᴷ e)`** (`Spec/SigExtend`). Its two facts moved to
  `Spec/Syntax`, beside `lookupK`: `<ˢ→≠` (a name below n is not n,
  structural via `<ˢ-pred`/`<ˢ-down`) and `lookupK-▸` (a lookup below the
  newest entry skips it). `Algorithm/NbETable` and `Knot/QuoteSig` had
  private copies; they now use these (NbETable's was a 25-line tower).
- **K4, the internal image of `Spec/SigWf` — split in two.**
  1. ✅ (`Examples/Knot/SigWf`): the code and its typing. `⌜EntryOK⌝ q m`
     = the typing family at the parameter `tAt q m = (q , m)` — the
     entry's PREFIX is the bound — inhabited at `◇ ⊢ty typesQ q m` and
     `◇ ⊢ bodiesQ q m ∷ typesQ q m`. ★ CHANGED 2026-10-12 from the Π form
     (`Π m. m+1 ≤ sizeQ q → ⌜EntryOK⌝ q m`, Spec's `EntriesOK` reading) to
     Spec's `WfUpTo` itself: `⌜WfUpTo⌝ q k = natrec ⌜Unit⌝ (⌜Σ⌝ IH
     (⌜EntryOK⌝ q m)) k`, `⌜WfK⌝ q = ⌜WfUpTo⌝ q (sizeQ q)` — a natrec into
     `U` (precedent `Lib/DvdArith.nfam`). The Π form's ENCODING needs one
     internal function of a variable `m` returning entry m's closed proof
     (a table by internal case analysis); the recursive form is nested
     pairs, and it is literally the kernel's definition.
  2. ✅ Faithfulness (`Examples/Knot/SigWfAgree`: `decWfK : ◇ ⊢ k ∷ El
     (⌜WfK⌝ q𝒮) → WfK 𝒮`, `enWfK : WfK 𝒮 → Σ k. Θ ⊢ k ∷ El (⌜WfK⌝ q𝒮)`). It needed the K5 layer at EVERY bound: its one
     `Spec.Typing 𝒮 (size 𝒮)` instance played two roles — the ambient
     typing of Knot terms (stays at `size`) and the judgement encoded /
     decoded (now at `𝓃`). Done as planned:
     - the K5 modules (TypingAgree, JudgeDecode{,Base,Hand,Tm,Ty}, Exact,
       ConvHead) take a module parameter `(𝓃 : ℕ)` after `core`;
       `t𝒮` is gone, replaced by `tN 𝓃 = tAt q𝒮 (num 𝓃)` (`Knot/QuoteSig`;
       `tAt`/`⊢tAt` moved to `Knot/QSig`), `⊢belowT` takes the bound;
     - the encoded judgement is `import Spec.Typing 𝒮 𝓃 as ᴺ` with
       `_⊢ᴺ_∷_`/`_⊢tyᴺ_` and `ᴺ.`-qualified constructors (the encoded
       side is the rarer one: result types, one constructor per clause);
     - `tools/planref.py` has a class `N` (a `C` module whose text uses
       `𝓃`, or imports an `N` module); the generators emit `tN 𝓃` and the
       `ᴺ` instance; regenerated output differs in 4 files (JudgeDecode{,Ty,Tm}, ConvHead);
     - ⊢ref's side condition decodes to `d <ˢ 𝓃` (`homLt d 𝓃`).
     `SigWfAgree` imports TypingAgree/Exact UNAPPLIED (an instance per
     entry, at its bound) and adds `⌜EntryOK⌝-sub` (via `D⊢-sub`, from
     `SD-sub` + `FIBMₒ-sub`) for `WfUpTo-suc : ⌜WfUpTo⌝ q (k+1) ⟶ ⌜WfUpTo⌝ q
     k × ⌜EntryOK⌝ q k`. Stated at `q𝒮`, as the K5 decoders are; at an
     arbitrary quoted `q` it would need decoders at arbitrary `q` (open).
  - Cost of the bound parameter: none measurable. Single-module times
    (before → after): JudgeDecodeTm 146 → 159 s, JudgeDecode 27 → 29,
    JudgeDecodeTy 26 → 27, TypingAgree 43 → 43, Exact 17 → 16,
    JudgeDecodeHand/Base 15 → 15, ConvHead 13 → 13, SigWf 11 → 10 (all
    within the ±12% noise floor); SigWfAgree 20 s.
- **Open problem 4 (signature-free data in parameterised modules): the
  cost half is CLOSED, the type half DEFERRED with a trigger.**
  - The measured cost (2026-10-11) came from RE-EXPORTS: an instance copies
    whatever its module `public`-re-exports. Two more such re-exports
    remained, both now plain imports: `Algorithm/DecideConversion`
    re-exported `DecEq`'s `Dec`/`yes`/`no` (no importer needed it), and
    `Algorithm/NbE` re-exported `NbE/Value` (NbEScope, NbESound,
    NbESoundTy, ConvLazyNbE and NbE/TblOK now import Value directly).
  - ★ The rule is now a gate: `lint-imports.py` check 3 makes it an ERROR
    for a parameterised module to `public`-re-export a non-parameterised
    project module. The `--control` seeds it, and the sweep refuses on it.
    It found the NbE case, which a grep missed.
  - Datatype GENERATIVITY (`Lib/Syn.Sig 𝒮₁` ≠ `Sig 𝒮₂`) only bites where
    two instances of one module meet. No module does (checked: per file,
    no Lib/Knot module is imported at two argument lists; the only doubles
    are `Spec.Typing`, whose data is signature-dependent anyway). The
    split has no customer, so ⏸. Trigger: the first module that needs
    one Lib/Knot datatype at two signatures (e.g. faithfulness at an
    arbitrary quoted `q`, or the core examples meeting the ambient Knot).

### 2026-10-12 — step 5, the measurement: the table's LOOKUP was the cost

- **PwCore after PLAN-REF, first measurement** (cold, alone, `-A64m -c`):
  95 s, 4.1 GB peak, **72.9M unfoldings**, against the baseline of 49.0M
  and 3.4 GB (PLAN-BIDI §3e, after the `lvlAt` fix). It was worse, not better.
- **Head-by-head against the surviving reports** (`PwCore-eraname.json`
  minus the later `len` fix ≈ the 49.0M baseline): `eval`, `force`/
  `forceR`/`refV` (3.38M each), `lookup`, `inst` and readback are
  UNCHANGED (within 5%). References are forced exactly as often as
  before, and evaluation barely dropped (`eval` 5.19M → 4.92M). All
  of the +24M was NEW: `lookupTT` + `pickV` (8.7M each) + 8.4M `_==_`.
  - ★ So E4's premise was a misreading: the "~38% reference
    evaluation" counted `eval`/`force` for EVERY value. Re-evaluating
    bodies was never the cost. The table is still the right shape (it is
    the mathematics, and the clarity win is real); its lookup was not.
  - The lookup walked a telescope from the NEWEST entry, comparing
    `d == n` per step (as `lookupK` walks the signature): 252k lookups ×
    35 steps × 3 unfoldings. References name OLD entries, the library at
    the bottom of the signature.
- **Fix: index by LEVEL.** A name is a de Bruijn level, so the table is a
  list OLDEST FIRST (`TVals`) and `lookupL` recurses structurally on the
  name: one unfolding per step, no comparison. Extension is `snocᵗ`
  (built once per entry, shared). A `Defs` whose `len` exceeds its
  telescope gets explicit `skipᵗ` levels that read as the stuck reference,
  as `lookupK` places them. `NbETable.lookT-step` keeps its statement
  (now a lemma, `look-snoc`), so `okUpTo` is unchanged. `extendAt` loses
  its unused level argument.

- **Measured after the fix** (same method: cold, alone, `-A64m -c`; the
  profile in the staged tree):

  | PwCore | unfoldings | allocated | time | peak |
  |---|---|---|---|---|
  | baseline (PLAN-BIDI §3e) | 49.0M | — | 84.5 s (shared) | 3.4 GB (profiler heap) |
  | table walked from the top | 72.9M | 336 GB | 95 s | 4.1 GB |
  | ★ table indexed by level | **49.4M** | **248 GB** | **81 s** | 4.0 GB |

  `lookupL`: 2.7M steps for 252k lookups (~11 each, one unfolding per
  step), against 26M. Every other head is unchanged.
- ★ **Step 5's verdict.** At PwCore, PLAN-REF is cost-NEUTRAL in
  unfoldings (49.4M vs 49.0M) and somewhat faster. It did not deliver the
  ~38% E4 predicted, because that prediction misattributed the cost (see
  above). What PLAN-REF bought is its other two criteria: the
  mathematics (a reference IS a projection; D082) and clarity (`ref d`
  with no body, `⊢ref` without a premise, `EraName` deleted). The
  remaining evaluator cost is `eval`/`force` on every value; that is
  PLAN-EVAL's business, not the reference representation's.
- Lesson: before predicting a saving from a profile, attribute each head
  to the code path that CALLS it. `force`/`refV` run for every value,
  not just references; only `lookup*` was reference-specific.
