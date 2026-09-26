# SPIKE-LEVITATION — can descriptions become TERMS? (2026-09-26)

> Question from the user: `IDescWf` (with `DConWf`, `DescWf`, `IConWf`,
> `ICodeWf`, `IDescWfFrom`) is a SECOND world of judgements beside typing.
> Is deleting it — descriptions as terms of an internal type, well-formedness
> as ordinary typing — the principled end state, and what follows?
> `PLAN-INDEXED` §15 (2026-09-01) said "not now" for four reasons; A-math
> (`PLAN-BIDI` §3e) and `bootstrap/tmp/ValidIxPos.agda` have since addressed
> two. These spikes test the rest. Each has a SUCCESS criterion and a CONTROL.

## The levitated kernel, as a sketch (what the spikes assume)

- **Descriptions are terms** of a type `IDescT cI` (index given by a CODE
  `cI : U` — "a family in `U` has its index in `U`", no separate judgement).
  Constructor telescopes use λ for dependency (`dσ S (λ s → C)`), recursive
  positions are `dρ j C` with no binding of the recursive value — strict
  positivity is the GRAMMAR, as A-math's abstract family made it.
- `IMu D i` / `⌜IMu⌝ D i` take the description as a TERM. Descriptions are
  no longer closed, so substitution traverses them.
- **Well-formedness is typing**: `Γ ⊢ D ∷ IDescT cI`. `IDescWf`, `IConWf`,
  `ICodeWf`, `DescWf`, `DConWf` disappear; a κ field's code is any `S : U`.
- `IDescT` is **large** (its elements contain codes), like `U`: level 1.

## The spikes

### S0 — STRATIFICATION: where does a description's MEANING live? (new, first)

Discovered while sketching: a description's semantic content is its
MEMBERSHIP in `⟦IDescT⟧`, which is a level-1 object (it stores `⊩₀`
witnesses for its codes, and tails over their members). But `IMu D i` is a
SMALL type, interpreted inside the `⊩₀` block, which cannot see level 1.

Proposed: `⊩₀IMu` stores a level-0 copy — the `IKInterp` shape that PASSED
in `ValidIxPos` (witness here, tail over members, index validity carried),
and `fund` converts `D`'s level-1 membership into it. A NEUTRAL description
has no content, so it gets its own clause `⊩₀IMuNe` (like `⊩₀ne`).

- SUCCESS: the two-level relation (⊩₀ with `Π`, `IMu`, `IMuNe`; ⊩₁ with `U`,
  `IDescT`, a neutral case) is accepted `--safe`, `⊩₀`/`⊩₁` in `Set`, AND the
  conversion `⟦IDescT⟧-membership → IKInterp` is DEFINABLE (not postulated).
- CONTROL: the same with `IMuMem` inside the `⊩₀` block must be REJECTED.

### S1 — NEUTRAL descriptions in the model

`ielim` over a neutral `D`: the ι-reduct contains `ilookupD D k`, `iihs …`
stuck on `D`. Needs: stuck description operators are NEUTRAL (types and
terms), their candidates are the SN ones, and `fund`'s `⊢icon`/`⊢ielim`
cases go through at `⊩₀IMuNe`.

- SUCCESS: in a small calculus with the real shapes (β, `icon`, `ielim`,
  `ilookupD`/`iihs` as formers that compute on canonical descriptions and are
  stuck on neutral ones), SN + the two fundamental cases at a neutral `D`.
- CONTROL: a deliberately wrong candidate (e.g. demanding canonical payloads
  at a neutral `D`) must fail to prove the `⊢icon` case.

### S2 — SUBSTITUTION through descriptions

Descriptions stop being closed. `renTy ρ (IMu D i) = IMu (renTm ρ D) (renTm
ρ i)`; `ipayTy`/`iihTy`/`iinst` become operators whose substitution laws must
commute. Expected mechanical (the renaming/substitution lemmas are generated
from the field table) — the spike checks that the COMPUTING operators'
substitution lemmas stay structural (no tower).

- SUCCESS: `sub-lemma`'s cases for the description formers and the payload
  operators, and the payload `-sub` lemmas, by structural induction.

### S3 — SUBJECT REDUCTION of description typing

New reductions (description operators on canonical descriptions, β inside
λ-closures of `dσ`) must preserve typing; `Γ ⊢ D ∷ IDescT cI` must survive
`D ⟶ D'`.

- SUCCESS: `sr` for the new rules; inversion for the description formers.

## Log

### ✅ S0 PASSED (2026-09-26) — `bootstrap/tmp/LevS0.agda`, control `LevS0Ctl.agda`

Accepted `--safe`, `⊩₀`/`⊩₁` both in `Set`, `Π` at both levels (∋ left of
an arrow), neutral clauses at both levels (`⊩₀IMuNe`, `cm-ne`/`iki-ne`).
The bridge is DEFINED, not postulated:

    toIK   : ConMem ⊩I C → IKInterp ⊩I C          -- level 1 → level 0
    imuSem : (⊩₁IDesc ⊩I) ⊩₁∋ D → ⊩₀ (IMuT D i)   -- what `fund` does at ty-IMu

— i.e. a description's meaning IS its membership in the LARGE type
`IDescT cI`, and the small family's interpretation is a level-0 COPY of it.
CONTROL: the same module with the telescope carrying ⊩₀ WITNESSES into the
membership (`IMuMemW` inside the ⊩₀ block — the shape of gates 6/6b and the
09-11 existential) is REJECTED: `IMuMemW is not strictly positive … _⊩₀∋_
… to the left of an arrow`.

★ Three facts the spike FIXES for the design:
- the LAW: a datatype the `⊩₀` block's `_⊩₀∋_` mentions must live OUTSIDE
  the block and take PREDICATES (the old design's rule, now a stated law);
- telescope interpretations are `⊩₀Σ`/`⊩₀Π`-shaped — the witness HERE, the
  TAIL a function over its MEMBERS — which keeps them in `Set` (a validity
  PREDICATE as an index made them `Set₁`: `tmp/ValidEnvPos.agda`);
- index validity is carried, so the interpretation is INDEX-DEPENDENT and
  `⊩₀IMu` stores the index type's `⊩₀` — hence the small-index requirement,
  which levitation states as `IDescT (cI : U)`.
