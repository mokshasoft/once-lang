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

### ✅ S1 PASSED (2026-09-26) — `bootstrap/tmp/LevS1.agda` (constructor-LIST form)

A concrete calculus (β, `icon`, `ielim`, `lkp`, `ihs`, `sel`, full
congruence), NOT an abstraction: one module `Calc Guard`, parameterised by
ι's side condition, instantiated twice.
- `Levitated` (ι only at a `Canon`ical description — as `natrec` only on
  numerals): `ne-pres` (neutrality is preserved), `sn-ielim`/`sn-ihs`/`sn-lkp`
  (the new SNe forms are SN from SN parts — only congruence steps exist), and
  the two `fund` cases at a neutral D: `fund-icon-ne` (payload only SN, which
  is all ⊩₀IMuNe asks) and `fund-ielim-ne` (result NEUTRAL ⇒ in ANY motive
  candidate by CR3; no case on the scrutinee, no use of the methods).
- CONTROL 1 — `Control`, ι unguarded: the same lemma is PROVED FALSE. The
  method TUPLE's type `imethsTy D M` is stuck at a neutral D, so it is known
  only SN; `ms = (ω , ·)`, `ielim x ms (icon 0 ω)` reduces to Ω.
- CONTROL 2 — the wrong candidate (canonical payloads at a neutral D) is
  refuted: a variable is SN and not a value.

### ⚠ FOUND while typing S3: the constructor LIST does not levitate

With `D` a term, `icon k p : IMu D i` must check `k` against `D`'s length —
impossible at a neutral `D` — and `lkp dnil k` is a STUCK CLOSED term (a
closed normal form of `ITel` that is not a constructor: canonicity breaks).
The principled form is the one of *The gentle art of levitation* (Chapman,
Dagand, McBride, Morris 2010): a datatype is ONE telescope, constructor
choice is an ordinary σ field over a tag type, and the eliminator takes ONE
method, a Π over the payload and its hypotheses. `icon k`, `ilookupD`, the
method tuple and `sel` all disappear. S2 was already done in list form (it
does not care); S3 and S1b use the one-telescope form.

### ✅ S1b PASSED (2026-09-26) — `bootstrap/tmp/LevS1b.agda` (one-telescope form)

In the one-telescope form ι needs NO guard: `ielim D M e i (con p) ⟶
e i p (ih D M e D p)` at ANY `D`. The method's type is a Π whose DOMAINS are
stuck at a neutral D (`pay D D i`, `ihTy D M D p` ⇒ SN candidates), but the
Π itself is not stuck, so its candidate still promises "applied to SN
arguments, lands in the motive". `ielim-ne` proves the neutral-D case by
Girard's CR3 (ielim is an elimination; every reduct is in the motive): the ι
reduct via the method's Π-candidate and `sn-ih` (ih over a stuck telescope is
SN). Assumed, as for every type interpretation: the motive's candidate
respects reduction of `M`, `i`, `t`.
CONTROL: know the method only SN (the tuple form's situation) and the same
statement is REFUTED — `e = λ i p h. p p`, `p = ω`, three β-steps to Ω.
⇒ S1's guard was forced by the TUPLE, not by neutrality.

### ✅ S2 PASSED (2026-09-26) — `bootstrap/tmp/LevS2.agda` + `LevSyn.agda`, control `LevS2Ctl.agda`

Generic syntax over an operator table (binder count per argument — the
kernel's field table), ONE traversal, the σ-calculus lemmas once
(`tmp/LevSyn.agda`, shared with S3). Telescopes are terms (`dι j`, `dσ S f`
with `f` a function, `dρ j C`); `pay`/`ih` are formers computing on the
telescope head. `sub-step : t ⟶ t' → sub σ t ⟶ sub σ t'` for every rule:
all cases definitional except β (Lemma B, `sub-β`) and `pay-σ`/`pay-ρ`
(Lemma W, `sub (exts σ) (wk t) ≡ wk (sub σ t)`, ONE binder). `ι`'s guard is
stable (`canon-sub`: a positive head condition). No tower.
CONTROL: `pay-σ`'s case with Lemma W replaced by `refl` is REJECTED
(`ren fs (sub … f) != sub (…) (ren fs f)`) — the lemma is needed, one level
of it suffices.

### ✅ S3 PASSED (2026-09-26) — `bootstrap/tmp/LevS3.agda`, control `LevS3Ctl.agda`

The one-telescope kernel fragment, typed: `Desc` (large — no `Desc ∷ U`),
`dι`/`dσ`/`dρ`, `mu D i`, `con`, `pay D C i` (the payload code, `eqc j i` at
`dι j`), `ihTy`/`ih`, `ielim D M e i t` with
`MethTy D M = Π i. Π (p : pay D D i). Π (h : ihTy D M D p). M i (con p)`,
and a closed index code `ix` (A-math's `◇ ⊢ty I`). Well-formedness of a
description IS `Γ ⊢ D ∷ Desc`.
- INVERSION for every description former, through `t-conv`
  (`inv-dι/dσ/dρ/pay/ihTy/ih/ielim/con`).
- `sr-desc : Γ ⊢ t ∷ A → t ⟶ᴰ t' → Γ ⊢ t' ∷ A` for ALL TEN description
  rules (ι, pay-ι/σ/ρ, ihTy-ι/σ/ρ, ih-ι/σ/ρ). The bookkeeping is S2's
  lemmas: `c1`/`c2`/`c3` (a weakening cancelled by 1–3 single
  substitutions, pointwise `refl`), `cw`, `wk-MotTy`.
- ASSUMED (module parameters — the kernel's standard metatheory, which
  levitation does not change in kind): weakening of typing; `El`/`mu`
  injectivity under conversion (Church–Rosser). NOT re-proved: SR for
  β/π/congruence.
CONTROL: give `pay-ρ` the wrong recursive index (`mu D i`, the target,
instead of `mu D j`) — REJECTED (`j != i`): SR really checks that `pay`
and `ih` agree on indices.

## Verdict (2026-09-26)

All four risks tested (S0 stratification, S1/S1b neutral descriptions, S2
substitution, S3 subject reduction) PASS, each with a control that fails.
Levitation is FEASIBLE — in the one-telescope form, not the list form.
What it deletes: `IDescWf`, `IDescWfFrom`, `IConWf` (A-math's abstract-`X`
telescope typing: positivity is now the GRAMMAR), `ICodeWf`, `DescWf`,
`DConWf`, `icon k`, `ilookupD`, the method tuple, and the Knot's whole
parallel judgement family for them (incl. option E's `ctxAtK` detour).
What it adds: `Desc` (large, level 1 — S0), `pay`/`ihTy`/`ih` as formers
with head rules, a tag type for constructor choice.

Open, NOT covered by these spikes:
- a TAG type (finite enumeration code + its eliminator) so constructors
  keep names and methods can be written per constructor — the surface /
  elaborator can keep presenting constructor lists and method tuples as
  sugar over σ-over-tags;
- the full SR (β/congruence) and `sub-⊢` with the new typing rules, and the
  normalization proof for the whole system (S0/S1b are its two new pieces);
- infinitary fields (a `dπ`), and the interaction with `Id`/`Hom`;
- the migration of Spec/Metatheory/Lib/examples/Knot.
