# PLAN-LEVITATION — descriptions become terms, one datatype former (2026-09-26)

> Decisions: D071 (Σ positive, `split`, no η), D072 (one former, indexed),
> D073 (index is a code in Γ).
> Evidence: `SPIKE-LEVITATION.md` S0–S4 (`bootstrap/tmp/Lev*.agda`).
> The goal is KNOT SIMPLICITY. Kernel/MT churn is cheap: A-math went through
> all the metatheory in hours.

## Target kernel (from S3/S4)

- `Desc I` is a LARGE type: no code, level 1 (S0). The index is a code
  in Γ, `Γ ⊢ I ∷ U` (D073). A-math's CONTENT survives as grammar: a
  telescope is typed with no family in scope, and `pay` instantiates it
  with `mu D`.
- Telescopes are terms: `dι j`, `dσ S f` (`f : Π (El S) (Desc I)`), `dρ j C`.
  ⬜ Infinitary `dπ` is NOT spiked. Leave it out unless an example needs it.
- `mu D i` and its code; `con p`; `ielim D M e i t` with ONE method
  (`MethTy`); ι fires at ANY D (S1b).
- Formers computing on the telescope head: `pay`, `ihTy`, `ih`.
- Tags: `enum c`, `tag k` (typed `k < c`), `switch c P t ms` (motive a type,
  so it also eliminates into `Desc`).
- Σ: `split` primitive; `fst`/`snd` derived (D071).
- DELETED: `Mu`/`⌜Mu⌝`/`con k`/`elim`, `IMu`'s closed `IDesc`, `icon k`,
  `ilookupD`, method tuples, `IDescWf`/`IDescWfFrom`/`IConWf`/`ICodeWf`/
  `DescWf`/`DConWf`, `Xinst`/`XEnv`.

## Stage 1 — DONE (2026-09-26, branch `ocp-0009-levitation`)

`Spec/Syntax`, `Spec/Typing`, `Spec/Variance`, `Spec/Annotated` (regenerated
by the reconstructed `tools/genA.py`, which checks its field table against
`Spec/Syntax`), `Spec/AnnotatedDesc`, `Spec/TypingA` — all check.
Concrete formers (names chosen not to clash with existing identifiers):
`IMu I D i`, `Desc I`, `DIh D M C p` (type, computes on the telescope
head), `Fin n`; `⌜IMu⌝ I D i`, `⌜Fin⌝ n`, `con p`, `ielim D i e t`,
`dι j`/`dσ S f`/`dρ j C`, `dpay I D C i` (payload CODE), `dih D e C p`,
`fzero`/`fsuc t`/`fcase t a b`/`fcase0 t`, `psplit b q`.
⚠ DEVIATION from S4: tags are `Fin (n+1) ≅ 1 + Fin n` with a binary
`fcase` (plus `fcase0` for the empty Fin 0), not an n-ary `switch` — a
first-order eliminator with no argument list in the syntax; `switch`
over c constructors is c-1 nested `fcase`s (the elaborator's job).
`fst`/`snd` remain primitive for now; deriving them from `psplit` (D071)
is a follow-up stage once everything is green.

## Stages (each ends GREEN on its own branch; straight-line history)

1. **Spec**: `Syntax` (formers, generic ren/sub — S2) and `Typing` (S3/S4
   rules), `TypingA` twin, `Variance`.
2. **Metatheory**, in dependency order:
   - `TySub` (sub-⊢, now with description terms);
   - `SubjectReductionBase`/`SubjectReduction` (S3's `sr-desc` + congruence);
   - `Confluence` (new rules are left-linear and non-overlapping; `ι`/`split-ι`/`switch-ι` head rules);
   - `Injectivity` (`El`/`mu`/`sig`/`enum`);
   - `LogicalRelation` (S0: ⊩₁ membership of `Desc`, ⊩₀ `mu` as a level-0 copy + `⊩₀IMuNe`; S1b: Girard CR3 for `ielim`);
   - `Fundamental`, `Canonicity` (tags: S4 `switch-fires`), `Erasure`, `NormTy`, `Validity`, `FormerCensus`;
   - `Algorithm/*` (conversion deciders, `Check`/`CheckA`).
3. **Lib**:
   - a new `Lib/Sugar` holds S4's verified elaboration (`Dₗ`, `conₗ`, `methₗ`, derived `ιₗ`, `⊢methₗ`);
   - port `IPay`/`IFold`/`IWk`/`ISub`/`ISz`/`IOcc`/`IMeths`/`ICast`/`IDepth`/… onto telescope terms;
   - the list-form API (method per constructor) is kept via the sugar.
4. **Examples**: 15 indexed and 6 non-indexed example files, ported through
   `Lib/Sugar`. Non-indexed ones go to the unit index (D072).
5. **Knot**:
   - delete the `Mu` family (41 files mention it) and the `IDescWf` family, including option E's `ctxAtK`;
   - description terms become ordinary term rows;
   - update `gen-knot.py`, then `gen-trust.sh`.
6. **Measure**:
   - Knot module/def/row counts before and after, i.e. the goal metric;
   - cold sweep time;
   - record the numbers in HANDOFF.

## Risks

- **Normalization proof size**: S0 and S1b are fragments. The real
  `LogicalRelation` is the biggest unknown, so stage 2 goes first.
- **Positivity**: A-math's abstract-`X` typing is replaced by the GRAMMAR.
  Re-check the ⊩₀ block's positivity law (S0) against the real clauses. The
  S0 lesson applies: include EVERY clause.
- **Knot cost**: description terms in rows. Measure before and after; do not
  assume.
