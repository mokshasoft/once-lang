# PLAN-LEVITATION — descriptions become terms, one datatype former (2026-09-26)

> Decisions: D071 (Σ positive, `split`, no η), D072 (one former, indexed),
> D073 (index is a code in Γ), ★ D074 (descriptions are FIBRED:
> `D : Π (El I) (Desc I)` — see "Stage F" below; it revises stages 1–4).
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

## ★ Stage F — the FIBRED form (D074, 2026-09-26)

Found while porting the examples (stage 4): with `D : Desc I` EVERY
constructor Fords its index, so syntaxes (`Scoped`, the Knot's depth) pay a
`jsub` per recursive field in every index-dependent consumer. The fibred
form is the definition (fibres of the target map), Fording its `Id`-encoding.

Kernel delta (everything else unchanged):
- `dι` is NULLARY; `dpay I D C` loses its index (`dpay-ι ⟶ ⌜Unit⌝`,
  `dpay-ρ ⟶ ⌜Σ⌝ (⌜IMu⌝ I D j) (wk …)`, `dpay-σ` as before);
- `D ∷ Π (El I) (Desc I)` in `ty-IMu`/`⊢⌜IMu⌝`/`⊢con`/`⊢ielim`/`⊢dih`/
  `ty-DIh`/`⊢dpay`; `⊢con`: `p ∷ El (dpay I D (app D i))`;
- ι: `ielim D i e (con p) ⟶ e i p (dih D e (app D i) p)`;
- `MethTy`: payload `dpay … (app D' (var vz))`, hypotheses at `app D'' i`;
- `⊢dih`/`ty-DIh` lose the index premise (the payload no longer mentions it).
LR: `⊩₀IMu` stores `⊩I` and `(j : RTm Γ) → ⊩I ⊩₀∋ j → IKInterp ⊩I (app D₀ j)`
(the `⊩₀Π` induction–recursion pattern: `⊩₀∋` negative, `IKInterp`
positive); the type's own index validity is stored too. `IKPred` takes the
index predicate `PI`; `ikp-ρ` stores `PI j`; `IMuMem PI KP i q t` with
`imm-con : ILift (KP i q) (IMuMem PI KP) p → IMuMem … i q (con p)`.
Lib: `Dₗ Cs = lam (dσ (⌜Fin⌝ c) (selF Cs))` with `Cs` over `Γ ∙` (the index
in scope); `Tel` over `Γ ∙`, `tι` nullary. Vec gets an explicit `⌜Id⌝` Ford
field; Scoped is Ford-free.
Order: Spec (Syntax/Typing/Variance/Annotated/TypingA via genA.py) → stage-2
modules in the same order as before → Sugar/Tel/TelFold/ICast/IHeadRed/
CongMacro → Vec, Scoped, ScopedDepth → continue stage 4.

### Stage F — log (2026-09-26/27)

- ✅ Spec, all of Metatheory (incl. Confluence, LR, Fundamental, NormTy,
  Canonicity, Erasure, Premises), all of Algorithm — green.
- LR: `⊩₀IMu` stores representatives `I ≅ I₀`, `D ≅ D₀`, `i ≅ i₀`, the
  validity of `i₀`, and a FAMILY `j ↦ IKInterp (app D₀ j)` over valid
  indices (the `⊩₀Π` IR pattern — positivity accepted). `IKPred` takes the
  index-validity predicate; `ikp-ρ` stores its index's validity; `IMuMem`
  is indexed by a valid index. No membership is ever transported between
  different terms (the fibres are joined, `app D i ⟶* app D* i*`).
- `Premises.MethG` takes the telescope OVER the index (`C : RTm (Δ ∙)`);
  `MethTy` is its instance at `app (wk D) (var vz)`.
- Sugar: `Dₗ Cs = λ i. dσ (⌜Fin⌝ c) (selF Cs)`; `⊢methσ` proves the one
  method at the open fibre, `⊢methₗ` is one β from it.
- Examples: `Vec` Fords EXPLICITLY (an `⌜Id⌝` field per constructor);
  `Scoped`'s syntax is FORD-FREE again (`lamT = tρ (suc n) tι`);
  `Fin` Fords explicitly.
- Tooling lesson: `fixusing.py` now follows `open … public` (it had pruned
  re-exported names — the lint-imports blind spot).

## ★ Stage 5 design — the Knot fibred by SORT (D075, 2026-09-27)

- Index `SortI ⌜Nat⌝ 2`: sort ∈ {Ty, Tm} (a `⌜Fin⌝` code), depth riding.
  `Var` is the nested `Fin` family (a σ-field `⌜IMu⌝ ⌜Nat⌝ FinD d`); it
  FORDS its own depth, as `Examples/Scoped`'s `Fin` does. The old
  Desc/DCon/IDesc/ICon sorts are gone: descriptions are terms (D072).
- No sort Ford: `Dₛ` presents the fibres (`Lib/Sorted`); methods are typed
  at `pair (tag s) j` (`Lib/MethAt`, `Lib/TelAt.entₛ`).
- Stage-4 status: every example is ported. `ScopeHazard` is retired
  (D079). `Mutual` is the sorted-family exemplar.
- Before-metrics (commit 1a98d1bf): 201 Knot modules, 74 494 lines,
  12 474 top-level signatures; 3 854 lines of `Lib/I*`; `gen-knot.py` 7 303
  lines.

### Stage 5 — log (2026-09-27)

- ✅ Library stack for sorted families: `Lib/MethAt`, `Lib/Sorted`,
  `Lib/TelAt`, `Lib/TelFoldS`. `Examples/Mutual` is its client.
- ✅ `tools/gen-knot.py` rewritten: 400 lines, down from 7 303. Rows are
  parsed from `Spec/Syntax`: 51 (13 Ty, 38 Tm). It emits:
  - `Knot/Desc`: the family, no Fords;
  - `Knot/Ctors`: typed at every depth, 14 s;
  - `Knot/Terms`: the typed quotation of the whole syntax, 7 s.
- ✅ Deleted as superseded: the old Knot (201 modules), `Lib/I*` (12),
  `ScopeHazard`, `Negative/WkK`, `Negative/WkEmp`. Sweep ALL GREEN at 155
  modules (before `Terms`).
- Lesson: pin `{Tss}{Ts}{T}` at concrete `⊢conₛₜ` uses; inferred, one row
  cost 16.5 s instead of 0.12 s.
- ✅ The syntax's operations, generic (`Lib/Syn`, `Lib/SynView`,
  `Lib/SynTrav`, `Lib/SynTravM`, `Lib/SynRen`, `Lib/SynSub`): one
  traversal per signature and kit. Renaming, weakening, substitution and
  `sub0` are all typed. `CONS` (`(ρ , u)`) is the σ-calculus primitive,
  and `LIFT`/`SINGLE` are its instances. Instantiated for the Knot in
  `Knot/Sig` (generated), `Knot/Ren`, `Knot/Sub`.
- ✅ `Knot/Ctx`: contexts fibred over the depth (NatFib), with typed
  `quoteCtx`. ✅ `Knot/Sz`: `⊢foldₛ sizeAlg` at the Knot signature.
  ⬜ Its adequacy on `quote`.
- ✅ D077 (decision log): judgement families are FIBRED BY THEIR SUBJECT,
  with a Ford only for computed outputs, one family per mutual block.
- ✅ `Knot/Lookup` + `Knot/LookupCon`: `Γ ∋ x ∷ A` complete. The fibre
  computes and both constructors are typed (64 s after the β-chain fix;
  memory `beta-chains-cast-each-step`).
- ✅ `Lib/SynFib`: a family fibred by case on a SYNTAX term, generic in the
  signature. Rows are natural families `R j p c` typed at any terms. The
  fibre method, its typing, its computation rule (`fib-β`) and its
  closedness are each proven ONCE (8.5 s).
- ✅ `gen-knot` emits `Knot/Ctors`: the 51 formers typed at any depth.
- 🟡 `Knot/Judge`: `⊢ty`/`⊢` as ONE family over both sorts, with a
  sort-dependent convoy (`Γ`, plus `A` for terms, by `fcase`). The
  family is well formed (`⊢D⊢`) and the fibre computes (`fibK`).
  Constructors `⊢ty-base` and `⊢ty-Π` are typed. 12 of 13 `⊢ty` rows are
  done (⬜ `DIh`: its index code is a σ-field).
- ★ Lessons (memory `knot-description-normalisation-trap`,
  `beta-chains-cast-each-step`, `agda-profile-script`). Every unpinned
  implicit, and every renamed type that mentions `KD`, normalises the
  whole description. A chain of `β _ _` builds substitution towers.
  `tools/agda-profile.sh` finds both.
- ✅ (2026-09-27/29) The judgement layer's FAMILIES, generated by
  `tools/gen-judge.py` from rule tables (D077/D078), every one fibred by its
  subject on `Lib/SynFam`/`Lib/SynFib`:
  - `⊢`: all 13 `⊢ty` and 38 `⊢` term heads (`Knot/JudgeRowsGen`), plus
    `⊢conv` in every term fibre (`Knot/JudgeConv`), one parametric row
    typed once. A pattern in the conclusion type is a case. A computed
    output Fords. A pattern under a binder Fords (D078).
  - Side conditions as lower-stratum families: `NoNatC`, `stkA?`, `stkC?`
    and `flat?` (`Knot/Preds`), and `pwBody`'s graph on `pw?` codes
    (`Knot/Pw`), whose convoy holds the body one binder deeper.
  - `⟶`/`⟶ᵀ` (`Knot/Red`, `Knot/RedT`): the ξ rows are derived from the
    signature. All 32 `⟶` and 17 `⟶ᵀ` computation rules are NESTED
    SUBJECT CASES (`Knot/NestIx`: the convoy is a stack of the payloads
    met so far); `ordtr` and `Hom-Nat` nest three levels deep.
    `natrec-suc` and `psplit-β` use the sort-1 double instantiation
    `iinstTmK`, `tr-pw` uses `pwShK` and `DIh-ρ` uses `wk2uK`
    (`Knot/SubEnv`).
  - `≅`/`≅ᵀ` (`Knot/Conv`): the rules have a bare-variable subject, so
    each is one parametric fibre.
- ★ Lesson: context-form mismatch (memory `context-form-mismatch-opaque`).
  A big closed code elaborated at two context forms is compared by
  normalising it. Every such code is OPAQUE: `sub0`, `wk`, `FIBMₒ`,
  `⌜Ty⌝`, `⌜Tm⌝`, the SubEnv operations, every family's `⌜·⌝` code, and
  SynPat's `CASE`. Typings are goal-directed: contexts flow from the goal
  and only terms are pinned (`okσJ`, `wkK`/`wkN`/`wkG`).
- ✅ (2026-09-29) CONSTRUCTORS for every rule of every family:
  - Generated: `Knot/JudgeConGen` (13 `⊢ty`, 37 `⊢`, 38 `⊢conv`) and
    `Knot/RedConGen` (99 `⟶`, 36 `⟶ᵀ`, 2 `Pw`).
  - Hand-written: `Knot/JudgeConFin` (fzero, fsuc) and `Knot/ConvCon`
    (the four `≅`/`≅ᵀ` rules, each ONCE for every head).
  - Each row telescope is a chain of TAILS `N⁽ᵏ⁾` with their own laws.
    A constructor builds its payload at VALUES. The source form is read
    at the values by ONE `mono-by` (`Lib/SynRed`: a substitution-natural
    object is ⟶*-monotone), fed by `prj-tup` per position. Case and
    nested rows prefix CASE-⟶ᵃ/CASE-⟶ᶜ/case-β per level.
  - The `⊢ty` rows are generated too; every hand row and hand
    constructor they replace is deleted.
- ✅ D079: `scopeAt` over Tel is NOT built. No level-comparing fold
  remains, and Shapes cannot express a closed-index child.
  `ScopeHazard` stays retired.
- ⬜ Remaining: Stage 6 metrics.

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
