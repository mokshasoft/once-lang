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

## Stage 2 — progress (2026-09-26)

- ✅ `SubjectReductionBase`, `RedCong`, `TySub` (committed).
- `Confluence`: rows done; ⚠ the family cloner's `NEW` list omitted `pcon`
  (the old `Mu` already had a `pcon`), so every family missed its `pcon`
  row — re-cloned for `pcon` alone. A cloned family member can itself be a
  REDEX row (`pielim … (pcon _)` is ι): drop it, the explicit redex row wins.
- `Injectivity`: `IMu-inj` gives three CONVERSIONS; `Desc-inj`, `Fin-inj`.
- `SubjectReduction`: generation lemmas for every levitated former; ι by
  `IMu-inj` + one payload transport + σ-calculus (`meth-inst`, no η);
  `dσ-step`/`dρ-step` (the payload's two halves) shared with `Validity`.
- ★ KERNEL FINDING (SR + Validity): every telescope former and `dpay`
  carries `Γ ⊢ I ∷ U`. `dpay-ι`'s reduct `⌜Id⌝ I j i` needs it, and
  `validity` of `dι j ∷ Desc I` needs it; the other premises give `I` only
  under `El`/`Desc`, i.e. up to conversion, and `El I` may DECODE. This is
  the levitation paper's rule shape (the index type is a premise).
- ★ KERNEL FINDING (Fundamental): `⊢⌜IMu⌝` also types `Γ ⊢ I ∷ U`. The CODE
  `⌜IMu⌝ I D i` contains `I`, so `fund` owes `SN I`; a type's semantic
  witness (`⊩₁Desc`, `⊩₁ne`, …) carries no SN of the terms inside the type.
  The rule shape is now uniform: every former types each term it CONTAINS.
- ★ KERNEL FINDING (NormTy): a premise in an EXTENDED context presupposes
  the extension — the convention `⊢lam`/`ty-Π` already follow (`⊢ctx`'s
  comment). `ty-DIh`, `⊢dih`, `⊢ielim` (premise `motCtx Γ I D ⊢ty M`) now
  type `Γ ⊢ I ∷ U`; `⊢psplit` (premises in `Γ ▹ Σ' A B`, `Γ ▹ A ▹ B`) types
  `A` and `B`. `validity` gives `Desc I` only up to conversion and there is
  no subject expansion, so `I ∷ U` is NOT recoverable from `D ∷ Desc I`.
- ★ NormTy is SUBSTITUTION-PARAMETRIC (`normTyS : … → Sub⊢ Γ Δ σ →
  WNᵀ (subTy σ A)`). `DIh-ρ` exposes the motive's instance
  `iinst j (fst p) M`; stating the theorem at every substitution keeps the
  recursion on the formation derivation structural. `DIh-σ`'s
  `app f (fst p)` has no syntactic measure: `dihNF` recurses on a `Walk`
  (the syntactic shadow of `dihTy`, read off the LR at `vs` by
  `dih-walk`, anti-renamed), generalised over a RENAMING so `DIh-ρ`'s
  second component is the same walk one scope out.
- ★ LR design change, measured necessary: `⊩₀IMu`/`⊩₁IMu` interpret a
  CONVERTIBLE REPRESENTATIVE (`I ≅ I₀`, `D ≅ D₀`). Interpreting the reduct's
  own slots would make `fwd₀` transport an interpretation along an
  arbitrary reduction of a TERM, which head expansion cannot do.
- ✅ `Validity`, `DecEq`, `DecideConversion`, `Injectivity`, `SubjectReduction`
  green after the `motCtx`/`psplit` premise change (committed).
- `Canonicity` REWRITTEN around ONE lemma (2082 → 1477 lines): inert type
  heads survive reduction (`inert-conv`), every canonical form but `hrefl`
  has an inert-headed type (`canTy`), and `canAt` hands a consumer at an
  inert type only its head's introduction forms — Agda's coverage refutes
  the rest. The pairwise clash matrix (~50 lemmas) is gone; each levitated
  eliminator's progress row is one `canAt` match. `hrefl`/Hom consumers use
  `homCan` (a `Hom` reaches only Hom/Π/Unit/base).
- `CheckA`: descriptions are terms, so EVERY former now infers (PLAN-BIDI
  §3d dissolved). New facts the checker needs: `MethTy-wf` (the method
  type is well-formed), `pairS⊢`, `fsucS⊢`, `motCtx-wf`. `liftTy`/`liftTm`
  regenerated from `tools/genA.py`'s field table.
- `Check` (RTm slice 1): `evTy`/`unEl` rows for `IMu`/`Desc`/`⌜Fin⌝`; it
  depends on `Lib/Eval`, so it compiles with stage 3.
- `LogicalRelation` ✅ (committed). `Fundamental/Indexed` rewritten:
  `payInterp₀`, `liftPay₀`/`payLift₀` (definitional — `ILift` is written in
  `⊩₀Σ`/`⊩₀Id` shape), `dihTy`, `sn-dpay` (SN under the binder by `sn-body`
  at `x₀`), and `ElimSem` — the eliminator, NOT mutual with `fund`
  (induction on the membership; the hypotheses are its mutual `dihSem`).
- `psplit` in `fund`: Σ's semantics is projection-based, so the case
  inspects the scrutinee's SN derivation (pair ⇒ fire, neutral ⇒ stuck,
  head step ⇒ expand, any other canonical form ⇒ its `fst` is not SN).

### LogicalRelation design (the stage's biggest unknown)

- `⊩₀IMu : A ⟶ᵀ* IMu I D i → (⊩I : ⊩₀ (El I)) → IKInterp ⊩I D → ⊩₀ A`.
  `IKInterp ⊩I C` (in the ⊩₀ block, S0-accepted shape) walks the
  telescope by WHNF: `iki-ne` (stuck, carries `SN C`), `iki-ι`
  (`C ⟶* dι j`), `iki-σ` (`C ⟶* dσ S f`, `w : ⊩₀ (El S)`, a tail over
  `w`'s MEMBERS), `iki-ρ` (`C ⟶* dρ j C'`, `⊩I ⊩₀∋ j` — index validity is
  what `⊢ielim`'s IH needs at the recursive field). SN at every node.
- Membership `SN t × IMuMem (ikpredsOf K) i t`. `IMuMem`/`IKPred`/`ILift`
  live BEFORE the block and take predicates (the S0 law). The `dι j` leaf's
  payload is `⌜Id⌝ I j i`, so `ILift` there is `SN p × IdPay j i p` —
  exactly `⊩₀Id`'s membership. No uniformity-in-the-index argument is
  needed any more: Fording is now IN the payload.
- `⊩₁Desc : A ⟶ᵀ* Desc I → ⊩₀ (El I) → ⊩₁ A`, membership `IKInterp`
  itself (a level-0 datatype used at level 1 — S0's `toIK` is the identity).
- `DIh` has no clause of its own when the telescope is canonical (it
  REDUCES to `Unit`/`Σ'`); a stuck one gets `⊩₁DIhNe` (membership `SN`).
- `Fin n`: `⊩₀Fin`/`⊩₁Fin` with a `NatMem`-shaped `FinMem`.
- Neutrals: `ielim` (scrutinee key `mustk?`), `dpay`/`dih` (telescope key),
  `fcase`/`fcase0` (tag key), `psplit` (SNe pair). The head steps carry SN
  of what they DISCARD (J–M): `dpay-ι` drops `D`, `dih-ι` drops `D e j p`,
  `dih-σ` drops `S`, `fcase-z` drops `b`, `fcase-s` drops `a`,
  `psplit-β` substitutes `x y` (both SN, as `snr-β`).
- `⊢ielim` in `fund`: induction on `IMuMem` — `imm-ne` ⇒ neutral; `imm-con`
  ⇒ one ι head step, the method's Π-membership at `i`, the payload (via
  the `payInterp`/`ILift` bridge) and `dih`'s membership (recursion on
  `ILift` with the outer IH at `ρ` nodes); `imm-exp` ⇒ expansion.
  A neutral `D` needs NO special case: ι is a head step at any `D` and
  the payload at a stuck telescope is only SN (S1b's result, restated in
  the J–M presentation).

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
