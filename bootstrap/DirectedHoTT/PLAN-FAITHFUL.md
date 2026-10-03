# PLAN-FAITHFUL — the Knot's judgements are FAITHFUL (`enJudge`)

> Opened 2026-09-29, after PLAN-LEVITATION Stage 6. Branch
> `ocp-0009-levitation` (no rebase for now).
> ✅ **F1–F5 DONE 2026-09-30** (commit `4e6e46904`). 🟡 **F6 (decoding, the converse) opened 2026-10-02; started 2026-10-03, BEFORE PLAN-BIDI S7b (user).** Next: PLAN-BIDI, after
> PLAN-LEVITATION's clean measurement (`HANDOFF-2026-10-02.md` §4).

## Goal

Type-checking proves the Knot's rows WELL-FORMED, never that they encode the
right rules (memory `typechecking-cannot-see-an-encoding`,
JUDGEMENT-ATTEMPTS §13: a row encoding the WRONG rule typechecks). The tier
that closes it is an **adequacy map**: every real derivation maps to a Knot
inhabitant AT THE QUOTED JUDGEMENT.

    enTy : Γ ⊢ty A     → Θ ⊢ ⌜d⌝ ∷ K⊢ (tyIx (dep Γ) ⌜Γ⌝ ⌜A⌝)
    enTm : Γ ⊢ t ∷ A   → Θ ⊢ ⌜d⌝ ∷ K⊢ (tmIx (dep Γ) ⌜Γ⌝ ⌜t⌝ ⌜A⌝)
    (and ∋, ⟶, ⟶ᵀ, ≅, ≅ᵀ, the side-condition families)

The target NAMES the index, so a row meaning something else is a type error.
The constructors (PLAN-LEVITATION Stage 5, `*ConGen`) are the building blocks.
The quotation exists (`Knot/Terms`: `quoteTy`/`quoteTm`/`quoteCtx`).

## The obstacle, known from the old Knot (PLAN-RENAMING §16)

A constructor's index uses Knot OPERATIONS (`⊢app` concludes at
`sub0 0 j ⌜B⌝ ⌜u⌝`), whereas the quoted judgement has `⌜B[u]⌝`. The two meet
by **agreement**, `sub0 … ⌜B⌝ ⌜u⌝ ⟶* ⌜subTy (single u) B⌝`, and then
`⊢conv` on the index. There is no `⌜σ⌝` for a Spec `Sub` (an Agda
function), so an encoded substitution is RELATED:

    Represents σ s  =  ∀ x → app s ⌜x⌝ ⟶* ⌜σ x⌝

⚠ Lesson (§16.2): agreement over a library is provable only if the library
ships REDUCTION lemmas for its methods. `Lib/SynTrav` ships typings only.

## Steps

| | step | what |
| --- | --- | --- |
| F1 | `Lib/SynTravRed` | `trav` COMPUTES at a node and at a variable, generic in the signature (template: `SynFib.fib-β` via `Sorted.ιₛ-red` + `βcast`; then `dih` over the payload so each field is the child's `trav`) |
| F2 | `Knot/SubAgree` | `Represents σ s → trav ⌜t⌝ s ⟶* ⌜subTm σ t⌝`, by induction on the Spec syntax, one case per former (generated) |
| F3 | op agreement | `sub0`, `wk`, the SubEnv ops (`nrsK`, `pairSK`, `fsucSK`, `methSK`, `lift2K`, `iinstK`, `MethTyK`, `iinstTmK`, `pwShK`, `wk2uK`): Represents for CONS/LIFT/WK environments |
| F4 | side conditions | the `Preds` families and `Pw` are COMPLETE for Spec's `NoNatC`, `stkA?`, `stkC?`, `flat?`, `pw?`/`pwBody` |
| F5 | `enJudge` | mutual maps from Spec derivations through the constructors; F2/F3 bridge indices by `⊢conv` |
| F6 | 🟡 **decoding** (adequacy, the converse) | every CLOSED Knot inhabitant at a quoted judgement comes from a Spec derivation — see below; NOW, before PLAN-BIDI S7b |

## ⬜ F6 — the OTHER half: decoding (opened 2026-10-02)

F1–F5 prove the quoted Spec sits INSIDE the Knot: a Knot rule too weak, or
of the wrong shape, to express a Spec rule fails `enTm`. Nothing yet
rules out a rule that is TOO PERMISSIVE: an extra row, or a missing side
condition, typechecks and passes F5. The full invariant, the standard
adequacy of an encoding, is both directions:

    (Γ ⊢ t ∷ A)  ↔  inhabited (K⊢ (tmIx (dep Γ) ⌜Γ⌝ ⌜t⌝ ⌜A⌝))      at CLOSED Knot terms
    (likewise ⊢ty, ∋, ⟶, ⟶ᵀ, ≅, ≅ᵀ, the side-condition families)

- **Why (user, 2026-10-02):** "the Knot/Dogfooding is the same as the
  original Agda Spec". With both directions each row is pinned EXACTLY
  (too weak breaks F5, too strong breaks F6), so the invariant guides
  the proofs. It also makes "Once-in-Once is the Spec" a theorem, which
  the dogfooding exhibit (PLAN-JUDGEMENT step 4) needs. And it is how
  hand-written Knot rows (PLAN-BIDI S7b onwards) are justified without
  trusting a generator.
- **Route:**
  - CANONICITY (`Metatheory/Canonicity`) turns a closed inhabitant of
    `IMu JT D⊢ i` into a `con`-tree.
  - Induction on that tree, row by row, back to a Spec constructor.
    Subject reduction keeps the tree's typing.
  - The agreements are used BACKWARDS: from `op ⌜x⌝ ⟶* ⌜y⌝` recover
    `y` as the Spec operation, via unique normal forms (`Algorithm/Eval`,
    `nf-irr` plus Church–Rosser) and injectivity of quotation.
- **Scope:** closed Knot terms only. Open ones (free variables in `Θ`)
  are not adequate in general, as usual for such theorems.
- **Expected cost:** inversion on closed `IMu` inhabitants per row, plus
  the backward agreements. Real, but no kernel change.
- **When:** ★ **NOW (user, 2026-10-03), before S7b:** "adding invariants
  that shape and limit is always good". F6 is the oracle the S7b
  migration runs against: a hand-written family is done when F5 AND F6
  hold for it. Decoding proofs of generated rows will be rewritten when
  their family migrates; that cost is accepted.

### F6 stages (2026-10-03)

Statement shape, per family (closed Knot terms, `◇`):

    decTm : ◇ ⊢ k ∷ IMu JT D⊢ (tmIx (dep Γ) ⌜Γ⌝ ⌜t⌝ ⌜A⌝) → Γ ⊢ t ∷ A
    decPw : ◇ ⊢ k ∷ ⌜Pw⌝-family at (⌜c⌝, ⌜b⌝)          → pw? c ≡ true × pwBody c ≡ b
    (likewise ⊢ty, ∋, ⟶, ⟶ᵀ, ≅, ≅ᵀ, the Preds families)

The core is stated on NORMAL closed inhabitants and recurses on `sz`
(the `Canonicity.prog` pattern); F6.6 wraps it with `wnorm` + SR.

| | step | what |
| --- | --- | --- |
| F6.0 | `Lib/Decode` (generic) | closed-normal inversion: `con-dec` (at `IMu I D i` a closed normal is `con p`, `p` normal at `El (dpay I D (app D i))`); `pay-dec` (at `dpay I D C` with `C ⟶*` `dι`/`dσ S f`/`dρ j C'`: `unit`/`pair a b`, each normal and typed); tags (`⌜Fin⌝ c` ⇒ `tag k`, `k < c`), `FinI d` ⇒ a numeral below `d`, `⌜Nat⌝` ⇒ a numeral, `⌜Id⌝ c a b` ⇒ `idrefl`, `a ≅ b` |
| F6.1 | `Lib/SynDecode` (generic) | a closed normal `SK sg s ⌜d⌝` is `conₗ k p` with `p`'s fields as normal `Args` — the converse of `⊢payArgsF` |
| F6.2 | `Knot/Unquote` | closed normal `⌜Ty⌝`/`⌜Tm⌝`/`Ctx` inhabitants ARE quotes (a 51-way dispatch on the tag, generated with the quotation); quotes are normal; `⌜x⌝ ≅ ⌜y⌝ → x ≡ y` (Church–Rosser + normality + injectivity) |
| F6.3 | `Lib/SynFibDecode` (generic) | a closed normal inhabitant of a `SynFib` family at a subject of head `k` is one of `k`'s rows, with its payload — the converse of `fib-β` + `⊢conRow` |
| F6.4 | backward agreements | `op ⌜x⌝ ≅ ⌜y⌝ → y ≡ op x` for every F3 operation: forward agreement + F6.2 injectivity |
| F6.5 | per family, bottom-up | `Pw` and `Preds` (F4⁻¹) → `∋` → `⟶`/`⟶ᵀ` → `≅`/`≅ᵀ` → `⊢ty`/`⊢` (F5⁻¹): each row's payload back to its Spec constructor |
| F6.6 | the wrapper | an arbitrary closed typed `k`: `wnorm`, SR, then the normal decoder |

**Pilot: `Pw`** (two rows, no dependency on other families, and S7b's
pilot too). It drives F6.0–F6.3 end to end before any big family.

## Log

- ✅ F1 (2026-09-29) `Lib/SynTravRed`: `trav-con` (a fields node reduces to
  `conₗ k (tpayT …)`, every recursive field the child's own `trav` at
  `nsucs k d` with the environment `LIFTS`-lifted) and `trav-var` (the
  variable node reduces to `NODE e (f (fst p))`).
  - Generic in the signature. It ASSUMES `LIFT-sub`/`NODE-sub` (the kit's
    closed codes; `refl` at a concrete signature) as module parameters.
  - Built from `Sorted.ιₛ-red`, `fibₛ-β`, `SynView.dihV-red` and one
    generic `β4`. Checks in 14 s.
- ✅ F2 library half (2026-09-29) `Lib/SynTravRed` §4: ENVIRONMENTS
  COMPUTE, generically. `cons-z`/`cons-s` (`(f , u)` at zero is `u`, at
  `fsuc y` it is `f y`) and `lift-z`/`lift-s` (the lifted environment
  gives the fresh variable, or the old value weakened by `WK`).
  - New pieces: `consM-sub`, `FinD-sub` (`refl`) and `β3`.
  - The kit's `V0`/`WK` closedness is a module parameter (`refl` at the
    Knot).
- ✅ F2 (2026-09-29) `Knot/RenAgree`, `Knot/SubAgree`, both GENERATED by
  `gen-knot.py` from the same rows as the quotation (they cannot drift):
  - `ren-agree-{ty,tm} : RepR ρ f → trav s ⌜t⌝ f ⟶* ⌜renTm ρ t⌝`;
  - `sub-agree-{ty,tm} : RepS σ f → trav s ⌜t⌝ f ⟶* ⌜subTm σ t⌝`.

  Each covers all 51 formers. Each case is `trav-con` followed by one
  `fld-rec` (the IH, the environment lifted `k` times) or `fld-nat` per
  field. The `RepS` lift at an old variable IS renaming agreement at `vs`
  (`repR-wk`). The two modules check in 20 s and 23 s.
- ✅ F3 core (2026-09-29) `Knot/OpAgree`.
  - Every environment REPRESENTS its Spec substitution. These are the
    substitutions' own clauses read back: `single`, `nrs`, `pairS`,
    `fsucS`, `methS`, `single2` (what `iinst` composes to), `pwShift` and
    the weakenings.
  - Every operation AGREES: `sub0`, `wk`, `nrsK`, `pairSK`, `fsucSK`,
    `methSK`, `iinstK`, `iinstTmK`, `pwShK`, `wk2uK`, `lift2K`.
  - Renamings used as substitutions are bridged by `subTy-var`. The module
    checks in 7.5 s.
  - ✅ …and the composite codes the rows' indices cite: `DF` (`DescF`), `mc`
    (`motCtx`) and `MethTyK` (`MethTy`). They are the agreements above,
    threaded through constructor positions (`node-1/2/3`). F3 is done.
- ✅ F4 (2026-09-29) the side conditions are COMPLETE, all generated:
  - `Knot/PredsCon`: constructors for all 24 side-condition rows, by the
    `JudgeConGen` scheme.
  - `Knot/PredsAgree`: `NoNatC c`, `stkA? c ≡ true`, `stkC? c ≡ true` and
    `flat? c ≡ true` each map to a Knot inhabitant at `⌜c⌝`. A true head
    builds its row, a false head is absurd. This is the "mirrored clause by
    clause" claim, checked.
  - `Knot/PwAgree`: `pw? c ≡ true` maps to `Pw` at `⌜c⌝`, `⌜pwBody c⌝`.
    The Knot's `wk` in the ⌜Hom⌝ body is bridged by F3's `wk-agree`.
  - `⊢payK` moved from `Judge` to `JudgeIx`, so constructor modules no
    longer import the whole ⊢ family.
- ✅ F5 (2026-09-30) `enJudge`: every Spec judgement maps to a Knot
  inhabitant AT THE QUOTED JUDGEMENT. The target names the index, so a row
  that encodes a different rule is a type error.
  - `Knot/RedAgree`, `Knot/RedTAgree` (generated by `gen-judge.py`): `⟶`
    (67 ξ + 32 computation rules) and `⟶ᵀ` (36). ξ rows come from parsing
    `Spec/Typing`. A computation rule's Knot target meets the Spec's by F3.
    The Spec's reduction constructors take the generalised `Γ` as their
    FIRST implicit, so the patterns start with `{_}`.
  - `Knot/QView` (generated by `gen-knot.py`): a quoted term is a node —
    head, payload, payload typing, `eq = refl`. `Knot/ConvAgree` uses it
    for `≅`/`≅ᵀ`, whose Knot rows are generic in the subject's head.
  - `Knot/LookupAgree`: `∋`. The row states the type as `wk 0 m ⌜A⌝`, and
    the Id-premise is converted by `wk-agree-ty`.
  - `Knot/TypingAgree`: `⊢ty`/`⊢`, all 13 + 40 rules. Most are EXACT. Where
    a row states a type through an operation (`sub0`, `wk`, `nrsK`, `DF`,
    `mc`, `MethTyK`, `iinstK`, …), F3's agreement converts the index:
    premises backwards, the conclusion forwards.
    - `⊢tr`: the row takes the motive's code and base point STRENGTHENED
      (`c[t]`, `a[t]`). `strength` shows that `renTm vs (c[t]) ≡ c` when
      `vz` does not occur, and `wk-cancel-tm` moves the endpoints.
    - `⊢conv` dispatches on the subject's head through
      `Knot/ConvHead.convAt` (generated, 38 clauses): the Knot's conversion
      rows are per head.
