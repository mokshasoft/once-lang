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

### F6 — log

- 🟡 (2026-10-03) F6.0 `Lib/Decode` and F6.1 `Lib/SynDecode` written
  (closed-normal inversion: `con-dec`, `pay-ι/σ/ρ`, `tag-dec`,
  `idrefl-dec`, the generic `Tel` decoder `tel-dec`; a syntax term is
  `conₗ k p` with `DArgs`).
- ★★ (2026-10-03) **F6 found a KERNEL gap on day one: `Unit` was not
  canonical.** `hrefl ⌜Nat⌝ nzero : Hom Nat 0 0`, which `Hom-Nat-z`
  computes to `Unit`, but no rule reduced the `hrefl`: a closed NORMAL
  inhabitant of `Unit` other than `unit`. `Canonicity.canView` had
  recorded it as an allowed escape (`HomHd hUnit`), so no metatheorem
  was false — the STRONG statement (data has exactly its constructor
  forms) was simply never made. Consistency never needs it; adequacy
  does (decoding cannot read junk back as syntax), and so would every
  Knot payload tail (`dι` ⇒ `⌜Unit⌝`).
  - **Fix (kernel, branch `ocp-0009-hrefl-nat`):** `hrefl-Nat-z :
    hrefl ⌜Nat⌝ nzero ⟶ unit`, `hrefl-Nat-s : hrefl ⌜Nat⌝ (nsuc m) ⟶
    hrefl ⌜Nat⌝ m` — the order's reflexivity computes in lockstep with
    its type. Left-linear, type-preserving, no overlap (`⌜Nat⌝` is
    neither `pw?` nor `stkC?`).
  - **Through the metatheory:** SR, Confluence (`HrV` view in the
    development), Injectivity, the LR (new key `hstk?` = `nopw?` ∧
    (`natstk?` arg ∨ `natcstk?` code); `natcstk?` = "never becomes
    `⌜Nat⌝`"; three weak-head steps, `natrec`'s shape), Fundamental
    (`snHNat`, `goN`/`goN₀`/`goNh`), `Eval` (`hreflN`), the Knot's two
    `⟶` rows + `RedAgree`.
  - ★ **New kernel theorem `Canonicity.canUnit`**: a closed normal
    inhabitant of `Unit` IS `unit`. Strong data canonicity is now a
    stated kernel invariant, not an F6 lemma.
  - ✅ Cold sweep ALL GREEN (230 modules, 3 064 s); `ocp-0009-stepext-once`
    fast-forwarded to `6c08c54f6` (2026-10-04), branch deleted.
- ✅ (2026-10-04) F6.2 DONE — `Lib/SynUnq` (100 s cold, 4.9 GB with its
  closure) and `Knot/Unquote` (39 s) check. Branch `ocp-0009-f6-unquote`
  (ff into `stepext-once` after the next cold sweep). Four fixes on the
  first check, all elaboration: a generalized constructor index is not
  nameable (bind it through the shape), argument order, `⌜ Ts ⌝ₛ` is not
  injective (pin `FinTs`), generalized `Θ` precedes `i``.
  - `Lib/SynUnq` (generic): the signature's syntax as an Agda datatype
    `STm sg s d`, its quotation `⌜_⌝ˢ` (the Knot's own encoding),
    `⌜⌝ˢ-inj` (structural), `nat-unq`/`fin-unq` (numerals, variables via
    `Lib/FinFam`'s fibres), and `syn-unquote`: a closed normal
    `SK sg s (num d)` term IS `⌜ x ⌝ˢ` — by fuel on `sz`.
  - `Knot/Unquote` (generated by `gen-knot.py` from the quotation's
    rows): `fromTy/fromTm`, `toTy/toTm`, three structural round trips,
    and the theorems `unqTy`/`unqTm` (closed normal Knot terms are
    quotes) and `quoteTy-inj`/`quoteTm-inj`.
  - Design point: ALL typing is generic (Lib); the Knot bridge is purely
    structural, so the generator emits no proofs about typing.
- ✅ (2026-10-04) F6.3 generic + the `Pw` PILOT: `Knot/PwDecode.decPw` —
  a closed normal `KPw (dep Γ) ⌜c⌝ ⌜b⌝` inhabitant gives `pw? c ≡ true`
  and `b ≡ pwBody c`. With F4's `⊢pwC` the Knot's `Pw` is EXACTLY the
  Spec's `pw?`/`pwBody` (15 s).
  - Lib: `rows-dec`/`rows-none` (a fibre of rules: one rule and its
    payload, or nothing), `nf-≅` (convertible normal forms are equal),
    `⌜⌝ˢ-normal` → `quoteTm-normal`.
  - Each row is decoded along its FORWARD constructor (`PwConGen`): the
    same `mono-by` reduction of the row's telescope to its values, the
    same β-casts, the payload peeled by `pay-σ`/`pay-ρ`, each identity
    proof closed by `nf-≅` + quote injectivity + the F3 agreement.
  - ⚠ Measured trap: `with` over a decoder's result in these contexts
    runs out of memory (> 5 GB); the same call as an ARGUMENT checks in
    8 s. Decoders are chains of helpers with stated types (`RowsDec`,
    `PayΣ`, `PayΡ`), never `with`.

- 🟡 (2026-10-04) NEXT: the reduction families `⟶` (67 ξ + 32 computation
  rules) and `⟶ᵀ` (36), then `≅`/`≅ᵀ`, then `⊢ty`/`⊢`. Design (decided):
  - decoders are GENERATED from the constructor generator's own state
    (`gen_con` records, per rule, the row entry at the sources, the value
    telescope and its `mono-by` R₀, the existentials, premises and Ford
    entries), so a decoder cannot drift from its constructor;
  - each rule's decoder is ONE expression chained with `x ▷ f = f x` and
    pattern lambdas (measured: `▷` chain 14.5 s, no `with`, no per-step
    signature) — existentials are unquoted and transported by `subst`, not
    matched (a nested lambda cannot refine an outer variable);
  - the Spec side of each rule comes from the forward map's own tables
    (ξ: parsed from `Spec/Typing`; computation: `RED_COMP`, whose agreement
    `TARGET ⟶* ⌜RHS⌝` closes the Ford by `nf-≅` + quote injectivity);
  - a NESTED pattern (β's `lam`, ordtr's numerals, …) is decoded by a
    generic "a CASE hit forces the head" lemma (`fib-β` + `rowAt-elim`:
    any other head's row is `noRow`, empty) and a generated head view of
    Spec terms (`hdTm`, `quoteTm t ≡ conₗ (hdTm t) …`, `is⟨H⟩`).

### F6 — FINDINGS LEDGER (what the invariant caught)

| # | date | where | finding | fix |
| --- | --- | --- | --- | --- |
| 1 | 2026-10-03 | KERNEL (`Spec/Typing`, metatheory) | `Unit` not canonical: `hrefl ⌜Nat⌝ nzero` a closed normal non-`unit` inhabitant (a junk tail in every Knot payload) | `hrefl-Nat-z/s` + `canUnit` |

Families decoded with NO finding (exact both ways):
- `Pw` (2 rules; `Knot/PwDecode`, hand-written pilot);
- `NoNatC`, `stkA?`, `stkC?`, `flat?` (24 rules; `Knot/PredsDecode`, GENERATED
  by `gen-judge.py` from the same `PREDS` table as the rows — 39 s).
- `∋` (2 rules, `here`/`there`; `Knot/LookupDecode`, hand-written along
  `⊢here∋`/`⊢there∋` — 9 s).


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
