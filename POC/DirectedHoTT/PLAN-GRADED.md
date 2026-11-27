# PLAN-GRADED — the graded dependent judgment (ROADMAP R5)

> Opened 2026-11-27. Sources: `HANDOFF-2026-11-26.md` (why R5 comes before
> the rest of R4), `MASTER-DT-ABSTRACTIONS.md` (each difference from master,
> judged on its merits), master's plan 0.158 (one sorted data former) and
> plan 0.147 §5 (what master asks of this kernel). Decisions to record in
> `docs/compiler/decision-log.md` as they are taken.

## 0. The decision, and the stance behind it

**The kernel's judgment becomes `Γ ⊢[ Ψ ] t ∷ A`, graded by usage
`0 ≤ 1 ≤ ω`. The dependent layer lives at usage 0 and erases completely.
Effects are a grade on the judgment (master's form, decided 2026-11-27),
added when the first effectful former arrives.**

The stance (the user, 2026-11-27): Once is a language in which you write a
program or a library and prove it correct. The kernel keeps NO run-time
information. Types and proofs erase. A run-time representation of some DT
construct may be added later, but it is not the goal. In concrete terms:

- **Types may mention run-time values.** To prove `sort xs` correct, the
  type mentions `xs`. So the kernel holds the programs as well as the
  proofs, and usage tells them apart: types, indices, motives and proofs at
  0, programs at 1 or ω (Atkey's QTT).
- **The extraction test.** *The extraction of a run-time type must not
  depend on any term.* `Σ (n : Nat) (Vec A n)` extracts to `Nat × List A`.
  `Dec P` extracts to `Bool`. `if b then Nat else Bool` with a run-time
  `b` has no extraction: it is allowed in proofs and rejected in programs,
  as are `U`, `El`, `Desc` and codes at run time.
- **Why it is principled.** By Pédrot–Tabareau's fire triangle, dependent
  elimination, substitution and effects cannot all hold. Here types depend
  only on 0-terms, and 0 implies pure (master's `positionGrade`), so the
  triangle never arises. "Types see only pure terms" is a consequence of
  the usage grade, not an extra side condition.

**Naming.** The POC already uses *erasure* for "the annotated kernel means
the unannotated one" (`Metatheory/Erasure.agda`, `⌈_⌉`). Removing usage 0
to reach master's core is called **extraction** in this plan.

## 1. Where we are (read 2026-11-27)

- **The judgment** is ungraded: `Spec/Typing.agda` (375 lines), `_⊢_∷_`
  with 40 term rules from `⊢var` to `⊢conv`, `_⊢ty_`, `⊢ctx_`. The annotated
  kernel is `Spec/TypingA.agda` (`⊢ᴬ`), and `Metatheory/Erasure.agda`
  bridges the two.
- **The metatheory** (`Metatheory/`): subject reduction, confluence,
  canonicity, the logical relation and `Fundamental`, consistency, NbE
  soundness (`Algorithm/NbESound*`), decidable checking (`Algorithm/CheckA`).
  Spec plus Metatheory is about 26.5k lines.
- **Grades:** none anywhere. The simply typed spikes in `POC/OCP0009/`
  (`NbEPQTT*`, `NbEPLinQTT`) are the only prior work. Their finding to
  reuse: a usage-indexed run-time context makes erasing 0 definitional.
- **Effects:** none. Every term is pure and total.
- **Master's grades** (`formal/Once/Spec/Grade.agda`, on
  `origin/0.146-linear-core-4`): usage `Zero ≤ One ≤ Many` with `+q`/`*q`,
  affine; effect `pure ≤ act ≤ eff`; the law 0 ⇒ pure; arrows
  `A ⇒[ mk-kind q π ] B`; `⊢sub-use`, `⊢sub-eff`.
- **The cost lesson.** Kernel changes are cheap (memory: A-math through all
  of the metatheory in hours). The Knot encodes every rule, so it is where
  cost lands. No Knot family migrates on the ungraded judgment.

## 2. The usage axis

Master's semiring is taken as it is. Agreement with it is evidence, not the
justification: `{0, 1, ω}` with the affine order is the least semiring that
separates "never run", "run at most once" and "run freely", which is what
extraction and the linear core each need.

- **Contexts carry a usage vector** `Ψ`. Context addition `+ᵘ` and scaling
  `*ᵘ` are as in master's `Spec/Context`.
- **Types are checked at 0.** `Γ ⊢ty A` uses its context at 0, so every
  variable may appear in a type. The 0-fragment is the ungraded type
  theory we have now.
- **Binders carry a usage.** `Π (x :^q A). B` and `lam q t`: the body uses
  `x` at most `q` times. `⊢app` scales the argument's usage by `q`, as
  master's `⊢app` does.
- **Σ carries a usage on its first component** (QTT's `(x :^q A) × B`), so
  `Σ (n :^0 Nat) (Vec A n)` is a vector with an erased length. `psplit`
  scales accordingly.
- **Per former group** (each decided when the rules are written):
  - *`var`, `lam`, `app`, `pair`, `fst`/`snd`, `psplit`:* as above. Whether
    `fst`/`snd` exist at grades other than ω, given `split` as the primitive
    (D490), is decided with the rules.
  - *`natrec`, `ielim`, `fcase`:* the motive at 0; the methods at the
    eliminator's usage; the scrutinee at the eliminator's usage. A runtime
    fold uses its algebra once per layer, so the method usage is ω unless
    linearity says otherwise (master's lent context `E`).
  - *`con`, `dpay`, `dih`:* fields at their declared usages (a `dσ` field
    may be declared at 0, giving erased constructor arguments).
  - *Codes `⌜Π⌝`, `⌜Σ⌝`, `⌜IMu⌝`, …, `Desc`, `dι`/`dσ`/`dρ`:* only at 0
    (the extraction test).
  - *`Hom`, `Id`, `hrefl`, `idrefl`, `tr`, `trU`, `ap`, `jsub`, `ordtr`:*
    proofs at 0. A transport is allowed at run time only where its
    extraction is the identity (§3).
  - *`ref`:* pure, and it uses the context at 0. The entry's own usage comes
    from its schema.
  - *`⊢conv`:* conversion relates the 0-images, so it never evaluates
    anything that runs.
- **Subsumption:** `⊢sub-use` (a term may claim more usage than it makes).

### 2.1 The rules, classified (read 2026-11-27, `Spec/Typing.agda:102-294`)

The term judgment has **41 rules**, and `⊢ty` has 14.

- **18 rules are 0-only:** their conclusion is a code, a description or a
  proof, so it never runs. These are `⊢ordtr`, `⊢⌜base⌝`, `⊢⌜Π⌝`, `⊢⌜Σ⌝`,
  `⊢⌜Hom⌝`, `⊢hrefl`, `⊢tr`, `⊢ap`, `⊢⌜Id⌝`, `⊢⌜Nat⌝`, `⊢⌜IMu⌝`, `⊢⌜Fin⌝`,
  `⊢⌜Unit⌝`, `⊢idrefl`, `⊢dι`, `⊢dσ`, `⊢dρ`, `⊢dpay`.
- **23 rules may run:** `⊢var`, `⊢lam`, `⊢app`, `⊢pair`, `⊢absurd`,
  `⊢fst`, `⊢snd`, `⊢trU`, `⊢jsub`, `⊢unit`, `⊢nzero`, `⊢nsuc`, `⊢natrec`,
  `⊢con`, `⊢dih`, `⊢ielim`, `⊢fzero`, `⊢fsuc`, `⊢fcase`, `⊢fcase0`,
  `⊢psplit`, `⊢ref`, `⊢conv`. Across them:
  - **30 premises become 0-premises:** type, code, index and proof premises,
    such as `natrec`'s motive, `con`'s `I D i`, and `jsub`'s endpoints and
    path. Also `absurd`'s and `fcase0`'s refutation (ex falso needs no
    run-time evidence).
  - **25 premises take the conclusion's usage**, scaled where a binder or
    an argument says so: `app`'s argument by the arrow's `q`, `pair`'s
    first component by Σ's `q`, and the method and scrutinee premises of
    the eliminators.
- **Two rules need care.**
  - `⊢trU` is transport along a universe path, which is APPLICATION of the
    path (directed univalence). With the path at 0, it runs only where its
    extraction is the identity (D9). In general it is therefore proof-only.
  - `⊢fst` at run time needs Σ's first component at a nonzero usage.

**A layering this suggests (proposed decision D10).** Atkey's QTT has a
judgment at σ = 0 in which resources are ignored. That judgment is exactly
today's `Spec/Typing`. The graded judgment `Γ ⊢[ Ψ ] t ∷ A` (σ = 1) then
needs new rules only for the 23 rules that may run. Their 30 0-premises
stay premises of the EXISTING judgment, and a forgetful theorem
`⊢[ Ψ ] ⇒ ⊢` (shaped like `Metatheory/Erasure`'s bridge) carries subject
reduction's typing part, canonicity and consistency across unchanged.
New proofs are needed only for the usage itself: the substitution lemma
with scaling, and subject reduction preserving `Ψ`.

The 18 0-only rules, `⊢ty` and the Knot's encodings of them stay as they
are. One raw-syntax change remains: Π, λ and Σ gain a usage field (D1),
which every consumer of `RTm`/`RTy`, the Knot included, must carry.

## 3. Extraction into master's core

The bridge to master: a theorem that a well-graded kernel term at usage 1 or
ω extracts to a well-typed term of master's graded `Spec.Core` `Tm`, with
the same meaning. The pipeline is then:

> kernel → (extraction) → master's graded core → (`Lq`) → `LinCore`

The kernel never meets `LinCore` directly. The allocation-aware evaluator
that ROADMAP R5 used to name is master's `LinCore` (plan 0.146), and the
POC does not build a second one.

What extraction does, construct by construct:

- **Π over `U` at 0** extracts to master's type variable (`Δ`). It is
  parametric because a 0-variable cannot be inspected at run time.
- **Run-time Π and Σ** extract to master's arrows and products. Σ with a
  0-first component extracts to its second component's extraction.
- **Families with an erased index** (`IMu I D i`, `D : Π (El I) (Desc I)`,
  D493). A fibred value carries no constructor tag, because the index
  selects the fibre. **Extraction adds the tag**: the extracted type is
  the tagged union of the fibres, so `Vec A n` extracts to `List A`. That
  union is independent of any term only if the fibre function is a case
  tree on the index whose leaves extract to fixed codes. That is the shape
  D494–D496 already use. A family whose fibres come from an arbitrary
  computation is proof-only.
- **Sort-indexed families** whose sort is closed at every use extract to
  master's sorted codes (plan 0.158), with no tag.
- **`dσ` over a finite tag** extracts to `⊕`, and a non-dependent `dσ` to
  `⊗`/`K`. So master's grammar is the extraction image (plan 0.158 §3.4,
  step 7).
- **Transport.** `tr` along `Id`, at a family whose extraction does not
  depend on the index, extracts to the identity: `Vec A (n + 0)` to
  `Vec A n` is the identity on `List A`. Directed transport along `Hom` is
  a functor's action, which need not be the identity on representation. It
  is allowed at run time only where its extraction is the identity.
- **Rejected at run time** (a type error at usage 1 or ω, fine at 0):
  `U`, `El` of a run-time code, `Desc`, codes, and large elimination on
  run-time data.

The first version covers the non-dependent fragment, where extraction is
one-to-one onto master's core. The dependent constructs follow in the
order above.

## 4. Data: the nesting former (the DT side of plan 0.158)

Master's plan 0.158 proposes one sorted data former on both branches, with
nested fields by composition (`data Rose a = Node a (List (Rose a))`: the
children are a real `List`). The kernel cannot express nesting today: a
recursive field `dρ j C` names an index, never a family
(`Spec/Syntax.agda:180-182`).

- **The former.** A description field `dnest E k C`: a field whose type is
  the family `E` instantiated at the recursive family, at index `k`. Its
  premise: `E` is covariant in that parameter. That is `Spec/Variance`'s
  `Pos`, already used by directed transport. Categorically, polynomial
  functors are closed under composition, and a parameterised initial
  algebra is a functor in its parameter.
- **Payload and IH.** `dpay` and `dih` gain a case for the nested field:
  the IH of a nested field is the inner family's functor action on the IH
  (`mapᶜ` in master's terms).
- **Extraction.** A nested field extracts to master's nested field.
- **Cost check.** The Knot's traversals recurse on the signature, so a new
  description former is a new case in every generic consumer. Measure one
  consumer (weakening) before adding the rest.

## 5. The signature: δ visible by segment

Master's side is decided (plan 0.147 §3.1.4 and §5): one `abstract`
attribute, abstract types as existential packages. The kernel's side:

- **Visibility.** A `ref d` unfolds by δ only at a use site inside the
  segment that may see `d`'s body. Outside, `ref d` is a neutral typed by
  its schema.
  - A nominal `data T` has a type entry that never unfolds.
  - `abstract data T` hides its constructor and fold entries outside its
    segment.
  - `abstract f` does not unfold outside its segment.
- **Module = segment: checked 2026-11-27.** The signature is a strict
  chain. `Algorithm/SigBuild`'s `SigExtend base …` appends one module's
  entries to exactly ONE base, which is checked once and reused
  (`WfSig (S ▸ˢ e) = WfSig S × EntryWf S e`). The Knot's core is such a
  chain: `PredsCore` over `PredsFlat` over `PredsStkC` over `PredsStkA`
  over `PwCore`. So every module is one contiguous segment by
  construction, and 0.147's per-module `abstract` is per-segment
  visibility.
  - **The gap: import DAGs.** Two modules extending the same base cannot be
    combined today. A diamond (C imports A and B, both over `core`) needs a
    linearisation `core ▸ A ▸ B ▸ C`. Each module stays contiguous, but
    references are LEVELS from the bottom (`d <ˢ size`), so B's entries,
    checked over `core`, are re-levelled by `|A|` when placed after A.
    `Metatheory/SigExt` gives monotonicity of typing; the re-levelling is a
    renaming on `ref`, still to write. Master has import DAGs (plan 0.154),
    so this is needed before the kernel meets real libraries. It is not
    needed for visibility itself.
  - **The fix comes from master (2026-11-27): names.** Master's identity of
    a definition is its `CanonicalName` (`Spec/Name`). The CLI loads all
    transitive imports into one module map with a cycle check, and the
    verified `resolveImports` flattens them. The core telescope gets its
    indices after flattening (`defName : Fin s → CanonicalName`), so a
    diamond is one set of entries. In the POC: each entry carries its
    canonical name; a checked module is a segment RELATIVE TO ITS IMPORTS;
    linking computes the linear order and the level renaming from the
    names. The kernel keeps levels (O(1) `ref`, PLAN-REF's reason), and the
    re-levelling is the renaming the names determine. Unlike master, which
    re-elaborates the flattened program, a segment's check is reused
    through the renaming.
- **NbE.** The value table (`Algorithm/NbE/TblOK`) unfolds only visible
  entries. Soundness (`nbe-sound`) is restated relative to a visibility.
- **Conservativity** (S5's δ-elimination) holds per segment: a segment that
  sees a body is a conservative extension of one that does not.
- **The categorical reading.** A transparent entry is a definitional
  extension, and an opaque entry is a generic element (a variable of its
  schema). Visibility says which part of the telescope is abstracted.

## 6. Effects

**Decided 2026-11-27: effects are a grade on the judgment** (master's form,
`⊢ t ∷ A ! π` over `pure ≤ act ≤ eff`, `⊢sub-eff`). The reasons are in
MASTER-DT-ABSTRACTIONS §3:

- the same model as effects-as-a-type;
- codegen parity only in this form;
- the grade does real work at run time (effectful fold methods with a pure
  motive);
- OCP-0007 rejects monad layers for the same reason.

- **Timing.** The kernel has no effectful former yet. The effect axis
  enters with the first one (§8's signature operations), not before. An
  axis on which every term is `pure` would be untested weight in every
  rule.
- **Positions.** Every 0-position is pure by `positionGrade`. Run-time
  positions (methods, function bodies) carry `π`. Sequencing joins (`·p`).
  The arms of a case meet at one grade.
- **Conversion** relates 0-images only, so NbE never runs an effect.

### 6.1 Reifying a computation at 0

For proofs about effectful programs: if `⊢ c ∷ A ! act`, then at 0,
`tree c : T A`, the free monad over the signature's operations. It is never
run and extracts to nothing. Handler correctness is stated through it:
`handle h c = fold h (tree c)`.

- **`T` needs an infinitary field.** An operation with an answer makes its
  continuation a function in a recursive position (`Read : (Int → X) → X`).
  The kernel's descriptions have no function-typed recursive field
  (master's G2, the infinitary `dπ`). It has never been spiked. Spike it
  before committing to §6.1.
- **`T∞`**, the meaning of `eff`, needs ν (§7).

## 7. Codata

Master keeps its run-time codata (`ν F f`, `unfold`, `iter` as core
formers, ν defunctionalised by D425). A loop that may run forever (`iter`)
never appears in a type, because types are at 0 and therefore pure. What
the kernel may need is a **pure, productive ν at 0**, for proofs about
servers: bisimulation, conversion that never unfolds a ν eagerly, and the
reification of `eff` (§6.1). Prior work: `POC/OCP0009/NbEPCoind`,
`NbEPOTTCoind`, `SpikeLinNu`.

## 8. Base types and signature operations

- **Words at every width.** Master's `Spec/Word.agda` defines `Int` at a
  width `bits`: residues in `[0, 2^bits)`, wrapping arithmetic, signed
  comparison, total division with RISC-V's results. `Spec/Numerics` has
  `int-bits` and `float-format`. **64 bits is not the default: every width
  is a target.** The kernel takes this model as the specification, with
  the width a 0-level parameter. A proof holds either at every width
  (`∀ w, 0 < w → …`) or at one target.
- **Conversion cannot compute `2^w` in unary `Nat`.** Literals and word
  arithmetic need binary naturals, either as a datatype or as primitive
  literals with computation rules.
- **`Float`** at a format, master's `Spec/Float`. It has no useful
  equational theory, so it is opaque in conversion except on literals.
- **Signature operations** (master's `SigOpInfo`) are the first effectful
  formers: an operation of type `Act A B` applied is a term at `act`. They
  bring the effect axis (§6).

## 9. Subtyping

`⊢sub-use` and `⊢sub-eff` are rules of the judgment. Master's type-level
`<:` (`Spec/Sub`: `Void <: B`, the effect order through arrows, sums,
products and ν; coherent, at most one derivation) is effect subsumption
pushed through the type formers. Inside a dependent kernel it would
complicate conversion.

- **Proposed:** keep it out of the kernel, and let the bidirectional
  elaborator insert the coercion. An arrow coercion is η-expansion around
  `⊢sub-eff` (Luo's coercive subtyping).
- **Cost check.** A coercion such as `ν F f → ν F f′` is a corecursive map.
  Master may have made subtyping primitive so that it costs nothing. Before
  deciding, check that extraction maps every such coercion to the identity.

## 10. Stages

Each stage gates on the full cold sweep, ALL GREEN, with
`tools/mem-guard.sh` and one agda at a time.

- **G0. Decisions.** §11's open items, with the user.
- **G1. The usage axis in the Spec.** `Spec/Syntax`: usages on Π, λ and Σ.
  `Spec/Typing` and `Spec/TypingA`: `Ψ`, scaling, `⊢sub-use`.
  `Metatheory/Erasure`. Then follow the red.
- **G2. The metatheory, graded.**
  - The substitution lemma with scaling. This is the key lemma, since every
    other proof goes through it.
  - Subject reduction.
  - Confluence (grades are annotations, so it is expected to be unaffected).
  - Canonicity, consistency, the logical relation, `Fundamental`.
- **G3. Algorithms, graded.** `CheckA` decides the graded annotated
  judgment. NbE soundness is restated. `Algorithm/Elab` infers usages
  bottom-up, the way master infers them.
- **G4. Extraction, first fragment.** The statement against master's
  `Spec/Core/Typing` (a copy of its definitions in the POC, since the POC
  owns its syntax), proved for the non-dependent fragment. Then the
  dependent constructs of §3, one at a time.
- **G5. δ visible by segment** (§5): the contiguity check first.
- **G6. The nesting former** (§4): one generic consumer measured first.
- **G7. Base types and signature operations** (§8), which bring the effect
  axis (§6). Then the `dπ` spike and reification (§6.1), and ν (§7) if D4
  says so.
- **G8. The R4 pilot.** One Knot family on the graded judgment, through the
  generic `⊢inst`. Measure what grades cost in the Knot before migrating
  further (ROADMAP Order, step 2).

G1–G4 are the core of R5. G5–G7 can run in any order once G3 is green.

## 11. Decisions for the user

| # | Question | Recommendation |
|---|---|---|
| D1 | Usages in the raw syntax (on Π, λ, Σ), as master's `lam A q π t`? | Yes: checking needs them, and conversion compares them syntactically |
| D2 | Σ graded on its first component? | Yes: erased-length vectors and every "value with a proof" need it |
| D3 | Effect axis: now, or with the first effectful former? | With the first effectful former (G7) |
| D4 | A pure ν at 0: in R5, or later? | Later: only reifying `eff` needs it, after the `dπ` spike |
| D5 | Binary naturals: a datatype, or primitive literals with computation rules? | A datatype, if conversion on `2^w` is fast enough when measured. Primitive literals add trusted code |
| D6 | Words: a library model, or a kernel primitive `Word w`? | A library model taken from master's `Spec/Word`. Extraction maps it to master's `Int` at the target's width |
| D7 | Type-level subtyping: in the kernel, or inserted by the elaborator? | Inserted by the elaborator, after the cost check in §9 |
| D8 | Visibility granularity: per module (= a contiguous segment) or per entry? | Per module, if the contiguity check in §5 holds |
| D9 | Directed transport at run time: only where its extraction is the identity? | Yes |
| D10 | The graded judgment as a σ = 1 layer over today's `⊢` (Atkey), with a forgetful bridge (§2.1)? | Yes: today's metatheory is reused, and the 18 0-only rules stay as they are |
| D11 | Generic syntax first: the Spec's syntax as a binding signature with one kit traversal (SPIKE-GENERIC-SYNTAX), before G1? | Yes, decided by the spike: S1–S2 green 2026-11-27; S3–S6 decide |
| D12 | Diamond imports (§5): flat levels re-levelled at link time, or segment-relative `ref` addresses? | Flat levels, IF D11 lands: re-levelling is then one kit instance with generic lemmas, and `ref`, the NbE table and the Knot are unchanged |

## 12. Done when

- The kernel's judgment is `Γ ⊢[ Ψ ] t ∷ A` (with `! π` once G7 lands), and
  every metatheorem and algorithm is green on it: subject reduction,
  confluence, canonicity, consistency, NbE soundness, `CheckA`.
- Extraction into master's core is stated and proved, at least for the
  non-dependent fragment and erased-index families.
- δ is visible by segment, the nesting former exists, and one Knot family
  is migrated and measured on the graded judgment.

## 13. Next step

G0: bring D1–D12 to the user. The generic-syntax spike (D11,
`SPIKE-GENERIC-SYNTAX.md`) runs first: S1–S2 are green, S3 is next. The two read-only checks are done (§2.1, §5).
Meanwhile, the decision-free groundwork: master's usage semiring and usage
vectors, copied into the POC with their laws.
