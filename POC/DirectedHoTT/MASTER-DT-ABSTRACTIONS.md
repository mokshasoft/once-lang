# Master and the DT POC: which abstraction is better, item by item

> Written 2026-11-27, after the rebase of the POC line onto master
> (HANDOFF-2026-11-26). It feeds PLAN-GRADED (ROADMAP R5).

Neither branch is the blueprint. Both are looking for the right
abstractions. For each place where they differ, this document asks which
abstraction is better on mathematical grounds. The better one moves to the
other branch, in whichever direction. The answer may be a third design that
neither branch has. Each row's direction is a proposal until the user
decides it.

Master here means `origin/master` plus the linear-core branch
`origin/0.146-linear-core-4` (plans 0.146 and 0.157), which is where the
graded judgment and `formal/Once/LinCore/` live.

## 0. The stance: the dependent layer erases completely

The user's position (2026-11-27): Once is a language in which you write a
program or a library and prove it correct. **The DT kernel keeps no
runtime information.** Types and proofs erase completely. A runtime
representation of some DT constructs may be added later, but it is not the
goal.

What follows from this:

- **Types may mention runtime values.** To prove `sort xs` correct, the type
  has to talk about `xs`, so the kernel holds the programs as well as the
  proofs. What separates "may run" from "only mentioned" is the usage grade:
  types, indices and proofs sit at usage 0, programs at 1 or ω.
- **The erasure test.** *The erasure of a runtime type must not depend on
  any term.* It is a structural test, with no hidden side condition.
  - `Σ (n : Nat) (Vec A n)` erases to `Nat × List A`. That is fine.
  - `Dec P` erases to `Bool`, with the proof at 0. That is fine.
  - `if b then Nat else Bool` with a runtime `b` has no erasure. It is
    allowed in proofs and rejected in programs. The same goes for `El`,
    `Desc` and `U` at runtime, and for transport (`tr`) unless its erasure
    is the identity (§10).
- **What the stance costs.** Generic programs written once over runtime
  descriptions (levitation's promise) do not run. The way to get them back
  later is staging: a 0-level program that computes runtime code at
  compile time. The stance does not rule that out.
- **Grounding.** Pédrot and Tabareau's "fire triangle" (2020) shows that
  substitution, dependent elimination and effects cannot all hold at once.
  The stance avoids the triangle structurally: types depend only on
  0-terms, and a 0-term is pure (master's own law, `positionGrade`). So
  "types see only pure terms" is the principled restriction, not just a
  convenient one.

## 1. Overview

| # | Item | Master | DT POC | Better abstraction (proposed) | Direction |
|---|---|---|---|---|---|
| 2 | Usage grades (QTT) | `0 ≤ 1 ≤ ω`, affine, `⊢sub-use` | none | Full QTT in one judgment; the dependent rules only distinguish 0 from runtime | master → DT |
| 3 | Effects | a grade on the judgment, `⊢ t ∷ A ! π`, with `M pure = Id`, `M act = T`, `M eff = T∞` | none at all | **Decided 2026-11-27: (A), master's form, on both branches.** Usage 0 keeps types pure; the DT kernel adds a 0-only reification of a computation into its tree | master → DT; no master plan |
| 4 | Signature references | `ref` typed from a schema, never unfolds | `ref` unfolds by δ; references are projections (D501) | One `ref`, with δ visible only inside the segment that may see the body | DT → master; master's side already decided (plan 0.147 §3.1.4, §5) |
| 5 | Data | polynomial codes `K`/`Id`/`⊕`/`⊗`, no index; one μ, one fold | one former `IMu` over levitated, FIBRED, indexed descriptions | One SORTED former on both; master's grammar is the erasable finite-sort fragment; nesting by composition | DT → master (plan 0.158); DT owes a nesting former |
| 6 | Polymorphism | type variables in a kinding context `Δ` | Π over `U` at usage 0 | Π over `U` at 0; `Δ` remains the erasure target | DT → master |
| 7 | Subtyping | `Spec/Sub`: canonical coercions (`Void`, effect order), at most one derivation | none | `⊢sub-eff` in the judgment; type-level `<:` possibly inserted by the elaborator | master → DT |
| 8 | Codata | ν, `unfold`, `iter` as core formers (servers) | none | A pure, productive ν at 0 for proofs (and for reifying `eff`) | master keeps its runtime story; DT adds ν at 0 |
| 9 | Base types | `Int` at the target's width, `Float` at its format, effectful operations | unary `Nat` only | Width-parametric word and float MODELS in the DT kernel, erasing to master's primitives | master → DT (the spec) |
| 10 | Equality | none in the core | `Id`, directed `Hom`, `tr`, `ap` | Proof-level only, at 0; laws stated as `Hom` | DT → master (as the logic) |
| 11 | Linear core | `LinCore`: point-free, simply typed, explicit `dup`/`drop` | none (`NbEPLinCore` was its seed) | Master's; the DT kernel reaches it only through erasure | stays on master |

## 2. Usage grades (QTT)

**Master.** `Spec/Grade.agda`: usage `Zero ≤ One ≤ Many` with `+q` and `*q`,
affine (`⊢sub-use`). The context carries a usage vector `Ψ`. `⊢app` scales
the argument's usage by the arrow's quantity. The linear core reads 1
versus ω from the graded derivation.

**DT POC.** No usage at all. The OCP0009 spikes (`NbEPQTT*`, `NbEPLinQTT`)
graded only simple types. Their useful finding is a runtime context indexed
by usage, which makes erasure at 0 definitional.

**Principled reading.** Under the stance, usage is what lets the kernel hold
programs and proofs in one judgment. That is Atkey's QTT: types are checked
at 0, and a runtime variable may be mentioned freely at 0. The dependent
formers (Π, Σ, `IMu`, `Hom`, `Id`) only need the 0-versus-runtime split.
The difference between 1 and ω is information about the program, and the
linear core needs it. Both belong in one semiring, as in master.

**Direction.** Master → DT. The POC's judgment becomes `Γ ⊢[ Ψ ] t ∷ A`.

**Open.** How usage meets the dependent eliminators (`ielim`'s motive and
methods, `natrec`, `split`), and how it meets the Knot. Each rule of the
judgment changes, so this precedes further R4 migration
(HANDOFF-2026-11-26).

## 3. Effects

**Master.** A grade on the judgment, `Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π`, over
`pure ≤ act ≤ eff`, with `⊢sub-eff`. The semantics (`Spec/Effect.agda`)
interprets the grades as three monads:
- `M pure = Id`;
- `M act = T`, the free monad `μY. X + H_Σ Y` over the signature's
  operations;
- `M eff = T∞ = νY. T (X + Y)`, the coinductive resumption monad.

The monad morphisms between them follow the order. A graded arrow
`A ⇒[ q, π ] B` means `⟦A⟧ → M π ⟦B⟧`. That is Moggi's call-by-value
reading.

**DT POC.** No effects. Every term is pure and total: `Nat`, `natrec`, folds
over `IMu`, and well-founded recursion.

**The fork.**

- **(A) Effects as a judgment grade (master's form).** Every DT rule carries
  `π`, and every dependent former is restricted to `pure`. Under the stance,
  `π` is dead weight in every dependent rule: types and proofs are always
  pure.
- **(B) Effects as a type.** The kernel judgment is pure. An effectful
  program is a pure term of type `A → M π B`, and proofs reason about its
  meaning directly: by induction for `T`, by bisimulation for `T∞`. A
  direct-style surface elaborates into this by the call-by-value
  translation, which is exactly master's semantics. The compiler reads `π`
  from the type. This needs no new kernel machinery for `act`: `T` is an
  ordinary inductive type, described by a `Desc` over the signature's
  operations. `T∞` needs ν (§8).
- **(C) Call-by-push-value**, with separate value and computation types and
  the `U`/`F` adjunction. It is the principled common refinement of (A) and
  (B), and dependent variants exist (Vákár; Ahman). It is the heaviest of
  the three, but worth weighing before deciding.

**Decided 2026-11-27: (A), on both branches.** An earlier lean towards (B)
was withdrawn for three reasons:

- **The same model.** (A) and (B) both mean morphisms in the Kleisli
  category of a graded, strong monad. Master's graded arrow
  `A ⇒[ q, π ] B` already is the internal Kleisli exponential
  `A → M π B`, and `Unit ⇒[ π ] B` is a suspended computation. (B)
  internalises nothing that (A) lacks. (A) is fine-grain call-by-value,
  (B) is Moggi's monadic form, and both embed in CBPV.
- **The grade is not dead weight.** Types, motives and indices sit at usage
  0, and 0 ⇒ pure, so types are pure as a consequence of usage, with no
  extra side condition. The grade does real work in the computational
  positions: a runtime fold with effectful methods (master's `foldM`) has a
  pure motive and effectful methods.
- **Codegen.** Taken literally, (B) makes `M π B` a value and `bind` a
  function, so every sequencing step risks a thunk. In (A) a computation is
  not a value: sequencing is evaluation order, and an effect is a call.
  (B) reaches parity only by being compiled back into (A).

**What (B) seemed to offer is a separate feature: effects as data that can
be eliminated.**
- *For proofs:* a 0-only REIFICATION rule. If `⊢ c ∷ A ! act`, then at 0,
  `tree c : T A`, with `T` an ordinary datatype in the DT kernel. It never
  runs and erases. `T∞` needs ν (§8).
- *For programs: handlers.* These are orthogonal to (A) versus (B).
  Plotkin and Pretnar's handlers are algebra homomorphisms out of the free
  model, and they are presented in direct style (Koka, Eff, OCaml 5), i.e.
  on (A). What they need from the Spec is an effect grade that says WHICH
  operations a computation may perform (a row, or a subset of the
  signature), so that `handle` can remove the handled ones. Master's grade
  is a three-point chain over one global signature.
  - Free monads over operations that return answers put functions in
    recursive positions (`Read : (Int → X) → X`). `LinCore`'s functor codes
    exclude those, and in the DT kernel they need an infinitary `dπ`,
    which has not been spiked (G2).
  - **Cost depends on how the continuation is used.** A tail-resumptive
    handler (state, reader, logging, mocked input) compiles to a direct
    call with no allocation. A one-shot continuation needs a closure or a
    stack segment. A multi-shot one (nondeterminism) copies the
    continuation. The usage grade on the continuation tells the compiler
    which case applies.
  - Master already has handlers at one level: a signature's
    Interpretation per Host (plan 0.96), chosen at link time.

**OCP-0007 (capability-graded effects) is that grade.** It rejects monad
layers and free monads for the reason (A) is kept (one graded category, no
lifting), and its §7 already presupposes pure in-language handlers for
`State`, `Error`, `NonDet`. The refinement that joins it with handlers:
- the NEEDED grade is a set of OPERATIONS (union bottom-up, OCP-0007 §5) times
  finiteness; master's chain is its image when the operations are forgotten
  (`pure` = (∅, finite), `act` = (S, finite), `eff` = (S, may diverge));
- capabilities are the image of that set under the deployment POLICY, a
  join-preserving map from operations to capabilities, applied once at the
  grant site (OCP-0007 §2's separation made structural: graded monads move
  along morphisms of their gradings, Katsumata 2014);
- an operation is discharged by HANDLING (interpreted in Once, removed from
  the set before the policy sees it) or by GRANTING (authority from root).

Stacks of known handlers inline: never-resuming (`Error`) and tail-resumptive
(`State`, `Reader`, logging, mocked IO) handlers cost no allocation, so such
stacks are free at run time; only multi-shot handlers (`NonDet`) allocate.
Parameterised capabilities (`Connect[host]`) are grades indexed by 0-terms,
and a use-once capability is a zero-word token at usage 1: both fit §0.

**Open.** Whether to turn OCP-0007 plus handlers into a master plan (a Spec
change of the grade lattice, generalising today's chain).

## 4. Signature references

**Master.** `ref : (d : Fin s) → GSub … → Tm n`, typed by `⊢ref` from the
entry's schema alone, at usage 0 and pure. The meaning is the environment of
entries. There is no δ: a reference never unfolds. Plan 0.147 §5 asks for
nominal and `abstract` declarations, with δ scoped by segment.

**DT POC.** A `ref` unfolds by δ: S5 route B, δ by erasure, conservativity
by δ-elimination. References are projections in the kernel (D501, and
master's D071 agrees). Proofs need this: the gcd proofs compute through
definitions.

**Principled reading.** These are two different things:
- a **definition**: transparent, it unfolds by δ, and proofs compute with it;
- a **declaration**: opaque, typed from its schema, and only its type is
  known.

One `ref` former covers both if δ is VISIBLE only inside the segment that
may see the body. Master's `ref` is the case where nothing sees the body.
Under the stance, δ only ever runs in conversion, at 0. The compiled
program just calls the entry, as master does.

**Direction.** DT → master, adding visibility by segment. Master's side is
already decided: plan 0.147 §3.1.4 (one `abstract` attribute, the
Mitchell–Plotkin reading) and §5 (δ scoped by segment). No new master plan;
the work left is the DT kernel's δ visibility.

**Open.** The form of the visibility (per segment, per entry, or by module
boundary), and its interaction with D501's projections.

## 5. Data: polynomial codes versus fibred descriptions

**Master.** `Spec/Polynomial.agda` and `Spec/Type.agda`: functor codes `K`
(a constant), `Id`, `⊕` and `⊗`, with one μ and one fold at every effect
grade. There is no index. Plan 0.147 §4 postpones GADTs and indexed families
to dependent types. G1 (nested types, "the plan's largest proof patch") and
G3 (mutual types by Bekić) are designed separately.

**DT POC.** One former, `IMu I D i`, over levitated descriptions that are
FIBRED (D493): `D : Π (El I) (Desc I)`, with telescopes `dι` (end, no
index), `dσ S f` (a field, then the rest as a function of it) and `dρ j C`
(a recursive field at index `j`). The fibre at `i` lists the shapes
available at `i`. A family with a computed target Fords explicitly, with an
`Id` field. Mutual families are one family fibred by sort (D494).
Judgements are fibred by their subject (D496).

**How they differ.**
- At `I = ⊤`, a fibred description is an ordinary description. Master's
  grammar is the fragment where every `dσ` is either over a finite tag
  (`⊕`) or non-dependent (`K`, `⊗`).
- That fragment is exactly what the erasure test lets through for
  single-sorted data. A `dσ` whose continuation depends on a runtime field
  passes only if the field is a finite tag, and then it is a sum. So
  **master's polynomial grammar is the erasable part of the POC's
  descriptions.** That is a principled reason for the two to agree, not a
  coincidence.

**Erasing a fibred family whose index is erased.** A fibred value carries no
constructor tag, because the index selects the fibre. For example,
`Vec A zero` has only `nil` and `Vec A (suc n)` has only `cons`. If the
index is erased, the runtime cannot tell the shape. **Erasure therefore has
to add a tag.** The erased type is the tagged union of all fibres, so
`Vec A n` erases to `List A`. That union is term-independent, which the
erasure test requires, only when the fibre function is a case tree on the
index whose leaves erase to fixed descriptions. That is exactly the shape
D495 and D496 already give: "the fibre function eliminates the subject".
A family whose fibres come from an arbitrary computation is proof-only.

If the index is runtime-relevant (`n` at ω), the fibred form needs no tag:
the index already determines the shape. Dropping the tag in that case is a
layout optimisation for later, and it needs its own proof.

A Forded family keeps its tag in the value and its equations at 0, so its
erasure is trivial. Under the stance, Ford is the erasure-friendly
presentation and fibring the proof-friendly one (D493's rationale:
consumers pay no transports). With `Id` and `J` the two are equivalent.
The case-tree rule lets the kernel keep fibring without giving up erasure.

**Would master benefit?**
- **One former for mutual types.** A family fibred by sort, with the sort
  index closed at every runtime use, costs nothing at runtime. It replaces
  Bekić's encoding (G3) with the former master already has.
- **GADTs and indexed families with erased indices** (plan 0.147 §4's
  postponed item). They come from the same former, erasing to the tagged
  union.
- **Nested types (G1).** These are families indexed by a type, at 0, whose
  fields have type `El i`. They pass the erasure test only if `El i`
  erases to a type variable, which means polymorphic recursion in the
  erasure target. **Not established**; to check before claiming it.
- **The runtime layout does not change.** It stays polynomial. The gain is
  one former and one fold rule for all of the above, instead of a separate
  design for each.

**A gap on the DT side: nesting.** Plan 0.147 §3.4 designs nested positive
fields (`data Rose a = Node a (List (Rose a))`) as "a fragment of the DT
kernel's `Desc`". It is not one yet: `dρ j C` names an index, never a
family, so a field cannot apply a declared type to the recursive position.
The principled fix is a nesting former, a field `F ∘ X` with `F` covariant in
the parameter (premise: `Spec/Variance`'s `Pos`). Elaborating nesting into
mutual sorts instead would make `List`'s functions inapplicable to the
children (copies, or a conversion).

**Direction.** DT → master for the former: plan 0.158 (one sorted data
former, nesting by composition, Bekić as a theorem; it reopens 0.147 §3.4).
Master's functor grammar becomes the erasable fragment, stated as a
theorem. The DT kernel owes the nesting former.

**Open.**
- The erasure function on `IMu` and its proof.
- Whether erasure may also add tags for computed fibres given in Ford form.

## 6. Polymorphism

**Master.** Type variables in a kinding context `Δ` (`KCtx m`). Schemas
carry their arity and kinds. The linear core is monomorphic: `LTy` has no
variables.

**DT POC.** Π over the universe: `Π (A : U) …`, with `El A`.

**Principled reading.** Π over `U` at usage 0 is one mechanism that covers
`Δ`. Because a 0-variable cannot be inspected at runtime, there is no
type-case at runtime, which makes it parametric. It therefore erases to a
type variable. `Δ` stays useful as the shape of the erasure target.

**Direction.** DT → master (the core needs no second binder), with `Δ`
remaining in the erased language.

**Open.** Universe levels or a single `U`, and how that interacts with
levitation (`Desc` and `U` as codes).

## 7. Subtyping

**Master.** `Spec/Sub.agda`. A conversion is admitted only if it is
canonical and loses nothing observable: `Void <: B`, and the effect order
on arrows and streams. It is closed under the formers, has at most one
derivation per judgment, and the joins `⊔` give a `case` its principal
type. The surface already composes each branch with its conversion.

**DT POC.** None.

**Principled reading.** Master's subtyping is coherent (one derivation),
which is good design. Its content is the effect order plus `Void`.
- §3 decided (A), so `⊢sub-eff` stays in the judgment. An arrow coercion
  is still η-expansion around it, so the type-level `<:` may be inserted
  by the elaborator rather than be a rule of the kernel (Luo's coercive
  subtyping). Decide that in PLAN-GRADED.
- Subtyping inside a dependent kernel would complicate conversion, which is
  the reason to keep it out.

**Cost to check.** Master may have made subtyping primitive so that it
costs nothing at runtime. A coercion such as `ν F f → ν F f′` is a
corecursive map. As a function it is the identity on representation only if
the compiler can see that. Before moving, measure whether erasure maps these
coercions to the identity.

**Direction.** Master → the DT surface (bidirectional elaborator), not into
the kernel.

## 8. Codata

**Master.** `ν F f`, a stream whose layers are produced at a finite grade.
`unfold` and `iter`, a loop that may run forever at `eff`, are core
formers. D425 defunctionalises a ν: its coalgebra is a label and its seed
an environment. `Spec/Effect` already states that "`ana` into `Eff` is the
stream unfold".

**DT POC.** None. The OCP0009 spikes `NbEPCoind`, `NbEPOTTCoind` and
`SpikeLinNu` exist, but nothing has been ported.

**Principled reading.** Split by grade.
- A loop that may not terminate never appears in a type, because types are
  at 0 and therefore pure.
- To prove things about servers, the logic needs a pure, productive ν at 0,
  with bisimulation, and conversion that never unfolds a ν eagerly.
- The reification rule (§3) needs `T∞` as a ν for `eff` computations.

**Direction.** Master keeps its runtime story (`unfold` and `iter` as
formers, ν defunctionalised by D425). The DT kernel adds a pure ν at 0.

**Open.** Is ν in scope for R5, or later? Proofs about `eff` programs need
it, and proofs about `act` programs do not.

## 9. Base types: words at every width, floats at every format

**Master.** `Spec/Word.agda`: `Int` denotes a word of the target's width,
in two's complement. The carrier is ℕ restricted to `[0, 2^bits)`, and
`Width bits` parameterises the operations. Addition, subtraction and
multiplication wrap. Comparisons are signed. Division and remainder are
total, with RISC-V's results. `Spec/Numerics.agda`: `TargetNum` has
`int-bits` (at least 1) and `float-format`. **64 bits is not the default:
every width is a target.** Effectful operations are the signature `H_Σ`.

**DT POC.** Only unary `Nat`.

**Principled reading.**
- Proofs need the *meaning* of `Int` and `Float`, so the DT kernel needs
  models of them. Master's `Spec/Word` and `Spec/Float` are those models,
  and they move as they are: master → DT, as the specification.
- The width stays a parameter, a 0-level `Nat`. A proof either holds for
  every width (`∀ w, 0 < w → …`) or for one target.
- Erasure maps the model to the machine primitive. Master's compiler
  theorem, relative to `TargetNum`, carries the proof to the compiled code.

**A hard constraint.** Conversion cannot compute `2^w` in unary `Nat`.
Literals and word arithmetic need binary naturals in the kernel, or
primitive literals with δ-rules. Lean does the latter for `Nat` with GMP;
that adds trusted code.

**Open.**
- A primitive `Word w` with computation rules, or a library model plus a
  trusted erasure table?
- How `Float` behaves in conversion. It has no useful equational theory, so
  probably it is opaque except on literals.

## 10. Equality: `Id`, `Hom`, transport

**Master.** No equality in the core. Plan 0.147 §5 asks for laws stated as
`Hom`.

**DT POC.** `Id`, the directed `Hom`, `tr` and `ap`. Σ is split, with no η
(D490).

**Principled reading.** These are proof-level, at 0, and erase. The erasure
test settles transport at runtime:
- Transport along `Id`, at a family whose erasure does not depend on the
  index, erases to the identity. For example, `Vec A (n + 0)` to `Vec A n`
  is the identity on `List A`. It is allowed in programs.
- Directed transport along `Hom` is a functor's action, which need not be
  the identity on representation. With a 0-proof of `Hom`, it is allowed in
  a program only where its erasure is the identity. Otherwise the proof
  would have to be runtime data, which the stance excludes.

**Direction.** DT → master, as the logic for stating laws. Nothing changes
at runtime.

## 11. The linear core

**Master.** `formal/Once/LinCore/`: symmetric monoidal structure with an
explicit comonoid (`dup`/`drop`, the only sources of copying and
discarding), additive sums, μ over codes that exclude function types, plus
`lcata` and `liter`. Closures and ν are defunctionalised (D424, D425).
`NoLeak` holds, and the bridge `Lq` connects the elaborator's graded
`Expr` to it. Its header says it started as OCP-0009's `NbEPLinCore`.
Plan 0.146 says its event trace supersedes `NbEPLinCore`'s cost counting
and `dyn-linear`.

**DT POC.** None, and it should not build one.

**Principled reading.** The linear core sits below the dependent kernel.
The pipeline is:

> DT kernel → (erase usage 0) → master's graded core → (`Lq`) → `LinCore`

So the DT kernel never meets `LinCore` directly. Its obligation is the
erasure theorem into master's core. ROADMAP R5's "allocation-aware
evaluator" and its `NbEPLinCore` blueprint are master's now; fix those
ROADMAP lines in PLAN-GRADED.

**Direction.** Stays on master. The POC's claim that "dup-free code
allocates nothing" (ROADMAP §6) should be stated against this core, not
proved again elsewhere.

## 12. For the user

1. **Effects (§3):** decided 2026-11-27, (A). Still open: whether user
   handlers (a signature-indexed effect grade) are wanted, and when.
2. **Codata (§8):** a pure ν at 0 in R5, or later?
3. **Base types (§9):** a primitive `Word w` with computation rules, or a
   library model with a trusted erasure table? Binary naturals in the
   kernel?
4. **Visibility of δ (§4):** per segment, per entry, or by module?
