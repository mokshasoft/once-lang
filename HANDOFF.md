# HANDOFF — branch `plan-0.76-context-indexed-composition`

## STATE

`master` is at `f5694a45a`: plan 0.72 (float parameter) MERGED and pushed
2026-08-30, after the full gate — cabal build 0, cabal test 692/0, exit tests
63/0/0 on x86-64, x86-32 and riscv64, MAlonzo re-extracted against the merged
tree.

This branch implements **plan 0.76 / D127** — context-indexed composition.
Read `plans/0.76-context-indexed-composition.md` first; it is the spec for
this work and it owes two obligations (O1, O2) that are the honest failure
conditions.

## PHASE A — DONE (71329816), green and pushed

`Once/TypeCheck/Judgment.agda` typechecks. Deleted the `⊢ᵍ` value realm, the
`⊢ᵐ` morphism realm, the three bridges (`t-morph-lift`, `t-value-lift`,
`t-closed-lift` — i.e. all of D126) and `extractMorphWitness`. Added to `⊢ᶜ`:
seven point-free leaves and five combinators with `⊢ᶜ` premises and summed
usage.

Two things held back deliberately (do NOT "simplify" them in later phases):
  * `t-cata-check` keeps the CLEARED context. Widening admits a CAPTURING
    algebra — plan 0.76 risk 3, its own decision entry.
  * `pair`/`curry` stay pure-fixed.

`Once/Spec/Typing.agda` changed by ONE COMMENT LINE (it named the two retired
realms). It is a verbatim re-export, so this is the only spec-side hunk and it
is documentation.

## THE RED LIST (Phase A's exit is "everything downstream is red")

16 modules mention `⊢ᵍ`/`⊢ᵐ`, by site count:

    Completeness 32 · CanonReflectMutual 21 · Realize 10 · CanonPolyTransport 10
    Elaborate 9 · CanonReflectPolyTransport 8 · Meaning 7 · CanonPreserveMutual 6
    CanonComposeMid 5 · MeaningBridge 4 · ElaborateProofs 3 · RealizeAgrees 3
    CanonPreserve 3 · ResolverBridge 1 · Judgment 2 (comments only)
    Spec/Typing 0 (fixed)

## PHASES A, B AND MOST OF D — DONE AND PUSHED

Green and committed: `Judgment`, `Denotation/Meaning`, `Denotation/Realize`,
`Denotation/SourceDenote`, `Denotation/ThinSound`, `Surface/Syntax`,
`Surface/Thinning`, `Surface/Elaborate`, `TypeCheck/Elaborate`,
`TypeCheck/ElaborateProofs`, `TypeCheck/Soundness`, `Adequacy/ResolveFaithful`.

**The usage decision (D127 follow-on, needs its own decision entry).**
Composition is LINEAR in each argument, so a combinator's usage is
`Ψ₁ +ᵘ Ψ₂`. QTT does not force otherwise: its lambda rule does NOT scale the
captured context, and the `Many *ᵘ` that an `app`-encoding produces is
application's conservative rule (`Γ + q·Δ ⊢ f x`), not a fact about `∘`.
Since the term language could only express the conservative reading, the TERM
LANGUAGE was under-expressive — `comp'`/`copair'`/`fork'`/`curry'` are new
`Surface.Expr` primitives whose typing rules state `Ψ₁ +ᵘ Ψ₂` directly.

**A bug this caught, worth not re-introducing.** The four elaborate to CLOSED
morphisms (`compIR`/`copairIR`/`forkIR`/`curryIR`) composed with
`⟨ elaborate f , elaborate g ⟩`. Do NOT fuse the arms inward as
`curry (apply ∘ ⟨ f ∘ fst , … ⟩)`: that puts them under the `curry`, so an
arm that EMITS re-emits on every call and the trace stops matching
`⟦ comp' f g ⟧ˢ`, which binds both arms outside the returned function.

`copair'` needed distributivity `Γ × (A + B) → (Γ × A) + (Γ × B)`, which never
arose while `case` arms were closed. DERIVED (`distribIR`, standard CCC
construction) — no new IR primitive.

## `SourceFaithful` IS DONE — all four combinators PROVED faithful

Green and committed. Structure follows `app-body`: a `<c>-transport` (all
`refl` on `refl refl refl`) plus an `evalᴰ-<c>-reduce` for the traces.
`curry'` is plain `refl`; `comp'`/`fork'` need one trailing `[]`
(`comp-trace`, explicit arguments for the same reason `app-trace` has them);
`copair'` case-splits on the sum because `case`-after-`distribIR` is stuck on
an abstract value, and both branches are then `refl`.

## IN FLIGHT: D131 — the PARAMETERIZED CATA. Cone is RED, migration is mechanical.

**Decided (D131).** A cata's algebra is OBTAINED once and APPLIED per layer,
uniform with every other combinator arm (D130). The spec already says this —
`⟦_⟧ᶜ`'s cata clause binds the algebra. The EMITTER did not: it produced
`Cata wfF (apply ∘ ⟨ ealg ∘ terminal , id ⟩)`, and `Cata`'s algebra runs per
layer, so the algebra was REBUILT every layer.

**Why there is no intermediate step.** The interim (a named residual saying
"the algebra's build is effect-free") would be FALSE — a closed arrow-typed
expression can emit while being built. The other interim (restricting the
algebra to value forms) narrows the language for the emitter's convenience.
Both were rejected: the branch exists to make the spec mathematically correct,
so the codegen moves to meet it.

**The change, landed in `Once/IR.agda`:**

    Cata : WellFormedFI F → IR (E * ⟦F⟧TI A) A → IR (E * μ-type F) A

so `CataM : IR (F C ⇛ C) (μF ⇛ C)` is CLOSED and the elaboration becomes
`CataM ∘ ealg` — structurally identical to `compIR ∘ ⟨ ef , eg ⟩`.

**The migration pattern**, set by `Once.CCC.Eval` (done, green):

    eval fmt (Cata {F} wf {E} {A} alg) (env , x) =
      sem-cata (wf-⌈⌉ wf) (λ fa → eval fmt alg (env , …)) x

Project the environment ONCE, outside the fold; close over it in the
per-layer algebra. Every consumer follows this.

**Scope, measured not guessed.** 83 modules mention `Cata`; 82 pattern-match
sites. Exactly ONE site CONSTRUCTS a `Cata` (`Surface/Elaborate.agda:428`), so
this is a migration, not a fork. By area: `CCC/Codegen` 24, `CCC/Machine` 10,
`Adequacy` 12, `Denotation` 4, `TypeCheck` 4, `Surface` 3. The codegen fold
loop (`CataNat*`) and the three arch cata paths are the substantial part; the
rest is mechanical.

**WORKLIST IS THE 53 REACHABLE MODULES, NOT 83.** `/tmp/cata_reach.txt` holds
them; `$SCRATCH/catasweep.sh` sweeps exactly that set. Rebuild the list with
the import-closure script over the seven gate roots (Compiler, Certified, the
three Targets, Spec/Correct, ErrorProofs) if it goes stale.

**Done, green**: `IR`, `CCC/Eval`, `CCC/IR/Stack`, `Denotation/DenotTrace`.

**In flight**: `Adequacy/CataErased`. `evalᴰ-Cata-erased` is generalized with
the environment as an ERASED SURFACE type `⌊ Eˢ ⌋` — `liftFn` is stated over
erased surface types, and the only environment the elaborator ever supplies is
the algebra closure `⟦F⟧T C ⇒ C`, which is one. The env is transported at each
use with `subst (λ t → t) (sym (cohᴰ Eˢ))`. REMAINING: `step-eq` compares
against `liftFn fmt mir`, which now takes a pair, so `evalᴰ-subst-dom` needs a
paired-motive variant (`λ o → IR (⌊Eˢ⌋ * o) B` instead of `λ o → IR o B`).

**THE 30 ISLANDS — a separate delete-or-justify pass.** Not on the migration
worklist. The whole `CataNat*` family (9 modules) is the cata codegen path the
decision log already records as DEAD; `Fusion*`, `Optimize/Correct`,
`Optimizer/*` are the optimizer proofs D039 found unsound.

Two of them are NOT deletion candidates and matter for O2:
`Once/Category/Laws.agda` and `Once/Semantics/Value/Laws.agda` are the
CATEGORICAL LAWS, and they are unreachable from every gate root. If the laws
were never wired to the apex, then "what `⊢ᵐ` was forcing" needs re-examining
from the start — check this BEFORE writing O2's answer.

**Then** finish `MeaningBridge` — its cata clause is what forced all this, and
with the parameterized fold it becomes an ordinary `RelT-bind` congruence like
the other four. The rest of `MeaningBridge` is already scoped:

  * DELETE `bridge-g`, `bridge-m`, `int-bridge`, `wrapM`, the three lift
    clauses; `named-sem` in `Denotation.Meaning` dies with `bridge-m`.
  * Seven point-free leaves reuse the OLD `bridge-m` bodies verbatim
    (`liftFn-id/fst/snd/terminal/inl/inr` all exist in `LiftFnReduce`).
  * Four combinators are `RelT-bind`/`RelT-return` congruences; `copair'`
    needs a `copair-rel` helper matching both injections.

## THEN

  * `Completeness` (32 realm sites) + `RealizeAgrees` — where `StrongElab`
    and `morph-elab` DISAPPEAR, taking D126's blocker with them.
  * The Canon family: `CanonReflectMutual` 21, `CanonPolyTransport` 10,
    `CanonReflectPolyTransport` 8, `CanonPreserveMutual` 6, `CanonComposeMid`
    5, `CanonPreserve` 3.
  * `ResolverBridge` 1.
  * **O2 is still owed** and is the plan's honest failure condition: `⊢ᵐ`'s
    structural recursion is what FORCED the categorical laws, and 15 spec
    rules are gone. Phase D must say where they are forced now. If there is
    no answer, D127 re-opens.
  * Phase C (O1: closed arms still emit `IR.∘`) is now a clean statement
    about the four closed morphisms alone — `compIR ∘ ⟨ lift-morphism a ,
    lift-morphism b ⟩ ≡ a ∘ b`.
  * Phase E: five surface sites use a literal as a compose arm and must be
    rewritten to `\_ -> …`; retire `closed-expr-lift.once`; add the test
    D127 is FOR (an arm capturing an enclosing binder).

## SUPERSEDED — the original Phase B note

The elaborator ALREADY checks each arm with `checkElabV` at the arrow type
(`checkComposeGo`, `Elaborate.agda:1716`). What changes:

  * drop `extract-morph-eff` / `extractMorphWitness` from the four combinator
    paths — both die with the realm;
  * the witness becomes `t-compose-check eqB wF wG` (etc.);
  * the usage becomes `Ψf +ᵘ Ψg`, not `zeroUsage`;
  * **the emitted term.** With `f : Expr Γ Ψ₁ (B ⇒[Many π] C)` and
    `g : Expr Γ Ψ₂ (A ⇒[Many π] B)`, the composite is the ordinary lambda

        lam Many (app (rename ⊆-wk f) (app (rename ⊆-wk g) (var zero)))

    at `π = pure`, and the `effApp` variant at `π = eff`. `rename` is
    `Once/Surface/Thinning.agda:183` — `(θ : Γ ⊆ Δ) → SExpr Γ Ψ A →
    SExpr Δ (thin-usage θ Ψ) A` — and `⊆-wk` (line 60) is the weakening.
    Expect `thin-usage`/`+ᵘ` rewriting at the usage index; the lemmas
    (`thin-usage-+ᵘ`, `thin-usage-refl`, `thin-usage-singleUse`) are already
    in that module.
  * delete `checkG` / `CheckGView` / `inspectCheckG` and the literal dispatch
    (B3) — a literal has ONE meaning at one type.

**Do not build C's specialization while doing B.** O1 (closed arms still emit
`IR.∘`) is a separate, PROVED equation used only in codegen; if it lands as a
typing-side premise the plan has failed its own point.

## HOUSE RULES THAT APPLY HERE

Top-down: make the change, follow the red, do not pre-build lemmas. Push every
commit. HANDOFF.md is untracked working notes — never `git add` it.

Gate scripts live in the session scratchpad: `judg.sh`, `arith.sh`, `gate.sh`
(j5 + apex), `island.sh`, `extract.sh`, `cabalbuild.sh`, `exit.sh`,
`fulltest.sh`, `chain.sh`. Poll the `.status` files. `make: *** Terminated` is
a sibling `pkill -x agda`, not a timeout — retry. The island backstop exits 2
on a PRE-EXISTING `Once/CCC/Machine/IR/ApplyWF.agda` module-arity rot; that is
not yours.

## OPEN, NOT ON THIS BRANCH

  * `plans/0.77-observe-compound-arguments.md` — `decode-unread`, the one new
    residual 0.72 merged. Heap-model work; starts with two questions, not Agda.
  * Float `%` still has no decision (D128 refuses it and pins the refusal).
  * `ApplyWF` island rot — pre-existing, unclaimed.
