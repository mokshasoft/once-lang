# HANDOFF — finish the SigOp-concreteness migration (Plan 0.58 / OCP-0006)

**DO NOT git-commit this file.** Branch: `ocp-0006-once-spec`. Plan:
`plans/0.58-once-spec-language-definition.md` (see the DECISION + Execution sections).
Memory: `project_plan_0_58_bridge_state`.

Per-module check: `timeout 250 formal/scripts/agda-safe.sh agda MODULE=Once/Path/File.agda`
(MODULE is a FILE PATH, not a dotted name). Apex: `formal/scripts/agda-safe.sh certified`.

---

## The one idea

A SigOp is an FFI/register-ABI boundary, so its types must be CONCRETE. Enforce this
BY CONSTRUCTION via a new predicate and thread the witness everywhere a SigOp is built.

`IsConcrete` (`Once.Functor.Translate`):
```
con-base : IsBaseType A → IsConcrete A
con-fun  : IsBaseType A → IsConcrete B → IsConcrete (A ⇒[ k ] B)   -- first-order fn ptr
```
Decider `isConcrete? : (A : Type) → Maybe (IsConcrete A)` in `Once.Functor.Decide`.

**ASYMMETRIC on a SigOp** (`SigOpInfo A B`): DOMAIN `A` is `IsBaseType` (a base scalar — a
higher-order callback ARG would need funext, out of scope, and doesn't work today anyway);
RESULT `B` is `IsConcrete` (base OR a first-order function pointer — gains first-class
references to first-order functions). `SigOpInfo` fields: `baseA : IsBaseType A`,
`conB : IsConcrete B`.

This is a JUSTIFIED SPEC REFINEMENT (top-down), NOT a proof shim: the spec was
under-constrained (`generic-semM` is a `postulate`, so a primitive's value is abstract over
arbitrary types), admitting programs a register machine cannot faithfully run.

---

## DONE — committed, each module green individually (WIP commits `c2538d68`..`f436a6f8`)

Foundation + the ENTIRE spec/reference-meaning layer is threaded:
- `Once/Functor/Translate.agda` — `IsConcrete` (`con-base`/`con-fun`).
- `Once/Functor/Decide.agda` — `isConcrete?`.
- `Once/SigOp/Info.agda` — `SigOpInfo` carries `baseA`/`conB`; `mk-info` threads them.
- `Once/Arith/SigOp/Builders.agda` — arith `con-base` codomains; `value-info`/`generic-info`/
  `arrow-info(-eff)` take `IsBaseType A → IsConcrete B`.
- `Once/Arith/SigOp/IntLit.agda`, `Once/Arith/SigOp/Block.agda` (`shape-as-type-base`).
- `Once/Surface/Syntax.agda` — `sigOp`/`closure` carry `IsConcrete A`; `poly` carries `IsConcrete T`.
- `Once/Surface/IR.agda` + `Once/Surface/Desugar.agda` — legacy `SurfaceIR.SigOp` carries the witness.
- `Once/Surface/Elaborate.agda` — `elaborate` reads the witness off `sigOp`/`closure`/`poly`.
- `Once/TypeCheck/Judgment.agda` — `m-named`/`m-named-resolved` carry `IsBaseType A × IsConcrete B`;
  `t-var-qualified/resolved/import` + `t-var-poly-instantiate` carry `IsConcrete T`;
  `extractMorphWitness` splits `con-fun bA cB → m-named … bA cB`.
- `Once/Denotation/Realize.agda` — reads the derivation's witness onto `Expr.sigOp`.
- `Once/Denotation/SourceDenote.agda` — reads it off `Expr.sigOp` (arrow → `con-fun bDom cCod`;
  non-arrow → `conc`).
- `Once/Denotation/Meaning.agda` — `named-sem` takes `IsBaseType A → IsConcrete B`; value-ref
  clauses use `value-info … base-Unit conc`.

**Also already done earlier this session (the bridge itself):** `bridge-i`, `bridge-c`,
apex `bridgeᵈ` (via `Once/Adequacy/MainMeaningBridge.agda`), and the `int`/`in-app`/`in`
leaves are discharged. Only the sigop leaves in `MeaningBridge` remain (see step 4 below).

---

## TODO — the deep half. Tree is RED until all of this lands.

Work bottom-up; typecheck each module, follow the red. Likely-affected set (from grep):
`TypeCheck/Elaborate`, `TypeCheck/Soundness`, `TypeCheck/Completeness`,
`Adequacy/{SourceFaithful,RealizeAgrees,ResolveFaithful,ResolverBridge,CanonComposeMid,
CanonPolyTransport,CanonPreserveMutual,CanonReflectMutual,CanonReflectPolyTransport,MeaningBridge}`.

### 0. FIRST add `IsConcrete-irrelevant` to `Once/Functor/Translate.agda`
Mirror the existing `IsBaseType-irrelevant`/`WellFormedF-irrelevant` (proof-irrelevance by
mutual induction: `con-base` uses `IsBaseType-irrelevant`; `con-fun` recurses). You WILL need
it to reconcile a DECIDED witness (`isConcrete? T`, elaborator side) with a DERIVATION-carried
witness (realize/judgment side) in `RealizeAgrees` and the `Canon*` transport proofs.

### 1. `Once/TypeCheck/Elaborate.agda`
Four emission sites produce BOTH a surface term AND a `t-var-*` derivation; the derivation now
REQUIRES the witness, so each site must DECIDE it and add a FAILURE branch for non-concrete refs
(this is the honest new behavior — a non-FFI-representable reference is a type error).
- `ext-arrow-info` (~1766) and `ext-resolved-info`/`ext-resolved-info-aux` (~1803/1811): add
  `IsBaseType A → IsConcrete B` params, thread to every `mk-info'` clause.
- `inferElabV-RQualified-aux` (~1786): arrow case — `with isBaseType? A | isConcrete? B` →
  `just bA | just cB` ⇒ `ext-arrow-info … bA cB` + `t-var-qualified eq (con-fun bA cB)`; else
  `failure …`. Non-arrow `(just ty)` case — `with isConcrete? ty` → `just conc` ⇒
  `Surface.sigOp (bare …) conc` + `t-var-qualified eq conc`; `nothing` ⇒ failure.
- `inferElabV-RResolved-aux` (~1817): same, `ext-resolved-info` + `t-var-resolved`.
- RVar-import (~1924): `Surface.sigOp (bare x) conc` + `t-var-import … conc`; `with isConcrete? T`.
- poly (~2412): `Surface.poly x T conc` + `t-var-poly-instantiate … conc`; `with isConcrete? T`.
- Pick/extend an `ElabError` constructor for the failure branches (grep the error datatype;
  reuse `UnboundVariable`-style or add `NonConcreteSigOpType`).

### 2. `Soundness` / `Completeness`
- Soundness (checkElab success ⇒ derivation): the produced `t-var-*` derivation now needs the
  witness — it is exactly the `conc`/`bA,cB` the elaborator decided in step 1; thread it.
- Completeness (derivation ⇒ checkElab succeeds): the derivation CARRIES the witness; the
  elaborator's `isConcrete? T`/`isBaseType? A` decision must reduce to `just <that witness>`.
  Since the type is concrete (the derivation says so), the decider returns `just`; reconcile the
  returned witness with the derivation's via `IsConcrete-irrelevant`.

### 3. Adequacy proofs
- `SourceFaithful` (`faithful : ⟦ elaborate e ⟧ᴰ ≡ ⟦ e ⟧ˢ`): both sides read the witness off the
  SAME `Expr e`, so it should stay `refl` — just add the witness binder to the sigOp/closure/poly
  clauses.
- `RealizeAgrees` (elaborate-term vs realize-term masquerade): the two terms carry a DECIDED vs a
  DERIVATION witness; reconcile with `IsConcrete-irrelevant` (and `IsBaseType-irrelevant`).
- `ResolveFaithful` / `ResolverBridge` / `Canon*` (resolver preserves/reflects typing): the
  resolver rewrites `RQualified→RResolved` etc. and transports `t-var-*` derivations — the type
  `T` is preserved, so `IsConcrete T` transports unchanged (thread the witness through; use
  `IsConcrete-irrelevant` where a fresh decision meets the carried one).

### 4. Discharge the sigop leaves in `Once/Adequacy/MeaningBridge.agda`
The 4 remaining leaf postulates are `sigop-ref-bridge`, `poly-ref-bridge`, `sigop-bridge`,
`cata-bridge`. The first three are now dischargeable because the derivations carry the witness.
Add helpers (funext-free):
```
base-rel→refl     : IsBaseType A → (v : ⟦ A ⟧ᴰ) → RelV A v v          -- induction on IsBaseType
concrete-rel→refl : IsConcrete B → (v : ⟦ B ⟧ᴰ) → RelV B v v          -- MUTUAL with:
RelT-refl         : IsConcrete B → (t : T ⟦ B ⟧ᴰ) → RelT B t t         -- ∀n → refl , concrete-rel→refl
```
`concrete-rel→refl` arrow case: given `RelV A x y` with `A` base, `base-rel→eq baseA` collapses
it to `x ≡ y`, so `v x ≡ v y` by `cong`, then `RelT-refl` on `v x`. (`base-rel→eq` already
exists in `MeaningBridge`, used by the `In` leaves.)
- `sigop-bridge` (bridge-m `m-named`): its `value-info` now carries `bA : IsBaseType A`,
  `cB : IsConcrete B` (from the derivation, via `Meaning.named-sem`). Update its signature to take
  them. Trace half `refl` (`value-info` is `Pure` ⇒ `emit-D … = []`). Value half:
  `base-rel→eq bA rv : forget a ≡ forget b` ⇒ `cong` the two `inject (semM (value-info …) …)`
  equal ⇒ `subst` into `concrete-rel→refl cB _`.
- `sigop-ref-bridge` / `poly-ref-bridge` (bridge-i/c value-refs): domain `Unit` (`forget tt`
  trivial), codomain witness `conc` from the derivation ⇒ `concrete-rel→refl conc`. (These leaf
  postulates in `MeaningBridge` currently pass `_` for the witness via `sigop-ref-bridge _ dγ₂`;
  once the derivation carries `conc`, pass it and discharge.)
- `cata-bridge` is INDEPENDENT of this migration (no sigop). Leave it postulated for now, OR
  discharge separately: strengthen its signature with the algebra relation `bridge-m alg`
  (passable from the `m-cata` site) then prove the `sem-cata` congruence over `cata-ev-algᴰ-D`.

### 5. Close out
`formal/scripts/agda-safe.sh certified` exit 0; then `make check-all` + `cabal test`. Update the
plan checklist, then continue P5 (rebuild `Once.Spec.Meaning`, canonicalize, delete duplicates,
update OCP-0006, delete the plan).

---

## Gotchas
- `agda-safe.sh` `MODULE=` is a FILE PATH (`Once/Foo/Bar.agda`), not a dotted module name.
- At an ARROW type, `IsConcrete` can ONLY be `con-fun` (`con-base` needs `IsBaseType (arrow)`
  which is uninhabited) — so `(con-fun bA cB)` is an exhaustive match there (as in
  `extractMorphWitness` and `SourceDenote`'s arrow `sigOp` clause).
- `IsBaseType`/`IsConcrete`/`WellFormedF` are proof-irrelevant — use the `-irrelevant` lemmas to
  equate a decided witness with a carried one; DON'T fight over which proof term you have.
- The elaborator failure branches are a genuine BEHAVIOR change (non-concrete refs now rejected).
  Expect Soundness/Completeness to need real (not purely mechanical) updates around them.
- Don't use `RelT-bind`/`RelT-return` at bridge call sites — inline `∀ n` (see the existing
  `bridge-g`/`bridge-m`/`bridge-i` clauses for the validated technique).
- Two internal SigOp construction sites do NOT come from a derivation and supply CONCRETE
  witnesses directly: arith/lit/block (`con-base base-Int` etc.) and `shape-as-type-base`.
