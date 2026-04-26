# `--exact-split` Census (Plan 0.9 Phase A)

Date: 2026-04-25
Build: `make compiler` with `flags: --exact-split` in `formal/Once.agda-lib`
Result: 151 unique warning sites across 30 files (770 raw warnings,
multiplied by repeated type-checks across `make compiler` subtargets).

## Summary by file

| Sites | File |
|---|---|
| 33 | Once/TypeCheck/Elaborate.agda |
| 26 | Once/Optimize.agda |
| 22 | Once/Type.agda |
|  8 | Once/Grammar/Convert.agda |
|  6 | Once/CCC/Machine/SMPrimitives.agda |
|  4 | Once/Parser/TypeRelation.agda |
|  4 | Once/Parser/PolyType.agda |
|  4 | Once/Parser/ExprRelation.agda |
|  4 | Once/Parser/Expr.agda |
|  4 | Once/Parser/Core.agda |
|  4 | Once/CCC/Machine/SMCore.agda |
|  3 | Once/Parser/Module/Resolve.agda |
|  3 | Once/Parser/Module.agda |
|  3 | Once/Parser.agda |
|  2 | Once/TypeCheck/Raw.agda |
|  2 | Once/Parser/Module/OpName.agda |
|  2 | Once/Parser/Module/Import.agda |
|  2 | Once/Parser/Module/DeclTail.agda |
|  2 | Once/Parser/Lexer.agda |
|  2 | Once/CCC/Target/X86-64/Syntax.agda |
|  2 | Once/CCC/Target/X86-64/DirectSimulation.agda |
|  1 | Once/Parser/Type.agda |
|  1 | Once/Parser/Module/FunDef/Params.agda |
|  1 | Once/Parser/Module/FunDef/OpDecl.agda |
|  1 | Once/Parser/Module/FunDef/Body.agda |
|  1 | Once/Parser/Module/Core.agda |
|  1 | Once/Parser/Module/Alloc.agda |
|  1 | Once/Grammar/ExprBridge.agda |
|  1 | Once/CCC/Machine/WriteOps.agda |
|  1 | Once/CCC/Machine/IR/RecTrace.agda |

(X86-32 and RiscV64 DirectSimulation files do not appear because
`make compiler` only builds X86-64. Those files will need a separate
audit pass if they are added to the default build.)

## Targets not exercised by census

- `Once/CCC/Target/X86-32/DirectSimulation.agda`
- `Once/CCC/Target/RiscV64/DirectSimulation.agda`

These are listed in the plan as likely mirrors of the X86-64 catch-
all bug. Audit out-of-band by adding them to the build or running
agda directly.

## Classification

Patterns observed (clause head → bucket):

### Bucket 1: `view`-style classifiers — **catchall-justified**

The function's purpose is "is this constructor X, or anything else?".
Catch-all is the function's whole reason to exist.

Examples:
- `composeFirstView g = cf-other g`
- `composeSecondView f = cs-other f`
- `coprodView-gen {D} f eq = is-other-coprod ...`
- `dbView toks = db-other toks`
- `doView toks = do-other toks`
- `fstSndView f = fsv-other f`
- `classifyAppHeadView (RApp _ _) = ahv-other`
- `pairView ...` (in Optimize.agda — likely)

Mostly in `Once/Optimize.agda`, `Once/Optimize/Shape.agda`,
`Once/Optimizer/Normal.agda`. Phase C target.

### Bucket 2: equality tests (`*EqBool`) — **catchall-justified**

Boolean equality functions enumerate matching constructor pairs
and fall through to `false`.

- `typeEqBool`
- `quantityEqBool`
- `purityEqBool`
- `functorEqBool _ _ = false`

The "matching = true, anything else = false" idiom is the standard
encoding. Catch-all is correct.

### Bucket 3: typecheck/elaborate failure fallbacks — **catchall-justified**

User-facing `failure (...)` returns when an expression doesn't
match an expected shape. Catch-all encodes "all unmatched cases are
the same error".

- `checkCompose _ _ _ _ = failure (BuiltinTypeMismatch "compose")`
- `checkCurry _ _ _ = failure (BuiltinTypeMismatch "curry")`
- `checkPair _ _ _ _ = failure (BuiltinTypeMismatch "pair")`
- `checkElab-RVar` family (eight variants for each builtin)

Probably correct as-is, though a stronger discipline could enumerate
RawExpr constructors and emit per-shape errors. Defer.

### Bucket 4: parser fallbacks (`nothing` on failure) — **catchall-justified**

Combinator-style parsers return `nothing` on input that doesn't fit.

- `anyWordB _ = nothing`
- `allTrailing _ = false`
- `check _ = nothing`
- `goTypeAliasB _ _ _ = nothing`
- `.extendedlambda0 _ = nothing`

Correct: the type `Maybe A` already encodes "may fail". Catch-all
is just the failure branch.

### Bucket 5: tail-recursion `go` helpers — **catchall-justified**

Local helpers driving structural recursion to a base case.

- `go (_ ∷ rest) = go rest`
- `go (_ ∷ rest) pending = go rest pending`
- `go other args = mkSpine other args`

Catch-all encodes "recurse on tail, ignore head" or "no special
case applied". Idiomatic.

### Bucket 6: `with`-clause translation artifacts — **catchall-justified or fix**

Many warnings are about Agda-generated `with-NNNN` definitions
arising from nested `with` statements with overlapping inner
patterns. The catch-all is at the inner level (`... | _ = ...`)
and is usually a "we already matched the case of interest, this
covers the rest" pattern.

Examples:
- `... | _ = 0` (Once/CCC/Target/X86-64/Syntax.agda:203)
- `... | _ | _ = case f g` (Once.Optimize.with-2970)
- `... | yes _ | no _ = refl` (SMCore.agda:414)
- `... | yes _ | no k≢k = no (...)` (decidable-equality witnesses)

Most are harmless. A few may benefit from refactoring the `with`
into separate clauses, but the cost-benefit weighs against it.

### Bucket 7: SEMANTIC CATCH-ALL — **fix**

The dangerous one, exactly as predicted in the plan:

- `Once/CCC/Target/X86-64/DirectSimulation.agda:216`
  → `exec-x86 _ xs _ = xs`

This is the catch-all that hid the lea-offset bug. **Phase B fixes
this directly.**

### Other notable named-function catch-alls

These aren't view/eq/parser; need closer examination:

- `Once.Optimize.alg-tree alg-trace = flat alg-trace`
  (Once/CCC/Machine/IR/RecTrace.agda:386)
- `Once.CCC.Machine.SMPrimitives.classifyAppHead (RApp _ _) = nothing`
- `complete-cmpWFraw (pcm-lt dL dR) (acc rec) = complete-cmpWFraw ...`
- `composeArgB ctx (RVar name) A = composeArgB ctx (RVar name) A`
- `collectStringB (c ∷ cs) = collectStringB ...`
- `parseArrowTailWF`
- `skipNewlines`
- `TraceNoHeapWrites (_ ∷ t) = TraceNoHeapWrites t`

To classify per-site during Phase D.

## Bucket totals (approximate)

| Bucket | ~Count | Phase |
|---|---|---|
| 1: view classifiers | ~20 | C |
| 2: equality tests | ~10 (×~4 functions) | D |
| 3: typecheck failures | ~30 | D |
| 4: parser fallbacks | ~25 | D |
| 5: `go` helpers | ~10 | D |
| 6: `with`-artifact | ~50 | D |
| 7: **semantic catch-all (BUG)** | **1** | **B** |
| Other named | ~10 | D |

The dangerous bucket (7) has a single site, exactly the one the
plan was scoped around. Buckets 1–6 are mostly mechanical
`{-# CATCHALL #-}` markings with one-line justification comments.

## Recommendation for sequencing

Plan 0.9 estimated 1–2 hours per phase; this census shows Phase
D is closer to 4–8 hours of mechanical marking. Two viable paths:

**Path A — full plan, sequenced as written.** Land Phase B
(the actual bug fix) first as a small commit, then Phases C/D as
mechanical sweeps. Phase E flips error promotion only after D.

**Path B — Phase B + scoped Phase E.** Land Phase B; instead of
fixing all 150 with `CATCHALL` markers, scope `--exact-split`
enforcement to specific module subtrees (e.g., `Once/CCC/Target/`
where semantic correctness is critical). Defer the parser /
elaborator / optimizer subtrees as a follow-on plan.

Path B trades some completeness for a 1-session landing and a
permanent guarantee in the high-stakes subtree. Path A is the plan
as written and gives a uniform discipline across the codebase.

## Files for next phases

- Phase B: `Once/CCC/Target/X86-64/DirectSimulation.agda:216`
- Phase B (mirror, out-of-band): X86-32 + RiscV64 DirectSimulation
- Phase C: `Once/Optimize.agda` (26 sites — heavy mix of bucket 1+6)
- Phase D: everything else (per the file table above)
