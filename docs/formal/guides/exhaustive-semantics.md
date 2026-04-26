# Exhaustive Semantic Case-Splits — Usage Guide

**Status:** Adopted (plan 0.9 / D049). `--exact-split` enabled
project-wide; full error promotion deferred until the Phase D
discipline backlog is cleared.

## TL;DR

```agda
-- BEFORE: silent catch-all hides bugs.
exec-x86 _ xs _ = xs

-- AFTER: explicit per-constructor clauses, OR a named postulate.
exec-x86 (mov dst src) xs _ = exec-x86-mov-other dst src xs
{-# CATCHALL #-}            -- justified: operand product space is unbounded
```

Adding a new `Instr` constructor without updating the function is
now a compile error.

## What `--exact-split` does

Agda's case-tree compiler translates pattern-match clauses into a
decision tree. Some clauses can't be preserved as definitional
equalities — typically when a clause sits as a catch-all relative
to a more specific sibling. `--exact-split` emits a warning
`CoverageNoExactSplit` whenever this happens.

This catches the "silent catch-all" bug class: a function that
returns the same type as a state value and silently absorbs
unmodeled cases as identity / zero / no-op. The lea-offset bug was
hidden by exactly this shape:

```agda
exec-x86 (mov ...) xs _ = ...        -- 15 explicit clauses
exec-x86 (lea rax (base+disp ...)) xs frame = ...
exec-x86 _ xs _ = xs                 -- ← absorbs lea r9 (rip+disp N)
                                     --   silently as no-op.
```

With `--exact-split`, the catch-all warns. The author must either
enumerate exhaustively or explicitly opt into the catch-all with
`{-# CATCHALL #-}`.

## Project setup

Enabled in `formal/Once.agda-lib`:

```
flags: --exact-split
```

Every module under `formal/` inherits the flag. No per-module
opt-in needed.

## When to refactor a catch-all

Three options, in preference order:

### 1. Exhaustive enumeration

The default. Enumerate every constructor of the data type being
matched.

```agda
isUnitType : Type → Bool
-- Old (warns):
-- isUnitType Unit = true
-- isUnitType _    = false

-- New:
isUnitType Unit         = true
isUnitType Void         = false
isUnitType (_ * _)      = false
isUnitType (_ + _)      = false
isUnitType (_ ⇒[ _ ] _) = false
isUnitType (μ-type _)   = false
isUnitType (ν-type _)   = false
isUnitType Int          = false
isUnitType Float        = false
isUnitType Str          = false
isUnitType Buffer       = false
```

Adding a new `Type` constructor breaks this function — a
compile-time reminder to update it.

### 2. Routing to a named postulate

When enumeration is impossible (e.g. operand product space with an
unbounded `imm : ℕ → Operand` constructor), declare a postulate
that captures the unmodeled semantics, and route the catch-all
through it.

```agda
postulate
  exec-x86-mov-other : Operand → Operand → X86State → X86State

{-# CATCHALL #-}
exec-x86 (mov dst src) xs _ = exec-x86-mov-other dst src xs
```

The postulate appears in `make postulates`. The `CATCHALL` pragma
documents that this is intentional dispatch to a named axiom — not
silent identity. Reviewers compare against the postulate audit
surface.

### 3. `{-# CATCHALL #-}` with justification

When neither (1) nor (2) is feasible, use the pragma with a
justification comment. Each instance is a finite, greppable audit
artifact.

```agda
-- Decidable-equality witness: yes/no branch constructs an
-- inequality proof from the inner k≢k. Marked CATCHALL because
-- the case tree can't preserve definitional equality with the
-- `yes refl | yes refl` branch.
{-# CATCHALL #-}
... | yes _ | no k≢k = no λ { refl → k≢k refl }
```

Reviewers treat `{-# CATCHALL #-}` like `postulate`: the count
should be finite, justified, and not growing without scrutiny.
`make catchalls` lists every instance with file:line.

## Avoid these traps

### Trap 1: catch-alls preserve definitional reductions

A catch-all `f X _ = body` typically compiles to a case-tree branch
that returns `body` for any second argument **without splitting it**.
If a downstream proof relies on this reduction for a variable
input, fully enumerating the catch-all breaks the proof.

```agda
-- Original: `Zero ≤q q ≡ true` reduces by `refl` for any q.
Zero ≤q _    = true
One  ≤q One  = true
...
_    ≤q _    = false   -- catch-all: Zero ≤q q reduces unaffected.

-- Naive refactor: enumerates all 9 cases. Now `Zero ≤q q ≡ true`
-- is stuck because `q` is a variable; downstream proofs break.
Zero ≤q Zero = true
Zero ≤q One  = true
Zero ≤q Many = true
...

-- Correct refactor: keep `Zero ≤q _` as a single-clause branch so
-- the case-tree doesn't need to split the second arg.
Zero ≤q _    = true
One  ≤q Zero = false
One  ≤q One  = true
...
```

When the special-case branch is single-clause, the `_` on the
remaining argument doesn't trigger the warning.

### Trap 2: `with`-block bodies coupled to function shape

The `gtypeToType` / `typeToGType` round-trip proofs in
`Once.Grammar.Convert` use `with gtypeToType A | gtypeToType B`
and pattern-match the inner Maybes. They rely on Agda's case-tree
compiler absorbing all 3 nothing-cases into a single absurd branch
where `eq : nothing ≡ just t` is contradictory.

If you replace the function's catch-all with explicit
enumeration of all 4 Maybe×Maybe combinations, Agda no longer
absorbs the nothing-cases — the proof must add explicit absurd
clauses. Treat the function and its dependent proofs as a single
unit; refactor both together or neither.

### Trap 3: `(yes refl)` mixed with `(yes _)`

When you split a `Dec X` into a helper, use `(yes refl)`
consistently. Mixing patterns:

```agda
helper (yes refl) (yes refl) = ...
helper (yes _)    (no _)     = ...    -- ← warns: overlap with yes refl
helper (no _)     (yes _)    = ...
```

The case-tree compiler can't preserve `(yes _)` overlap-free with
`(yes refl)`. Use `(yes refl)` everywhere or none.

```agda
helper (yes refl) (yes refl) = ...
helper (yes refl) (no _)     = ...    -- ← exact-split clean
helper (no _)     (yes refl) = ...
helper (no _)     (no _)     = ...
```

## Auditing

Two finite, greppable audit surfaces:

```
make postulates-grep   # lists every `postulate` declaration
make catchalls         # lists every `{-# CATCHALL #-}` pragma
make exact-split-census  # counts unique CoverageNoExactSplit sites
```

Treat both pragma counts the way you treat the postulate count:
small, justified, and audited per change.

## Bug-Hiding Class — Closed

The motivating subset — **catch-alls that return the same type as
state and silently absorb unmodeled cases as identity / zero /
no-op** — is fully closed as of plan 0.9. Both known sites
(`exec-x86` and `instr-consumed-slots`) are now exhaustive at the
constructor level. Adding new `Instr` / `AbstractInstr`
constructors that allocate stack or mutate state forces those
functions to be updated.

## Discipline Backlog

`make exact-split-census` reports ~85 remaining sites. None are in
the bug-hiding class. They're in:

- `Once/TypeCheck/Elaborate.agda` — `inferElab` shape-mismatch
  catch-alls and `checkElab-RVar` failure-propagation patterns.
- `Once/Grammar/Convert.agda` — round-trip-proof-coupled
  `with`-blocks (see Trap 2).
- `Once/Parser/*.agda` — Token-enumeration boilerplate for the
  `Not*` predicates and `*View` classifiers.
- `Once/Grammar/ExprBridge.agda` — `complete-cmpWFraw` proof
  completeness.

Address file-by-file. Run `make compiler` between commits — some
catch-alls are load-bearing for proof reductions (Trap 1).

Once the backlog is cleared, flip
`-W error=CoverageNoExactSplit` in `Once.agda-lib` to enforce the
discipline mechanically.

## See Also

- Plan 0.9 (`plans/0.9-exhaustive-semantics.md`) — full plan
  including the gap-class catalogue (classes A–H).
- D049 in `docs/compiler/decision-log.md` — adoption decision and
  per-phase summary.
- `Once.CCC.Target.X86-64.DirectSimulation.exec-x86` — canonical
  example of the postulate-routing pattern.
- `Once.Optimize` — canonical example of the enumerate-everything
  pattern (24 IR constructors per view function).
