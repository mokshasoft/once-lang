# OCP-0007: Graded Algebraic Effects via Effect-Row Grades

**Author:** Jonas Claeson
**Status:** Draft
**Created:** 2026-06-26

---

## Summary

Generalize the binary `Purity` component of `Kind` (`pure | eff`) into an
**effect-row grade** — a finite set of effect labels ordered by a bounded
join-semilattice. Composition combines rows by **union** (`∪`), exactly the way
the quantity component already combines by the QTT semiring. Algebraic
**handlers** become ordinary morphisms in the Interpretations stratum that
**lower the grade** (discharge a label). A complete program is one whose
top-level row has been driven to the irreducible platform set.

This makes Once a true *graded* effect language: effect tracking, combination,
and interpretation all fall out of the grading machinery Once already has, with
no monads, no monad transformers, and no runtime free-monad interpreter.

---

## Motivation

### The Haskell effect problem

Composing effects is the perennial pain point in Haskell, and the reason a zoo
of libraries exists (`mtl`, `free`, `freer-simple`, `polysemy`,
`fused-effects`, `effectful`, `cleff`). They each trade off on three axes —
**performance**, **expressivity**, **conciseness** — because they are all
working around two underlying problems:

- **(A) The plumbing problem.** Monads don't compose, so you stack
  *transformers*. That forces two categories (pure `a → b` vs Kleisli
  `a → m b`) with constant `lift`ing, O(n²) `MonadX (TransY m)` instances, and
  effect *order* baked into the type (`StateT s (Except e)` ≠
  `ExceptT e (State s)`).
- **(B) The interpretation problem.** You want to *name* an effect abstractly
  and give it multiple *interpretations* (prod vs test, IO vs pure). This is
  what the free/algebraic-effect libraries solve, at a recurring cost: free
  trees are slow to interpret, higher-order operations (`local`, `catch`,
  `listen`) are hard, and effect membership clutters every signature.

### Once already solved problem (A)

Three existing decisions delete the plumbing problem by construction:

- **Arrows, not monads** (`docs/design/io.md`): `Eff A B` is a first-class
  arrow; one composition operator serves everyone.
- **One unified graded category** (D046): `Eff A B ≡ A ⇒[ mk-kind Many eff ] B`.
  Purity is a *grade on the arrow*, not a wrapper type. Pure and effectful
  morphisms share one hom-set; value-lift (D018) embeds pure into effectful
  with no `lift` tower.
- **Kind is a product of orthogonal grades** (`formal/Once/Type.agda`):
  `Kind = Quantity × Purity`. `compose` already *combines* operand grades —
  for the quantity axis via the QTT semiring (D003).

So Once has no transformer stack, no n² lifting, no two-category bookkeeping —
the bulk of what the Haskell libraries spend their complexity budget on.

### The remaining gap (problem B)

`Purity` is **binary**: the type records *whether* a morphism is effectful,
never *which* effects. There are no effect rows and no handlers — `SigOp`s
lower directly to syscalls in the Interpretations stratum, which is the only
"interpretation" mechanism. Today you cannot express "uses `Console` and
`State` but not `FileIO`", cannot combine those abstractly, and cannot
reinterpret them (test double, pure state-threading).

`docs/design/categorical-foundations.md` already sketches the target shape:

```
(>>>) : Eff e1 A B -> Eff e2 B C -> Eff (e1 ∪ e2) A C
```

This OCP makes that real, as a second grade rather than a new mechanism.

---

## Proposal

### 1. Effect rows as a grade

Replace binary `Purity` with an effect-set grade over a bounded
join-semilattice:

```
Kind     = Quantity × Effects          -- was Quantity × Purity
Effects  = a finite set of effect labels  { Console, FileIO, State s, … }
           ∅  is bottom / unit              (pure  ≡  Effects ∅)
           ∪  is join                       (eff   ≡  any non-empty set)
```

`pure` and `eff` become the extremal points of the lattice, so the existing
binary world is the special case `{∅, non-∅}` — a strict generalization.

### 2. Grade combination is homogeneous with QTT

Each structural former combines the effect grade the same way it already
combines the quantity grade, just on the join-semilattice instead of the
semiring:

| former | quantity rule (existing) | effects rule (new) | rationale |
|---|---|---|---|
| `compose` | semiring `·` | `∪` | sequential: both run |
| `pair` (applicative / `both`) | `+` | `∪` | both run; independence enables parallelism |
| `case` | `⊔` (per-position max) | `∪` of branch rows | one branch runs, but the type is a conservative union |
| `id` / `terminal` / value-lift | unit | `∅` | pure by construction |

This dovetails with `docs/design/parallelism.md`: "only parallelize
applicative, not monadic" becomes a *checkable grade property* (a `pair` of
disjoint-or-commuting rows is safe to run in parallel) rather than a heuristic.

### 3. Rows are inferred by default

As with quantities (D003), the effect row is **inferred**. Users write
point-free morphisms; the compiler computes the union. Optional annotations
give a checked contract. This is the `mtl`-polymorphism benefit without the
constraint salad — and without `Member e es` boilerplate.

### 4. Handlers = grade-lowering morphisms in the Interpretations stratum

An algebraic handler is just a morphism that discharges one label from the row:

```
handleState  : s -> Eff (State s ∪ r) A B  ->  Eff r A (B × s)
runConsole   :      Eff (Console ∪ r) A B  ->  Eff (FileIO ∪ r) A B   -- reinterpret
pureConsole  :      Eff (Console ∪ r) A B  ->  Eff r A (B × List String) -- test double
```

This fits the three strata directly: **SigOps name effects; the
Interpretations stratum supplies handlers that lower the grade**. A runnable
program is one whose top-level row has been driven to `∅` (or to the
irreducible platform set, e.g. `{Linux}`). The free/`polysemy` modularity story
— multiple interpretations, reinterpretation, mocking — expressed as grade
arithmetic, not as an interpreter walking a syntax tree.

### 5. Scope of the first cut

First-order algebraic effects only. Higher-order/scoped operations (`local`,
`catch`, `listen`) and effects over linear (QTT-tracked) resources are called
out as explicit follow-ups (see Open Questions).

---

## Example: Composing Effects

Effect labels are declared per signature, extending the existing Plan 0.38 `!`
effect-shape annotation (`Once.SigEffect`). A morphism's row is then **inferred**
from the SigOps it transitively uses — no `Member`/constraint boilerplate.

```once
-- Each external arrow declares the effect label it inhabits.
signature getLine : Eff Unit String   ! Console
signature putLine : Eff String Unit   ! Console
signature get     : Eff Unit Nat      ! State Nat
signature put     : Eff Nat Unit      ! State Nat

-- greet uses only Console ops → row {Console}, inferred (no annotation written).
--   inferred kind:  Unit ⇒[ Many , {Console} ] Unit
greet : Eff Unit Unit
greet = getLine >>> arr (\name -> "Hello, " ++ name) >>> putLine

-- tick uses only State ops → row {State Nat}.
tick : Eff Unit Unit
tick = get >>> arr succ >>> put

-- Composing across DIFFERENT effects: the row is the UNION (the ∪ rule).
--   inferred kind:  Unit ⇒[ Many , {Console, State Nat} ] Unit
session : Eff Unit Unit
session = greet >>> tick >>> greet
```

Handlers live in the Interpretations stratum; each **discharges one label**,
lowering the grade. A program is runnable once its row reaches the irreducible
platform set:

```once
-- Handler signatures (grade-lowering morphisms; `r` is the residual row).
runState     : Nat -> Eff (State Nat ∪ r) A B -> Eff r        A (B * Nat)
runConsoleIO :        Eff (Console   ∪ r) A B -> Eff r        A B
pureConsole  :        Eff (Console   ∪ r) A B -> Eff r        A (B * List String)

-- Production: discharge State, then interpret Console onto the platform.
--   runState 0   : {Console, State Nat}  ↓  {Console}
--   runConsoleIO : {Console}             ↓  ∅       ✓ runnable
main : IO Unit
main = runConsoleIO (runState 0 session)

-- The SAME `session`, reinterpreted for a test — zero real IO, output captured.
test : Eff Unit ((Unit * Nat) * List String)
test = pureConsole (runState 0 session)
```

Two structural points the example makes concrete:

- **Order is set by handlers, not the type.** `runState`-then-`runConsoleIO`
  vs the reverse changes nothing in `session`'s (unordered) row; it is the
  handler application order that fixes semantics (the StateT-vs-ExceptT
  question, Open Questions §1).
- **Applicative composition unions rows too.** `both greet tick : Eff Unit
  (Unit * Unit)` has row `{Console, State Nat}`; when two rows are disjoint or
  commuting, this is the checkable license to parallelize from
  `docs/design/parallelism.md`.

---

## Impact

### Performance

Standout win, and the reason this beats the Haskell libraries rather than
matching them. Effect labels are **compile-time grades**, like quantities, so
they **erase**. There is no runtime free-monad tree to interpret: handlers are
morphism rewrites applied during lowering, and `SigOp`s already compile to
direct IR / direct syscalls. The first-order point-free IR has nowhere to hide
an interpreter, so you get `effectful`/`cleff`-class performance *by
construction*. Net runtime cost over today's binary `eff`: zero.

### Expressivity

| | Before | After |
|---|--------|-------|
| **Least** (simplest program) | `=` — pure stays pure, no annotations needed | `=` — rows inferred, no new burden |
| **Most** (maximum capability) | `↓` — effects are an undifferentiated blob; no abstraction, no reinterpretation | `↑` — named effects, abstract over rows, multiple interpretations, test doubles, checked contracts |

### Formal Verification — Blast Radius

Two structural facts about the proof architecture bound the damage, and both
are favourable (file-level specifics deliberately omitted — they will drift):

- **Purity is already a grade, not a wrapper.** Purity is a two-point
  join-lattice (`pure` the unit, `eff` absorbing) and the morphism judgment is
  already *grade-indexed* by it (D066). This OCP swaps the two-point lattice for
  a finite-label join-semilattice; it does **not** introduce a new structure.
  The binary world is the special case, so existing statements specialize
  rather than break in spirit.
- **The grade is erased at realization.** Realization discards the purity index
  and emits a grade-free IR. Everything downstream — abstract machine, codegen,
  targets, memory/allocator, optimizer, the abstract↔concrete trace bridges —
  is invariant to the row and is **not** in the blast radius.

So the affected surface is the *front* of the pipeline only: the kind
definition, the grade-indexed morphism judgment, the proofs that recurse on it
(completeness/soundness/determinism and friends), and the elaboration bridge
that constructs kinds. The epicenter is the composition/case/pair rules, which
today pin `pure`/`eff` and would gain genuine row-combination content.

**New proof obligations** (all mirror or extend existing shapes):
1. The effect grade is a bounded join-semilattice (assoc/comm/idem of `∪`, `∅`
   unit) — parallels the QTT-semiring laws already proven for `Quantity`.
2. `compose`/`pair`/`case` combine the row lawfully — parallels the existing
   quantity-combination lemmas.
3. Per-handler adequacy against the OCP-0024 trace semantics (`obs`) —
   genuinely new, but well-scoped per handler.

**Risks to flag honestly:**
- **Re-disturbs recently-stabilized code.** Grade-indexing the morphism realm
  and the morph-complete discharge are recent and still carry scoped
  postulates; re-indexing the judgment will reopen exactly those proofs, and
  some discharged cases may revert to obligations under the richer grade.
- **Little existing join-threading to reuse.** The purity join is defined but
  not yet threaded through composition, so the row-combination in the
  combinator rules is largely *net-new* code, not a find-and-replace.
- **PolyType carries the quantity grade only**, not purity. Effect-row
  polymorphism in the user-polymorphism layer is extra work; v1 can defer it
  (monomorphic rows at poly boundaries).

---

## Trade-offs

**Gained:**
- Named, combinable, reinterpretable effects with inferred rows.
- Algebraic handlers as ordinary morphisms — no new runtime, no interpreter.
- `effectful`-class performance for free (grades erase).
- A single homogeneous grading story: QTT and effects combine identically.

**Lost:**
- The type system grows a second non-trivial grade lattice (more inference,
  more error-message surface).
- Effect *ordering* is no longer visible in the type (see Open Questions);
  semantics is determined by handler application order, not the row.

---

## Alternatives

- **IO monad + transformers.** Rejected: reintroduces the two-category split
  and n² lifting that D046 / arrows already removed. Contradicts the
  foundation.
- **Free / freer monad in the surface language.** Rejected on performance: a
  runtime syntax tree to interpret is exactly what Once's compile-time grades
  and first-order IR let us avoid.
- **Stay binary (status quo).** Rejected: cannot name, combine, or reinterpret
  effects; blocks testable effectful code and modular interpretations.
- **Ordered effect rows (list, not set).** Deferred: encodes handler order in
  the type, but the modern consensus (`polysemy`/`effectful`) is an unordered
  set with order decided by handler application. Start there; revisit if a
  concrete need for type-level ordering appears.

---

## Open Questions

- **Effect ordering / non-commutativity.** A set grade discards the
  StateT-vs-ExceptT distinction. Plan: the row is an unordered set; *handler
  application order* decides semantics (state-on-error kept vs dropped). Should
  this be surfaced anywhere, or left entirely to handler composition?
- **Higher-order / scoped effects** (`local`, `catch`, `listen`). `curry`/
  `apply` (ArrowApply) give the raw power, but threading a handler through the
  sub-computation it scopes is the open research problem (Wu–Schrijvers scoped
  effects; the `eff` / in-and-out line). Out of scope for v1.
- **QTT × Effects interaction.** An effect consuming a *linear* resource (file
  handle, one-shot continuation) couples the two grades. Likely a unique
  opportunity (linearity-aware effects ≈ session types, affine handlers,
  provably-safe one-shot resumption), but the joint combination rules at
  `compose`/`case`/`pair` must be worked out together, not independently.
- **Surface syntax.** Do we expose `>>>`/`|||`/`***` and/or do-notation
  desugaring to arrow composition (the unimplemented items in
  `docs/design/effect-composition.md`)? Independent of this OCP but ergonomically
  linked.
- **Label identity.** Are effect labels nominal (`State s` per-`s`) or
  structural? How do they interact with module/import namespacing (D033-era
  provenance)?

---

## Discussion

[Comments, concerns, resolutions as they arise.]
