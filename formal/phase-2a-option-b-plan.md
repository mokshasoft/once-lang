# Phase 2A Option B — split `alloc.next-slot` from `AllocState`

**Date:** 2026-05-18
**Status:** Plan; not yet executed

## The abstraction fight

`alloc.next-slot` currently does two unrelated jobs:

1. **Job A — runtime tracking:** bumped by `instr-alloc-stack` at execution.
2. **Job B — proof-side slot frontier:** "where this IR's scratch starts," threaded through `rec-wf`.

These got fused because `instr-alloc-stack` happened to update both. When PairHeapWF emits `instr-alloc-stack pair-heap-overhead`, jobs A and B align trivially. When `IRToTrace` drops the instruction (since the function prologue handles slot allocation), jobs A and B diverge but share a field — so the divergence becomes a hidden proof gap.

**Option B splits them.** Job A's bookkeeping moves to `regs.stackSlot` (already exists). Job B becomes an explicit parameter `start-slot : ℕ` threaded into the proof-side `RecDispatcherWF`. `alloc.next-slot` ceases to exist.

## Why this is "follow the typechecker"

Drop `next-slot` from `AllocState`. The typechecker flags every site (~835 by raw count). Each is either:

1. **Passive read** (`next-slot alloc` for some local computation): replace with `start-slot` parameter. Mechanical rename for the right scope.
2. **Active update** (`record alloc { next-slot = ... }`): producer wanted to pass a new start-slot to sub-IR; replace with direct `start-slot` arg.
3. **Semantic update** (`instr-alloc-stack`'s `exec-abstract`): becomes no-op on alloc; preserves regs.stackSlot.
4. **Bound checks** (`BeforeFrontier alloc loc` for stack locations): rephrase against `start-slot`.

Each error is a guided fix. Risk: there are cascading sites where I miss the right new parameter to thread.

## Migration order

Layered, low-coupling first:

1. **Define new shape** (1 session):
   - Remove `next-slot` from `AllocState`.
   - Add `start-slot : ℕ` parameter to `RecDispatcherWF` and `IRResultAWF` (or as a field).
   - Update `exec-abstract` for `instr-alloc-stack` / `instr-dealloc-stack` / `instr-reclaim-to` to be alloc no-ops.

2. **Migrate primitives + helpers** (2-3 sessions):
   - `SMPrimitives` module: update all signatures that mention `next-slot alloc`.
   - `Allocation` module: rephrase frontier predicates.
   - Slot-bound lemmas.

3. **Migrate producers** (~1 session each, ~12 producers):
   - SimpleWF (simple — minimal next-slot use)
   - ComposeWF
   - PairWF2, PairHeapWF (heart of the change)
   - CurryWF, CurryHeapWF
   - ApplyWF
   - SumRecWF, SumInlHeapWF, SumInrHeapWF
   - AnaWF, ParaWF, RecCoreWF, RecTrace

   Per producer:
   - Add `start-slot` to signature
   - Replace `next-slot alloc` with `start-slot` in scratch slot computation
   - Replace `record alloc { next-slot = ... }` for sub-IR dispatch with `start-slot + offset`
   - `trace-is-ir-to-trace = refl` should now work (gap closes)

4. **Migrate Dispatcher** (1 session):
   - `run-ir-wf` threading of start-slot.

5. **Migrate consumers** (1-2 sessions):
   - `IRTraceCorrect` bridges (which reference `next-slot alloc`).
   - `Compile` / `EntryPointCCC` (top-level callers; pass start-slot=0).

6. **Verify + cleanup** (1 session):
   - Layer 0/1/2 runtime tests still pass.
   - `trace-is-ir-to-trace = refl` everywhere (Phase 1A's structural goal achieved).
   - Drop now-unused proof scaffolding (`alloc-after-scratch` records, etc.).

**Total estimate: 15-20 sessions.**

## Risk surfaces

1. **`BeforeFrontier`-style invariants on stack locations.** Currently `BeforeFrontier alloc (AtStack frame k)` checks `k < next-slot alloc`. After the migration, this becomes `k < start-slot`. The invariant needs to thread start-slot too. This might require a parallel split in `BeforeFrontier` definitions.

2. **`stack-alloc-advances` and similar `alloc` advancement lemmas.** These currently model alloc.next-slot bumping. After the migration, they're either deprecated or split into start-slot-explicit versions.

3. **`exec-trace-preserves-frame` and `frame-preserved` fields.** Should be unaffected (next-slot was orthogonal to current-frame), but worth verifying.

4. **MAlonzo extraction.** Runtime semantics change for instr-alloc-stack means re-extraction. The actual emitted assembly shouldn't change (instr-alloc-stack already extracted as `sub $n*8, %rsp` — that's CODEGEN, not abstract semantics — see compile-abstract in AbstractToX86).

   Wait — if exec-abstract changes to no-op on alloc but compile-abstract still emits `sub $n*8, %rsp`, then runtime and abstract diverge. Need to also update compile-abstract to emit `[]`, AND verify the function prologue still allocates the full budget (it does — separately via ir-stack-budget).

## Stopping points

I'll commit after each producer migration. If any single producer's cascade exceeds ~1 hour, I'll pause and surface.

If risk #1 (`BeforeFrontier`) turns out to need its own architectural change, I'll pause and re-plan rather than push through.

## Smoke test

After migration completes:
- All 8 Layer 0/1/2 runtime tests pass.
- All `trace-is-ir-to-trace` are `refl` (or proven equality; no SMP.!!).
- No new postulates introduced.
- `formal/architecture.md` updated to reflect the new shape.
