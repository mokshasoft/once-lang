# Phase 2A Alignment Blocker — `instr-alloc-stack` divergence

**Date:** 2026-05-18
**Status:** Diagnostic — what's blocking each producer's `trace-is-ir-to-trace = refl`

## Summary

After Phase 1A added `trace-is-ir-to-trace : trace ≡ ir-to-trace-at-frontier (next-slot alloc) ir` to `IRResultBase`, four heap-mode producers (`SimpleWF`, `SumInlHeapWF`, `SumInrHeapWF`, `CurryHeapWF`) accept `refl` definitionally. Every other producer (10 of 14) hits the same structural divergence: their WF spec emits `instr-alloc-stack <scratch-count>` as a proof-side bookkeeping instruction that `IRToTrace` does not emit.

## The divergence

Each producer's WF spec follows the pattern:

```agda
setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ instr-alloc-stack <scratch-size> ∷ []
                                                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                                                       ⚠ NOT EMITTED BY IRToTrace
```

But `IRToTrace.ir-to-trace'` threads its slot frontier `n` internally as a function-local counter — it doesn't emit `instr-alloc-stack` instructions for the per-IR scratch budget. The function's prologue (`subq $stack-budget*8, %rsp`) allocates the entire frame upfront.

So at runtime, `instr-alloc-stack` is *not part of the emitted trace*. The WF spec putting it in `setup-trace` is purely proof-side bookkeeping — it makes `alloc.next-slot` match what sub-IRs need when reasoning under `exec-trace`.

## Affected producers (`trace-is-ir-to-trace = SMP.!!`)

| Producer | `instr-alloc-stack` scratch | Used by |
|----------|------------------------------|---------|
| `PairHeapWF.run-pair-heap` | `pair-heap-overhead = 4` | Heap-mode pair (Layer 2+) |
| `PairWF2.run-pair` | `pair-overhead = 3` | Stack-mode pair (escape-analyzed sites) |
| `CurryWF.run-curry` | `closure-slots = 2` | Stack-mode curry (dead path) |
| `CurryHeapWF.run-curry-heap` | — | **Already refl** (no instr-alloc-stack in trace) |
| `ApplyWF.run-apply` | `pair-slots = ?` | Apply (Layer 2+) |
| `ComposeWF.run-compose` | — (via rec-wf threading) | Compose (every Layer 0+) |
| `SumRecWF.run-inl` (Stack) | `sum-slots = 2` | Stack-mode inl |
| `SumRecWF.run-inr` (Stack) | `sum-slots = 2` | Stack-mode inr |
| `SumRecWF.run-case` | — (via rec-wf threading) | Case (Layer 2) |
| `AnaWF`, `ParaWF`, `RecCoreWF`, `RecTrace` | various | Recursion schemes (Layer 3+) |

`ComposeWF` and `SumRecWF.run-case` don't directly emit `instr-alloc-stack`, but they thread `f-trace`/`g-trace` from sub-results via `rec-wf` — those sub-results have non-`refl` traces if they're affected, so the compose-of-them transitively diverges.

## Why this design was chosen

`PairHeapWF.setup-trace` documents the rationale:

> Plan 0.14: setup ends with `instr-alloc-stack pair-heap-overhead` so the runtime next-slot bumps to match `alloc-after-scratch` (= the construction-time alloc passed to f's rec-wf). Eliminates the runtime/construction-time alignment story that PairWF2 had to thread by hand.

The `instr-alloc-stack` in the WF spec keeps `alloc.next-slot` in sync between (a) the alloc threaded into f's `rec-wf` (which is `alloc-after-scratch = record alloc { next-slot = next-slot alloc + scratch }`) and (b) the runtime `exec-trace` state passed to f-trace. With instr-alloc-stack, both have `next-slot = next-slot alloc + scratch`.

This made the alloc-correct chain (which proves runtime alloc matches the WF-tracked alloc) discharge cleanly via segment-by-segment `cong proj₂` chains.

## What the principled alignment requires

To make `trace-is-ir-to-trace = refl` work, every producer above must drop `instr-alloc-stack` from its setup-trace. That re-introduces the construction-vs-runtime alloc divergence:

- **WF spec**: sub-IR `rec-wf` called with `alloc-after-scratch.next-slot = N + scratch`.
- **Runtime**: `exec-trace f-trace s alloc.next-slot = N` (no bump).
- After f runs:
  - WF: `result-f.final-alloc.next-slot = N + scratch + f-internal-bumps`
  - Runtime: `proj₂ (exec-trace f-trace s alloc).next-slot = N + f-internal-bumps`

Bridging needs one of:

1. **Per-producer alignment lemma**: `result-f.final-alloc.next-slot ≡ proj₂ (exec-trace f-trace s alloc).next-slot + scratch`. Provable since `exec-abstract`'s state output doesn't depend on `alloc.next-slot` (only `instr-alloc-stack` reads/writes it, by a constant delta). PairWF2-style threading.

2. **Generic invariance lemma**: `proj₁ (exec-trace t s alloc) ≡ proj₁ (exec-trace t s (record alloc { next-slot = n }))` for any `n`. Then the state is independent of `next-slot`, and only `alloc` projection needs the offset bridge.

3. **Refactor `IRResultAWF`**: replace explicit `alloc-after-scratch` with a "logical scratch" annotation, computed without an actual `record alloc` update. Decouples WF reasoning from `next-slot`.

(2) is probably the cleanest but is a new lemma over `exec-abstract` per instruction (most are nothing-uses-next-slot; instr-alloc-stack is the exception).

## Estimated effort

- Generic invariance lemma (option 2): ~1 session.
- Per-producer migration after the lemma: ~30 min each × 10 producers = 5 sessions.

Total: ~6 sessions to make `trace-is-ir-to-trace = refl` work universally.

## Lower-effort intermediate options

- **Migrate Heap-only producers first**: `PairHeapWF`, `ApplyWF`, `ComposeWF` (heap branches), `SumRecWF.run-case`. Skip stack-mode variants until `--alloc stack` is exercised by a runtime test. ~3 sessions.
- **Postulate trace-is-ir-to-trace for non-Layer-2 producers**: AnaWF, ParaWF, RecCoreWF, RecTrace stay postulated indefinitely until Layer 3+ work begins. Stack-mode pair/inl/inr/curry stay postulated until escape analysis lands.

The third pragmatic option is what's currently in place. The hidden gap is now a *visible* gap (named SMP.!! site per producer), per the goal of Phase 1A.
