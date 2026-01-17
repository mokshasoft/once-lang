# Architectural Proof Instructions

## Summary

- **No shortcuts**: Shortcuts take longer. Only the cleanest approach is good.

- **Top-down design**: Understand what "makes sense" semantically first, then make proofs align with that design.

- **No hard-coded numerics in signatures**: Function parameters should use symbolic names (e.g., `ir-stack-requirement ir`), not literal numbers.

- **Single source of truth**: `ir-stack-requirement` defines capacity needs once; all proofs derive from it.

- **Internal derivation**: If a sub-proof needs a numeric relationship, derive it internally - don't require callers to provide it.

- **Minimal caller burden**: Entry points should only require `StackCapacity s (ir-stack-requirement ir)` - nothing more.

- **Proofs at module top**: Helper proofs go in `private` blocks at module top, not in `where` clauses.

- **Name invariants, not relationships**: Names like `x≤y` or `2≤4` are wrong. Name what the invariant *means* (e.g., `frame-fits-in-capacity`), not the numeric relationship.

- **No backwards compatibility shims**: When changing design, change it cleanly.

## Proof Structure Patterns

- **Validity over encode**: Work with `ValidAt` internally. Use `encode` only at system entry/exit boundaries. Eliminates "bridging" conversions throughout the codebase.

- **Region-based memory**: Model memory as disjoint regions (stack, heap, code) rather than concrete address arithmetic. Prove disjointness by showing addresses belong to different regions.

- **Star-based execution**: Break execution into named phases (`setup-star`, `call-star`, etc.). Each phase has a result record. Assemble final result from phase results.

- **Capacity threading**: Bundle stack invariants into `StackCapacity` records. Thread capacity through proof chains - don't re-derive at each step.

- **Compute from codegen**: Derive slot counts from instruction lists (`instrs-consumed-slots`), not magic numbers. Single source of truth in `CodeGen.agda`.

- **No capacity weakening**: Take exact requirements. Don't derive `≥ 2` from `≥ 4` unnecessarily - pass the actual requirement through.

- **Single encode boundary**: `valid-from-encode` at entry, `addr-from-valid` at exit. All internal proofs use validity.
