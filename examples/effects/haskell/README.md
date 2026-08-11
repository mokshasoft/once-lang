<!-- SPDX-License-Identifier: AGPL-3.0-or-later -->
<!-- Copyright (C) 2025-2026 Jonas Claesson -->

# The same program, three Haskell effect libraries

Each file implements the **same** program as the Once examples
(`03`–`05`): a `Teletype` effect (`readTTY` / `writeTTY`) and a `State Int`,
a `session` that greets, bumps the counter, greets again, plus a **pure
reinterpretation** for testing. The goal is to see, side by side, how much
*structure* each approach forces on you to do something Once does with plain
`>>>` and an inferred row.

> Illustrative — imports/pragmas/versions may need adjusting to typecheck.
> The point is the shape, not a build.

| File | Library | Effect set lives in… | Composing 2 effects | Reinterpret for test |
|------|---------|----------------------|---------------------|----------------------|
| `Mtl.hs` | `mtl` | a transformer **stack** (order fixed in the type) | every carrier needs an instance of **every** effect class (O(n²)) | a **second newtype** carrier + all instances re-derived |
| `Polysemy.hs` | `polysemy` | a type-level **row** `Sem r` + `Member` constraints | add a `Member` constraint; free-monad tree interpreted at run | swap one `interpret` handler |
| `Effectful.hs` | `effectful` | a type-level **row** `Eff es` + `:>` constraints | add a `:>` constraint; runs as `ReaderT IO` (fast) | swap one `interpret` handler |

## How Once differs (in one breath)

- **Composition operator:** unchanged. `mtl` needs `lift`/instances;
  `polysemy`/`effectful` need `Member`/`:>` plumbing. Once uses the same
  `>>>` it uses for pure code — the row is inferred and unioned by the compiler.
- **Effect order:** `mtl` bakes it into the stack *type* (`StateT s (ExceptT e)`
  ≠ the reverse). `polysemy`/`effectful`/Once all make the row unordered and let
  **handler application order** decide — Once agrees with the modern consensus.
- **Performance:** `mtl` is fast but rigid; `polysemy` pays for interpreting a
  free-monad tree at runtime; `effectful` is fast because it is `ReaderT IO`
  underneath. Once's row is a **compile-time grade that erases** — no runtime
  representation at all, and handlers are resolved during lowering. The thing
  these libraries trade against each other, Once gets by construction.
- **Boilerplate to declare an effect:** `mtl` = class + N instances;
  `polysemy`/`effectful` = a GADT + `makeSem`/`makeEffect` + interpreters; Once
  = a plain `signature` for the operation, with the capability assigned
  separately by the deployment policy.

## The axis these libraries don't have at all

`mtl`, `polysemy`, and `effectful` track the **presence** of an effect. None of
them track **authority** (who may perform it) or **information flow** (what may
move from where). To build a capability-secure system — the seL4 model, or MLS —
on top of them you bolt on a *separate* mechanism and keep it in sync by hand.

Capability-graded effects fold all three into one inferred grade: the same set
that says "this touches the console" says "this requires the console
capability," and the lattice that orders capabilities enforces no-write-down.
Authority is **orthogonal to the interpretation** and checked at compile time
(under-grant is a type error). That is the real differentiator — not just nicer
effect composition. See the parent `README.md` and the OCP.
