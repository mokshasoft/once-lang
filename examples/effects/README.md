<!-- SPDX-License-Identifier: AGPL-3.0-or-later -->
<!-- Copyright (C) 2025-2026 Jonas Claesson -->

# Effects POC — OCP-0007 (capability-graded effects)

> **These examples do not compile today.** They are a *test-driven design*
> sketch of the surface proposed in
> [`docs/proposals/OCP-0007-capability-graded-effects.md`](../../docs/proposals/OCP-0007-capability-graded-effects.md):
> effects tracked as an inferred grade of **capabilities** (authority), with
> capabilities kept **orthogonal to interpretations**. They exist to
> pressure-test the ergonomics before any compiler work.

## The one thing to notice

**Composing effects uses the *same* operators as composing pure code**, and the
program never mentions a capability. You write `f >>> g`; the compiler infers
each computation's *needed* capabilities (bottom-up, by union) and checks they
are *granted* (top-down, from a root capability via attenuation). Read the
files in order — each adds one idea:

| File | Idea |
|------|------|
| `01-operations-and-policy.once` | Operations carry no caps; the policy is a separate, orthogonal artifact; the grade is **inferred**. |
| `02-compose-unions-capabilities.once` | `>>>` **unions** the needed capabilities, bottom-up. |
| `03-not-every-effect-is-a-capability.once` | Console is a capability (needs authority); State is a plain effect (just needs a handler). |
| `04-grant-and-attenuate.once` | `main` holds the root capability; grants discharge requirements; authority **attenuates** downward, never up. |
| `05-undergrant-is-a-type-error.once` | A capability is a **precondition**; under-grant is a **type error**, not a runtime check (D007). |
| `06-orthogonal-interpretations.once` | One policy, many interpretations (Linux/seL4/test); the **capability-secure unikernel**. |

## Where do the pieces live? (Ownership)

The whole design turns on keeping three things in different hands:

- **Operation** — *what it does* (`putLine : Eff (String Utf8) Unit`). Declared
  by the library **and its interpretations**. No capabilities here.
- **Capability policy** — *what authority it requires* (`require putLine :
  {Console}`). A separate, **orthogonal** artifact owned by the **deployment**,
  which chooses the granularity. The same operation under the same
  interpretation can carry different policies in different deployments.
- **Grant** — *who holds the authority* (`withConsole …`, attenuation in
  `main`). Flows top-down from the root capability.

This is why `! Cap`-style annotations on operations are gone: that would weld
authority to the library, which cannot know what a deployment wants to enforce.

## Do we need anything new at the surface? (Mostly no.)

- **Composition needs nothing new** — `>>>`, `compose`, `pair`/`both`,
  point-free, all identical to pure code; the cap grade rides along silently.
- **You rarely write the grade.** `→[{…}]` is mostly *shown to you by the
  compiler*, like an inferred type. You annotate only to assert a budget, and
  per D007 that annotation is a **check, never a coercion**.
- **New, but small and out-of-band:** a way to declare the orthogonal policy
  (`require …`) and the capability lattice. These live with the deployment, not
  the program or the operation.

## Side-by-side with Haskell

[`haskell/`](haskell/) implements the **same** State + Teletype program three
ways — `mtl`, `polysemy`, `effectful` — to show the structural cost of each.
The sharper contrast is on the next axis: none of those libraries track
**authority** or **information flow** at all. Capability-graded effects make the
effect system *also* an authorization and IFC system. See `haskell/README.md`.
