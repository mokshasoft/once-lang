# OCP-0007: Capability-Graded Effects

**Author:** Jonas Claesson
**Status:** Draft
**Created:** 2026-06-26

---

## Summary

Track effects as an inferred set of **capabilities** — the *authority* a
computation requires to run — carried as a grade on the arrow alongside the
existing QTT quantity and purity grades. Capabilities are **orthogonal to
interpretations**: the library (including its interpretations) declares only
*operations*; a separate **deployment policy** assigns capability requirements
at whatever granularity that deployment wants to enforce.

The **needed** capabilities of a computation are *inferred* bottom-up by union
from the leaf operations; the **granted** capabilities flow top-down from a
single root capability via attenuation. A capability is a **precondition**
(the Agda analogue is an instance/implicit argument `⦃ Cap c ⦄`); writing it in
a signature is a *check*, never a coercion (D007). Under-granted authority is a
**type error, not a runtime check** — there is no ambient authority.

One grade thus serves three jobs at once: effect tracking, authorization, and
information-flow control.

---

## Motivation

### The plumbing problem is already solved

Haskell needs a zoo of effect libraries (`mtl`, `free`, `polysemy`,
`effectful`, …) largely because monads don't compose: you stack transformers,
which forces two categories, O(n²) lifting, and effect order baked into the
type. Once already deletes this by construction — arrows, one unified graded
category (D046: `Eff A B ≡ A ⇒[ mk-kind Many eff ] B`), and a `Kind` that is a
*product of orthogonal grades* combined at composition. Composition needs
nothing new.

### What no mainstream effect system gives you

Those libraries track the *presence* of an effect. None of them track
**authority** (who is allowed to perform it) or **information flow** (what may
move from where to where). To build a capability-secure system — the seL4
model, or Multi-Level Security (MLS) — on top of them, you bolt on a *separate*
mechanism and keep it in sync by hand.

The first-principles goal here is to refuse that split. The same grade that
says "this touches the network" should say "this requires the network
capability," and the lattice that orders capabilities should enforce
no-write-down. The mistake to avoid is the one this proposal originally made:
**conflating what an operation *does* with what authority it *requires*.** Those
are owned by different people and must be separable.

---

## Proposal

### 1. Capabilities are an orthogonal arrow grade

The arrow grade gains a capability set. Conceptually:

```
Kind = Quantity × Purity × Capabilities
```

`Capabilities` is a set of capability labels ordered by a bounded lattice
(see §4). It composes by **join (union)** on `compose`/`pair`/`case`, exactly
as the quantity grade composes via the QTT semiring. It is *not* a wrapping
type constructor: `Cap[…]` is at most a compiler-side label (like the Plan 0.38
`!` annotation), so there is no transformer-style "lift" through an outer layer.

### 2. Ownership — capabilities are orthogonal to interpretations

This is the crux, and the correction this revision is built around.

- The library **and its interpretations** declare only **operations**
  (`Eff A B`) and their platform implementations. *Neither carries
  capabilities.* The interpretation is the library side — putting caps there
  would re-couple authority to implementation.
- The capability system is a **separate, orthogonal axis** (just as Quantity
  and Purity are orthogonal). The *same* operation under the *same*
  interpretation may carry *different* capability policies in different
  deployments; the *same* policy holds across interpretations.
- Capability requirements are assigned by the **deployment/policy author**, who
  owns granularity — split `FileRead` from `FileDelete`, attach an MLS level,
  or enforce nothing at all. Not the library. Not the interpretation. The
  library author cannot know what a given deployment intends to enforce, so the
  decision cannot live with them.

### 3. The capability set is a grade, combined by join, erased at compile time

- Sequential `>>>` and parallel `pair`/`both` both **union** the operand cap
  sets. `arr`/pure code contributes the empty set ∅.
- The grade is **static and erases at realization** — no runtime
  representation. Enforcement is the type system plus a single root grant at
  program start (§5), never a per-call runtime check.

### 4. The capability lattice and attenuation

Capabilities form a bounded lattice with a partial order = **attenuation**:

- A *stronger* capability discharges a *weaker* requirement (`FileRead ⊑
  FileReadWrite`): holding RW satisfies a Read requirement.
- You may **mint a weaker capability to pass downstream, never a stronger
  one.** Amplification is forbidden — this is the capability-safety invariant.
- MLS falls out as a special case: lattice points carry security levels and
  composition must respect flow constraints (no-write-down) unless a trusted
  `declassify` capability is in scope.

### 5. Two flows: needed (bottom-up) and granted (top-down)

- **Needed** capabilities flow **bottom-up**: inferred by union from the leaf
  operations through every composition. This is the *truth*, computed — like an
  inferred type, not something written by hand.
- **Granted** capabilities flow **top-down**: `main` holds the **root
  capability**; authority is attenuated as it is delegated to components.
  Granting a capability = **discharging** the corresponding requirement.
- The two flows meet at the **handler/grant site**. A program type-checks only
  when every needed capability has been discharged from root.

### 6. A capability is a precondition

The needed set behaves exactly like an accumulating **precondition**. The Agda
analogue is an instance/implicit argument: an operation requiring `c` is like a
function taking `⦃ Cap c ⦄`. Requirements accumulate bottom-up as unmet
obligations; granting supplies the instance; `main` is well-typed only when all
obligations are discharged.

Consequences:

- **Annotation is optional and is a *check*, not a coercion.** Per D007, a
  signature verifies but never changes the meaning of a program. So `→[{…}]`
  is mostly *shown to you by the compiler*; you write it only to assert a
  budget, and the compiler confirms the inferred set fits. You do **not** label
  every signature.
- **Under-granted authority is a type error.** A component without capability
  `c` in its grade *cannot call* an operation requiring `c` — rejected at
  compile time. There is no ambient authority.

### 7. Not every effect is a capability

Pure / in-language effects (`State`, `Error`, `NonDet`) are discharged by pure
handlers written in Once and carry **no** capability — they require no
authority over the outside world. Capabilities are specifically authority over
external resources. (In the example below, `State` carries no cap.)

---

## Example: composing under capabilities

The program mentions no capabilities at all — operations are plain `Eff`:

```once
-- operations: plain Eff. Capabilities are NOT a library/interpretation concern.
signature getLine : Eff Unit (String Utf8)
signature putLine : Eff (String Utf8) Unit
signature get     : Eff Unit Nat
signature put     : Eff Nat Unit

greet   = getLine >>> arr (\name -> "Hello, " ++ name) >>> putLine
bump    = get >>> arr succ >>> put
session = greet >>> bump >>> greet
```

The capability policy is a *separate, orthogonal* artifact (a deployment
choice, independent of which interpretation provides the operation):

```once
-- deployment policy (orthogonal to the interpretation):
require getLine, putLine : {Console}
-- State is discharged by a pure in-language handler → no capability
```

What the compiler **infers** — this is the authority manifest, not hand-written:

```once
greet   : Unit →[{Console}]            Unit
bump    : Unit →[{State Nat}]          Unit
session : Unit →[{Console, State Nat}] Unit    -- union, bottom-up
```

The precondition discipline, as a type error rather than a runtime check:

```once
-- a component whose granted budget is State only:
logOnly : Unit →[{State Nat}] Unit
logOnly = bump        -- ok: needs {State Nat}, has it
-- logOnly = greet    -- TYPE ERROR: greet needs {Console}, not in the grade
```

See [`examples/effects/`](../../examples/effects/) for a progression of
runnable-style sketches and a side-by-side comparison with Haskell `mtl` /
`polysemy` / `effectful`.

---

## Thought experiment: a capability-based unikernel OS

This grade is enough to express a capability-secure OS, with the policy checked
by the type system rather than a kernel.

- A Once unikernel is **program + interpretation linked into one image**; the
  interpretation stratum *is* the OS runtime. There is **no kernel/user
  boundary**.
- The layers compose orthogonally: interpretations provide operations; a
  **deployment policy** (separate) assigns capability requirements; **`main`
  holds the root capability** and attenuates authority top-down to components.
- Enforcement = **compile time** (the inferred cap grade + a type error on
  under-grant) **plus** the single root grant at boot. No runtime ambient
  authority, no syscall check.
- A component without a capability in its grade **cannot call** the operation —
  a type error. Its inferred type **is** its authority manifest.
- The result is a capability-secure OS whose security policy is verified by the
  type system and rooted at boot — and the *same* policy is reusable across
  interpretations (Linux dev box, seL4, bare metal), because capabilities are
  orthogonal to interpretations.

---

## Impact

### Performance

Standout win. Capability labels are compile-time grades that **erase**; there
is no runtime free-monad tree to interpret and no per-call authority check.
Enforcement cost over today's binary `eff` is **zero** — the policy is gone by
the time code runs, leaving only the root grant at boot.

### Expressivity

| | Before | After |
|---|--------|-------|
| **Least** (simplest program) | `=` — pure stays pure, no annotations | `=` — caps inferred, nothing to write |
| **Most** (maximum capability) | `↓` — effects are an undifferentiated blob; no authority, no flow control | `↑` — capability-secure programs, attenuation, MLS/IFC, all statically checked |

### Formal Verification — Blast Radius

Two structural facts bound the damage, both favourable (file-level specifics
omitted — they will drift):

- **The grade is a generalization, not a new mechanism.** Purity is already a
  two-point join-lattice and the morphism judgment is already grade-indexed by
  it (D066). Capabilities swap the two-point lattice for a finite-label
  lattice; the binary world is the special case.
- **The grade erases at realization.** Realization discards the grade and emits
  a grade-free IR, so everything downstream — abstract machine, codegen,
  targets, memory/allocator, optimizer, the abstract↔concrete trace bridges —
  is invariant to it and **not** in the blast radius.

So the affected surface is the *front* of the pipeline only: the kind
definition, the grade-indexed morphism judgment, the proofs that recurse on it,
and the elaboration that constructs kinds. The epicenter is the
composition/case/pair rules, which gain genuine capability-combination content.

**New proof obligations** (all mirror or extend existing shapes):
1. The capability grade is a bounded lattice (join laws; attenuation order) —
   parallels the QTT-semiring laws already proven for `Quantity`.
2. `compose`/`pair`/`case` combine the cap set lawfully — parallels existing
   quantity-combination lemmas.
3. Discharge soundness: a grant removes exactly the discharged capability;
   `main` well-typed ⟹ root grant covers the inferred needed set.
4. (Future) MLS non-interference modulo `declassify`.

**Risks to flag honestly:**
- **Re-disturbs recently-stabilized code.** Grade-indexing the morphism realm
  and the morph-complete discharge are recent and still carry scoped
  postulates; re-indexing the judgment reopens exactly those proofs.
- **Little existing join-threading to reuse** — the purity join is defined but
  not yet threaded through composition, so capability-combination in the
  combinator rules is largely net-new code.
- **PolyType carries the quantity grade only** — capability polymorphism in the
  user-polymorphism layer is extra work; v1 can defer it.

---

## Trade-offs

**Gained:**
- One inferred grade that is effect-tracking *plus* authorization *plus* IFC.
- Capability-secure programs with no ambient authority, checked statically.
- Policy orthogonal to interpretation — the same policy ports across targets.
- `effectful`-class performance for free (grades erase).

**Lost / cost:**
- A second non-trivial grade lattice (more inference, more error surface).
- Capability *order* in a sequence is decided by handler/grant structure, not
  the (unordered) cap set.
- Dynamic concerns (revocation) are out of reach of a static grade.

---

## Alternatives

- **Inline `! Cap` on operations.** Rejected: re-couples authority to the
  library/interpretation, exactly the mistake this revision removes. Granularity
  is a deployment concern.
- **`Cap (Eff …)` as a real wrapping monad/functor.** Rejected as a *layer*:
  it reintroduces lifting (the transformer problem one storey up). Acceptable
  only as compiler-side labelling, which is what the grade is.
- **Flat effect set / "domains."** Rejected: tracks presence but carries no
  authority or information-flow semantics, so it cannot express a
  capability-secure system.
- **IO monad + transformers, or a free/freer monad in the surface.** Rejected:
  reintroduces the two-category split / a runtime interpreter Once's
  compile-time grades avoid.

---

## Open Questions

- **Parameterized capabilities** (`Connect[host]`, `@Secret`) need indexed
  grades. Once plans to add **dependent types later** (kind TBD), which makes
  this tractable then rather than a hard blocker now; v1 can stay with flat
  labels.
- **Revocation** is dynamic; a static grade captures requirement/grant/
  attenuation but not runtime revocation. What stays static, what must be a
  runtime mechanism?
- **Linear/affine capabilities** (use-once authority) = capabilities × QTT
  interaction; the joint combination rules need working out.
- **MLS information flow** (no-write-down, trusted `declassify`) is the
  motivating case; the full non-interference proof is future work.
- **Where the policy artifact lives** and its surface syntax (per-operation,
  per-class, lattice declaration) — orthogonal to interpretations by decision,
  but the concrete form is open.
- **Vocabulary** — "capability" vs "authority"; how labels are namespaced
  against module/import provenance.

---

## Discussion

[Comments, concerns, resolutions as they arise.]
