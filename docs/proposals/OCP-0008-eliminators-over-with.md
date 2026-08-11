# OCP-0008: Eliminators over `with` (no opaque case-analysis in dependent Once)

**Author:** Jonas Claesson
**Status:** Draft
**Created:** 2026-06-30

---

## Summary

When Once gains dependent types, its object language should NOT inherit a raw
`with`-style construct. Case-analysis should elaborate to transparent,
motive-explicit eliminators (the categorical `case`/copair and `cata` Once
already has in its IR), with the scrutinee's defining equation available by
default. `with` is a metalanguage ergonomics wart, not a feature the verified
core should adopt.

---

## Motivation

Agda's `with` repeatedly blocks proofs in the Once development. Two distinct
problems, one fundamental:

1. **Syntactic (`...` ambiguity).** Nested `with`s attach continuation clauses
   by column/arity counting; same-arity neighbours mis-attach
   (`UnexpectedWithPatterns`, "constructor of the wrong datatype"). A shorthand
   defect — verbose full-LHS spelling works around it.

2. **Semantic (opacity) — fundamental.** `with e` compiles to an *anonymous
   auxiliary* whose internal case-tree is invisible to callers. A function
   defined by `with` is a black box: `f x` stays stuck and a proof cannot see or
   drive the internal split. The only recourse is to re-`with` the same `e` and
   hope Agda's abstraction aligns the two — impossible when `e` is buried inside
   a stuck term. (Concrete instance: Plan 0.52 `subsume-complete-RVar` could not
   drive the bare-builtin failure-aux's internal `≟T`.)

Root cause: `with` conflates (a) intensional case-analysis, (b) an *implicit*
motive, and (c) compilation to a *non-reusable anonymous* aux. (b)+(c) = opacity
= un-reason-about-able.

The development already routes around this with the **view / inspect idiom**:
reify the case-analysis as a datatype whose constructors carry the defining
equation (`cgv-just : checkG … ≡ just … → CheckGView …`,
`classifyBareBuiltin x : BareBuiltinClass x`). Matching a view refines indices
AND yields the equation, so proofs reduce. Every clean discharge went through a
view; every fight was a raw `with`.

---

## Proposal

For dependent Once:

- **No raw `with` in the object language.** Surface pattern-matching is sugar
  that elaborates to the eliminator (sum → `case`/copair morphism; inductive →
  `cata`/recursor). Once already has these as IR — they are named, transparent,
  motive-explicit terms one reasons about directly.
- **Explicit motive** where dependency is needed (cf. Coq `match … in … return …`
  / Lean), eliminating inferred-motive guesswork.
- **Scrutinee equation by default** (`case e as eq of …`) — the view idiom built
  in, rather than hand-rolled per call site. (Agda's `with e in eq` is the
  half-measure.)

This is just the surface-sugar → categorical-core discipline Once already
enforces everywhere else, applied to case-analysis.

---

## Impact

### Performance

No runtime impact (eliminators are what the IR already uses).

### Expressivity

| | Before | After |
|---|--------|-------|
| **Least** | raw `with`, opaque | sugar elaborates to eliminator; same surface ease |
| **Most** | = | = (eliminators are complete for the algebraic types) |

### Formal Verification

Proofs reason about named eliminator morphisms instead of anonymous auxiliaries
→ no opacity, no `...` ambiguity. Strictly easier.

---

## Trade-offs

**Gained:**
- Reasoning-transparent case-analysis; no stuck anonymous auxiliaries.
- Equations available by construction (view-by-default).

**Lost:**
- Implementation effort: an elaboration pass from surface match to eliminators
  with explicit motives.

---

## Alternatives

- **Keep `with`, fix the shorthand only.** Addresses (1) not (2); the opacity
  remains.
- **Mandate the view idiom by convention** (status quo in the proofs). Works but
  is hand-rolled per site and easy to forget.

---

## Open Questions

- Exact surface syntax for the explicit motive and the scrutinee equation.
- How far to push: only sums/inductives, or all matching?
- Interaction with the QTT grade discipline (does the motive see grades?).

---

## Discussion

Spun out of the Plan 0.52 M1 `subsume-complete-RVar/RApp` blocker (2026-06-30),
where mirroring the elaborator's `with`-defined bare-builtin failure-auxes was
unprovable from completeness. Details to be fleshed out later.
