# Devil's Advocate: Challenging Once's Design Claims

*A critical examination of the structured recursion + effects design for future review*

---

## Purpose

This document captures challenges to Once's design claims. Each item should be:
1. Examined honestly
2. Either refuted with evidence, or acknowledged as a limitation
3. Addressed in documentation if the claim needs qualification

---

## Claim 1: Cata/Ana/Hylo + observation is complete for practical programming

**The claim:** All practical recursion patterns can be expressed with the recursion schemes plus observation primitives (obs, obsWhile, obsUntil).

**Challenge:** This is an empirical claim asserted without formal proof.

**Potential counterexamples examined:**

| Pattern | Challenge | Resolution |
|---------|-----------|------------|
| Dataflow analysis | "Iterate until fixpoint" — not structural? | Lattice has finite height h → bounded by h×n iterations. Structure exists. |
| Consensus (Paxos/Raft) | "Loop until agreement" — depends on network | Synchronous: terminates. Asynchronous: FLP impossibility. Real systems use timeouts. |
| Garbage collection | "Trace until done" — not structural? | Heap is finite → Cata over reachable objects. Structure exists. |
| SAT solving | Can run "forever" on hard instances | Search tree is finite → terminates. NP-complete ≠ non-terminating. |
| Training loops | "Until convergence" — may not converge | Either convergence is proven (structure exists) or should be bounded. |

**Current position:** The counterexamples either have hidden structure or are problematic (should be bounded anyway). Non-terminating "algorithms" aren't algorithms.

**Resolution:**
- Don't claim formal "completeness" — that requires defining "practical algorithm" precisely
- Instead claim: "covers all well-founded patterns we've encountered"
- Issue challenge to readers: show us a terminating algorithm that doesn't fit
- Shift burden of proof: if you can't prove termination, it's a bug, not a counterexample

**Documentation updated:**
- index.md: Added challenge to readers
- structured-recursion.md: Renamed "Completeness" to "Coverage", added challenge

**Status:** [x] Resolved — reframed as empirical coverage with open challenge

---

## Claim 2: Effects compose orthogonally via carrier type

**The claim:** No special effectful schemes needed. Use `Eff X Y` as carrier type, sequence with `>>>`.

**Challenge:** Several effect patterns may not compose cleanly:

### 2a. Short-circuiting

```once
-- Stop on first error
validateAll : List Input → Eff Unit (Either Error (List Output))
```

With carrier type approach:
- Algebra receives `Eff Unit (Either Error (List Output))` for rest
- To short-circuit, must avoid sequencing `restEff` on error
- Requires conditional effect execution — is this clean?

**Question:** Can short-circuiting be expressed cleanly, or does it require awkward encoding?

### 2b. Concurrent effects

```once
-- Process all elements in parallel
processAll : List Request → Eff Unit (List Response)
```

Sequential `>>>` doesn't capture parallelism. Need `(***)` and restructuring.

**Question:** Is parallel processing ergonomic, or does it require restructuring the recursion?

### 2c. Resource cleanup

If an effect fails midway through a Cata, what happens to resources acquired earlier?

**Question:** How does Once handle effect failure and cleanup? Is this the effect system's concern (outside recursion schemes)?

### 2d. Effect ordering

In `alg (Cons x restEff) = ...`, the algebra controls when `restEff` executes.

**Question:** Is the ordering intuitive? Left-to-right? Explicit?

**Current position:** These are effect system concerns, not recursion scheme concerns. The orthogonality claim is about structure, not about solving all effect problems.

**Analysis of sub-challenges:**

### 2a. Short-circuiting
- **Need:** ArrowChoice (`|||`) to branch effects based on sum type
- **Pattern:** `validateOne >>> (returnError ||| continueWithRest)`
- **Status:** Proposed in effects-proposal.md, needs implementation
- **Verdict:** Expressible but verbose; needs `|||`, `first`, `second`

### 2b. Concurrent effects
- **Need:** Parallel composition `(***) : Eff A B → Eff C D → Eff (A * C) (B * D)`
- **Status:** Derivable from `first`/`second` which come from products in IR
- **For lists:** Would need `parTraverse` or restructuring to nested pairs
- **Verdict:** Pairwise parallelism derivable; list parallelism needs dedicated combinator or runtime support

### 2c. Resource cleanup
- **Context:** D023 says no exceptions in Once — errors via sum types
- **With sum types:** Cleanup is explicit in error branch, not automatic
- **With linear types:** Resources must be consumed; compiler ensures cleanup
- **Verdict:** Orthogonal to recursion; handled by sum types + linear types

### 2d. Effect ordering
- **Programmer controls:** `effectForX >>> restEff` vs `restEff >>> effectForX`
- **Verdict:** Explicit and clear; not a problem

**Resolution:**
- "Effects compose orthogonally" is accurate for sequential effects (`>>>`)
- Branching/parallel effects need more Arrow infrastructure (ArrowChoice, `first`/`second`, `(***)`)
- This infrastructure is designed (effects-proposal.md) but needs implementation
- Resource cleanup is handled by sum types + linear types, not exceptions

**Status:** [x] Resolved — effects compose orthogonally; complex patterns need Arrow infrastructure (proposed, to be implemented)

---

## Claim 3: No special effectful schemes needed

**The claim:** Carrier-type approach is sufficient; CataEff/AnaEff would be redundant.

**Challenge:** Carrier-type approach may be verbose compared to dedicated schemes.

Compare:
```once
-- Carrier type approach
sumLogging : List Int → Eff Unit Int
sumLogging = Cata alg where
    alg Nil = arr (const 0)
    alg (Cons x restEff) = logInt x >>> restEff >>> arr (+ x)

-- Hypothetical CataEff approach
sumLogging : List Int → Eff Unit Int
sumLogging = CataEff alg where
    alg Nil = 0
    alg (Cons x rest) = log x; x + rest  -- effects implicit
```

**Question:** Is the verbosity acceptable? Does explicitness outweigh conciseness?

**Current position:** Explicitness is a feature — you see exactly where effects are sequenced. Verbosity is the cost of clarity.

**Analysis:**

Arguments for carrier-type approach:
1. **Explicitness** — Effect sequencing visible (`>>>`), aligns with Once philosophy
2. **No new primitives** — Uses existing Arrow infrastructure, simpler language
3. **Compositionality** — Arrow combinators reusable across contexts
4. **Clear ordering** — No implicit sequencing rules

Arguments for dedicated schemes:
1. **Conciseness** — Less boilerplate
2. **Familiarity** — Haskell's `traverse` is popular

**Resolution:** Carrier-type is philosophically consistent. For verbosity, provide **derived convenience combinators**, not new primitives:

```once
-- Derived, not primitive
traverseEff : Eff A B → List A → Eff Unit (List B)
traverseEff f = Cata alg where
    alg Nil = arr (const [])
    alg (Cons a restEff) =
        f a >>> arr (\b -> (b, ()))
        >>> second restEff
        >>> arr (uncurry (::))
```

Like `map` is derived from `Cata` — useful convenience without primitive machinery.

**Status:** [x] Resolved — carrier-type is sufficient; derive convenience combinators as needed

---

## Claim 4: Polynomial functors are sufficient

**The claim:** `K`, `Id`, `⊕`, `⊗` cover practical recursive types.

**Challenge:** Real programs use patterns that don't fit:

| Pattern | Why it doesn't fit |
|---------|-------------------|
| HOAS (higher-order abstract syntax) | `F X = (X → X) → X` — exponential functor |
| Typed ASTs (GADTs) | `Expr : Type → Type` — indexed types |
| Nested types | `Perfect a = Tip a \| Branch (Perfect (a, a))` — non-regular |
| Free monads | `Free f a` — higher-kinded |

**Question:** Are these exotic, or common enough to matter?

**Current position:** Polynomial functors cover common cases. Richer representations can be added later.

**Analysis:**

| Pattern | Use case | Assessment |
|---------|----------|------------|
| **HOAS** | Language implementations | First-order representations (de Bruijn) work |
| **GADTs** | Typed interpreters, safe APIs | Nice-to-have; most programs don't need |
| **Nested types** | Specialized structures | Rare; regular types with depth tracking work |
| **Free monads** | Effects-as-data, DSLs | Once uses Arrows — different design |

**Who needs these?**
- PL researchers: Yes
- Typed DSL builders: Sometimes
- Application developers: Rarely
- Systems programmers: Almost never

**Honest assessment:** Polynomial functors cover lists, trees, options, results, streams — the common cases.

**Key insight:** This is orthogonal to the core design. The functor representation is independent of:
- How Cata/Ana/Hylo work
- How effects compose (Arrows)
- The μ/ν split

Extending to richer functors (exponentials, indexed, nested) would expand WHAT we can recurse over, not change HOW recursion or effects work. It's like adding more base types — the core semantics stay the same.

**Resolution:** Current implementation scope, not fundamental design limitation. Polynomial functors are the starting point; richer representations can be added without redesign.

**Status:** [x] Resolved — orthogonal to core design; extensible when needed

---

## Claim 5: Hylo termination is acceptable

**The claim:** Hylo can diverge, but this is an acceptable hole.

**Challenge:** The "clean picture" downplays a real issue.

```once
-- This diverges
badHylo : Unit → Int
badHylo = Hylo alg coalg
  where
    coalg () = Cons 1 ()      -- Never produces Nil
    alg (Cons x r) = x + r    -- Never reaches base case
```

**Question:** How big is this hole? What percentage of Hylos are "safe"?

### Deep Dive: The TERMINATING Pragma

On investigation, the hole is in `sem-hylo` in `Once.Semantics.Core`:

```agda
{-# TERMINATING #-}
sem-hylo : ∀ (F : Functor) {A B : Set}
         → (⟦ F ⟧F B → B)  -- algebra
         → (A → ⟦ F ⟧F A)  -- coalgebra
         → A → B
sem-hylo F alg coalg x = alg (sem-fmap F (sem-hylo F alg coalg) (coalg x))
```

The `{-# TERMINATING #-}` pragma tells Agda to trust termination without proof.
This is problematic because the claimed totality of the IR relies on *proven*
properties, not trusted ones.

### The Category Theory Solution: Paramorphism

The established solution from category theory is **paramorphism (Para)**:

```
para : (F (μF × A) → A) → μF → A
```

Para gives the algebra access to both:
- The original substructures (μF values)
- The recursive results (A values)

**Key insight:** Para can be derived from Cata by returning pairs:

```agda
paraS alg x = proj₂ (cataS alg' x)
  where alg' fx = (⟨ sfmap F proj₁ fx ⟩ , alg fx)
```

**This is terminating without any pragma** because Cata is structurally recursive.

### Bounded Hylomorphism via Para

With Para, we can implement fuel-bounded iteration:

```
boundedHylo alg coalg (fuel, state) = para paraAlg fuel state
  where
    paraAlg gOfPairs state' =
      let gOfFuel = fmap proj₁ gOfPairs
          fLayer = coalg (gOfFuel, state')
          -- Apply continuations from gOfPairs to recursive positions
      in alg (fmap ...)
```

The `obs` function fits this pattern:
- Fuel: Nat (the count)
- State: Stream A
- Coalgebra: uses `out-μ` to destruct Nat, produces ListF with predecessor

**With Para-based implementation, `obs` terminates provably.**

### Analysis

| Hylo pattern | Terminates? | Why |
|--------------|-------------|-----|
| `Cata alg` (Hylo with id coalgebra) | Always | μ-type is finite |
| `obs n` (bounded by Nat) | Always | Para over Nat; structurally recursive |
| `obsWhile p` | If predicate fails | Depends on predicate + data |
| User-defined arbitrary | Maybe | Depends on coalgebra design |

**The hole compared to alternatives:**
- Smaller than general `fix` — must fit algebra/coalgebra pattern
- Larger than Cata alone — Cata on μ-type always terminates
- Para-based bounded Hylos: no hole! Termination follows from fuel structure

### Proposed Solution

1. **Add Para to IR** — Derived from Cata, terminating by construction
2. **Add BoundedHylo** — Uses Para, requires μ-type fuel
3. **Keep general Hylo** — For expert use with TERMINATING, documented limitation
4. **Migrate obs** — Rewrite using Para, remove reliance on trusted termination

See `docs/design/para-bounded-hylo.md` and `docs/design/para-implementation-draft.agda`.

**Resolution:** The hole is real but has a known fix. Para-based bounded Hylos terminate provably. General Hylo remains as escape hatch for cases requiring external termination arguments.

**Status:** [x] Path forward identified — add Para; migrate obs; document Hylo as expert-only

---

## Claim 6: The μ/ν split is worth the complexity

**The claim:** Distinguishing least (μ) and greatest (ν) fixed points prevents bugs.

**Challenge:** Adds cognitive overhead.

- Every recursive type requires deciding: μ or ν?
- CoList is "maybe finite, maybe infinite" — confusing
- How often would you accidentally Cata an infinite structure anyway?

**Question:** Does the safety justify the complexity?

### Connection to Termination (Claim 1)

The μ/ν split is **the same principle** as "non-terminating algorithms are bugs" — just enforced at the type level:

| Perspective | Without split (Haskell Fix) | With split (Once μ/ν) |
|-------------|----------------------------|----------------------|
| Termination | `cata alg (ana coalg x)` may hang | Type error: can't Cata a ν-type |
| Computability | Turing-complete | Sub-Turing (total) |
| Philosophy | Non-termination is possible | Non-termination prevented by types |

**The split IS what prevents Turing from entering.** Without it, general recursion sneaks back in via `Cata ∘ Ana` composition on the same type. The split forces you through observation primitives (`obs`, `obsWhile`) which bound the computation.

This reframes the "cognitive overhead" — it's not arbitrary complexity, it's the **type-level manifestation of totality**.

### Library Functions Reduce Cognitive Load

For common cases, users don't think about μ vs ν:

```once
-- Library provides familiar names:
List A      -- finite lists (μ internally)
Stream A    -- infinite streams (ν internally)
Tree A      -- finite trees (μ internally)

-- Observation handles boundaries:
take    : Nat → Stream A → List A      -- ν → μ, bounded
toList  : CoList A → Maybe (List A)    -- ν → μ, if finite
```

Most programmers work with `List`, `Stream`, `Tree` — not raw `μ F` and `ν F`. The split surfaces only when:
1. Defining new recursive types
2. Crossing ν → μ boundaries (which forces bounding)

**The cognitive load is localized** to type designers and boundary crossings, not everyday programming.

### Analysis

**The bug prevented:**
```haskell
-- Haskell: typechecks, hangs silently
sum (ana (\n -> Cons n (n+1)) 0)

-- Once: compile-time error
sum infiniteStream  -- Type error: Stream ≠ List
```

**Cost-benefit (revised):**
| Without split | With split |
|---------------|------------|
| Turing-complete | Sub-Turing (total/productive) |
| Silent hang in production | Compile-time error |
| No upfront cost | Library hides most complexity |
| General recursion possible | Must use bounded observation |

**CoList clarified:** "Might be finite, might not" — use for external data where finiteness is unknown. Pattern: `obs n` or `obsWhile` to bound before folding.

**Verdict:** The split is not "extra complexity" — it's the **mechanism** that makes Once total. Library abstractions hide the details for common cases. The "overhead" is paying for what you're actually getting: guaranteed termination.

**Status:** [x] Resolved — the split prevents Turing-completeness; library abstractions minimize cognitive load

---

## Claim 7: Arrows are better than monads for effects

**The claim:** Arrow-based effects (Eff, >>>) are preferable to monadic effects.

**Challenge:** Trade-offs exist — monads are more familiar to most FP programmers.

**Question:** Is the unfamiliarity cost justified?

### Reframing: It's Not a Choice

The framing "Arrows vs Monads" is misleading. **Once's IR is a CCC** (Cartesian Closed Category). What we call "arrows" are just the morphisms:

| CCC concept | Once IR | "Arrow" vocabulary |
|-------------|---------|-------------------|
| Morphism A → B | `IR A B` / `Eff A B` | Arrow |
| Composition ∘ | `_∘_` | `>>>` |
| Products | `⟨_,_⟩`, `fst`, `snd` | `(***)`, `first`, `second` |
| Coproducts | `case`, `inl`, `inr` | `(⎮⎮⎮)`, `left`, `right` |
| Exponentials | `curry`, `apply` | `arr` |

**"Arrows" aren't a design choice — they're what computation looks like in a CCC.**

Monads would be an additional abstraction layer *on top of* the categorical foundation, not an alternative to it. You could add monadic sugar that desugars to morphism composition, but the morphisms are fundamental.

### Parallel to Claim 6

This is the same pattern as the μ/ν split:

| Claim 6 | Claim 7 |
|---------|---------|
| μ/ν split isn't "extra complexity" | Arrows aren't "a choice over monads" |
| It's the mechanism for totality | It's what morphisms look like in a CCC |
| Library functions hide the details | Combinators are just categorical structure |

### The Real "Familiarity Cost"

The cost isn't "learning Arrow combinators" — it's **learning to think categorically**:

- Morphisms compose: `f >>> g >>> h`
- Products give parallel structure: `f *** g`
- Coproducts give branching: `f ||| g`
- No hidden control flow (no exceptions, no implicit sequencing)

This is a feature, not a bug. The categorical view makes the structure explicit, enabling:
- Static analysis (compiler sees composition structure)
- Optimization (fusion, reordering where safe)
- Reasoning (categorical laws)

### Monadic Sugar (If Desired)

For adoption, monadic syntax could desugar to morphisms:

```once
-- Sugar
do x <- readFile path
   y <- process x
   writeFile out y

-- Desugars to
readFile >>> process >>> writeFile out
```

This aids familiarity without changing the categorical foundation.

**Verdict:** "Arrows" are just morphisms in the CCC — not a choice, but the natural representation. The "familiarity cost" is learning categorical thinking, which pays off in explicit structure and optimization opportunities.

**Status:** [x] Resolved — Arrows ARE morphisms in the CCC; not a choice over monads but the fundamental abstraction

---

## Claim 8: The formal development is sound

**The claim:** Once's recursion schemes have solid theoretical foundations.

**Challenge:** The Agda development has gaps.

| Component | Status |
|-----------|--------|
| IR definition | Complete |
| Functor semantics | Complete |
| Coherence proofs | Complete for polynomial functors |
| sem-cata termination | Sound (structural recursion on μS) |
| sem-ana productivity | Uses `{-# TERMINATING #-}` pragma |
| sem-hylo termination | Uses `{-# TERMINATING #-}` pragma |
| Primitive operations | Postulated |

**Question:** What exactly is proven vs. trusted?

**Current position:** Core Cata is proven; Ana and Hylo use trust pragmas; primitives are trusted.

**Analysis:**

| Component | Mechanism | Trust level |
|-----------|-----------|-------------|
| IR definition | Agda datatype | Verified (type-correct by construction) |
| Type semantics | Agda functions | Verified |
| Coherence | Agda proofs | Verified for polynomial functors |
| sem-cata | Structural recursion on μS | **Sound** (Agda's termination checker) |
| sem-ana | `{-# TERMINATING #-}` | **Trusted** (productivity argument informal) |
| sem-hylo | `{-# TERMINATING #-}` | **Trusted** (termination depends on coalgebra) |
| Primitives | Postulated | Trusted (standard practice) |

**The honest position:**
- **Cata is fully verified** — structural recursion on well-founded μS
- **Ana uses trust pragma** — productivity argument is informal (each step terminates, but Agda can't verify coinductive productivity)
- **Hylo uses trust pragma** — termination depends on coalgebra; Para-based bounded Hylo would be verifiable
- **Primitives are trusted** — same as any language

**Path to stronger guarantees:**
- Para: derivable from Cata, provably terminating
- BoundedHylo: via Para, provably terminating for bounded observation
- General Hylo: keep with trust pragma, document as expert-only

See Claim 5 for details on the Para solution.

**Status:** [x] Acknowledged — Cata sound; Ana/Hylo use trust pragmas; Para offers path to verified bounded recursion

---

## Claim 9: This design is practical

**The claim:** Once's approach works for real programs.

**Challenge:** Unproven at scale — no ecosystem, no production deployments yet.

**Question:** Is "practical" aspirational or demonstrated?

### Reframing: Constraints as an Edge

The constrained space (CCC + structured recursion + totality + productivity) is an **edge**, not a limitation. Same pattern as Claims 6 and 7:

| Claim | Seems like | Actually is |
|-------|------------|-------------|
| 6 (μ/ν split) | Extra complexity | Mechanism for totality |
| 7 (Arrows) | Unfamiliar choice | Morphisms in CCC — fundamental |
| 9 (Constraints) | Less expressive | Guarantees + predictability |

**The edge you get:**
- **No silent hangs** — guaranteed by μ/ν + totality
- **No GC mysteries** — linear types give predictable memory
- **Optimization visible** — categorical structure enables fusion
- **If it compiles, it terminates** — the program does what you think

This is like moving from Java to Haskell: you give up some "flexibility" (mutation everywhere, null everywhere) and gain guarantees (purity, types). The Once step is similar: give up unbounded recursion, gain termination guarantees.

### The Learning Investment

Yes, there's a learning curve:
- Categorical thinking (morphisms, composition)
- μ vs ν (finite vs infinite)
- Structured recursion (Cata/Ana/Para)

But this is an **investment**, not a tax. Once learned, you:
- Write programs that can't hang
- Reason about performance structurally
- Get optimization "for free" from the categorical structure

### The Bridge: Libraries + Examples

The learning curve is bridged by:

1. **Libraries for common types** — Users work with `List`, `Stream`, `Tree`, not raw `μ F`/`ν F`
2. **Derived combinators** — `map`, `filter`, `fold` — familiar names, structured implementation
3. **Real-world examples** — Show the 99.9% common patterns
4. **The constrained space helps** — Fewer ways to do things wrong means easier to find the right way

### Current Status (Honest)

| Aspect | Status |
|--------|--------|
| Core design | Sound, principled |
| Formal proofs | Substantial Agda development |
| Compiler | Working (C backend, some x86) |
| Examples | Toy-sized + competitive programming |
| Libraries | Minimal (Strata) — needs growth |
| Production use | None yet |

**What "practical" needs:**
- More library coverage (common patterns wrapped nicely)
- Real-world examples (not just toy programs)
- User experience feedback (error messages, learning curve)
- Performance validation at scale

**Verdict:** The design gives you an edge (guarantees) in exchange for learning (categorical thinking). Libraries and examples bridge the gap. "Practical" will be demonstrated as the ecosystem matures — the foundation is solid.

**Status:** [x] Resolved — constraints are an edge; learning curve bridged by libraries + examples; ecosystem needs growth

---

## Summary: Claims Status

| # | Claim | Status | Resolution |
|---|-------|--------|------------|
| 1 | Schemes are complete | ✓ Resolved | Reframed as "coverage" with open challenge |
| 2 | Effects orthogonal | ✓ Resolved | True for sequential; branching/parallel need Arrow infra |
| 3 | No effectful schemes needed | ✓ Resolved | Carrier-type approach; derive convenience combinators |
| 4 | Polynomial functors sufficient | ✓ Resolved | Orthogonal to core design; extensible when needed |
| 5 | Hylo termination acceptable | ✓ Path forward | Para-based BoundedHylo provably terminates; general Hylo expert-only |
| 6 | μ/ν split worth it | ✓ Resolved | Prevents Turing-completeness; library abstractions minimize cognitive load |
| 7 | Arrows > Monads | ✓ Resolved | Arrows ARE morphisms in the CCC; not a choice but the fundamental abstraction |
| 8 | Formal development sound | ✓ Acknowledged | Cata sound; Ana/Hylo use TERMINATING pragma; Para path available |
| 9 | Design is practical | ✓ Resolved | Constraints are an edge; learning curve bridged by libraries + examples |

---

## Next Steps

### Immediate (Para Implementation)
1. [ ] Add `paraS` to `Once.Functor.Base` (derived from `cataS`)
2. [ ] Add `Para` constructor to `Once.CCC.IR`
3. [ ] Add `sem-para` to `Once.Semantics.Core` (via `sem-cata`, no pragma)
4. [ ] Rewrite `obs` in `Once.Derived.Observation` using Para
5. [ ] Document Hylo as expert-only with external termination requirement

### Future
- Consider removing general Hylo if all uses can be Para-based
- Investigate Ana's TERMINATING pragma (productivity vs termination)
- Add ArrowChoice infrastructure for effect branching
- User experience testing as language matures

### Design Documents
- `docs/design/para-bounded-hylo.md` — rationale and plan
- `docs/design/para-implementation-draft.agda` — code sketches

This document should be revisited as Once matures.
