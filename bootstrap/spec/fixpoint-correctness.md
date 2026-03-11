# Fixpoint Correctness: Zero-Code TCB via Unique Fixpoints

## Core Insight

For a sufficiently constrained language, we can prove:

```
UNIQUE FIXPOINT EXISTS  →  REACHING FIXPOINT PROVES CORRECTNESS
```

This eliminates all code from the TCB. We trust only mathematics.

## The Argument

### Setup

Let L be a minimal language (subset of CCC IR).
Let N : L → L be a normalizer (reduces terms to normal form).
Let ⟦_⟧ : L → Set be the denotational semantics.

### Key Properties of CCC Reduction

1. **Confluence (Church-Rosser):**
   If t →* u and t →* v, then ∃w. u →* w and v →* w

2. **Termination:**
   All reduction sequences are finite.

3. **Unique Normal Forms:**
   From (1) and (2): every term has exactly one normal form.

### The Fixpoint Theorem

```
Theorem (Fixpoint Correctness):

Let N : L → L be any function.
If N(⟦N⟧) = ⟦N⟧  (fixpoint condition)
Then ∀t ∈ L. N(t) = nf(t)  (N computes normal forms correctly)

where ⟦N⟧ is the representation of N as a term in L
and nf(t) is the unique normal form of t.
```

### Proof Sketch

1. Assume N(⟦N⟧) = ⟦N⟧

2. Since CCC has unique normal forms, ⟦N⟧ must be in normal form
   (otherwise N(⟦N⟧) would reduce it further, contradicting fixpoint)

3. N maps ⟦N⟧ to its normal form (itself).

4. The semantics ⟦_⟧ is compositional:
   - N is built from CCC combinators
   - Each combinator has fixed semantics
   - N's behavior is determined by its normal form

5. Since ⟦N⟧ is in normal form and N(⟦N⟧) = ⟦N⟧:
   - N correctly normalizes at least one term (itself)
   - By compositionality, N correctly normalizes all subterms
   - By induction on term structure, N correctly normalizes all terms

6. Therefore N = nf (N computes normal forms correctly) □

## Why This Works for Minimal CCC

The minimal CCC has these properties:

| Property | Status | Reference |
|----------|--------|-----------|
| Confluence | Proven | Lambek & Scott, 1986 |
| Termination | Proven | Simply-typed λ-calculus |
| Unique NF | Follows | From above |
| Decidable equality | Yes | Syntactic |

For this restricted language, the fixpoint theorem is provable.

## The Minimal Language

The smallest CCC subset that can express a normalizer:

```
Types:
  T ::= Unit | T × T | T + T

Terms:
  t ::= id
      | compose t t
      | fst | snd | pair t t
      | inl | inr | case t t
      | terminal

No exponentials (no curry/apply) - added in Level 1
No recursion (no fold/unfold) - added in Level 2
```

Can this express a normalizer? Yes:
- Pattern matching via case
- Building results via pair
- Composition via compose

The normalizer operates on a **representation** of terms as data:

```
TermRep = μT. Unit                    -- id
            + (T × T)                 -- compose
            + Unit + Unit             -- fst, snd
            + (T × T)                 -- pair
            + Unit + Unit             -- inl, inr
            + (T × T)                 -- case
            + Unit                    -- terminal
```

## The Bootstrap Tower

```
┌─────────────────────────────────────────────────────────────┐
│ Level 0: Minimal CCC (no exponentials, no recursion)        │
│                                                             │
│ Prove: Unique fixpoint exists                               │
│ Result: Fixpoint = correctness, TCB = pure math             │
├─────────────────────────────────────────────────────────────┤
│ Level 1: CCC + Exponentials (curry/apply)                   │
│                                                             │
│ Prove: Extends Level 0 conservatively                       │
│ Result: Verified by Level 0                                 │
├─────────────────────────────────────────────────────────────┤
│ Level 2: CCC + Exponentials + Recursion (cata/ana)          │
│                                                             │
│ Prove: Termination by construction (OCP-0003)               │
│ Result: Verified by Level 1                                 │
├─────────────────────────────────────────────────────────────┤
│ Level 3: Full Once                                          │
│                                                             │
│ Result: Verified by Level 2 (self-hosting)                  │
└─────────────────────────────────────────────────────────────┘
```

## What We Need to Prove in Agda

### Part 1: CCC Reduction Properties

```agda
-- Confluence
confluence : ∀ {t u v} → t →* u → t →* v → ∃ w. (u →* w) × (v →* w)

-- Termination (via strong normalization)
terminating : ∀ t → Acc _→_ t

-- Unique normal forms
unique-nf : ∀ {t u v} → NormalForm u → NormalForm v → t →* u → t →* v → u ≡ v
```

### Part 2: Fixpoint Correctness

```agda
-- The representation of a normalizer as data
⟦_⟧ : Normalizer → Term

-- Fixpoint implies correctness
fixpoint-correct : ∀ (N : Normalizer) →
  N (⟦ N ⟧) ≡ ⟦ N ⟧ →
  ∀ t → N t ≡ nf t
```

### Part 3: Existence of Unique Fixpoint

```agda
-- There exists exactly one normalizer satisfying the fixpoint property
unique-fixpoint : ∀ (N₁ N₂ : Normalizer) →
  N₁ (⟦ N₁ ⟧) ≡ ⟦ N₁ ⟧ →
  N₂ (⟦ N₂ ⟧) ≡ ⟦ N₂ ⟧ →
  ∀ t → N₁ t ≡ N₂ t
```

## The Revolutionary Implication

If we prove the above in Agda:

```
Traditional TCB:          Our TCB:
─────────────────         ────────────────
Hardware                  Hardware
OS                        Mathematics (proven theorems)
Agda (~50k lines)
Normalizer (~100 lines)
                          That's it.
```

The Agda proofs are checked once, by Agda. But the RESULT is a mathematical
theorem. Once proven, we don't need to trust Agda anymore — we trust the
theorem itself.

Anyone can verify the theorem by:
1. Reading the proof (it's math, not code)
2. Checking it with any proof assistant
3. Checking it by hand

## Open Questions

1. **Self-representation:** Can minimal CCC represent its own terms?
   - Need to encode TermRep without recursive types
   - May need a fixed finite depth

2. **Normalizer expressibility:** Can we write a normalizer in minimal CCC?
   - No general recursion available
   - May need bounded iteration

3. **Bootstrapping the proof:** How do we trust the Agda proof?
   - The theorem is mathematical, independent of Agda
   - Multiple proof assistants can verify
   - Ultimately, human mathematicians verify

## Current Status (MinimalCCC.agda)

Compiles with Agda. Structure defined, key theorems postulated.

### Completed
- [x] Types: Unit, *, +, μF
- [x] Functors: Id, K, ⊕, ⊗
- [x] Terms: id, ∘, fst, snd, pair, inl, inr, case, terminal, In, cata
- [x] Reduction rules: CCC laws + cata-β
- [x] fmap for functors
- [x] Self-representation type (TermCode)
- [x] Fixpoint theorem statements

### To Prove
1. [ ] Confluence (parallel reduction technique)
2. [ ] Termination (strong normalization)
3. [ ] Unique normal forms
4. [ ] Define ⌜_⌝ encoding concretely
5. [ ] Prove fixpoint-correctness
6. [ ] Prove fixpoint-unique
7. [ ] Implement actual normalizer
8. [ ] Verify it reaches fixpoint
9. [ ] Bootstrap complete

## References

- Lambek, J. & Scott, P.J. (1986). Introduction to Higher Order Categorical Logic.
- Curien, P.-L. (1993). Categorical Combinators, Sequential Algorithms and Functional Programming.
- Thompson, K. (1984). Reflections on Trusting Trust. (The problem we're solving)
