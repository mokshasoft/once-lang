# Devil's Advocate Analysis: Bootstrap Normalizer Proofs

**Date:** 2026-03-23 (Updated)
**Purpose:** Pre-publication review of mathematical claims vs. formal proofs

## Executive Summary

The proof system establishes a compelling argument for normalizer correctness via the fixpoint property.

**Key Finding:** The core TCB0 theorem (`fixpoint-property`) is **fully proven in Agda without any postulates**. The postulates are only used for general correctness claims (Theorem 4.1 in the paper), not for the fixpoint itself.

This means:
- **For TCB0:** The proof is complete and postulate-free
- **For general correctness:** Additional reasoning (partly prose) is needed

---

## 0. Critical Clarification: What Uses Postulates?

### Postulate-Free (Fully Proven)

| Theorem | File | Status |
|---------|------|--------|
| `fixpoint-property` | `Implementation/NormalForm.agda:97` | **PROVEN** (no postulates) |
| `noredex-fixpoint` | `Implementation/Normalize/Fixpoint/MainTheorem.agda` | **PROVEN** (structural induction) |
| `normalize-noredex` | `Implementation/Normalize.agda:43` | **PROVEN** (structural) |
| `encode-is-betanf` | `Foundations/BetaNormalForm.agda` | **PROVEN** (structural) |

### Uses Postulates (Conditional on EstablishedMath)

| Theorem | Depends On | Purpose |
|---------|-----------|---------|
| `confluence` | `complete`, `⟹-to-complete` | Unique normal forms |
| `CorrectNormalizer` properties | `strong-normalization`, `normalize-semantics-equiv` | General correctness |
| Theorem 4.1 interpretation | All postulates | "Fixpoint implies correctness" |

### Proof Chain for TCB0

```
fixpoint-property : (normalize ∘ normalize-encoded) ⟶* normalize-encoded
    │
    └── noredex-fixpoint normalize normalize-noredex
            │
            ├── noredex-fixpoint (structural induction, NO postulates)
            │       └── 14 case proofs with explicit reduction chains
            │
            └── normalize-noredex : NoRedex normalize
                    └── nr-cata nr-normalize-step (structural, NO postulates)
```

**The Implementation/ modules do not import EstablishedMath at all.**

---

## 1. Postulates vs. Established Lemmas

### The 4 Postulates in `EstablishedMath.agda` (lines 35-83)

| Postulate | Claimed Justification | Devil's Advocate Concern | Used By TCB0? |
|-----------|----------------------|-------------------------|---------------|
| `complete` | Lambek & Scott parallel reduction | No witness function constructed | **NO** |
| `⟹-to-complete` | Triangle lemma | Depends on `complete` | **NO** |
| `strong-normalization` | Tait's logical relations | μ-types need justification | **NO** |
| `normalize-semantics-equiv` | CCC soundness | Overly general claim | **NO** |

### Important: These Postulates Are NOT Used for `fixpoint-property`

The postulates exist to support:
1. **Confluence proofs** - needed for unique normal forms
2. **CorrectNormalizer** properties - termination, semantic preservation
3. **Theorem 4.1's meta-argument** - "fixpoint implies general correctness"

But the core TCB0 claim ("this normalizer achieves fixpoint on its own encoding") is proven by pure structural induction.

### Concerns (Only Relevant for General Correctness)

**Strong normalization scope**: The system has μ-types (inductive types with `cata`). The claim is that recursion is well-founded (strictly positive functors), but this is not formalized.

**`normalize-semantics-equiv` is suspicious**: Claims that for ANY endomorphism N and ANY term t, either `N ∘ t ⟶* t` or `t ⟶* N ∘ t`. This is stronger than standard soundness.

---

## 2. The Main Theorem Gap

### What the Paper Claims (Theorem 4.1)

> "If N satisfies the fixpoint property (N ∘ ⌜N⌝ →* ⌜N⌝), then N is correct (∀t. N ∘ ⌜t⌝ →* ⌜nf(t)⌝)."

### What Agda Actually Proves

**For TCB0 (postulate-free):**
```agda
fixpoint-property : (normalize ∘ normalize-encoded) ⟶* normalize-encoded
```

**As a lemma (postulate-free):**
```agda
noredex-fixpoint : ∀ {A B} (t : Term A B) →
                   NoRedex t →
                   (normalize ∘ encode t) ⟶* encode t
```

### The Gap (Only Affects General Correctness)

The paper's Theorem 4.1 claims correctness for ALL inputs. The Agda proves:
1. Fixpoint for NoRedex terms (via `noredex-fixpoint`)
2. The normalizer itself is NoRedex (via `normalize-noredex`)
3. Therefore, fixpoint holds for the normalizer (via `fixpoint-property`)

The step from "fixpoint holds" to "correct for all inputs" is the prose argument in Theorem 4.1, which relies on:
- Unique normal forms (needs confluence + termination postulates)
- Transparency of normal forms (meta-argument)

**For TCB0, this gap doesn't matter** - you only need the fixpoint itself, which is fully proven.

---

## 3. The "All Normalizers" vs "This Normalizer" Question

### For TCB0: This Normalizer

**Fully proven (no postulates):**
- `normalize-noredex : NoRedex normalize`
- `fixpoint-property : (normalize ∘ normalize-encoded) ⟶* normalize-encoded`

This is sufficient for TCB0: run the normalizer on its own encoding, verify the result.

### For General Claims: All Normalizers

**Not fully formalized:**
- The `CorrectNormalizer` record exists but isn't instantiated for `normalize`
- The general theorem "spec implies three properties" is not formalized
- Depends on postulates

---

## 4. Paper vs. Proofs: Key Differences

| Paper Claim | Agda Status | Gap | Affects TCB0? |
|-------------|-------------|-----|---------------|
| Fixpoint for this normalizer | **PROVEN** (`fixpoint-property`) | None | **NO** |
| Theorem 4.1 (fixpoint → correctness) | Prose proof only | Not formalized | No (meta-argument) |
| Lemma 4.1 (fixpoint → N is normal form) | Proven but trivial | Encodings always NF | No |
| Corollary 4.2 (uniqueness) | Not proven | Follows from 4.1 | No |
| Lemma 3.1 (encodings are NF) | **PROVEN** (`encode-is-betanf`) | None | No |
| Lemma 3.2 (encoding injectivity) | Claimed structural | Not explicit theorem | No |

---

## 5. Fixpoint Theorem Statement Analysis

### FixpointTheorem.agda (lines 61-63):
```agda
fixpoint-implies-betanf : (normalize ∘ normalize-encoded) ⟶* normalize-encoded →
                          IsBetaNormalForm normalize-encoded
fixpoint-implies-betanf _ = normalize-encoding-is-betanf
```

**This is almost trivial!** The proof ignores the fixpoint hypothesis entirely (`_`) and just returns `normalize-encoding-is-betanf`, which is proven independently.

This is correct but misleading - the theorem doesn't USE the fixpoint property.

---

## 6. NoRedex Definition: Is It Complete?

The `NoRedex` predicate defines 10 base cases and 5 recursive cases. Note:

```agda
-- Pair: not eta (⟨fst, snd⟩), and subterms are normal
-- Note: we don't check eta since handle-pair doesn't implement it
```

This is **intentional incompleteness**. The normalizer doesn't reduce η-redexes, so NoRedex doesn't exclude them.

**For TCB0:** This is fine - the normalizer is consistent with its own definition of "normal."

---

## 7. The SafeComp Constraint

`SafeComp f g` doesn't catch `fst ∘ ⟨h, k⟩` (a redex). Why?

**Answer** (from comments): "they don't arise in encoded terms."

**Critical assumption:** The normalizer only needs to handle patterns that appear in encodings.

**For TCB0:** This is validated by the fixpoint - if the assumption were wrong, the fixpoint wouldn't hold.

---

## 8. Is the Fixpoint Approach Novel?

### Related Work

- **Self-certification in F***: Bootstraps typechecker, but uses external Coq for proofs
- **CakeML verified bootstrap**: Self-compiling verified compiler, but proofs are in HOL4
- **CompCert TCB analysis**: Analyzes what must be trusted, but doesn't use fixpoint for correctness

### Novel Aspects of This Approach

1. **Fixpoint as correctness criterion** - The specific theorem "fixpoint ⟹ correctness" for CCC normalizers
2. **Zero-code TCB** - Trusting only mathematics, not tools
3. **Constrained language** - Using CCC's unique normal forms as the key enabling property
4. **Postulate-free fixpoint proof** - The core TCB0 theorem needs no axioms

### Precedents

- Kleene's recursion theorem
- Quines and reflective towers
- Thompson's "trusting trust" (the problem being solved)

**The novel contribution** is the precise mathematical theorem connecting CCC fixpoint to normalizer correctness, and the insight that CCC's confluence + termination + self-representation makes this work.

---

## 9. Recommendations Before Publication

### For TCB0 Claims: No Action Needed

The fixpoint proof is complete and postulate-free. You can claim:
> "We formally prove in Agda that our normalizer achieves fixpoint on its own encoding, without any axioms or postulates."

### For General Correctness Claims

If the paper claims Theorem 4.1 (fixpoint implies correctness for all inputs):

1. **Be explicit** that this is a meta-theorem argued in prose, not formalized in Agda
2. **Justify the postulates** - especially `normalize-semantics-equiv` and strong normalization for μ-types
3. **Clarify the trust model**: TCB0 for fixpoint, additional mathematical trust for general correctness

### Medium Issues

4. **Encoding injectivity**: Either formalize as Agda theorem or mark as "structural claim"
5. **η-redexes**: Clarify that the normalizer doesn't handle them and why this is acceptable

### Minor Issues

6. **`fixpoint-implies-betanf` is trivial**: Consider removing or renaming since it doesn't use the hypothesis

---

## 10. Final Assessment

### Strengths

- **Postulate-free fixpoint proof** - The core TCB0 theorem is fully proven
- Elegant mathematical insight (fixpoint as universal test)
- Clean separation of concerns (Foundations/Correctness/Implementation)
- Detailed structural proofs for 14+ cases

### For TCB0

**The proof is complete.** You have formally proven:
```agda
fixpoint-property : (normalize ∘ normalize-encoded) ⟶* normalize-encoded
```
This requires no postulates, no axioms - just Agda's type theory.

### For General Correctness

The gap is between:
- **Agda proves:** Fixpoint holds for this normalizer
- **Paper claims:** Fixpoint implies correctness for all inputs

The bridge (Theorem 4.1) is prose, relying on:
- Confluence (uses postulates)
- Strong normalization (uses postulates)
- Transparency of normal forms (meta-argument)

### Publication Readiness

- **TCB0 claims:** Ready to publish, fully formalized
- **General correctness claims:** Need to be transparent about formalization boundaries

### Novelty

Yes, the specific fixpoint theorem for CCC normalizers and the "zero-code TCB" application to Thompson's trusting trust is novel and publishable. The postulate-free nature of the fixpoint proof strengthens this contribution.

---

## References

- Lambek & Scott, "Introduction to Higher Order Categorical Logic" (1986)
- Tait, "Intensional interpretations of functionals of finite type" (1967)
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
- Thompson, "Reflections on trusting trust" (1984)
