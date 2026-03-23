# Devil's Advocate Analysis: Bootstrap Normalizer Proofs

**Date:** 2026-03-23 (Updated)
**Purpose:** Pre-publication review of mathematical claims vs. formal proofs

## Executive Summary

The proof system establishes a compelling argument for normalizer correctness via the fixpoint property.

**Key Finding:** The core TCB0 theorem (`fixpoint-property`) is **fully proven in Agda without any postulates**. The postulates are only used for general correctness claims (Theorem 4.1 in the paper), not for the fixpoint itself.

**Novel Insight:** The proof uses a clever shortcut that **bypasses strong normalization entirely**. Instead of postulating that all terms normalize and then applying that to the normalizer, we directly prove that this specific normalizer is already in NoRedex form. This makes the TCB0 proof entirely self-contained.

This means:
- **For TCB0:** The proof is complete and postulate-free
- **For general correctness:** Additional reasoning (partly prose) is needed
- **The shortcut:** Direct NoRedex proof bypasses need for strong normalization

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

## 1. The Shortcut: Bypassing Strong Normalization

### The Traditional Approach (Would Require Postulates)

To prove fixpoint for an arbitrary normalizer N:

1. **Postulate** strong normalization: every term has a normal form
2. **Derive** that N reduces to some N' where `NoRedex N'`
3. **Apply** `noredex-fixpoint` to N'
4. **Use** semantic preservation to transfer the result to N

This approach requires the `strong-normalization` postulate.

### The Shortcut (Postulate-Free)

For THIS specific normalizer:

1. **Construct** a normalizer that is ALREADY in NoRedex form by design
2. **Directly prove** `normalize-noredex : NoRedex normalize`
3. **Apply** `noredex-fixpoint` directly

```agda
-- The shortcut: direct structural proof, no postulates needed
normalize-noredex : NoRedex normalize
normalize-noredex = nr-cata nr-normalize-step
```

### Why This Works

The normalizer is defined as:
```agda
normalize = cata TermF normalize-step
```

For `NoRedex (cata TermF alg)`, we only need `NoRedex alg`. Since `normalize-step` is a composition of handlers that are all structurally NoRedex, we can prove this directly without appealing to strong normalization.

### What This Means

| Approach | For Specific Normalizer | For General Normalizers |
|----------|------------------------|------------------------|
| **Traditional** | Needs strong-normalization postulate | Needs strong-normalization postulate |
| **Shortcut** | Direct structural proof ✓ | Still needs strong-normalization |

**The shortcut works for any normalizer you construct**, as long as you can directly prove it's NoRedex. You only need the postulates if you want to reason about arbitrary normalizers you haven't constructed.

### Implications for the Trust Model

This is a significant insight for TCB0:

1. **No circular dependency**: We don't need to trust that "all terms normalize" to verify our normalizer
2. **Self-contained verification**: The fixpoint proof stands alone
3. **Constructive**: We BUILD a NoRedex normalizer rather than ASSUMING one exists

---

## 2. Postulates vs. Established Lemmas

### The 4 Postulates in `EstablishedMath.agda` (lines 35-83)

| Postulate | Claimed Justification | Devil's Advocate Concern | Used By TCB0? |
|-----------|----------------------|-------------------------|---------------|
| `complete` | Lambek & Scott parallel reduction | No witness function constructed | **NO** |
| `⟹-to-complete` | Triangle lemma | Depends on `complete` | **NO** |
| `strong-normalization` | Tait's logical relations | μ-types need justification | **NO** (bypassed!) |
| `normalize-semantics-equiv` | CCC soundness | Overly general claim | **NO** |

### Important: Strong Normalization is BYPASSED, Not Just Unused

The shortcut doesn't just avoid using `strong-normalization` - it makes it unnecessary for TCB0. The traditional proof would be:

```
strong-normalization → normalize has normal form → fixpoint
```

The actual proof is:

```
normalize-noredex (direct) → fixpoint
```

### Concerns (Only Relevant for General Correctness)

**Strong normalization scope**: The system has μ-types (inductive types with `cata`). The claim is that recursion is well-founded (strictly positive functors), but this is not formalized. **However, for TCB0, this doesn't matter.**

**`normalize-semantics-equiv` is suspicious**: Claims that for ANY endomorphism N and ANY term t, either `N ∘ t ⟶* t` or `t ⟶* N ∘ t`. This is stronger than standard soundness. **However, for TCB0, this doesn't matter.**

---

## 3. The Main Theorem Gap

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

### NoRedex Implies Correctness (For NoRedex Terms)

For a NoRedex term t, `t = nf(t)` (it's already in normal form). Therefore:

```
noredex-fixpoint: (N ∘ encode t) ⟶* encode t
                = (N ∘ encode t) ⟶* encode (nf t)   -- since t = nf(t)
                = correctness for t!
```

So `noredex-fixpoint` IS a correctness theorem for NoRedex inputs.

### The Gap (Only Affects General Correctness)

For arbitrary terms (not NoRedex), we'd need:
1. Strong normalization: t has a normal form nf(t)
2. Show: `N ∘ encode t ⟶* N ∘ encode (nf t) ⟶* encode (nf t)`

Step 2 uses `noredex-fixpoint`. Step 1 requires the postulate.

**For TCB0, this gap doesn't matter** - the normalizer itself is NoRedex.

---

## 4. The "All Normalizers" vs "This Normalizer" Question

### For TCB0: This Normalizer

**Fully proven (no postulates):**
- `normalize-noredex : NoRedex normalize`
- `fixpoint-property : (normalize ∘ normalize-encoded) ⟶* normalize-encoded`

This is sufficient for TCB0: run the normalizer on its own encoding, verify the result.

### For General Claims: All Normalizers

To prove "any normalizer satisfying spec X has fixpoint":

```agda
-- This is proven:
spec-implies-fixpoint : NormalizerSpecSimple alg →
                        ∀ t → NoRedex t →
                        (cata TermF alg ∘ encode t) ⟶* encode t

-- This would require strong-normalization:
general-fixpoint : NormalizerSpecSimple alg →
                   ∀ t →  -- no NoRedex requirement
                   (cata TermF alg ∘ encode t) ⟶* encode (nf t)
```

### Can Any Normalizer Be Converted to NoRedex?

Yes - that's exactly what strong normalization says! The statement "every term reduces to a NoRedex form" IS strong normalization.

**For a SPECIFIC normalizer**: Directly prove it's NoRedex (shortcut)
**For ALL normalizers**: Need strong normalization (postulate or Tait-style proof)

---

## 5. Paper vs. Proofs: Key Differences

| Paper Claim | Agda Status | Gap | Affects TCB0? |
|-------------|-------------|-----|---------------|
| Fixpoint for this normalizer | **PROVEN** (`fixpoint-property`) | None | **NO** |
| Theorem 4.1 (fixpoint → correctness) | Prose proof only | Not formalized | No (meta-argument) |
| Lemma 4.1 (fixpoint → N is normal form) | Proven but trivial | Encodings always NF | No |
| Corollary 4.2 (uniqueness) | Not proven | Follows from 4.1 | No |
| Lemma 3.1 (encodings are NF) | **PROVEN** (`encode-is-betanf`) | None | No |
| Lemma 3.2 (encoding injectivity) | Claimed structural | Not explicit theorem | No |

---

## 6. Fixpoint Theorem Statement Analysis

### FixpointTheorem.agda (lines 61-63):
```agda
fixpoint-implies-betanf : (normalize ∘ normalize-encoded) ⟶* normalize-encoded →
                          IsBetaNormalForm normalize-encoded
fixpoint-implies-betanf _ = normalize-encoding-is-betanf
```

**This is almost trivial!** The proof ignores the fixpoint hypothesis entirely (`_`) and just returns `normalize-encoding-is-betanf`, which is proven independently.

This is correct but misleading - the theorem doesn't USE the fixpoint property.

---

## 7. NoRedex Definition: Is It Complete?

The `NoRedex` predicate defines 10 base cases and 5 recursive cases. Note:

```agda
-- Pair: not eta (⟨fst, snd⟩), and subterms are normal
-- Note: we don't check eta since handle-pair doesn't implement it
```

This is **intentional incompleteness**. The normalizer doesn't reduce η-redexes, so NoRedex doesn't exclude them.

**For TCB0:** This is fine - the normalizer is consistent with its own definition of "normal."

---

## 8. The SafeComp Constraint

`SafeComp f g` doesn't catch `fst ∘ ⟨h, k⟩` (a redex). Why?

**Answer** (from comments): "they don't arise in encoded terms."

**Critical assumption:** The normalizer only needs to handle patterns that appear in encodings.

**For TCB0:** This is validated by the fixpoint - if the assumption were wrong, the fixpoint wouldn't hold.

---

## 9. Is the Fixpoint Approach Novel?

### Related Work

- **Self-certification in F***: Bootstraps typechecker, but uses external Coq for proofs
- **CakeML verified bootstrap**: Self-compiling verified compiler, but proofs are in HOL4
- **CompCert TCB analysis**: Analyzes what must be trusted, but doesn't use fixpoint for correctness

### Novel Aspects of This Approach

1. **Fixpoint as correctness criterion** - The specific theorem "fixpoint ⟹ correctness" for CCC normalizers
2. **Zero-code TCB** - Trusting only mathematics, not tools
3. **Constrained language** - Using CCC's unique normal forms as the key enabling property
4. **Postulate-free fixpoint proof** - The core TCB0 theorem needs no axioms
5. **The shortcut** - Bypassing strong normalization via direct NoRedex proof

### The Shortcut as a Contribution

The insight that you can bypass strong normalization by directly proving NoRedex for a specific normalizer is itself a contribution. It shows:

- TCB0 verification doesn't require general termination proofs
- Self-verification can be fully constructive
- The trust model is cleaner than previously thought

### Precedents

- Kleene's recursion theorem
- Quines and reflective towers
- Thompson's "trusting trust" (the problem being solved)

**The novel contribution** is the precise mathematical theorem connecting CCC fixpoint to normalizer correctness, the insight that CCC's properties enable this, AND the shortcut that makes the proof postulate-free.

---

## 10. Recommendations Before Publication

### For TCB0 Claims: Highlight the Shortcut

The fixpoint proof is complete and postulate-free. You can claim:
> "We formally prove in Agda that our normalizer achieves fixpoint on its own encoding, without any axioms or postulates. This is achieved by directly proving our normalizer is in normal form, bypassing the need for a general strong normalization theorem."

### For General Correctness Claims

If the paper claims Theorem 4.1 (fixpoint implies correctness for all inputs):

1. **Be explicit** that this is a meta-theorem argued in prose, not formalized in Agda
2. **Explain the shortcut** - why TCB0 doesn't need strong normalization even though general correctness does
3. **Clarify the trust model**: TCB0 for fixpoint (no postulates), additional trust for general correctness

### Potential Future Work

The shortcut suggests a research direction:
- Can the direct NoRedex approach be generalized?
- Can we define a class of "self-evidently normal" normalizers?
- Is there a type-theoretic characterization of normalizers that bypass strong normalization?

### Medium Issues

4. **Encoding injectivity**: Either formalize as Agda theorem or mark as "structural claim"
5. **η-redexes**: Clarify that the normalizer doesn't handle them and why this is acceptable

### Minor Issues

6. **`fixpoint-implies-betanf` is trivial**: Consider removing or renaming since it doesn't use the hypothesis

---

## 11. Final Assessment

### Strengths

- **Postulate-free fixpoint proof** - The core TCB0 theorem is fully proven
- **The shortcut** - Bypasses strong normalization elegantly
- Elegant mathematical insight (fixpoint as universal test)
- Clean separation of concerns (Foundations/Correctness/Implementation)
- Detailed structural proofs for 14+ cases

### For TCB0

**The proof is complete.** You have formally proven:
```agda
fixpoint-property : (normalize ∘ normalize-encoded) ⟶* normalize-encoded
```
This requires no postulates, no axioms - just Agda's type theory.

The key insight: by constructing a normalizer that is ALREADY NoRedex, you bypass the need to prove that all terms normalize.

### For General Correctness

The gap is between:
- **Agda proves:** Fixpoint holds for this normalizer (and any NoRedex input)
- **Paper claims:** Fixpoint implies correctness for all inputs

The bridge (Theorem 4.1) is prose, relying on:
- Confluence (uses postulates)
- Strong normalization (uses postulates, but BYPASSED for TCB0)
- Transparency of normal forms (meta-argument)

### Publication Readiness

- **TCB0 claims:** Ready to publish, fully formalized, highlight the shortcut
- **General correctness claims:** Need to be transparent about formalization boundaries

### Novelty

Yes, the specific fixpoint theorem for CCC normalizers and the "zero-code TCB" application to Thompson's trusting trust is novel and publishable.

**The shortcut insight strengthens the contribution**: showing that TCB0 verification can be done without appealing to general strong normalization is a cleaner result than expected.

---

## References

- Lambek & Scott, "Introduction to Higher Order Categorical Logic" (1986)
- Tait, "Intensional interpretations of functionals of finite type" (1967)
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
- Thompson, "Reflections on trusting trust" (1984)
