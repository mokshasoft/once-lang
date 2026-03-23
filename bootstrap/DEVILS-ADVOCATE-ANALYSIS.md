# Devil's Advocate Analysis: Bootstrap Normalizer Proofs

**Date:** 2026-03-23
**Purpose:** Pre-publication review of mathematical claims vs. formal proofs

## Executive Summary

The proof system establishes a compelling argument for normalizer correctness via the fixpoint property. However, there are **several gaps between what the paper claims and what Agda formally proves**, and some **philosophical concerns** about the postulates.

---

## 1. Postulates vs. Established Lemmas

### The 4 Postulates in `EstablishedMath.agda` (lines 35-83)

| Postulate | Claimed Justification | Devil's Advocate Concern |
|-----------|----------------------|-------------------------|
| `complete` | Lambek & Scott parallel reduction | **No witness function is constructed.** The postulate asserts existence but doesn't provide the algorithm. |
| `⟹-to-complete` | Triangle lemma | This depends on `complete` existing correctly. |
| `strong-normalization` | Tait's logical relations | **Only applies to simply-typed λ-calculus.** The system has μ-types (inductive types with `cata`). Is this still simply-typed? |
| `normalize-semantics-equiv` | CCC soundness | **This is a VERY strong claim**: for ANY `N : Term A A`, either `N ∘ t ⟶* t` or `t ⟶* N ∘ t`. This seems overly general. |

### Specific Concerns

**Strong normalization scope**: The Agda code comments claim it applies because "cata is not recursive" (line 54). But `cata` IS a recursive scheme - it unfolds with `cata F alg ∘ In → alg ∘ fmap F (cata F alg)`. The claim seems to be that the recursion is **well-founded** (because μ-types are "strictly positive"), but this is **not formalized**.

**`normalize-semantics-equiv` is suspicious**: The postulate at lines 81-83 says:
```agda
postulate
  normalize-semantics-equiv : ∀ {A} (N : Term A A) (t : Term Unit A) →
                              ((N ∘ t) ⟶* t) ⊎ (t ⟶* (N ∘ t))
```
This claims that for ANY endomorphism N and ANY term t, one of these reduction sequences exists. This is **stronger than standard soundness**. Standard soundness says reductions preserve denotation; this says something about the reduction graph structure itself.

---

## 2. The Main Theorem Gap

### What the Paper Claims (Theorem 4.1)

> "If N satisfies the fixpoint property (N ∘ ⌜N⌝ →* ⌜N⌝), then N is correct (∀t. N ∘ ⌜t⌝ →* ⌜nf(t)⌝)."

### What Agda Actually Proves

**File**: `Implementation/Normalize/Fixpoint/MainTheorem.agda` (lines 17-20)
```agda
noredex-fixpoint : ∀ {A B} (t : Term A B) →
                   NoRedex t →
                   (normalize ∘ encode t) ⟶* encode t
```

**This is weaker**: It only proves fixpoint for **NoRedex** terms, not arbitrary terms. The claim `N ∘ ⌜t⌝ →* ⌜nf(t)⌝` for arbitrary t requires:
1. First normalizing t to nf(t)
2. Then showing `N ∘ ⌜nf(t)⌝ →* ⌜nf(t)⌝` (which noredex-fixpoint gives)
3. Then showing `N ∘ ⌜t⌝ →* N ∘ ⌜nf(t)⌝` (NOT proven in Agda!)

The step from `⌜t⌝` to `⌜nf(t)⌝` is NOT the same as the reduction `t →* nf(t)`. The encoding happens BEFORE normalization.

### The Gap

The paper's Theorem 4.1 proof (prose) argues:
1. N is in normal form (from fixpoint)
2. By induction on t, show correctness

But the Agda only proves: "if t is already NoRedex, fixpoint holds." The **inductive step** that handles `N ∘ ⌜f ∘ g⌝` where `f ∘ g` IS a redex is **not formalized**.

---

## 3. The "All Normalizers" vs "This Normalizer" Question

### Did we prove ALL normalizers satisfying the spec have the three properties?

**No.** The `CorrectNormalizer` record in `Record.agda` (lines 27-42) defines:
- `terminates`
- `produces-betanf`
- `preserves`

But the code does NOT prove: "If N satisfies NormalizerSpec, then N is a CorrectNormalizer."

What IS proven:
- `NormalizerSpec` → `noredex-fixpoint` (in `SpecImpliesFixpoint`)
- The concrete `normalize-step` satisfies `NormalizerSpecSimple` (in `SatisfiesSpec`)

The **general theorem "spec implies three properties"** is NOT formalized.

### Did we prove THIS normalizer has these properties?

**Partially.** Looking at `MainTheorem.agda` (lines 92-96):
```agda
open import normalizer.Correctness.Correctness
  normalize
  strong-normalization
  normalize-preserves-semantics
  confluence
  public
```

The Correctness module is parameterized by `strong-normalization` and `normalize-preserves-semantics` (both postulates!). So the proof that THIS normalizer is correct **depends on the postulates being true**.

---

## 4. Paper vs. Proofs: Key Differences

| Paper Claim | Agda Status | Gap |
|-------------|-------------|-----|
| Theorem 4.1 (fixpoint → correctness) | **Prose proof only** | Not formalized at all |
| Lemma 4.1 (fixpoint → N is normal form) | Proven but trivial | Actually, encodings are always NF by construction (`encode-is-betanf`), so fixpoint isn't needed |
| Corollary 4.2 (uniqueness) | **Not proven** | Follows from Theorem 4.1 but that's not formalized |
| Lemma 3.1 (encodings are NF) | **Proven** (`encode-is-betanf`) | Solid |
| Lemma 3.2 (encoding injectivity) | **Claimed structural** | Not an explicit Agda theorem |
| Appendix A.4 (encoding completeness) | **Claimed structural** | Not formalized |

The **most critical gap** is Theorem 4.1 - the central argument that fixpoint implies general correctness.

---

## 5. Fixpoint Theorem Statement Analysis

### FixpointTheorem.agda (lines 61-63):
```agda
fixpoint-implies-betanf : (normalize ∘ normalize-encoded) ⟶* normalize-encoded →
                          IsBetaNormalForm normalize-encoded
fixpoint-implies-betanf _ = normalize-encoding-is-betanf
```

**This is almost trivial!** The proof ignores the fixpoint hypothesis entirely (`_`) and just returns `normalize-encoding-is-betanf`, which is proven independently by `encode-is-betanf normalize`.

The theorem says: "If fixpoint holds, the target is beta-normal." But the proof is: "Encodings are always beta-normal, regardless of fixpoint."

This is **correct but misleading**. The theorem doesn't USE the fixpoint property - it's just a structural observation about encodings.

---

## 6. NoRedex Definition: Is It Complete?

The `NoRedex` predicate in `NoRedex.agda` (lines 230-273) defines 10 base cases and 5 recursive cases. But look at the comment at lines 253-255:

```agda
-- Pair: not eta (⟨fst, snd⟩), and subterms are normal
-- Note: we don't check eta since handle-pair doesn't implement it
```

This is an **intentional incompleteness**. The normalizer doesn't reduce η-redexes, so NoRedex doesn't exclude them. This means:

**NoRedex terms may still have reducible substructure** (eta-redexes).

The system is proving fixpoint for "NoRedex" which is NOT the same as "normal form." It's "no β-redex + no id-composition redex."

---

## 7. The SafeComp Constraint

Looking at `NoRedex.agda` (lines 182-193), `SafeComp f g` requires:
- `NotIdStruct f` (f is not `id`)
- `NotIdStruct g` (g is not `id`)
- `NotApplyStruct f` OR `NotCurryPairLeft g`

But the composition `fst ∘ ⟨h, k⟩` is a redex that **passes SafeComp** (fst is not id, pair is not id). Why isn't this caught?

**Answer** (from comment lines 175-177): "they don't arise in encoded terms."

This is a **critical assumption**: the normalizer only needs to handle patterns that appear in encodings. But is this actually proven? If `encode t` could produce `fst ∘ ⟨_, _⟩` for some t, the proof would be incomplete.

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

### Precedents

The idea of "self-representation implies correctness" has precedent in:
- Kleene's recursion theorem
- Quines and reflective towers
- Thompson's "trusting trust" (the problem being solved)

**The novel contribution** is the precise mathematical theorem connecting CCC fixpoint to normalizer correctness, and the insight that CCC's confluence + termination + self-representation makes this work.

---

## 9. Recommendations Before Publication

### Critical Issues (must address)

1. **Formalize Theorem 4.1**: The central theorem is prose only. Either:
   - Formalize it in Agda, OR
   - Be explicit in the paper that it's NOT formalized and explain why

2. **Justify `normalize-semantics-equiv`**: This postulate is suspiciously strong. Either:
   - Weaken it to what's actually needed, OR
   - Provide a careful prose argument why it holds

3. **Strong normalization for μ-types**: Explicitly address whether Tait's theorem applies to your system with inductive types.

### Medium Issues (should address)

4. **noredex-fixpoint vs general correctness**: Be clear in the paper that Agda proves fixpoint for NoRedex inputs, and general correctness relies on additional reasoning.

5. **Encoding injectivity**: Either formalize as Agda theorem or mark as "structural claim."

6. **η-redexes**: Clarify that the normalizer doesn't handle them and why this is acceptable.

### Minor Issues

7. **`fixpoint-implies-betanf` is trivial**: Consider removing or renaming since it doesn't use the hypothesis.

8. **Make explicit what CorrectNormalizer is proven for**: The record exists but isn't instantiated for `normalize`.

---

## 10. Final Assessment

### Strengths

- Elegant mathematical insight (fixpoint as universal test)
- Clean separation of concerns (Foundations/Correctness/Implementation)
- Only 4 postulates, all from established sources
- Detailed structural proofs for 14+ cases

### Weaknesses

- Central theorem (4.1) not formalized
- Gap between paper claims and Agda proofs
- Some postulates may be stronger than justified
- NoRedex ≠ full normal form

### Publication Readiness

The mathematical argument is compelling, but you should be **transparent about the formalization boundaries**. The paper currently implies more is proven in Agda than actually is.

### Novelty

Yes, the specific fixpoint theorem for CCC normalizers and the "zero-code TCB" application to Thompson's trusting trust is novel and publishable.

---

## References

- Lambek & Scott, "Introduction to Higher Order Categorical Logic" (1986)
- Tait, "Intensional interpretations of functionals of finite type" (1967)
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
- Thompson, "Reflections on trusting trust" (1984)
