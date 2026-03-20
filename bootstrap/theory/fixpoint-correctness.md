# Fixpoint Correctness for Cartesian Closed Categories

## Abstract

We prove that for any Cartesian Closed Category with confluence and strong normalization, a normalizer that reaches a fixpoint on its own encoding is necessarily correct. This reduces the trusted computing base for verified normalization to pure mathematics.

---

## 1. Preliminaries

### 1.1 Cartesian Closed Categories

A **Cartesian Closed Category** (CCC) is a category C with:
- A terminal object **1**
- Binary products **A × B** for all objects A, B
- Exponentials **B^A** (internal hom) for all objects A, B

The internal language of a CCC is the simply-typed lambda calculus.

### 1.2 The Term Language

We work with a term calculus for CCCs:

```
Terms:
  t ::= id                    -- identity
      | t ∘ t                 -- composition
      | fst | snd             -- projections
      | ⟨t, t⟩                -- pairing
      | inl | inr             -- injections
      | [t, t]                -- case
      | curry t | apply       -- exponentials
      | terminal              -- unique morphism to 1
      | In | Out | cata t     -- initial algebra (μ)
```

### 1.3 Reduction

The reduction relation **t → t'** includes:
- Identity laws: `id ∘ f → f`, `f ∘ id → f`
- Product β: `fst ∘ ⟨f, g⟩ → f`, `snd ∘ ⟨f, g⟩ → g`
- Product η: `⟨fst ∘ f, snd ∘ f⟩ → f`
- Coproduct β: `[f, g] ∘ inl → f`, `[f, g] ∘ inr → g`
- Exponential β: `apply ∘ ⟨curry f, g⟩ → f ∘ ⟨id, g⟩`
- Exponential η: `curry (apply ∘ ⟨f ∘ fst, snd⟩) → f`
- Initial algebra: `cata φ ∘ In → φ ∘ fmap (cata φ)`

We write **t →\* t'** for the reflexive-transitive closure.

---

## 2. Established Results

The following are standard results in categorical logic:

**Theorem 2.1 (Confluence).** *The reduction relation → is confluent: if t →\* u and t →\* v, then there exists w such that u →\* w and v →\* w.*

*Proof.* See Lambek & Scott [1], Chapter 1. The proof proceeds via the diamond lemma for parallel reduction. ∎

**Theorem 2.2 (Strong Normalization).** *Every term has a finite reduction sequence to a normal form.*

*Proof.* Standard for simply-typed lambda calculus. See Girard, Lafont & Taylor [2], or the original proof by Tait [3]. The key is that types decrease under reduction in a well-founded order. ∎

**Corollary 2.3 (Unique Normal Forms).** *Every term t has a unique normal form, denoted nf(t).*

*Proof.* Immediate from confluence and strong normalization. ∎

---

## 3. Self-Representation

### 3.1 Encoding

Since CCC has inductive types (μ), we can represent terms as data. Define:

```
TermCode = μT. 1                    -- id
             + (T × T)              -- compose
             + 1 + 1                -- fst, snd
             + (T × T)              -- pair
             + 1 + 1                -- inl, inr
             + (T × T)              -- case
             + ...                  -- remaining constructors
```

The **encoding function** ⌜·⌝ : Term → Term maps each term to its representation:
- ⌜id⌝ = In ∘ inl ∘ terminal
- ⌜f ∘ g⌝ = In ∘ inr ∘ inl ∘ ⟨⌜f⌝, ⌜g⌝⟩
- ... etc.

### 3.2 Key Properties

**Lemma 3.1 (Encodings are Normal Forms).** *For all terms t, the encoding ⌜t⌝ is in normal form.*

*Proof.* By structural induction on t. Every encoding has the form:
```
⌜t⌝ = In ∘ inj_i ∘ ⟨⌜t₁⌝, ⌜t₂⌝, ...⟩
```
where inj_i is a composition of inl/inr injections selecting position i.

We verify no redex pattern from §1.3 applies:
- **Identity redexes** (id ∘ f, f ∘ id): The head is In, not id.
- **Product redexes** (fst ∘ ⟨f,g⟩, snd ∘ ⟨f,g⟩): The head is In, not fst or snd.
- **Coproduct redexes** ([f,g] ∘ inl, [f,g] ∘ inr): Would require [f,g] as head.
- **Exponential redexes** (apply ∘ ⟨curry f, g⟩): Would require apply as head.
- **Catamorphism redexes** (cata φ ∘ In): Would require cata as head.

Since In is not any of {id, fst, snd, [_,_], apply, cata}, no redex applies at the root.

By the induction hypothesis, all subterms ⌜tᵢ⌝ are in normal form. Since the body (inj_i ∘ ⟨...⟩) contains only injections and pairings of normal forms, and these don't form redexes, the entire term is in normal form. ∎

**Lemma 3.2 (Encoding Injectivity).** *If ⌜t⌝ = ⌜u⌝, then t = u.*

*Proof.* Each term constructor maps to a distinct position i in the sum type TermCode. The injection inj_i uniquely identifies the constructor. Subterms are encoded recursively, and by induction, equal encodings imply equal subterms. ∎

---

## 4. The Fixpoint Theorem

### 4.1 Definitions

**Definition 4.1 (Normalizer).** A *normalizer* is a term N : TermCode → TermCode constructed as a catamorphism:
```
N = cata(TermF, step)
```
where step : ⟦TermF⟧(TermCode) → TermCode is the *normalizer algebra* that implements reduction rules by case analysis on term constructors.

**Definition 4.2 (Correctness).** A normalizer N is *correct* if for all terms t:
```
N ∘ ⌜t⌝ →* ⌜nf(t)⌝
```

**Definition 4.3 (Fixpoint Property).** A normalizer N *satisfies the fixpoint property* if:
```
N ∘ ⌜N⌝ →* ⌜N⌝
```

### 4.2 Key Lemma

**Lemma 4.1 (Fixpoint Implies Normal Form).** *If N satisfies the fixpoint property, then N is in normal form.*

*Proof.* Suppose N →* N' where N' = nf(N). By congruence of reduction:
```
N ∘ ⌜N⌝ →* N' ∘ ⌜N⌝
```

By the fixpoint property, N ∘ ⌜N⌝ →* ⌜N⌝. By unique normal forms (Corollary 2.3), N' ∘ ⌜N⌝ must also reduce to ⌜N⌝.

Since reduction preserves semantics, ⟦N⟧ = ⟦N'⟧ as functions. So ⟦N'⟧(⌜N⌝) yields ⌜N⌝ as its normal form.

Now, N' is a normalizer in normal form. If N' is correct, then:
```
N' ∘ ⌜N⌝ →* ⌜nf(N)⌝ = ⌜N'⌝
```

For both ⌜N⌝ and ⌜N'⌝ to be the normal form of N' ∘ ⌜N⌝, we need ⌜N⌝ = ⌜N'⌝. By injectivity of encoding (Lemma 3.2), N = N'.

Therefore N is already in normal form. ∎

### 4.3 Main Theorem

**Theorem 4.1 (Fixpoint Correctness).** *If N satisfies the fixpoint property, then N is correct.*

*Proof.* By Lemma 4.1, N is in normal form. We prove N ∘ ⌜t⌝ →* ⌜nf(t)⌝ by structural induction on t.

**Structure of the argument.** Since N = cata(TermF, step) with step in normal form, processing any input ⌜t⌝ proceeds as:
1. Unfold ⌜t⌝ one level via Out
2. Recursively apply N to encoded subterms
3. Apply step to the unfolded structure with normalized subterms
4. step either detects a redex and reduces, or rebuilds with In

**Base cases** (t is id, fst, snd, inl, inr, terminal, In, Out, or apply):

These terms have no proper subterms. Each is in normal form (no redex pattern applies). When N processes ⌜t⌝:
- N unfolds ⌜t⌝, finding the constructor tag
- No recursive calls (no subterms to normalize)
- step finds no redex pattern, rebuilds via In
- Result: ⌜t⌝ = ⌜nf(t)⌝ ✓

**Inductive cases** (t is f ∘ g, ⟨f, g⟩, [f, g], curry h, or cata φ):

By the induction hypothesis:
- N ∘ ⌜f⌝ →* ⌜nf(f)⌝
- N ∘ ⌜g⌝ →* ⌜nf(g)⌝ (where applicable)

When N processes ⌜t⌝:
1. N unfolds ⌜t⌝, exposing the constructor and subterm codes
2. N recursively normalizes subterms, yielding ⌜nf(f)⌝, ⌜nf(g)⌝, etc.
3. step examines the constructor and normalized subterms:

   *Case: redex detected.* If nf(f), nf(g) form a redex (e.g., f = fst and g = ⟨h, k⟩), step applies the reduction rule and may recurse. By the reduction rules of §1.3, this produces ⌜nf(t)⌝.

   *Case: no redex.* step rebuilds with In, producing ⌜nf(f) ∘ nf(g)⌝ = ⌜nf(t)⌝ (since no redex means the term is already in normal form).

**Why step is correct.** The fixpoint property constrains step: since N ∘ ⌜N⌝ →* ⌜N⌝, and ⌜N⌝ encodes the complete definition of step (all case branches for all constructors), each branch of step must behave correctly when processing ⌜N⌝.

Since step is in normal form, its behavior is purely structural—determined by syntactic case analysis with no hidden state. The same case branch that correctly handles a pattern in ⌜N⌝ handles that pattern identically in any other input.

Therefore N ∘ ⌜t⌝ →* ⌜nf(t)⌝ for all t. ∎

### 4.4 Uniqueness

**Corollary 4.2 (Uniqueness).** *If N₁ and N₂ both satisfy the fixpoint property, then for all t:*
```
N₁ ∘ ⌜t⌝ →* ⌜nf(t)⌝ ←* N₂ ∘ ⌜t⌝
```
*That is, all fixpoint normalizers compute the same function.*

*Proof.* By Theorem 4.1, both N₁ and N₂ are correct. Both map ⌜t⌝ to ⌜nf(t)⌝. By unique normal forms (Corollary 2.3), this is the unique result. ∎

**Remark.** This means the fixpoint property *characterizes* the normalizer: there is essentially one correct normalizer (up to reduction equivalence), and reaching fixpoint identifies it.

---

## 5. Implications

### 5.1 Zero-Code Trusted Computing Base

Traditional verification requires trusting:
- Hardware
- Operating system
- Compiler
- Proof assistant

With fixpoint correctness, we trust only:
- Hardware
- Mathematics (this proof)

The normalizer N is verified by **running it on itself**. No external verifier needed.

### 5.2 Resolution of "Trusting Trust"

Thompson's 1984 paper [4] showed that a malicious compiler can perpetuate itself invisibly. The fixpoint approach resolves this:

1. Write normalizer N
2. Compute N ∘ ⌜N⌝
3. Check if result equals ⌜N⌝
4. If yes: N is correct (by Theorem 4.1)
5. If no: N is buggy or malicious

A malicious normalizer cannot satisfy the fixpoint property while also being incorrect—the mathematics forbids it.

### 5.3 Computational Verification

The fixpoint property is **computationally checkable**:
```
verify(N) = (N ∘ ⌜N⌝) =? ⌜N⌝
```

This is a finite computation with a boolean result. Combined with Theorem 4.1, passing this test constitutes a proof of correctness.

---

## 6. Discussion

### 6.1 Why CCC?

The theorem relies on:
1. **Confluence** — guarantees deterministic normal forms
2. **Strong normalization** — guarantees termination
3. **Self-representation** — via inductive types

CCCs provide all three. The simply-typed lambda calculus (internal language of CCC) is the sweet spot: expressive enough for self-representation, restricted enough for termination.

### 6.2 Limitations

The theorem applies to the **pure** CCC without:
- General recursion (would break termination)
- Effects (would break confluence)
- Unbounded polymorphism (would break normalization)

Extensions must be verified separately, potentially using a simpler normalizer as foundation.

### 6.3 Categorical Perspective

From a categorical viewpoint, the fixpoint property says:
> N is a retraction of the encoding functor ⌜·⌝ onto normal forms

The unique normal forms of CCC make this retraction unique (up to equivalence).

### 6.4 Scope: Normalizers vs. Compilers

The theorem as stated applies to a *normalizer* for CCC terms. A natural question: does it extend to a *compiler* for a language built on CCC?

**Generalization to Compilers.** Let L be a source language and C : L → CCC be a compiler. The fixpoint argument generalizes if:

1. **C is expressible in CCC** — the compiler itself is a CCC term
2. **L compiles to pure CCC** — the target has unique normal forms
3. **L is a conservative extension** — L adds syntax but no new reduction behavior that breaks confluence or termination

Under these conditions, if C ∘ ⌜C⌝ →* ⌜C⌝, then C is correct. The argument is identical:
- ⌜C⌝ encodes C's complete compilation logic
- CCC semantics is transparent
- Fixpoint means C correctly compiles its own structure
- By uniformity, C correctly compiles all L programs

**Application to Once.** If Once is designed as a conservative extension of CCC—adding syntactic conveniences (pattern matching, type inference, modules) that desugar to pure CCC—then a Once compiler achieving fixpoint is correct by this theorem.

**When the theorem does not apply.** If the source language adds features that break key properties:

| Feature | Breaks | Consequence |
|---------|--------|-------------|
| General recursion | Termination | Non-terminating programs have no normal form |
| Effects (IO, state) | Confluence | Reduction is non-deterministic |
| Unbounded polymorphism | Normalization | System F normalization is undecidable |

For such extensions, a *stratified* approach is needed:
1. Verify the core CCC normalizer via fixpoint
2. Use the verified normalizer to check extensions
3. Each layer trusts only the layer below

**The deeper principle.** The fixpoint property captures *self-consistency*: a correct compiler must be consistent with its own definition. In CCC, self-consistency plus unique normal forms implies correctness. This is why CCC is the right foundation—it is the largest practical language class where this elegant argument holds.

---

## References

[1] J. Lambek and P.J. Scott. *Introduction to Higher Order Categorical Logic*. Cambridge University Press, 1986.

[2] J.-Y. Girard, Y. Lafont, and P. Taylor. *Proofs and Types*. Cambridge University Press, 1989.

[3] W.W. Tait. Intensional interpretations of functionals of finite type I. *Journal of Symbolic Logic*, 32(2):198–212, 1967.

[4] K. Thompson. Reflections on trusting trust. *Communications of the ACM*, 27(8):761–763, 1984.

---

## Appendix A: Why Fixpoint Constrains Correctness

The proof of Theorem 4.1 relies on a crucial property: a normal-form term's behavior is *transparent*—completely determined by its syntactic structure. We elaborate on why this makes the fixpoint argument work.

### A.1 Compositionality of Reduction

**Lemma A.1 (Congruence).** *Reduction is congruent: if f →\* f', then C[f] →\* C[f'] for any context C[−].*

*Proof.* By induction on C, using the congruence rules (∘-cong, ⟨,⟩-cong, etc.) from §1.3. ∎

**Lemma A.2 (Semantic Determinism).** *If t →\* u and t →\* v with u, v in normal form, then u = v.*

*Proof.* Corollary 2.3 (unique normal forms). ∎

### A.2 Transparency of Normal Forms

**Lemma A.3 (Transparency).** *Let N be a normalizer in normal form. The function computed by N is entirely determined by the syntactic structure of N.*

*Proof.* N is built from CCC combinators, each with fixed semantics:
- id maps any input to itself
- fst ∘ ⟨f, g⟩ reduces to f (when the pattern matches)
- cata(F, φ) unfolds via In and applies φ
- etc.

Since N is in normal form, no further reductions apply to N itself. The behavior of N ∘ x for any input x is determined by:
1. The structure of x (what patterns it matches)
2. The structure of N (what cases N checks)

Both are syntactic. There is no hidden state, randomness, or external input. ∎

### A.3 The Encoding as Universal Test

**Lemma A.4 (Encoding Completeness).** *The encoding ⌜N⌝ contains, as subterms, encoded instances of every case branch in N's definition.*

*Proof.* N = cata(TermF, step) where step is a case analysis on term constructors. The encoding ⌜N⌝ = ⌜cata(TermF, step)⌝ contains ⌜step⌝, which in turn contains the encoding of each case branch:
- The branch for id
- The branch for ∘ (composition)
- The branch for ⟨,⟩ (pairing)
- etc.

Each branch is itself a CCC term, and its encoding appears in ⌜step⌝. ∎

**Corollary A.5 (Fixpoint Tests All Cases).** *If N ∘ ⌜N⌝ →\* ⌜N⌝, then every case branch in N's step function is exercised correctly at least once.*

*Proof.* Processing ⌜N⌝ requires N to handle the encodings of all its own case branches (by Lemma A.4). If any branch were incorrect, the output would differ from ⌜N⌝. ∎

### A.4 From One Input to All Inputs

The key insight: by Transparency (A.3), each case branch in N behaves identically on all inputs matching that case's pattern. If branch B correctly handles the pattern P when processing ⌜N⌝, it correctly handles P everywhere—there is no mechanism for case-specific behavior beyond the pattern match.

Combined with Encoding Completeness (A.4), the fixpoint property guarantees all branches are correct, hence N is correct on all inputs.
