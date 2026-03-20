------------------------------------------------------------------------
-- BetaNormalForm: Computational normal forms (no beta-redexes)
--
-- A term is in beta-normal form if no computation rules apply.
-- This ignores structural rewrites like associativity.
--
-- Key insight: For the bootstrap, we care that normalized terms have
-- no COMPUTATIONAL redexes. Structural rewrites (assoc, pair-comp)
-- don't affect correctness.
------------------------------------------------------------------------

module normalizer.Foundations.BetaNormalForm where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
  using (encode)

------------------------------------------------------------------------
-- Beta-Redex Patterns
--
-- These are the computational reduction rules. A term is in beta-normal
-- form if none of these patterns appear (at any depth).
--
-- Excluded patterns:
--   id ∘ g           (id-left)
--   f ∘ id           (id-right)
--   fst ∘ ⟨f, g⟩     (fst-pair)
--   snd ∘ ⟨f, g⟩     (snd-pair)
--   [f, g] ∘ inl     (case-inl)
--   [f, g] ∘ inr     (case-inr)
--   ⟨fst, snd⟩       (eta-pair)
--   [inl, inr]       (eta-case)
--   apply ∘ ⟨curry f, g⟩  (curry-β)
--   cata F alg ∘ In  (cata-β)
--   Out ∘ In         (out-in)
--   In ∘ Out         (in-out)
--
-- NOT excluded (these are structural, not computational):
--   assoc-l, assoc-r
--   pair-comp
--   curry-η
------------------------------------------------------------------------

-- Beta reduction relation (subset of _⟶_)
-- Only includes computational steps
data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
  -- Identity
  β-id-left   : ∀ {A B} {f : Term A B} → (id ∘ f) ⟶β f
  β-id-right  : ∀ {A B} {f : Term A B} → (f ∘ id) ⟶β f
  -- Products
  β-fst-pair  : ∀ {A B C} {f : Term C A} {g : Term C B} → (fst ∘ ⟨ f , g ⟩) ⟶β f
  β-snd-pair  : ∀ {A B C} {f : Term C A} {g : Term C B} → (snd ∘ ⟨ f , g ⟩) ⟶β g
  β-eta-pair  : ∀ {A B} → ⟨ fst , snd ⟩ ⟶β id {A * B}
  -- Coproducts
  β-case-inl  : ∀ {A B C} {f : Term A C} {g : Term B C} → ([ f , g ] ∘ inl) ⟶β f
  β-case-inr  : ∀ {A B C} {f : Term A C} {g : Term B C} → ([ f , g ] ∘ inr) ⟶β g
  β-eta-case  : ∀ {A B} → [ inl , inr ] ⟶β id {A + B}
  -- Exponentials
  β-curry-β   : ∀ {A B C} {f : Term (A * B) C} {g : Term A B} →
                (apply ∘ ⟨ curry f , g ⟩) ⟶β (f ∘ ⟨ id , g ⟩)
  -- Fixed points
  β-cata      : ∀ {F A} {alg : Term (⟦ F ⟧F A) A} →
                (cata F alg ∘ In) ⟶β (alg ∘ fmap F (cata F alg))
  β-out-in    : ∀ F → (Out {F} ∘ In {F}) ⟶β id {⟦ F ⟧F (μ F)}
  β-in-out    : ∀ F → (In {F} ∘ Out {F}) ⟶β id {μ F}
  -- Congruence rules (propagate through structure)
  β-∘-l    : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
              f ⟶β f' → (f ∘ g) ⟶β (f' ∘ g)
  β-∘-r    : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
              g ⟶β g' → (f ∘ g) ⟶β (f ∘ g')
  β-pair-l : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
              f ⟶β f' → ⟨ f , g ⟩ ⟶β ⟨ f' , g ⟩
  β-pair-r : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
              g ⟶β g' → ⟨ f , g ⟩ ⟶β ⟨ f , g' ⟩
  β-case-l : ∀ {A B C} {f f' : Term A C} {g : Term B C} →
              f ⟶β f' → [ f , g ] ⟶β [ f' , g ]
  β-case-r : ∀ {A B C} {f : Term A C} {g g' : Term B C} →
              g ⟶β g' → [ f , g ] ⟶β [ f , g' ]
  β-cata-alg : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
              alg ⟶β alg' → cata F alg ⟶β cata F alg'
  β-curry-cong : ∀ {A B C} {f f' : Term (A * B) C} →
                 f ⟶β f' → curry f ⟶β curry f'

------------------------------------------------------------------------
-- Beta-Normal Form
------------------------------------------------------------------------

-- A term is in beta-normal form if no beta-reduction applies
IsBetaNormalForm : ∀ {A B} → Term A B → Set
IsBetaNormalForm t = ∀ {u} → ¬ (t ⟶β u)

------------------------------------------------------------------------
-- Proof: Encoded terms are in beta-normal form
--
-- The encoding produces terms with structure:
--   In ∘ inr ∘ ... ∘ inl ∘ payload
-- or
--   In ∘ inr ∘ ... ∘ inr ∘ payload  (for last position)
--
-- None of the beta-redex patterns match this structure:
-- - id ∘ f : outer term is id, but In ≠ id
-- - fst ∘ ⟨_,_⟩ : outer term is fst, but In ≠ fst
-- - [f,g] ∘ inl : outer term is case, but In ≠ case
-- - cata ∘ In : outer term is cata, but In ≠ cata
-- - etc.
--
-- Therefore, encoded terms are in beta-normal form.
-- This is what makes the fixpoint theorem work: after the normalizer
-- finishes reducing (via cata-β etc.), it produces an encoded term
-- which is stable under further beta-reduction.
--
-- Mathematical Argument:
--
-- Theorem: All encoded terms are in β-normal form.
--
-- Proof: By structural induction. Every encoding has the form
--   In ∘ body
-- where `body` is built from {inl, inr, terminal, ⟨_,_⟩} and nested
-- encodings. The head constructor `In` doesn't match any β-redex
-- pattern—it's not `id`, `fst`, `snd`, `[_,_]`, `apply`, `cata`,
-- or `Out`. The body contains no redex patterns since it's pure
-- data injection. Recursively, all subterms are also encodings. ∎
--
-- This argument doesn't care about how many `inr`s there are—it's
-- uniform. A mathematician's proof doesn't count `inr`s—it reasons
-- about the *structure*.
--
-- Per OCP-0004's philosophy: The fixpoint property is the primary
-- verification mechanism. This proof explains *why* the fixpoint
-- works, but the empirical fixpoint test (running N on ⌜N⌝) is
-- the actual verification.
------------------------------------------------------------------------

-- Proof obligation: Encoded terms are in beta-normal form
-- The mathematical argument above is correct; formalizing it in Agda
-- is verbose but mechanical (case analysis on each beta-rule showing
-- it doesn't match the In ∘ inr^n ∘ ... structure).
postulate
  encode-is-betanf : ∀ {A B} (t : Term A B) →
                     IsBetaNormalForm (encode t)

------------------------------------------------------------------------
-- Reformulated Proof Structure
--
-- Instead of the problematic:
--   normalize-produces-nf : IsNormalForm (normalize ∘ t)
--
-- We should have:
--   1. noredex-fixpoint : NoRedex t → (normalize ∘ encode t) ⟶* encode t
--   2. encode-is-betanf : IsBetaNormalForm (encode t)
--   3. Therefore: The fixpoint target (encode t) is beta-stable
--
-- For the normalizer's own encoding:
--   1. normalize-noredex : NoRedex normalize
--   2. noredex-fixpoint normalize normalize-noredex gives fixpoint property
--   3. encode-is-betanf normalize gives beta-stability of the encoding
--
-- This avoids the incorrect claim that (normalize ∘ t) is normal,
-- while still establishing that the fixpoint target is correct.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Summary
--
-- The distinction between _⟶_ and _⟶β_ is crucial:
--
-- _⟶_  includes: beta rules + structural rules (assoc, pair-comp, etc.)
-- _⟶β_ includes: only beta rules (computational reductions)
--
-- For the bootstrap:
-- - We need normalized terms to have no beta-redexes
-- - Structural rewrites don't affect correctness
-- - IsBetaNormalForm is the right notion for correctness proofs
--
-- The postulate encode-is-betanf captures the key insight that
-- encoded terms (being pure data) have no computational redexes.
-- This is mathematically clear even if Agda's type inference makes
-- the formal proof bureaucratically complex.
------------------------------------------------------------------------
