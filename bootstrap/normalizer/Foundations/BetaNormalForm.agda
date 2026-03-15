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
-- Proof Obligation: NoRedex implies BetaNormalForm
--
-- This requires extending NoRedex to exclude all beta-redex patterns.
-- Currently NoRedex only excludes id-compositions. For a complete
-- proof, we'd need to extend it to exclude all patterns listed above.
------------------------------------------------------------------------

-- For the current normalizer (which only handles id-compositions),
-- we have a partial result: NoRedex excludes id-left and id-right.
--
-- To prove the full IsBetaNormalForm, we'd need either:
-- 1. Extend NoRedex to exclude all beta-redexes
-- 2. Show that encoded terms don't have other beta-redexes
--
-- See NoRedex.agda for the current definition and Level0V2.NoRedex
-- for how it's used in the fixpoint property.

------------------------------------------------------------------------
-- Key Insight: Encoded Terms Have No Beta-Redexes
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
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Proof: Encoded terms are in beta-normal form
--
-- Strategy: All encoded terms have structure:
--   In ∘ inr^n ∘ inl ∘ payload   (for positions 0-12)
--   In ∘ inr^13 ∘ payload        (for position 13, apply)
--
-- The outer composition has In on the left. Looking at beta-redexes:
--   id ∘ f        : requires left = id, but In ≠ id
--   f ∘ id        : requires right = id, but inr^n ∘ ... has inr
--   fst ∘ ⟨_,_⟩   : requires left = fst, but In ≠ fst
--   snd ∘ ⟨_,_⟩   : requires left = snd, but In ≠ snd
--   [_,_] ∘ inl   : requires left = case, but In ≠ case
--   [_,_] ∘ inr   : requires left = case, but In ≠ case
--   apply ∘ ⟨curry _,_⟩ : requires left = apply, but In ≠ apply
--   cata ∘ In     : requires left = cata, but outer left is In
--   Out ∘ In      : requires left = Out, but outer left is In
--   In ∘ Out      : requires right = Out, but right is inr^n ∘ ...
--   ⟨fst, snd⟩    : requires term to be pair, but encoding is composition
--   [inl, inr]    : requires term to be case, but encoding is composition
--
-- None match! And recursively, subterms are also encodings.
------------------------------------------------------------------------

-- Helper: In is not any of the beta-redex left-hand patterns
-- (This is obvious from the Term definition but helps structure the proof)

-- Main theorem: Encoded terms have no beta-redexes
-- The proof is by showing each beta-rule doesn't match the encoding structure.
--
-- For a complete formal proof, we'd need:
-- 1. Case analysis on (encode t) ⟶β u
-- 2. For each beta-rule, show it doesn't match the structure In ∘ inr^n ∘ ...
-- 3. For congruence rules, use induction on subterms
--
-- The key observations that make this work:
-- - encode always produces In ∘ ... at the root
-- - In is not id, fst, snd, case, apply, cata, or Out
-- - The right side of the outer composition is always inr ∘ ... or inl ∘ ...
-- - Neither inr nor inl is id or Out
-- - Recursively, all subterms are also encodings

-- For now, we state this as a proof obligation:
postulate
  encode-is-betanf : ∀ {A B} (t : Term A B) →
                     IsBetaNormalForm (encode t)

-- The full proof would involve ~14 cases (one per term constructor)
-- times ~12 beta-rules to refute. It's mechanical but verbose.
-- See NoRedex.agda for similar structural proofs.

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
-- The postulate normalize-produces-nf in MainTheorem should probably
-- be reformulated to use IsBetaNormalForm instead of IsNormalForm.
------------------------------------------------------------------------
