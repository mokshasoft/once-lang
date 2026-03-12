------------------------------------------------------------------------
-- Level 0 Normalizer
--
-- The foundation of the bootstrap tower. This normalizer handles the
-- minimal CCC IR and is verified by the fixpoint property.
--
-- IR: id, ∘, fst, snd, ⟨,⟩, inl, inr, [,], terminal, In, cata
--
-- Reduction rules:
--   id ∘ f        ⟶ f           (id-left)
--   f ∘ id        ⟶ f           (id-right)
--   fst ∘ ⟨f,g⟩   ⟶ f           (fst-pair)
--   snd ∘ ⟨f,g⟩   ⟶ g           (snd-pair)
--   ⟨fst,snd⟩     ⟶ id          (eta-pair)
--   [f,g] ∘ inl   ⟶ f           (case-inl)
--   [f,g] ∘ inr   ⟶ g           (case-inr)
--   [inl,inr]     ⟶ id          (eta-case)
--   cata F a ∘ In ⟶ a ∘ fmap F (cata F a)  (cata-β)
------------------------------------------------------------------------

module normalizer.Level0.Normalizer where

-- Import shared foundations from spec/
open import spec.Types
open import spec.MinimalCCC
open import spec.Encoding
open import spec.Fixpoint

------------------------------------------------------------------------
-- Overview
--
-- The normalizer is a CCC term: N : Term TermCode' TermCode'
-- It is built as a cata over the TermF functor.
--
-- The algebra takes an "unfolded" term (where subterms are already
-- normalized encodings) and produces the normalized encoding of
-- the whole term.
--
-- Key insight: The encoding of a term t is always of the form:
--   In ∘ (inl ∘ ... | inr ∘ inl ∘ ... | ...)
-- where the nested inl/inr path identifies the constructor.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Term Constructor Tags (from Encoding.agda)
--
-- TermF encodes constructors as:
--   tag 0:  id A           = In ∘ inl ∘ ⌜A⌝
--   tag 1:  f ∘ g          = In ∘ inr ∘ inl ∘ ⟨encode f, encode g⟩
--   tag 2:  fst A B        = In ∘ inr ∘ inr ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩
--   tag 3:  snd A B        = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩
--   tag 4:  ⟨f, g⟩         = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨f', g'⟩
--   tag 5:  inl A B        = In ∘ inr ∘ ... ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩
--   tag 6:  inr A B        = In ∘ inr ∘ ... ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩
--   tag 7:  [f, g]         = In ∘ inr ∘ ... ∘ inl ∘ ⟨f', g'⟩
--   tag 8:  terminal A     = In ∘ inr ∘ ... ∘ inl ∘ ⌜A⌝
--   tag 9:  In F           = In ∘ inr ∘ ... ∘ inl ∘ ⌜F⌝
--   tag 10: cata F alg     = In ∘ inr ∘ ... ∘ inl ∘ ⟨⌜F⌝, encode alg⟩
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Strategy: Work with Term patterns directly
--
-- Rather than trying to decode the encoding, we work with the
-- actual Term type. The normalizer will:
--
-- 1. Pattern match on terms (the actual syntax)
-- 2. Check for redex patterns
-- 3. Return the reduced term or the original
--
-- Then we prove that this corresponds to the encoding-based version.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Single-step reducer
--
-- Tries to apply one reduction rule at the root.
-- Returns nothing if no rule applies.
--
-- We handle composition specially since most rules involve it.
------------------------------------------------------------------------

-- Helper: try to reduce a composition f ∘ g
-- We use separate functions for each rule to avoid unification issues.

-- Check if first argument is id
reduce-id-left : ∀ {A B C} → Term B C → Term A B → Maybe (Term A C)
reduce-id-left id g = inj₂ g
reduce-id-left _  _ = inj₁ tt

-- Check if second argument is id
reduce-id-right : ∀ {A B C} → Term B C → Term A B → Maybe (Term A C)
reduce-id-right f id = inj₂ f
reduce-id-right _ _  = inj₁ tt

-- Check for fst ∘ ⟨f, g⟩
reduce-fst-pair : ∀ {A B C} → Term B C → Term A B → Maybe (Term A C)
reduce-fst-pair fst ⟨ f , _ ⟩ = inj₂ f
reduce-fst-pair _   _         = inj₁ tt

-- Check for snd ∘ ⟨f, g⟩
reduce-snd-pair : ∀ {A B C} → Term B C → Term A B → Maybe (Term A C)
reduce-snd-pair snd ⟨ _ , g ⟩ = inj₂ g
reduce-snd-pair _   _         = inj₁ tt

-- Check for [f, g] ∘ inl
reduce-case-inl : ∀ {A B C} → Term B C → Term A B → Maybe (Term A C)
reduce-case-inl [ f , _ ] inl = inj₂ f
reduce-case-inl _         _   = inj₁ tt

-- Check for [f, g] ∘ inr
reduce-case-inr : ∀ {A B C} → Term B C → Term A B → Maybe (Term A C)
reduce-case-inr [ _ , g ] inr = inj₂ g
reduce-case-inr _         _   = inj₁ tt

-- Check for cata ∘ In
reduce-cata-In : ∀ {A B C} → Term B C → Term A B → Maybe (Term A C)
reduce-cata-In (cata F alg) In = inj₂ (alg ∘ fmap F (cata F alg))
reduce-cata-In _            _  = inj₁ tt

-- Maybe choice
infixr 3 _<|>_
_<|>_ : ∀ {A : Set} → Maybe A → Maybe A → Maybe A
inj₂ x <|> _ = inj₂ x
inj₁ _ <|> y = y

-- Combined: try all composition reductions
reduce-comp : ∀ {A B C} → Term B C → Term A B → Maybe (Term A C)
reduce-comp f g =
  reduce-id-left f g <|>
  reduce-id-right f g <|>
  reduce-fst-pair f g <|>
  reduce-snd-pair f g <|>
  reduce-case-inl f g <|>
  reduce-case-inr f g <|>
  reduce-cata-In f g

------------------------------------------------------------------------
-- Full normalization (recursive)
--
-- Normalize subterms, then check for root redex, repeat until fixed.
------------------------------------------------------------------------

-- Normalize a term to its normal form
-- This uses structural recursion on the term
{-# TERMINATING #-}  -- We'll replace this with a proper termination proof
normalize : ∀ {A B} → Term A B → Term A B

normalize id = id
normalize (f ∘ g) with reduce-comp (normalize f) (normalize g)
... | inj₂ reduced = normalize reduced
... | inj₁ _       = normalize f ∘ normalize g
normalize fst = fst
normalize snd = snd
normalize ⟨ f , g ⟩ = ⟨ normalize f , normalize g ⟩
-- TODO: eta-pair ⟨fst, snd⟩ ⟶ id requires more careful handling
normalize inl = inl
normalize inr = inr
normalize [ f , g ] = [ normalize f , normalize g ]
-- TODO: eta-case [inl, inr] ⟶ id requires more careful handling
normalize terminal = terminal
normalize In = In
normalize (cata F alg) = cata F (normalize alg)

------------------------------------------------------------------------
-- Correctness: normalize computes the normal form
------------------------------------------------------------------------

-- normalize produces a normal form
normalize-nf : ∀ {A B} (t : Term A B) → NF (normalize t)
normalize-nf t = {!!}

-- normalize preserves the reduction relation
normalize-sound : ∀ {A B} (t : Term A B) → t ⟶* normalize t
normalize-sound t = {!!}

------------------------------------------------------------------------
-- The Normalizer as a CCC Term
--
-- To satisfy NormalizerSpec, we need N : Term TermCode' TermCode'
-- This is the normalizer expressed as a CCC morphism operating on
-- encoded terms.
--
-- N = cata TermF normalizeAlg
--
-- For now, we postulate this and focus on the meta-level normalize.
------------------------------------------------------------------------

postulate
  N : ConcreteNormalizer

  -- N corresponds to normalize
  N-correct : ∀ {A B} (t : Term A B) →
    (N ∘ encode t) ⟶* encode (normalize t)

------------------------------------------------------------------------
-- NormalizerSpec Proofs
------------------------------------------------------------------------

N-wf : WellFormed N
N-wf = {!!}

N-fixpoint : IsFixpoint'' N
N-fixpoint = {!!}

produces-encoding : ∀ {A B} (t : Term A B) →
  Σ (Term A B) (λ u → ((N ∘ encode t) ⟶* encode u) × NF u)
produces-encoding t = normalize t , (N-correct t , normalize-nf t)

correct-reduction : ∀ {A B} (t : Term A B) {u : Term A B} →
  (N ∘ encode t) ⟶* encode u →
  t ⟶* u
correct-reduction t {u} red = {!!}

------------------------------------------------------------------------
-- Bundle into NormalizerSpec
------------------------------------------------------------------------

level0Spec : NormalizerSpec
level0Spec = record
  { N = N
  ; N-wf = N-wf
  ; N-fixpoint = N-fixpoint
  ; produces-encoding = produces-encoding
  ; correct-reduction = correct-reduction
  }

------------------------------------------------------------------------
-- Correctness Theorem
------------------------------------------------------------------------

level0-correct : ∀ {A B} (t : Term A B) →
  Σ (Term A B) (λ u → ((t ⟶* u) × NF u) × ((N ∘ encode t) ⟶* encode u))
level0-correct = concrete-fixpoint-correctness level0Spec
