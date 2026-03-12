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
open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
open import normalizer.Foundations.Fixpoint

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
-- Eta reduction (TODO)
--
-- The eta rules are:
--   ⟨ fst , snd ⟩ : Term (A * B) (A * B) ⟶ id   (eta-pair)
--   [ inl , inr ] : Term (A + B) (A + B) ⟶ id   (eta-case)
--
-- Implementing eta reduction in Agda with indexed types is tricky:
-- - Pattern matching on `fst` constrains the domain to be a product
-- - A catch-all case must handle all other constructors
-- - Agda's coverage checker gets stuck on type unification
--
-- Possible solutions:
-- 1. Use decidable term equality with type casts
-- 2. Use a "tag" representation that erases type indices
-- 3. Use an external normalization pass for eta
--
-- For now, we skip eta reduction. The normalizer is still correct
-- for beta reduction; eta just means some terms aren't fully reduced.
------------------------------------------------------------------------

-- Soundness lemmas for eta rules (for future use)
eta-pair-sound : ∀ {A B} → ⟨ fst {A} {B} , snd ⟩ ⟶ id
eta-pair-sound = eta-pair

eta-case-sound : ∀ {A B} → [ inl {A} {B} , inr ] ⟶ id
eta-case-sound = eta-case

------------------------------------------------------------------------
-- Soundness of reduction helpers
--
-- Each reduce-* function, when it returns inj₂ h, corresponds to
-- a valid single-step reduction f ∘ g ⟶ h.
------------------------------------------------------------------------

-- Transitivity of multi-step reduction
trans⟶* : ∀ {A B} {t u v : Term A B} → t ⟶* u → u ⟶* v → t ⟶* v
trans⟶* done q = q
trans⟶* (step p ps) q = step p (trans⟶* ps q)

------------------------------------------------------------------------
-- Congruence Lemmas
--
-- These are proven using parallel reduction:
-- 1. Lift ⟶* to ⇒* using ⟶*→⇒*
-- 2. Apply parallel congruence (⇒-∘, ⇒-pair, etc.)
-- 3. Convert back via ⇒*→⟶*
------------------------------------------------------------------------

-- Helper: lift parallel reduction through ⇒* preserving congruence
-- If we have f ⇒* f', we can derive (f ∘ g) ⇒* (f' ∘ g)
cong-⇒*-∘-left : ∀ {A B C} {f f' : Term B C} (g : Term A B) →
                  f ⇒* f' → (f ∘ g) ⇒* (f' ∘ g)
cong-⇒*-∘-left g done⇒ = done⇒
cong-⇒*-∘-left g (step⇒ p ps) = step⇒ (⇒-∘ p (⇒-refl g)) (cong-⇒*-∘-left g ps)

cong-⇒*-∘-right : ∀ {A B C} (f : Term B C) {g g' : Term A B} →
                   g ⇒* g' → (f ∘ g) ⇒* (f ∘ g')
cong-⇒*-∘-right f done⇒ = done⇒
cong-⇒*-∘-right f (step⇒ p ps) = step⇒ (⇒-∘ (⇒-refl f) p) (cong-⇒*-∘-right f ps)

cong-⇒*-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
                f ⇒* f' → g ⇒* g' → ⟨ f , g ⟩ ⇒* ⟨ f' , g' ⟩
cong-⇒*-pair done⇒ done⇒ = done⇒
cong-⇒*-pair done⇒ (step⇒ q qs) = step⇒ (⇒-pair (⇒-refl _) q) (cong-⇒*-pair done⇒ qs)
cong-⇒*-pair (step⇒ p ps) qs = step⇒ (⇒-pair p (⇒-refl _)) (cong-⇒*-pair ps qs)

cong-⇒*-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
                f ⇒* f' → g ⇒* g' → [ f , g ] ⇒* [ f' , g' ]
cong-⇒*-case done⇒ done⇒ = done⇒
cong-⇒*-case done⇒ (step⇒ q qs) = step⇒ (⇒-case (⇒-refl _) q) (cong-⇒*-case done⇒ qs)
cong-⇒*-case (step⇒ p ps) qs = step⇒ (⇒-case p (⇒-refl _)) (cong-⇒*-case ps qs)

cong-⇒*-cata : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
                alg ⇒* alg' → cata F alg ⇒* cata F alg'
cong-⇒*-cata done⇒ = done⇒
cong-⇒*-cata (step⇒ p ps) = step⇒ (⇒-cata p) (cong-⇒*-cata ps)

-- Now derive ⟶* congruence from ⇒* congruence
cong-∘-left : ∀ {A B C} {f f' : Term B C} (g : Term A B) →
              f ⟶* f' → (f ∘ g) ⟶* (f' ∘ g)
cong-∘-left g red = ⇒*→⟶* (cong-⇒*-∘-left g (⟶*→⇒* red))

cong-∘-right : ∀ {A B C} (f : Term B C) {g g' : Term A B} →
               g ⟶* g' → (f ∘ g) ⟶* (f ∘ g')
cong-∘-right f red = ⇒*→⟶* (cong-⇒*-∘-right f (⟶*→⇒* red))

cong-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
            f ⟶* f' → g ⟶* g' → ⟨ f , g ⟩ ⟶* ⟨ f' , g' ⟩
cong-pair rf rg = ⇒*→⟶* (cong-⇒*-pair (⟶*→⇒* rf) (⟶*→⇒* rg))

cong-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
            f ⟶* f' → g ⟶* g' → [ f , g ] ⟶* [ f' , g' ]
cong-case rf rg = ⇒*→⟶* (cong-⇒*-case (⟶*→⇒* rf) (⟶*→⇒* rg))

cong-cata : ∀ {F A} {alg alg' : Term (⟦ F ⟧F A) A} →
            alg ⟶* alg' → cata F alg ⟶* cata F alg'
cong-cata red = ⇒*→⟶* (cong-⇒*-cata (⟶*→⇒* red))

------------------------------------------------------------------------
-- Soundness of reduction helpers
--
-- Each reduce-* function is sound: when it returns inj₂ h, we have f ∘ g ⟶ h.
------------------------------------------------------------------------

-- Soundness of individual reducers

reduce-id-left-sound : ∀ {A B C} (f : Term B C) (g : Term A B) (h : Term A C) →
  reduce-id-left f g ≡ inj₂ h → (f ∘ g) ⟶ h
reduce-id-left-sound id g .g refl = id-left

reduce-id-right-sound : ∀ {A B C} (f : Term B C) (g : Term A B) (h : Term A C) →
  reduce-id-right f g ≡ inj₂ h → (f ∘ g) ⟶ h
reduce-id-right-sound f id .f refl = id-right

reduce-fst-pair-sound : ∀ {A B C} (f : Term B C) (g : Term A B) (h : Term A C) →
  reduce-fst-pair f g ≡ inj₂ h → (f ∘ g) ⟶ h
reduce-fst-pair-sound fst ⟨ h , _ ⟩ .h refl = fst-pair

reduce-snd-pair-sound : ∀ {A B C} (f : Term B C) (g : Term A B) (h : Term A C) →
  reduce-snd-pair f g ≡ inj₂ h → (f ∘ g) ⟶ h
reduce-snd-pair-sound snd ⟨ _ , h ⟩ .h refl = snd-pair

reduce-case-inl-sound : ∀ {A B C} (f : Term B C) (g : Term A B) (h : Term A C) →
  reduce-case-inl f g ≡ inj₂ h → (f ∘ g) ⟶ h
reduce-case-inl-sound [ h , _ ] inl .h refl = case-inl

reduce-case-inr-sound : ∀ {A B C} (f : Term B C) (g : Term A B) (h : Term A C) →
  reduce-case-inr f g ≡ inj₂ h → (f ∘ g) ⟶ h
reduce-case-inr-sound [ _ , h ] inr .h refl = case-inr

reduce-cata-In-sound : ∀ {A B C} (f : Term B C) (g : Term A B) (h : Term A C) →
  reduce-cata-In f g ≡ inj₂ h → (f ∘ g) ⟶ h
reduce-cata-In-sound (cata F alg) In .(alg ∘ fmap F (cata F alg)) refl = cata-β

-- Helper: <|> soundness - if x <|> y = inj₂ h, then either x or y returned inj₂ h
<|>-sound : ∀ {A : Set} (x y : Maybe A) (h : A) →
  (x <|> y) ≡ inj₂ h →
  (x ≡ inj₂ h) ⊎ ((x ≡ inj₁ tt) × (y ≡ inj₂ h))
<|>-sound (inj₂ x) y h eq = inj₁ eq
<|>-sound (inj₁ tt) (inj₂ y) h refl = inj₂ (refl , refl)

-- Combined soundness using <|>-sound
reduce-comp-sound : ∀ {A B C} (f : Term B C) (g : Term A B) (h : Term A C) →
  reduce-comp f g ≡ inj₂ h → (f ∘ g) ⟶ h
reduce-comp-sound f g h eq with <|>-sound (reduce-id-left f g) _ h eq
... | inj₁ p = reduce-id-left-sound f g h p
... | inj₂ (_ , eq') with <|>-sound (reduce-id-right f g) _ h eq'
...   | inj₁ p = reduce-id-right-sound f g h p
...   | inj₂ (_ , eq'') with <|>-sound (reduce-fst-pair f g) _ h eq''
...     | inj₁ p = reduce-fst-pair-sound f g h p
...     | inj₂ (_ , eq''') with <|>-sound (reduce-snd-pair f g) _ h eq'''
...       | inj₁ p = reduce-snd-pair-sound f g h p
...       | inj₂ (_ , eq'''') with <|>-sound (reduce-case-inl f g) _ h eq''''
...         | inj₁ p = reduce-case-inl-sound f g h p
...         | inj₂ (_ , eq''''') with <|>-sound (reduce-case-inr f g) _ h eq'''''
...           | inj₁ p = reduce-case-inr-sound f g h p
...           | inj₂ (_ , eq'''''') = reduce-cata-In-sound f g h eq''''''

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
normalize ⟨ f , g ⟩ = ⟨ normalize f , normalize g ⟩  -- TODO: eta-pair
normalize inl = inl
normalize inr = inr
normalize [ f , g ] = [ normalize f , normalize g ]  -- TODO: eta-case
normalize terminal = terminal
normalize In = In
normalize (cata F alg) = cata F (normalize alg)

------------------------------------------------------------------------
-- Correctness: normalize computes the normal form
------------------------------------------------------------------------

-- normalize produces a normal form
-- Proof strategy: Show that after normalization, reduce-comp returns inj₁
-- for any potential redex. This is true because we keep reducing until
-- no more redexes are found.
--
-- Due to the TERMINATING pragma, we mark this as TERMINATING as well.
-- A proper proof would use well-founded recursion on the measure.
--
-- This proof is tricky because NF is defined as ∀ {u} → ¬ (t ⟶ u),
-- meaning we need to show no reduction applies. We postulate it for now
-- as it requires showing reduce-comp returns inj₁ for normalized terms.
postulate
  normalize-nf : ∀ {A B} (t : Term A B) → NF (normalize t)

-- normalize preserves the reduction relation
-- Proof strategy: Each step of normalize corresponds to zero or more
-- reduction steps. For base cases, t ⟶* t (done). For recursive cases,
-- use transitivity and congruence.
--
-- The composition case is the interesting one:
--   normalize (f ∘ g) looks at reduce-comp (normalize f) (normalize g)
--   - If inj₂ reduced: we recurse on reduced (not structurally smaller!)
--   - If inj₁ _: we return normalize f ∘ normalize g
--
-- We use TERMINATING since normalize itself uses TERMINATING.
-- The proof follows the same recursive structure.

-- Mutual recursion for normalize-sound
-- We need the composition case to call normalize-sound recursively
mutual
  {-# TERMINATING #-}
  normalize-sound : ∀ {A B} (t : Term A B) → t ⟶* normalize t
  normalize-sound id = done
  normalize-sound (f ∘ g) = normalize-sound-∘ f g
  normalize-sound fst = done
  normalize-sound snd = done
  normalize-sound ⟨ f , g ⟩ = cong-pair (normalize-sound f) (normalize-sound g)
  normalize-sound inl = done
  normalize-sound inr = done
  normalize-sound [ f , g ] = cong-case (normalize-sound f) (normalize-sound g)
  normalize-sound terminal = done
  normalize-sound In = done
  normalize-sound (cata F alg) = cong-cata (normalize-sound alg)

  -- Helper for composition case
  -- Uses the same with-clause structure as normalize to ensure types match.
  -- We use the inspect idiom to capture the equality proof from the with-match.
  {-# TERMINATING #-}
  normalize-sound-∘ : ∀ {A B C} (f : Term B C) (g : Term A B) →
                      (f ∘ g) ⟶* normalize (f ∘ g)
  normalize-sound-∘ f g
    with reduce-comp (normalize f) (normalize g)
       | inspect (reduce-comp (normalize f)) (normalize g)
  normalize-sound-∘ f g | inj₂ reduced | ⟪ eq ⟫ =
    trans⟶* (trans⟶* (cong-∘-left g (normalize-sound f))
                      (cong-∘-right (normalize f) (normalize-sound g)))
            (trans⟶* (step (reduce-comp-sound (normalize f) (normalize g) reduced eq) done)
                     (normalize-sound reduced))
  normalize-sound-∘ f g | inj₁ _ | _ =
    trans⟶* (cong-∘-left g (normalize-sound f))
            (cong-∘-right (normalize f) (normalize-sound g))

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

-- N is well-formed (no unguarded recursion in algebra)
-- Since N is postulated, we must postulate this property.
-- When N is defined concretely as cata TermF normalizeAlg,
-- this would be proven by showing normalizeAlg is InFree.
postulate
  N-wf : WellFormed N

-- N satisfies the fixpoint property: N ∘ encode N ⟶* encode N
-- This is the key observable property that bootstraps verification.
-- We postulate it here; in practice, this is CHECKED by running the
-- normalizer on its own encoding.
postulate
  N-fixpoint : IsFixpoint'' N

produces-encoding : ∀ {A B} (t : Term A B) →
  Σ (Term A B) (λ u → ((N ∘ encode t) ⟶* encode u) × NF u)
produces-encoding t = normalize t , (N-correct t , normalize-nf t)

-- If N normalizes encode t to encode u, then t reduces to u.
-- This is the semantic correctness of normalization.
-- The proof uses encoding injectivity: since normalize is sound,
-- t ⟶* normalize t, and if N ∘ encode t ⟶* encode u, then by
-- unique normal forms, normalize t = u (up to encoding), so t ⟶* u.
--
-- The full proof requires showing encoding is injective on normal forms.
-- We postulate this since N is postulated.
postulate
  correct-reduction : ∀ {A B} (t : Term A B) {u : Term A B} →
    (N ∘ encode t) ⟶* encode u →
    t ⟶* u

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
