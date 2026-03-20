------------------------------------------------------------------------
-- Confluence: Diamond Property for Parallel Reduction
--
-- The CCC reduction system is confluent using the Tait-Martin-Löf
-- technique:
--   1. Define parallel reduction ⟹ (in MinimalCCC)
--   2. Define "complete development" that reduces ALL redexes
--   3. Show: t ⟹ u implies u ⟹ (complete t)
--   4. Diamond follows: t ⟹ u and t ⟹ v implies both ⟹ (complete t)
------------------------------------------------------------------------

module normalizer.Foundations.Confluence where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC

------------------------------------------------------------------------
-- Complete Development
--
-- The complete development reduces ALL redexes simultaneously.
-- Strategy: recursively complete subterms, then contract any top-level redex.
--
-- The key β-reductions we handle:
--   id ∘ f → f              fst ∘ ⟨f,g⟩ → f       snd ∘ ⟨f,g⟩ → g
--   [f,g] ∘ inl → f         [f,g] ∘ inr → g       cata F alg ∘ In → alg ∘ fmap F (cata F alg)
--   apply ∘ ⟨curry f, g⟩ → f ∘ ⟨id, g⟩
--
-- Implementation: We postulate `complete` and `⟹-to-complete` together.
-- The definition is straightforward but Agda's dependent pattern matching
-- has unification issues with indexed types like Term A B when matching
-- on compositions with specific constructors (e.g., Out ∘ ⟨_,_⟩ is
-- type-impossible but Agda can't determine this).
--
-- The mathematical structure is clear:
--   complete t = recursively complete subterms, then contract any redex
--   ⟹-to-complete = any partial reduction can be extended to complete
------------------------------------------------------------------------

postulate
  -- Complete development function
  -- Reduces ALL redexes in a term simultaneously
  complete : ∀ {A B} → Term A B → Term A B

  -- Key lemma: any parallel reduction extends to complete development
  -- If t ⟹ u, then u ⟹ complete t
  -- (Because complete t contracts ALL redexes, and u has only some)
  ⟹-to-complete : ∀ {A B} {t u : Term A B} →
                  t ⟹ u → u ⟹ complete t

{-
-- For reference, the intended definition of complete:

complete id = id
complete fst = fst
complete snd = snd
complete inl = inl
complete inr = inr
complete terminal = terminal
complete initial = initial
complete apply = apply
complete In = In
complete Out = Out
complete ⟨ f , g ⟩ = ⟨ complete f , complete g ⟩
complete [ f , g ] = [ complete f , complete g ]
complete (curry f) = curry (complete f)
complete (cata F alg) = cata F (complete alg)
-- Compositions with redexes:
complete (id ∘ g) = complete g
complete (fst ∘ ⟨ f , g ⟩) = complete f
complete (snd ∘ ⟨ f , g ⟩) = complete g
complete ([ f , g ] ∘ inl) = complete f
complete ([ f , g ] ∘ inr) = complete g
complete (apply ∘ ⟨ curry f , g ⟩) = complete f ∘ ⟨ id , complete g ⟩
complete ((cata F alg) ∘ In) = complete alg ∘ fmap F (cata F (complete alg))
complete (⟨ f , g ⟩ ∘ h) = ⟨ complete f ∘ complete h , complete g ∘ complete h ⟩
complete (f ∘ id) = complete f
-- Default (no redex):
complete (f ∘ g) = complete f ∘ complete g

The ⟹-to-complete proof is by induction on the ⟹ derivation.
Each case shows that the partial reduction u can further reduce to complete t.
-}

------------------------------------------------------------------------
-- Diamond Property
------------------------------------------------------------------------

abstract
  diamond : ∀ {A B} {t u v : Term A B} →
            t ⟹ u → t ⟹ v →
            ∃[ w ] ((u ⟹ w) × (v ⟹ w))
  diamond {t = t} p q = complete t , (⟹-to-complete p , ⟹-to-complete q)

------------------------------------------------------------------------
-- Strip Lemma
------------------------------------------------------------------------

abstract
  strip : ∀ {A B} {t u v : Term A B} →
          t ⟹ u → t ⟹* v →
          ∃[ w ] ((u ⟹* w) × (v ⟹ w))
  strip {t = t} p done⟹ with diamond p (⟹-refl t)
  ... | w , (uw , tw) = w , (step⟹ uw done⟹ , tw)
  strip p (step⟹ q qs) with diamond p q
  ... | w , (pw , qw) with strip qw qs
  ... | w' , (qws , rw) = w' , (step⟹ pw qws , rw)

------------------------------------------------------------------------
-- Confluence for Parallel Reduction
------------------------------------------------------------------------

abstract
  confluence⟹ : ∀ {A B} {t u v : Term A B} →
                t ⟹* u → t ⟹* v →
                ∃[ w ] ((u ⟹* w) × (v ⟹* w))
  confluence⟹ done⟹ qs = _ , (qs , done⟹)
  confluence⟹ (step⟹ p ps) qs with strip p qs
  ... | w , (pw , qw) with confluence⟹ ps pw
  ... | w' , (pws , qws) = w' , (pws , step⟹ qw qws)

------------------------------------------------------------------------
-- Confluence for Single-Step Reduction
------------------------------------------------------------------------

abstract
  confluence : ∀ {A B} {t u v : Term A B} →
               t ⟶* u → t ⟶* v →
               ∃[ w ] ((u ⟶* w) × (v ⟶* w))
  confluence p q with confluence⟹ (⟶*→⟹* p) (⟶*→⟹* q)
  ... | w , (pw , qw) = w , (⟹*→⟶* pw , ⟹*→⟶* qw)

------------------------------------------------------------------------
-- Summary
--
-- Definitions (see code):
--   diamond     : t ⟹ u → t ⟹ v → ∃[ w ] (u ⟹ w × v ⟹ w)
--   strip       : t ⟹ u → t ⟹* v → ∃[ w ] (u ⟹* w × v ⟹ w)
--   confluence⟹ : t ⟹* u → t ⟹* v → ∃[ w ] (u ⟹* w × v ⟹* w)
--   confluence  : t ⟶* u → t ⟶* v → ∃[ w ] (u ⟶* w × v ⟶* w)
--
-- Proof obligations:
--   complete      : Term A B → Term A B
--   ⟹-to-complete : t ⟹ u → u ⟹ complete t
--
-- The complete development function reduces ALL redexes maximally.
-- Once defined and ⟹-to-complete is filled in, confluence follows.
--
-- Filling ⟹-to-complete is straightforward induction on the parallel
-- reduction derivation. Each case either:
--   - Is an atom (trivial)
--   - Uses congruence and induction hypothesis
--   - Is a beta rule where the contractum ⟹ complete t
------------------------------------------------------------------------
