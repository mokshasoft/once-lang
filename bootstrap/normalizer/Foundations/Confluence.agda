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
-- Complete Development (proof obligation)
--
-- For any term t, the complete development reduces ALL redexes.
-- Filling this in requires careful case analysis on term structure.
------------------------------------------------------------------------

postulate
  -- Complete development function
  complete : ∀ {A B} → Term A B → Term A B

  -- Key lemma: any parallel reduction extends to complete development
  ⟹-to-complete : ∀ {A B} {t u : Term A B} →
                  t ⟹ u → u ⟹ complete t

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
