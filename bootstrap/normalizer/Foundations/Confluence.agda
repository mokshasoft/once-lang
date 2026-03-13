------------------------------------------------------------------------
-- Confluence: Diamond Property for Parallel Reduction
--
-- We prove that our CCC reduction system is confluent using the
-- Tait-Martin-Löf technique:
--   1. Define parallel reduction ⟹ (already done in MinimalCCC)
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
-- For any term t, the complete development reduces ALL redexes.
-- This is postulated here; proving it requires careful case analysis.
------------------------------------------------------------------------

postulate
  -- Complete development function
  complete : ∀ {A B} → Term A B → Term A B

  -- Key lemma: any parallel reduction extends to complete development
  ⟹-to-complete : ∀ {A B} {t u : Term A B} →
                  t ⟹ u → u ⟹ complete t

------------------------------------------------------------------------
-- Diamond Property (proven from ⟹-to-complete)
------------------------------------------------------------------------

diamond : ∀ {A B} {t u v : Term A B} →
          t ⟹ u → t ⟹ v →
          ∃[ w ] ((u ⟹ w) × (v ⟹ w))
diamond {t = t} p q = complete t , (⟹-to-complete p , ⟹-to-complete q)

------------------------------------------------------------------------
-- Strip Lemma (proven)
------------------------------------------------------------------------

strip : ∀ {A B} {t u v : Term A B} →
        t ⟹ u → t ⟹* v →
        ∃[ w ] ((u ⟹* w) × (v ⟹ w))
strip {t = t} p done⟹ with diamond p (⟹-refl t)
... | w , (uw , tw) = w , (step⟹ uw done⟹ , tw)
strip p (step⟹ q qs) with diamond p q
... | w , (pw , qw) with strip qw qs
... | w' , (qws , rw) = w' , (step⟹ pw qws , rw)

------------------------------------------------------------------------
-- Confluence for Parallel Reduction (proven)
------------------------------------------------------------------------

confluence⟹ : ∀ {A B} {t u v : Term A B} →
              t ⟹* u → t ⟹* v →
              ∃[ w ] ((u ⟹* w) × (v ⟹* w))
confluence⟹ done⟹ qs = _ , (qs , done⟹)
confluence⟹ (step⟹ p ps) qs with strip p qs
... | w , (pw , qw) with confluence⟹ ps pw
... | w' , (pws , qws) = w' , (pws , step⟹ qw qws)

------------------------------------------------------------------------
-- Confluence for Single-Step Reduction (proven)
------------------------------------------------------------------------

confluence : ∀ {A B} {t u v : Term A B} →
             t ⟶* u → t ⟶* v →
             ∃[ w ] ((u ⟶* w) × (v ⟶* w))
confluence p q with confluence⟹ (⟶*→⟹* p) (⟶*→⟹* q)
... | w , (pw , qw) = w , (⟹*→⟶* pw , ⟹*→⟶* qw)

------------------------------------------------------------------------
-- Summary
--
-- PROVEN (from the two postulates):
--   diamond     : t ⟹ u → t ⟹ v → ∃[ w ] (u ⟹ w × v ⟹ w)
--   strip       : t ⟹ u → t ⟹* v → ∃[ w ] (u ⟹* w × v ⟹ w)
--   confluence⟹ : t ⟹* u → t ⟹* v → ∃[ w ] (u ⟹* w × v ⟹* w)
--   confluence  : t ⟶* u → t ⟶* v → ∃[ w ] (u ⟶* w × v ⟶* w)
--
-- POSTULATED (2):
--   complete      : Term A B → Term A B
--   ⟹-to-complete : t ⟹ u → u ⟹ complete t
--
-- The complete development function reduces ALL redexes maximally.
-- Once we define it and prove ⟹-to-complete, confluence follows.
--
-- Proving ⟹-to-complete is a straightforward (but tedious) induction
-- on the parallel reduction derivation. Each case either:
--   - Is an atom (trivial)
--   - Uses congruence and IH
--   - Is a beta rule where we show the contractum ⟹ complete t
------------------------------------------------------------------------
