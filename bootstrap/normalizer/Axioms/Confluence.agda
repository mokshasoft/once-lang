------------------------------------------------------------------------
-- Confluence: Diamond Property for Full Reduction
--
-- Full confluence for _⟹_ (which includes both CCC and cata rules).
--
-- The combined complete development and triangle lemma are in
-- CataAxioms, which combines:
--   - StandardCCC.ccc-complete, ccc-triangle (established)
--   - CataAxioms.cata-complete, cata-triangle
--   - CCC/cata commutation properties
------------------------------------------------------------------------

module normalizer.Axioms.Confluence where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC

------------------------------------------------------------------------
-- Import Combined Complete Development from CataAxioms
--
-- The full _⟹_ relation includes CCC, cata-beta, and Out/In rules.
-- The combined complete development handles all of these:
--
--   complete (cata F alg ∘ In) = alg' ∘ fmap F (cata F alg')
--     where alg' = complete alg
--   complete (fst ∘ ⟨ f , g ⟩) = complete f
--   complete (Out ∘ In) = id
--   complete (In ∘ Out) = id
--   ... (other CCC rules)
--   ... (structural recursion)
------------------------------------------------------------------------

open import normalizer.Axioms.CataAxioms
  using (complete; ⟹-to-complete)
  public

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
-- Derivation Path (TODO)
--
-- To eliminate the postulates above, prove:
--
-- 1. Define: complete = ccc-part ∘ cata-part
--    where ccc-part handles CCC redexes, cata-part handles cata redexes
--
-- 2. Prove: ⟹-to-complete by cases on the ⟹ derivation
--    - For ⟹-cata-β: use cata-triangle
--    - For ⟹-fst-pair, etc.: use ccc-triangle
--    - For congruence: use IH
--    - Key: ccc and cata parts don't interfere (commutation)
--
-- 3. The commutation lemmas needed:
--    - cata-then-ccc ⟹ ccc-then-cata (reordering)
--    - Or: complete handles interleaved reductions correctly
--
-- This is straightforward but tedious case analysis.
------------------------------------------------------------------------
