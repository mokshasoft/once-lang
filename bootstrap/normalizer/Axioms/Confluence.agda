------------------------------------------------------------------------
-- Confluence: Diamond Property for Full Reduction
--
-- Full confluence for _⟹_ (which includes both CCC and cata rules).
--
-- STATUS: The complete and ⟹-to-complete are still axioms here,
-- but they SHOULD be derivable from:
--   - StandardCCC.ccc-complete, ccc-triangle (established)
--   - CataAxioms.cata-complete, cata-triangle
--   - CCC/cata commutation properties
--
-- The derivation requires proving that CCC and cata reductions
-- commute, allowing the combined complete development to work.
------------------------------------------------------------------------

module normalizer.Axioms.Confluence where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC

------------------------------------------------------------------------
-- Combined Complete Development
--
-- The full _⟹_ relation includes both CCC and cata-beta rules.
-- The complete development handles both:
--
--   complete (cata F alg ∘ In) = alg' ∘ fmap F (cata F alg')
--     where alg' = complete alg
--   complete (fst ∘ ⟨ f , g ⟩) = complete f
--   ... (other CCC rules from ccc-complete)
--   ... (structural cases)
--
-- This combines ccc-complete and cata-complete into one function.
-- The definition is straightforward by structural recursion.
------------------------------------------------------------------------

postulate
  complete : ∀ {A B} → Term A B → Term A B

------------------------------------------------------------------------
-- Triangle Lemma for Full Reduction
--
-- To derive from StandardCCC + Cata:
--   1. If t ⟹ u via CCC rules only: use ccc-triangle
--   2. If t ⟹ u via cata rules only: use cata-triangle
--   3. If mixed: use commutation (CCC and cata don't interfere)
--
-- The key property: ccc-preserves-cata-structure shows CCC
-- reductions preserve the cata reduction structure, and vice versa.
------------------------------------------------------------------------

postulate
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
