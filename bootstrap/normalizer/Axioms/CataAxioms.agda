------------------------------------------------------------------------
-- CataAxioms: Axioms for Catamorphism Properties
--
-- This module contains axioms about catamorphism reductions.
-- The types are defined in Theory/, the axioms about them are here.
------------------------------------------------------------------------

module normalizer.Axioms.CataAxioms where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
  using (Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_];
         terminal; initial; curry; apply; In; Out; cata; fmap;
         _⟶*_; _⟹_)
open import normalizer.Encoding.Encoding
  using (encode; TermF)
open import normalizer.Axioms.StandardCCC
  using (_⟶ccc_; _⟶*ccc_; _⟹ccc_; ccc-complete)

-- Import type definitions (no axioms in these)
open import normalizer.Theory.StandardCCCExtension.CataElimination
  using (_⟶*cata_)
open import normalizer.Theory.StandardCCCExtension.ParallelCata
  using (_⟹cata_)

------------------------------------------------------------------------
-- Cata Termination
--
-- Argument for termination:
-- 1. encode t has finite depth (structural recursion on t)
-- 2. cata-beta consumes one In layer
-- 3. fmap distributes cata to recursive positions
-- 4. Eventually all In layers are processed
------------------------------------------------------------------------

postulate
  cata-terminates : ∀ {A B} (t : Term A B) {X} (alg : Term (⟦ TermF ⟧F X) X) →
                    ∃[ r ] ((cata TermF alg ∘ encode t) ⟶*cata r)

------------------------------------------------------------------------
-- Cata Complete Development and Triangle Lemma
------------------------------------------------------------------------

postulate
  cata-complete : ∀ {A B} → Term A B → Term A B

postulate
  cata-triangle : ∀ {A B} {t u : Term A B} →
                  t ⟹cata u → u ⟹cata cata-complete t

postulate
  ccc-preserves-cata-structure : ∀ {A B} {t u : Term A B} →
                                 t ⟶ccc u →
                                 cata-complete t ⟹cata cata-complete u

------------------------------------------------------------------------
-- Reduction Factorization and CCC Confluence
------------------------------------------------------------------------

postulate
  ccc*-confluence : ∀ {A B} {t u v : Term A B} →
                    t ⟶*ccc u → t ⟶*ccc v →
                    ∃[ w ] ((u ⟶*ccc w) × (v ⟶*ccc w))

postulate
  factorize-reduction : ∀ {A B} {t u : Term A B} →
                        t ⟶* u →
                        ∃[ mid ] ((t ⟶*cata mid) × (mid ⟶*ccc u))

------------------------------------------------------------------------
-- Combined Complete Development
--
-- The combined complete development handles all redex types:
--   - CCC redexes (via ccc-complete)
--   - Cata redexes (via cata-complete)
--   - Out∘In and In∘Out (iso rules)
--
-- The definition (conceptually):
--   complete (cata F alg ∘ In) = complete alg ∘ fmap F (cata F (complete alg))
--   complete (fst ∘ ⟨ f , g ⟩) = complete f
--   complete (Out ∘ In) = id
--   complete (In ∘ Out) = id
--   ... (other CCC and cata rules)
--   ... (structural recursion for non-redex patterns)
--
-- This is well-defined by structural recursion on terms.
------------------------------------------------------------------------

postulate
  -- Combined complete development
  complete : ∀ {A B} → Term A B → Term A B

------------------------------------------------------------------------
-- Triangle Lemma (Combined)
--
-- The key property: any parallel step reaches the complete development.
--
-- Derivation sketch by cases on t ⟹ u:
--   - ⟹-cata-β: use cata-triangle, then ccc-complete is reflexive
--   - ⟹-fst-β, etc.: use ccc-triangle, then cata-complete is reflexive
--   - ⟹-out-in, ⟹-in-out: id reaches complete t via reflexivity
--   - ⟹-∘, ⟹-pair, etc.: use IH, complete distributes
--
-- The commutation property ensures CCC and cata steps don't interfere:
--   ccc-complete (cata-complete t) = cata-complete (ccc-complete t)
-- which follows from orthogonality of redex patterns.
------------------------------------------------------------------------

postulate
  ⟹-to-complete : ∀ {A B} {t u : Term A B} →
                   t ⟹ u → u ⟹ complete t

------------------------------------------------------------------------
-- Commutation Properties
--
-- These ensure that CCC and cata reductions can be reordered.
-- Conceptually: CCC redexes and cata redexes are orthogonal because:
--   - CCC redexes match patterns like (fst ∘ ⟨_,_⟩), ([_,_] ∘ inl), etc.
--   - Cata redex matches (cata F alg ∘ In)
--   - These patterns don't overlap
--
-- After reducing one type of redex, the other type's structure is preserved.
------------------------------------------------------------------------

-- After cata reduction, CCC structure is preserved
postulate
  cata-preserves-ccc-structure : ∀ {A B} {t u : Term A B} →
                                 t ⟹cata u →
                                 ccc-complete t ⟹cata ccc-complete u

-- Combining complete developments commutes (up to ⟹)
postulate
  complete-commutation : ∀ {A B} (t : Term A B) →
                         ccc-complete (cata-complete t) ⟹ complete t
