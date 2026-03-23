------------------------------------------------------------------------
-- CataAxioms: Axioms for Catamorphism Properties
--
-- This module contains axioms about catamorphism reductions.
-- The types are defined in Theory/, the axioms about them are here.
------------------------------------------------------------------------

module normalizer.Axioms.CataAxioms where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
  using (Term; _∘_; cata; fmap; In; _⟶*_)
open import normalizer.Encoding.Encoding
  using (encode; TermF)
open import normalizer.Axioms.StandardCCC
  using (_⟶ccc_; _⟶*ccc_)

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
