------------------------------------------------------------------------
-- CataCommutation: Local Confluence for Cata Reductions
--
-- This module establishes local confluence (diamond property) for
-- cata reductions. The key insight is:
--
--   1. Two cata-beta reductions at the same position: trivially join
--   2. Two cata-beta reductions at disjoint positions: commute
--   3. Nested cata reductions: outer proceeds, inner is preserved
--
-- Combined with termination (CataElimination), this gives confluence
-- for the cata-reduction phase.
------------------------------------------------------------------------

module normalizer.Theory.StandardCCCExtension.CataCommutation where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
  using (Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_];
         terminal; initial; curry; apply; In; Out; cata; fmap;
         _⟶_; _⟶*_; done; step; ⟶*-trans;
         ⟶*-∘-l; ⟶*-∘-r; ⟶*-pair; ⟶*-case; ⟶*-curry; ⟶*-cata; fmap-⟶*)
open import normalizer.Encoding.Encoding
  using (encode; TyFuncCode; TermCode'; TermF)
open import normalizer.Theory.StandardCCCExtension.CataFree
  using (CataFree; encode-is-catafree)
open import normalizer.Theory.StandardCCCExtension.CataElimination
  using (_⟶cata_; _⟶*cata_; done-cata; step-cata;
         ⟶*cata-trans; ⟶cata→⟶; ⟶*cata→⟶*;
         ⟶*cata-∘-l; ⟶*cata-∘-r; ⟶*cata-pair; ⟶*cata-case;
         ⟶*cata-curry; ⟶*cata-cata;
         cata-β; cata-∘-l; cata-∘-r; cata-pair-l; cata-pair-r;
         cata-case-l; cata-case-r; cata-curry; cata-cata;
         catafree-no-cata-reduction)
open import normalizer.Axioms.StandardCCC
  using (_⟶ccc_; _⟶*ccc_; done-ccc; step-ccc;
         _⟹ccc_; ⟹ccc-refl;
         ccc-diamond; ccc-confluence⟹)

-- Import parallel cata reduction and basic lemmas
open import normalizer.Theory.StandardCCCExtension.ParallelCata
  using (_⟹cata_; ⟹cata-refl; ⟶cata→⟹cata; ⟹cata→⟶*cata;
         _⟹*cata_; done⟹cata; step⟹cata;
         ⟶*cata→⟹*cata; ⟹*cata→⟶*cata)
  public

------------------------------------------------------------------------
-- Cata Complete Development and Triangle Lemma (from CataAxioms)
------------------------------------------------------------------------

open import normalizer.Axioms.CataAxioms
  using (cata-complete; cata-triangle; ccc-preserves-cata-structure)

open _⟶_
open _⟶cata_
open _⟶ccc_

------------------------------------------------------------------------
-- Diamond Property for Cata (from triangle lemma)
------------------------------------------------------------------------

cata-diamond : ∀ {A B} {t u v : Term A B} →
               t ⟹cata u → t ⟹cata v →
               ∃[ w ] ((u ⟹cata w) × (v ⟹cata w))
cata-diamond {t = t} p q = cata-complete t , (cata-triangle p , cata-triangle q)

------------------------------------------------------------------------
-- Strip Lemma for Cata
------------------------------------------------------------------------

cata-strip : ∀ {A B} {t u v : Term A B} →
             t ⟹cata u → t ⟹*cata v →
             ∃[ w ] ((u ⟹*cata w) × (v ⟹cata w))
cata-strip {t = t} p done⟹cata with cata-diamond p (⟹cata-refl t)
... | w , (uw , tw) = w , (step⟹cata uw done⟹cata , tw)
cata-strip p (step⟹cata q qs) with cata-diamond p q
... | w , (pw , qw) with cata-strip qw qs
... | w' , (qws , rw) = w' , (step⟹cata pw qws , rw)

------------------------------------------------------------------------
-- Confluence for Parallel Cata Reduction
------------------------------------------------------------------------

cata-confluence⟹ : ∀ {A B} {t u v : Term A B} →
                   t ⟹*cata u → t ⟹*cata v →
                   ∃[ w ] ((u ⟹*cata w) × (v ⟹*cata w))
cata-confluence⟹ done⟹cata qs = _ , (qs , done⟹cata)
cata-confluence⟹ (step⟹cata p ps) qs with cata-strip p qs
... | w , (pw , qw) with cata-confluence⟹ ps pw
... | w' , (pws , qws) = w' , (pws , step⟹cata qw qws)

------------------------------------------------------------------------
-- Cata and CCC Commutation
--
-- Cata reductions and CCC reductions commute in the sense that
-- their order doesn't affect the final result (when both terminate).
--
-- This is because:
--   - cata-beta operates on (cata F alg ∘ In) patterns
--   - CCC reductions operate on CCC-specific patterns
--   - These patterns don't overlap (cata is not a CCC constructor)
------------------------------------------------------------------------

-- For CataFree terms, cata reductions have no effect
catafree-cata-trivial : ∀ {A B} {t : Term A B} →
                        CataFree t → t ⟹cata t
catafree-cata-trivial cf = ⟹cata-refl _

------------------------------------------------------------------------
-- Local Confluence: Two Cata-Beta Reductions Join
--
-- If t ⟶cata u and t ⟶cata v, then there exists w such that
-- u ⟶*cata w and v ⟶*cata w.
------------------------------------------------------------------------

cata-local-confluence : ∀ {A B} {t u v : Term A B} →
                        t ⟶cata u → t ⟶cata v →
                        ∃[ w ] ((u ⟶*cata w) × (v ⟶*cata w))
cata-local-confluence p q with cata-diamond (⟶cata→⟹cata p) (⟶cata→⟹cata q)
... | w , (uw , vw) = w , (⟹cata→⟶*cata uw , ⟹cata→⟶*cata vw)

------------------------------------------------------------------------
-- Summary
--
-- Re-exported from ParallelCata:
--   _⟹cata_, ⟹cata-refl, ⟶cata→⟹cata, ⟹cata→⟶*cata
--   _⟹*cata_, ⟶*cata→⟹*cata, ⟹*cata→⟶*cata
--
-- From Axioms/CataAxioms:
--   cata-complete, cata-triangle, ccc-preserves-cata-structure
--
-- Derived here (by standard parallel reduction technique):
--   cata-diamond         : From triangle
--   cata-strip           : By induction on ⟹*cata
--   cata-confluence⟹     : By induction using strip
--   cata-local-confluence: From diamond
--
-- These establish confluence for the cata-reduction phase.
------------------------------------------------------------------------
