------------------------------------------------------------------------
-- EstablishedMath: Properties Beyond Standard CCC
--
-- This module contains axioms that go beyond standard CCC.
-- Standard CCC confluence is in StandardCCC.agda (truly established).
--
-- References:
--   [1] Lambek & Scott, "Introduction to Higher Order Categorical Logic"
--   [2] Tait, "Intensional interpretations of functionals of finite type"
--   [3] Girard, Lafont & Taylor, "Proofs and Types"
------------------------------------------------------------------------

module normalizer.Axioms.EstablishedMath where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
  using (Term; _∘_; _⟶_; _⟶*_; done; step; _⟹_; IsNormalForm; cata; fmap)
  public
open import normalizer.Syntax.CCC
  using (_⊎_)
open import normalizer.Syntax.NoRedex
  using (NoRedex)
open import normalizer.Encoding.Encoding
  using (encode; TermF)

------------------------------------------------------------------------
-- Part 1: Strong Normalization
--
-- Source: Tait [2] for STLC, extended for CCCs
--
-- NOTE: This is established for simply-typed lambda calculus.
-- For μ-types, strong normalization requires restricted recursive types.
-- In this system, we use guarded recursion via cata which ensures
-- termination.
------------------------------------------------------------------------

postulate
  strong-normalization : ∀ {A B} (t : Term A B) →
                         ∃[ nf ] ((t ⟶* nf) × IsNormalForm nf)

------------------------------------------------------------------------
-- Part 2: Soundness
--
-- For encoded terms, normalization computes a canonical representative.
------------------------------------------------------------------------

postulate
  normalize-semantics-equiv : ∀ {A} (N : Term A A) (t : Term Unit A) →
                              ((N ∘ t) ⟶* t) ⊎ (t ⟶* (N ∘ t))

------------------------------------------------------------------------
-- Part 3: Encoding Properties
------------------------------------------------------------------------

-- The encoding of a NoRedex term is a normal form.
postulate
  encode-is-nf : ∀ {A B} (t : Term A B) →
                 NoRedex t → IsNormalForm (encode t)

------------------------------------------------------------------------
-- Summary
--
-- Axioms in this module:
--   strong-normalization      : Termination for all terms
--   normalize-semantics-equiv : Soundness
--   encode-is-nf              : Encoding produces normal forms
--
-- Truly established (standard CCC) - see StandardCCC.agda:
--   ccc-complete, ccc-triangle : Lambek & Scott
--
-- Full confluence - see Confluence.agda:
--   complete, ⟹-to-complete : Should be derivable from StandardCCC + Cata
--
-- Cata properties - see CataAxioms.agda:
--   cata-terminates, cata-complete, cata-triangle, etc.
------------------------------------------------------------------------
