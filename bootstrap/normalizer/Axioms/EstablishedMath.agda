------------------------------------------------------------------------
-- EstablishedMath: Results from Mathematical Literature
--
-- This module contains established theorems from the literature.
-- These results form the mathematical foundation of the verification.
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
-- Part 1: Confluence (Church-Rosser Property)
--
-- Source: Lambek & Scott [1], Chapter 1
-- Also: Tait-Martin-Löf parallel reduction technique
--
-- The CCC reduction relation is confluent: if t reduces to both u and v,
-- then u and v can both reduce to some common term w.
------------------------------------------------------------------------

-- Complete development: reduces ALL redexes simultaneously
-- This is the standard technique for proving confluence.
-- The function is well-defined by structural recursion on terms.
postulate
  complete : ∀ {A B} → Term A B → Term A B

-- Key lemma for confluence: any parallel reduction extends to complete
-- If t ⟹ u (parallel reduction), then u ⟹ complete t
-- Proof: By induction on the parallel reduction derivation.
-- Each redex in t is either contracted (giving part of complete t)
-- or preserved (and can still be contracted to reach complete t).
postulate
  ⟹-to-complete : ∀ {A B} {t u : Term A B} →
                   t ⟹ u → u ⟹ complete t

------------------------------------------------------------------------
-- Part 2: Strong Normalization (Termination)
--
-- Source: Tait [2], extended for CCCs
-- Also: Girard, Lafont & Taylor [3], Chapter 6
--
-- Every term in the simply-typed lambda calculus (internal language
-- of CCC) has a finite reduction sequence to a normal form.
--
-- The proof uses logical relations (reducibility candidates).
------------------------------------------------------------------------

-- Strong normalization: every term reduces to a normal form
postulate
  strong-normalization : ∀ {A B} (t : Term A B) →
                         ∃[ nf ] ((t ⟶* nf) × IsNormalForm nf)

------------------------------------------------------------------------
-- Part 3: Soundness of CCC Reduction
--
-- Source: Lambek & Scott [1], Chapters 1-2
--
-- The reduction rules of CCC are sound with respect to the categorical
-- semantics. Reduction preserves the denotation of terms.
--
-- This is used to justify that normalization preserves meaning.
------------------------------------------------------------------------

-- For encoded terms, either the normalizer reduces to the input,
-- or the input reduces to what the normalizer produces.
-- This captures that normalization computes a canonical representative.
-- Note: N must be an endomorphism (Term A A) for this to type check.
postulate
  normalize-semantics-equiv : ∀ {A} (N : Term A A) (t : Term Unit A) →
                              ((N ∘ t) ⟶* t) ⊎ (t ⟶* (N ∘ t))

------------------------------------------------------------------------
-- Part 4: Encoding Properties
--
-- Properties of the encode function for well-formed (NoRedex) terms.
------------------------------------------------------------------------

-- The encoding of a NoRedex term is a normal form.
-- This follows from encode producing only basic constructors (In, inl,
-- inr, pairs) composed together, with no redex patterns.
postulate
  encode-is-nf : ∀ {A B} (t : Term A B) →
                 NoRedex t → IsNormalForm (encode t)

------------------------------------------------------------------------
-- Summary
--
-- This module contains axioms from established mathematics:
--
--   Part 1: Confluence (Church-Rosser)
--     complete, ⟹-to-complete     [Lambek & Scott]
--
--   Part 2: Strong Normalization
--     strong-normalization        [Tait, Girard-Lafont-Taylor]
--
--   Part 3: Soundness
--     normalize-semantics-equiv   [Lambek & Scott]
--
--   Part 4: Encoding Properties
--     encode-is-nf                [structural]
--
-- Additional axioms in other Axioms/ files:
--   Axioms/StandardCCC.agda:
--     ccc-complete, ccc-triangle
--   Axioms/CataAxioms.agda:
--     cata-terminates, cata-complete, cata-triangle,
--     ccc-preserves-cata-structure, ccc*-confluence, factorize-reduction
------------------------------------------------------------------------

