------------------------------------------------------------------------
-- Uniqueness: Normal Forms are Unique for Encoded Terms
--
-- This module proves that for NoRedex terms t:
--   If (normalize ∘ encode t) reduces to normal forms u and v,
--   then u ≡ v.
--
-- The proof combines:
--   1. Restricted confluence from StandardCCCExtension
--   2. The fixpoint property from TCB0
--
-- This establishes UNIQUENESS of normal forms, complementing the
-- EXISTENCE proof (noredex-fixpoint) from TCB0.
------------------------------------------------------------------------

module normalizer.Theory.Uniqueness where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
  using (Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_];
         terminal; initial; curry; apply; In; Out; cata; fmap;
         _⟶_; _⟶*_; done; step; ⟶*-trans; IsNormalForm)
open import normalizer.Syntax.NoRedex
  using (NoRedex)
open import normalizer.Encoding.Encoding
  using (encode; TyFuncCode; TermCode'; TermF)
open import normalizer.TCB0
  using (normalize; noredex-fixpoint)
open import normalizer.Theory.StandardCCCExtension.RestrictedConfluence
  using (restricted-confluence; restricted-confluence-noredex)

------------------------------------------------------------------------
-- Normal Forms and Confluence Imply Uniqueness
--
-- Standard lemma: if the reduction relation is confluent, then
-- normal forms are unique.
------------------------------------------------------------------------

-- If two normal forms are reachable from a common source in a
-- confluent system, they must be equal.
--
-- Proof sketch:
--   t ⟶* u (normal)
--   t ⟶* v (normal)
--   By confluence: ∃ w. u ⟶* w ∧ v ⟶* w
--   Since u is normal: u = w
--   Since v is normal: v = w
--   Therefore: u = v

-- A normal form cannot reduce further
normal-no-step : ∀ {A B} {t u : Term A B} →
                 IsNormalForm t → t ⟶* u → t ≡ u
normal-no-step nf done = refl
normal-no-step nf (step r _) = ⊥-elim (nf r)

-- Confluence + normal forms → unique normal form
confluence-unique-nf : ∀ {A B} (t u v : Term A B) →
                       (∀ {u' v' : Term A B} →
                         t ⟶* u' → t ⟶* v' →
                         ∃[ w ] ((u' ⟶* w) × (v' ⟶* w))) →
                       t ⟶* u → IsNormalForm u →
                       t ⟶* v → IsNormalForm v →
                       u ≡ v
confluence-unique-nf t u v conf red-u nf-u red-v nf-v with conf red-u red-v
... | w , (u→w , v→w) = trans (normal-no-step nf-u u→w) (sym (normal-no-step nf-v v→w))

------------------------------------------------------------------------
-- Main Theorem: Normalizer Produces Unique Results for NoRedex Terms
--
-- For any NoRedex term t:
--   If (normalize ∘ encode t) ⟶* u with IsNormalForm u
--   And (normalize ∘ encode t) ⟶* v with IsNormalForm v
--   Then u ≡ v
------------------------------------------------------------------------

normalizer-unique : ∀ {A B} (t : Term A B) (nr : NoRedex t) →
                    (u v : Term Unit TermCode') →
                    (normalize ∘ encode t) ⟶* u → IsNormalForm u →
                    (normalize ∘ encode t) ⟶* v → IsNormalForm v →
                    u ≡ v
normalizer-unique t nr u v red-u nf-u red-v nf-v =
  confluence-unique-nf (normalize ∘ encode t) u v
    (λ red-u' red-v' → restricted-confluence-noredex t nr _ red-u' red-v')
    red-u nf-u red-v nf-v

------------------------------------------------------------------------
-- Corollary: Fixpoint Result is Unique
--
-- The encoding of the normalizer (encode normalize) produces a unique
-- normal form when normalized.
------------------------------------------------------------------------

-- First, we need to know that normalize is NoRedex
-- This is exported from TCB0 as normalize-noredex
open import normalizer.TCB0.Normalizer.Definition
  using (normalize-noredex)

fixpoint-unique : (u v : Term Unit TermCode') →
                  (normalize ∘ encode normalize) ⟶* u → IsNormalForm u →
                  (normalize ∘ encode normalize) ⟶* v → IsNormalForm v →
                  u ≡ v
fixpoint-unique = normalizer-unique normalize normalize-noredex

------------------------------------------------------------------------
-- Strong Uniqueness: The Fixpoint IS encode normalize
--
-- Combined with noredex-fixpoint, we know:
--   (normalize ∘ encode normalize) ⟶* encode normalize
--
-- If encode normalize is a normal form, then ANY normal form u
-- reachable from (normalize ∘ encode normalize) must be encode normalize.
------------------------------------------------------------------------

-- encode t is a normal form for NoRedex t
-- (imported from EstablishedMath - follows from encode structure)
open import normalizer.Axioms.EstablishedMath
  using (encode-is-nf)

-- Specialization for normalize itself
encode-normalize-is-nf : IsNormalForm (encode normalize)
encode-normalize-is-nf = encode-is-nf normalize normalize-noredex

fixpoint-is-unique-nf : (u : Term Unit TermCode') →
                        (normalize ∘ encode normalize) ⟶* u →
                        IsNormalForm u →
                        u ≡ encode normalize
fixpoint-is-unique-nf u red-u nf-u =
  fixpoint-unique u (encode normalize) red-u nf-u
    (noredex-fixpoint normalize normalize-noredex) encode-normalize-is-nf

------------------------------------------------------------------------
-- CANONICAL FORM THEOREM (Corollary 4.2)
--
-- This is the key result for compiler verification:
--   For any NoRedex term t, any normal form of (normalize ∘ encode t)
--   is exactly (encode t).
--
-- This combines:
--   - Existence: noredex-fixpoint gives (normalize ∘ encode t) ⟶* encode t
--   - Uniqueness: normalizer-unique proves all normal forms are equal
--
-- The canonical form theorem says: the normalizer faithfully preserves
-- the encoding of any NoRedex term. This is exactly what we need for
-- compiler verification: running the normalizer on encoded code gives
-- back that code's encoding.
------------------------------------------------------------------------

canonical-normal-form : ∀ {A B} (t : Term A B) → NoRedex t →
                        (u : Term Unit TermCode') →
                        (normalize ∘ encode t) ⟶* u → IsNormalForm u →
                        u ≡ encode t
canonical-normal-form t nr u red-u nf-u =
  normalizer-unique t nr u (encode t) red-u nf-u
    (noredex-fixpoint t nr) (encode-is-nf t nr)

------------------------------------------------------------------------
-- Summary
--
-- Derived (from confluence + normal form definition):
--   confluence-unique-nf  : Standard lemma
--   normalizer-unique     : From restricted-confluence
--   fixpoint-unique       : Instantiation for normalize
--   fixpoint-is-unique-nf : Combines existence + uniqueness
--   canonical-normal-form : The key compiler verification theorem
--
-- The CANONICAL FORM THEOREM (canonical-normal-form) says:
--
--   "The normalizer faithfully preserves NoRedex terms"
--
-- If you encode a well-formed program, normalize it, and reach a
-- normal form, that normal form IS the original encoding. This is
-- exactly what bootstrapping requires.
--
-- Trust chain:
--   TCB0           : noredex-fixpoint (structural induction)
--   StandardCCC    : CCC confluence (Lambek & Scott)
--   EstablishedMath: encode-is-nf (structural)
--   This module    : Unique normal forms + canonical form theorem
------------------------------------------------------------------------
