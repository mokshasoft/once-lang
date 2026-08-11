------------------------------------------------------------------------
-- Theory.Models.StrongCCL3.Typed.Forget
--
-- The forgetful morphism from the typed encoding (Layer A) to the
-- type-erased encoding (Layer B), and the coherence theorem linking
-- the two layers.
--
-- DEFINITION:
--
--   forget : Term TypedCode Code
--   forget = snd ∘ snd
--
--   The TypedCode carrier is TyCode × TyCode × Code (right-associating
--   to TyCode × (TyCode × Code)). Two snd projections drop the source
--   and target type tags, returning the erased term encoding.
--
-- COHERENCE:
--
--   ∀ {A B} (t : Term A B) →
--     (forget ∘ encode-typed t) ≈ encode t
--
--   This is the principled bridge that justifies stating RF correctness
--   at the erased layer (uniform Code, simpler Transparency statement)
--   while letting the compiler IR live at the typed layer (round-trip,
--   faithful over all morphisms).
--
-- PROOF SHAPE:
--
--   (snd ∘ snd) ∘ ⟨ encode-ty A , ⟨ encode-ty B , encode t ⟩ ⟩
--   ≈⟨ assoc ⟩
--   snd ∘ (snd ∘ ⟨ encode-ty A , ⟨ encode-ty B , encode t ⟩ ⟩)
--   ≈⟨ ∘-cong-on-right snd-pair ⟩
--   snd ∘ ⟨ encode-ty B , encode t ⟩
--   ≈⟨ snd-pair ⟩
--   encode t
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Models.StrongCCL3.Typed.Forget where

import Theory.Syntax.StrongCCL.CCT3 as Syn
open Syn using (Term; _∘_; snd; ⟨_,_⟩; _≈_; ≈-trans; ∘-≈-congʳ)

open import Theory.Systems.CCT3 using (CCT3Structure)
open CCT3Structure Syn.canonical using (snd-pair; assoc)

open import Theory.Models.StrongCCL3.Encoding using (Code; encode)
open import Theory.Models.StrongCCL3.Typed.TyEncoding using (TyCode; encode-ty)
open import Theory.Models.StrongCCL3.Typed.Encoding using (TypedCode; encode-typed)

------------------------------------------------------------------------
-- The forgetful morphism.
--
-- Drops the source-type tag and the target-type tag, leaving only the
-- erased term encoding.
------------------------------------------------------------------------

forget : Term TypedCode Code
forget = snd ∘ snd

------------------------------------------------------------------------
-- Coherence: forgetting from the typed layer recovers the erased layer.
--
-- Reduces by associativity + two applications of snd-pair.
------------------------------------------------------------------------

forget-encode-typed :
  ∀ {A B} (t : Term A B) →
  (forget ∘ encode-typed t) ≈ encode t
forget-encode-typed {A} {B} t =
  ≈-trans assoc                    -- (snd ∘ snd) ∘ ⟨a,⟨b,e⟩⟩ ≈ snd ∘ (snd ∘ ⟨a,⟨b,e⟩⟩)
  (≈-trans (∘-≈-congʳ snd-pair)    -- snd ∘ (snd ∘ ⟨a,⟨b,e⟩⟩) ≈ snd ∘ ⟨b,e⟩
           snd-pair)               -- snd ∘ ⟨b,e⟩            ≈ e
