------------------------------------------------------------------------
-- Theory.Models.StrongCCL3.Typed.ForgetCoded
--
-- The forgetful morphism and coherence theorem for the Phase 2 coded
-- typed encoding (Theory.Models.StrongCCL3.Typed.EncodingCoded).
--
--   forget-c : Term TypedCodeC Code
--   forget-c = snd ∘ snd
--
-- Same shape as Theory.Models.StrongCCL3.Typed.Forget; only the source
-- carrier differs (TypedCodeC instead of TypedCode).
--
-- COHERENCE:
--
--   ∀ {A B : TyClosed} (t : Term (lift A) (lift B)) →
--     (forget-c ∘ encode-typed-c t) ≈ encode t
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Models.StrongCCL3.Typed.ForgetCoded where

import Theory.Syntax.StrongCCL.CCT3 as Syn
open Syn using (Term; _∘_; snd; _≈_; ≈-trans; ∘-≈-congʳ)

open import Theory.Systems.CCT3 using (CCT3Structure)
open CCT3Structure Syn.canonical using (snd-pair; assoc)

open import Theory.Models.StrongCCL3.Encoding using (Code; encode)
open import Theory.Models.StrongCCL3.Typed.Func using (TyClosed; lift)
open import Theory.Models.StrongCCL3.Typed.EncodingCoded
  using (TypedCodeC; encode-typed-c)

------------------------------------------------------------------------
-- The coded forgetful morphism.
------------------------------------------------------------------------

forget-c : Term TypedCodeC Code
forget-c = snd ∘ snd

------------------------------------------------------------------------
-- Coherence: forgetting from the coded typed layer recovers the erased
-- layer.  Same proof shape as Typed.Forget (assoc + two snd-pair).
------------------------------------------------------------------------

forget-c-encode-typed-c :
  ∀ {A B : TyClosed} (t : Term (lift A) (lift B)) →
  (forget-c ∘ encode-typed-c t) ≈ encode t
forget-c-encode-typed-c {A} {B} t =
  ≈-trans assoc
    (≈-trans (∘-≈-congʳ snd-pair) snd-pair)
