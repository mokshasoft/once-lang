------------------------------------------------------------------------
-- Theory.Models.StrongCCL3.Typed.EncodingCoded
--
-- The refined typed encoding using Func-coded TyClosed types.
--
-- This is the Phase 2 upgrade to Theory.Models.StrongCCL3.Typed.Encoding.
-- The Phase 1 version paired (encode-ty A , encode-ty B , encode t) with
-- encode-ty opaque on μ-types. Here, source and target are restricted
-- to the closed-type universe TyClosed (Theory.Models.StrongCCL3.Typed.
-- Func), and encode-tyc is faithful on all of TyClosed including μ —
-- the μ-tag now carries an encoded Func code (Theory.Models.StrongCCL3.
-- Typed.Coded).
--
--   encode-typed-c : ∀ {A B : TyClosed} →
--                    Term (lift A) (lift B) → Term Unit TypedCodeC
--
--   TypedCodeC = CodedCode × CodedCode × Code
--
-- The morphism's source / target types are recovered as TyClosed values
-- through the implicit arguments and encoded via encode-tyc; the term
-- is encoded via the existing erased encoder.
--
-- Faithfulness over ALL morphisms (including those whose source / target
-- type involves μ) follows once encode-tyc is shown faithful — that
-- proof lives in a sibling .CodedFaithful module (forthcoming).
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Models.StrongCCL3.Typed.EncodingCoded where

import Theory.Syntax.StrongCCL.CCT3 as Syn
open Syn using (Term; ⟨_,_⟩)

open import Theory.Models.StrongCCL3.Typed.Func using (TyClosed; lift)
open import Theory.Models.StrongCCL3.Typed.Coded using (CodedCode; encode-tyc)
open import Theory.Models.StrongCCL3.Encoding using (Code; encode)

------------------------------------------------------------------------
-- The coded typed carrier.
--
-- TypedCodeC = CodedCode × CodedCode × Code
--            = source-type ⊗ target-type ⊗ erased-term-encoding
------------------------------------------------------------------------

TypedCodeC : Syn.Ty
TypedCodeC = CodedCode Syn.× CodedCode Syn.× Code

------------------------------------------------------------------------
-- The coded typed encoding function.
------------------------------------------------------------------------

encode-typed-c :
  ∀ {A B : TyClosed} → Term (lift A) (lift B) → Term Syn.Unit TypedCodeC
encode-typed-c {A} {B} t =
  ⟨ encode-tyc A , ⟨ encode-tyc B , encode t ⟩ ⟩
