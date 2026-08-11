------------------------------------------------------------------------
-- Theory.Models.StrongCCL3.Typed.Encoding
--
-- The typed encoding for StrongCCL CCT3 — Layer A of the two-layer
-- design. This is the encoding a verified Once compiler manipulates as
-- its IR; it pairs the encoded source / target types with the erased
-- term encoding from Theory.Models.StrongCCL3.Encoding.
--
-- DESIGN:
--
--   encode-typed : ∀ {A B} → Term A B → Term Unit (TyCode × TyCode × Code)
--   encode-typed {A} {B} t = ⟨ encode-ty A , ⟨ encode-ty B , encode t ⟩ ⟩
--
--   The carrier TyCode × TyCode × Code is uniform (no Ty-indexing on
--   the carrier). The type information lives as data, encoded into a
--   pair of TyCodes preceding the term encoding.
--
-- WHY THIS LIFTS FAITHFULNESS TO ALL MORPHISMS:
--
--   The erased encoding (Theory.Models.StrongCCL3.Encoding) is
--   faithful only over same-type morphisms — encode-faithful states
--
--     encode t₁ ≡ encode t₂  ⟹  t₁ ≡ t₂        (assuming A₁ = A₂, B₁ = B₂).
--
--   Pairing with (encode-ty A , encode-ty B) recovers the missing type
--   information. Combined with TyCode-faithfulness (encode-ty injective
--   on the μ-free fragment, opaque on μ-types), the typed encoding is
--   faithful over ALL morphisms (modulo the μ-opacity limitation).
--
-- LIMITATIONS (Phase 1, inherited from TyEncoding):
--   - μ-types encode opaquely: encode-typed cannot distinguish
--     two morphisms differing only in their μ-carrier.
--   - F is not stored for `cata` / `fmap`. F is recoverable from the
--     source type only up to the same μ-opaqueness.
--
-- Both lift in Phase 2 once a Func universe of SPF codes is introduced.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Models.StrongCCL3.Typed.Encoding where

import Theory.Syntax.StrongCCL.CCT3 as Syn
open Syn using (Ty; Unit; _×_; Term; ⟨_,_⟩)

open import Theory.Models.StrongCCL3.Typed.TyEncoding using (TyCode; encode-ty)
open import Theory.Models.StrongCCL3.Encoding using (Code; encode)

------------------------------------------------------------------------
-- The typed carrier.
--
-- TypedCode = TyCode × TyCode × Code
--           = source-type ⊗ target-type ⊗ erased-term-encoding
--
-- Note: _×_ is right-associative, so this parses as
--       TyCode × (TyCode × Code).
------------------------------------------------------------------------

TypedCode : Ty
TypedCode = TyCode × TyCode × Code

------------------------------------------------------------------------
-- The typed encoding function.
--
-- For t : Term A B,
--   encode-typed t = ⟨ encode-ty A , ⟨ encode-ty B , encode t ⟩ ⟩.
--
-- Both A and B are recoverable as implicit arguments at the call site.
------------------------------------------------------------------------

encode-typed : ∀ {A B} → Term A B → Term Unit TypedCode
encode-typed {A} {B} t =
  ⟨ encode-ty A , ⟨ encode-ty B , encode t ⟩ ⟩
