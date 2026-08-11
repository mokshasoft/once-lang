------------------------------------------------------------------------
-- Theory.Models.StrongCCL3.Typed.TyEncoding
--
-- A μ-type encoding of Theory.Syntax.StrongCCL.CCT3.Ty.
--
-- This is the type-side of the two-layer encoding for StrongCCL CCT3.
-- The term-side lives in Theory.Models.StrongCCL3.Typed.Encoding and
-- pairs an (encoded source type, encoded target type) with the
-- type-erased term encoding from Theory.Models.StrongCCL3.Encoding.
--
-- DESIGN:
--
--   TyF X = Unit ⊎ Unit ⊎ Unit ⊎ (X × X) ⊎ (X × X) ⊎ (X × X)
--           tag00  tag01  tag02   tag03    tag04    tag05
--           Unit   Void   μ-op    _×_      _⊎_      _⇒_
--
--   TyCode = μ TyF
--
-- LIMITATION (Phase 1):
--   The μ-constructor is encoded as the constant tag tag02 ("μ-opaque")
--   with no payload. This means
--
--     encode-ty (μ F) = encode-ty (μ G)         for all F, G : Ty → Ty.
--
--   Lifting this requires a Func universe of SPF codes (a separate
--   datatype Func with constructors for the closure of strictly-positive
--   functors under sum/product/exponential/recursion). Phase 2 introduces
--   Func and refines tag02 from a constant to "μ ∘ encode-func".
--
--   Until then, encode-ty is faithful only on μ-free types. The two-
--   layer scaffold (this file + Typed/Encoding.agda + Typed/Forget.agda)
--   is independent of this refinement: only TyF and encode-ty change in
--   Phase 2; TermF, encode-typed, and the coherence proof are unaffected.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Models.StrongCCL3.Typed.TyEncoding where

import Theory.Syntax.StrongCCL.CCT3 as Syn
open Syn using
  ( Ty; Unit; _×_; _⇒_; Void; _⊎_; μ
  ; Term; id; _∘_; terminal; ⟨_,_⟩; inl; inr; In )

------------------------------------------------------------------------
-- TyF — type-syntax functor with 6 alternatives.
--
-- Layout (in order of inr-injection nesting):
--   00: Unit       (constant)
--   01: Void       (constant)
--   02: μ-opaque   (constant; placeholder for Func-coded μ in Phase 2)
--   03: _×_        (binary)
--   04: _⊎_        (binary)
--   05: _⇒_        (binary)
------------------------------------------------------------------------

TyF : Ty → Ty
TyF X =
  -- 3 constants
  Unit ⊎ Unit ⊎ Unit ⊎
  -- 3 binary
  (X × X) ⊎ (X × X) ⊎ (X × X)

TyCode : Ty
TyCode = μ TyF

------------------------------------------------------------------------
-- Tag helpers — Term Unit TyCode at each constructor position.
--
-- Constants: In ∘ inr^k ∘ inl ∘ terminal.
-- Binary:    In ∘ inr^k ∘ inj_lr ∘ ⟨ payload₁ , payload₂ ⟩.
------------------------------------------------------------------------

private
  ty-tag00 : Term Unit TyCode
  ty-tag00 = In ∘ inl ∘ terminal

  ty-tag01 : Term Unit TyCode
  ty-tag01 = In ∘ inr ∘ inl ∘ terminal

  ty-tag02 : Term Unit TyCode
  ty-tag02 = In ∘ inr ∘ inr ∘ inl ∘ terminal

  ty-tag03 : Term Unit TyCode → Term Unit TyCode → Term Unit TyCode
  ty-tag03 a b = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ a , b ⟩

  ty-tag04 : Term Unit TyCode → Term Unit TyCode → Term Unit TyCode
  ty-tag04 a b = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ a , b ⟩

  ty-tag05 : Term Unit TyCode → Term Unit TyCode → Term Unit TyCode
  ty-tag05 a b = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ a , b ⟩

------------------------------------------------------------------------
-- The type-encoding function.
--
-- Phase 1: μ F encodes opaquely. Phase 2 will replace ty-tag02 by a
-- payload-bearing tag carrying a Func code for F.
------------------------------------------------------------------------

encode-ty : Ty → Term Unit TyCode

encode-ty Unit    = ty-tag00
encode-ty Void    = ty-tag01
encode-ty (μ _)   = ty-tag02
encode-ty (a × b) = ty-tag03 (encode-ty a) (encode-ty b)
encode-ty (a ⊎ b) = ty-tag04 (encode-ty a) (encode-ty b)
encode-ty (a ⇒ b) = ty-tag05 (encode-ty a) (encode-ty b)
