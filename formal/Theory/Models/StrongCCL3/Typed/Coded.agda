------------------------------------------------------------------------
-- Theory.Models.StrongCCL3.Typed.Coded
--
-- Object-level encoding of the Func / TyClosed universes from
-- Theory.Models.StrongCCL3.Typed.Func into the StrongCCL CCT3 syntax.
--
-- DESIGN — single combined carrier:
--
--   CodedF X is a 10-alternative sum, with the first 6 tags representing
--   TyClosed constructors and the next 4 representing Func constructors:
--
--     00: Unit  01: Void  02: Mu(X)  03: ×(X×X)  04: ⊎(X×X)  05: ⇒(X×X)
--     06: K(X)  07: Id    08: ⊕(X×X) 09: ⊗(X×X)
--
--   CodedCode = μ CodedF.   encode-tyc and encode-func both target
--   Term Unit CodedCode; the tag distinguishes which universe each
--   value comes from. The cross-references (TyClosed.Mu carries a Func;
--   Func.K carries a TyClosed) are honored by placing the encoded
--   payload at the recursive X position with the *opposite-universe*
--   tag at the top.
--
-- WHY ONE CARRIER:
--   Two separate μ-types whose functors mutually reference each other's
--   carriers (TyClosedF mentions FuncCode, FuncF mentions TyClosedCode)
--   trip Agda's termination check at the type level. Fusing into one
--   μ-type sidesteps that without giving up structural fidelity:
--   encoders are still injective because their tag ranges are disjoint.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Models.StrongCCL3.Typed.Coded where

import Theory.Syntax.StrongCCL.CCT3 as Syn
open Syn using
  ( Term; _∘_; terminal; ⟨_,_⟩; inl; inr; In )

open import Theory.Models.StrongCCL3.Typed.Func
  using (TyClosed; Func)
import Theory.Models.StrongCCL3.Typed.Func as F

------------------------------------------------------------------------
-- The combined functor and its carrier.
------------------------------------------------------------------------

CodedF : Syn.Ty → Syn.Ty
CodedF X =
  -- TyClosed tags (00–05)
  Syn.Unit Syn.⊎ Syn.Unit Syn.⊎ X Syn.⊎
  (X Syn.× X) Syn.⊎ (X Syn.× X) Syn.⊎ (X Syn.× X) Syn.⊎
  -- Func tags (06–09)
  X Syn.⊎ Syn.Unit Syn.⊎ (X Syn.× X) Syn.⊎ (X Syn.× X)

CodedCode : Syn.Ty
CodedCode = Syn.μ CodedF

------------------------------------------------------------------------
-- Tag helpers.
--
-- Constants:  In ∘ inr^k ∘ inl ∘ terminal
-- Unary:      In ∘ inr^k ∘ inl ∘ payload
-- Binary:     In ∘ inr^k ∘ inj_lr ∘ ⟨ p , q ⟩
------------------------------------------------------------------------

private

  -- TyClosed-side tags (00–05)

  c-tag00 : Term Syn.Unit CodedCode
  c-tag00 = In ∘ inl ∘ terminal

  c-tag01 : Term Syn.Unit CodedCode
  c-tag01 = In ∘ inr ∘ inl ∘ terminal

  c-tag02 : Term Syn.Unit CodedCode → Term Syn.Unit CodedCode
  c-tag02 e = In ∘ inr ∘ inr ∘ inl ∘ e

  c-tag03 :
    Term Syn.Unit CodedCode → Term Syn.Unit CodedCode →
    Term Syn.Unit CodedCode
  c-tag03 a b = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ a , b ⟩

  c-tag04 :
    Term Syn.Unit CodedCode → Term Syn.Unit CodedCode →
    Term Syn.Unit CodedCode
  c-tag04 a b = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ a , b ⟩

  c-tag05 :
    Term Syn.Unit CodedCode → Term Syn.Unit CodedCode →
    Term Syn.Unit CodedCode
  c-tag05 a b = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ a , b ⟩

  -- Func-side tags (06–09)

  c-tag06 : Term Syn.Unit CodedCode → Term Syn.Unit CodedCode
  c-tag06 e = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ e

  c-tag07 : Term Syn.Unit CodedCode
  c-tag07 = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ terminal

  c-tag08 :
    Term Syn.Unit CodedCode → Term Syn.Unit CodedCode →
    Term Syn.Unit CodedCode
  c-tag08 a b =
    In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ a , b ⟩

  c-tag09 :
    Term Syn.Unit CodedCode → Term Syn.Unit CodedCode →
    Term Syn.Unit CodedCode
  c-tag09 a b =
    In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ a , b ⟩

------------------------------------------------------------------------
-- The mutually-recursive encoders.
------------------------------------------------------------------------

mutual

  encode-tyc : TyClosed → Term Syn.Unit CodedCode
  encode-tyc F.Unit       = c-tag00
  encode-tyc F.Void       = c-tag01
  encode-tyc (F.Mu φ)     = c-tag02 (encode-func φ)
  encode-tyc (a F.× b)    = c-tag03 (encode-tyc a) (encode-tyc b)
  encode-tyc (a F.⊎ b)    = c-tag04 (encode-tyc a) (encode-tyc b)
  encode-tyc (a F.⇒ b)    = c-tag05 (encode-tyc a) (encode-tyc b)

  encode-func : Func → Term Syn.Unit CodedCode
  encode-func (F.K T)     = c-tag06 (encode-tyc T)
  encode-func F.Id        = c-tag07
  encode-func (φ F.⊕ ψ)   = c-tag08 (encode-func φ) (encode-func ψ)
  encode-func (φ F.⊗ ψ)   = c-tag09 (encode-func φ) (encode-func ψ)
