-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.HonestSound — the honesty predicates mean what they say.
--
-- Plan 0.113 B2. `Type.Honest` decides halting/emitting UP TO ISOMORPHISM on a
-- skeleton: an honest data codomain is `NotEmpty` (and, effectful, also
-- `NotSingleton`). Here the first half is a fact about the value domain: a
-- `NotEmpty` type is INHABITED — so a value or answer contract at an honest
-- codomain can be implemented, and no honest signature forces `Impl Σ` to be
-- empty (the vacuity the skeleton exists to rule out). Kept out of the Spec's
-- closure (D140: the Spec is proof-free).
------------------------------------------------------------------------

module Once.Type.HonestSound {IntRep FloatRep : Set} (i₀ : IntRep) (f₀ : FloatRep) where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Once.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; rigid)
open import Once.Type.Honest using (NotEmpty)
open import Once.Semantics.Value IntRep FloatRep using (⟦_⟧)

inhabited : (T : Type) → NotEmpty T → ⟦ T ⟧
inhabited Unit    _          = tt
inhabited Void    ()
inhabited Int     _          = i₀
inhabited Float   _          = f₀
inhabited (A * B) (a , b)    = inhabited A a , inhabited B b
inhabited (A + B) (inj₁ a)   = inj₁ (inhabited A a)
inhabited (A + B) (inj₂ b)   = inj₂ (inhabited B b)
inhabited (_ ⇒[ _ ] _) ()
inhabited (μ-type _)   ()
inhabited (ν-type _ _) ()
inhabited (rigid _ _)  ()
