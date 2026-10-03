-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Honest — an FFI declaration's type does not hide an effect
-- (D231: `pure` means no side effects).
--
-- A SigOp's effect is read off its codomain (D225): returning `Unit` EMITS,
-- returning `Void` HALTS. So an FFI arrow into `Unit`/`Void` must be
-- effectful, and a bare constant of type `Unit`/`Void` — a nullary effect,
-- whose every REFERENCE would emit — is not a declaration at all: effects live
-- on arrows (D032), so it is written `Eff Unit Unit`. A curried declaration is
-- honest when its innermost Unit/Void-returning arrow is.
------------------------------------------------------------------------

module Once.Type.Honest where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Type

-- The codomain `B` of an arrow at grade `π`.
HonestCod : Purity → Type → Set
HonestCod π Unit                       = π ≡ eff
HonestCod π Void                       = π ≡ eff
HonestCod π (A ⇒[ mk-kind q π′ ] B)    = HonestCod π′ B
HonestCod π (_ * _)                    = ⊤
HonestCod π (_ + _)                    = ⊤
HonestCod π (μ-type _)                 = ⊤
HonestCod π (ν-type _ _)                 = ⊤
HonestCod π Int                        = ⊤
HonestCod π Float                      = ⊤
HonestCod π (rigid _ _)               = ⊥   -- D243: an FFI signature is ground

HonestFFI : Type → Set
HonestFFI Unit                    = ⊥
HonestFFI Void                    = ⊥
HonestFFI (A ⇒[ mk-kind q π ] B)  = HonestCod π B
HonestFFI (_ * _)                 = ⊤
HonestFFI (_ + _)                 = ⊤
HonestFFI (μ-type _)              = ⊤
HonestFFI (ν-type _ _)              = ⊤
HonestFFI Int                     = ⊤
HonestFFI Float                   = ⊤
HonestFFI (rigid _ _)             = ⊥   -- D243: an FFI signature is ground

------------------------------------------------------------------------
-- Deciders (implementation; the elaborator checks a reference with them)
------------------------------------------------------------------------

isEff? : (π : Purity) → Maybe (π ≡ eff)
isEff? pure = nothing
isEff? eff  = just refl

honestCod? : (π : Purity) (B : Type) → Maybe (HonestCod π B)
honestCod? π Unit                     = isEff? π
honestCod? π Void                     = isEff? π
honestCod? π (A ⇒[ mk-kind q π′ ] B)  = honestCod? π′ B
honestCod? π (_ * _)                  = just tt
honestCod? π (_ + _)                  = just tt
honestCod? π (μ-type _)               = just tt
honestCod? π (ν-type _ _)               = just tt
honestCod? π Int                      = just tt
honestCod? π Float                    = just tt
honestCod? π (rigid _ _)              = nothing

honest? : (T : Type) → Maybe (HonestFFI T)
honest? Unit                    = nothing
honest? Void                    = nothing
honest? (A ⇒[ mk-kind q π ] B)  = honestCod? π B
honest? (_ * _)                 = just tt
honest? (_ + _)                 = just tt
honest? (μ-type _)              = just tt
honest? (ν-type _ _)              = just tt
honest? Int                     = just tt
honest? Float                   = just tt
honest? (rigid _ _)             = nothing

------------------------------------------------------------------------
-- Completeness of the deciders: an honest type is decided honest.
------------------------------------------------------------------------

open import Data.Product using (∃-syntax; _,_)

honestCod?-complete : ∀ (π : Purity) (B : Type) → HonestCod π B → ∃[ h ] honestCod? π B ≡ just h
honestCod?-complete π Unit                    refl = refl , refl
honestCod?-complete π Void                    refl = refl , refl
honestCod?-complete π (A ⇒[ mk-kind q π′ ] B) h    = honestCod?-complete π′ B h
honestCod?-complete π (_ * _)                 tt   = tt , refl
honestCod?-complete π (_ + _)                 tt   = tt , refl
honestCod?-complete π (μ-type _)              tt   = tt , refl
honestCod?-complete π (ν-type _ _)              tt   = tt , refl
honestCod?-complete π Int                     tt   = tt , refl
honestCod?-complete π Float                   tt   = tt , refl
honestCod?-complete π (rigid _ _)         ()

honest?-complete : ∀ {T : Type} → HonestFFI T → ∃[ h ] honest? T ≡ just h
honest?-complete {Unit} ()
honest?-complete {Void} ()
honest?-complete {A ⇒[ mk-kind q π ] B} h = honestCod?-complete π B h
honest?-complete {_ * _}      tt = tt , refl
honest?-complete {_ + _}      tt = tt , refl
honest?-complete {μ-type _}   tt = tt , refl
honest?-complete {ν-type _ _}   tt = tt , refl
honest?-complete {Int}        tt = tt , refl
honest?-complete {Float}      tt = tt , refl
honest?-complete {rigid _ _}  ()
