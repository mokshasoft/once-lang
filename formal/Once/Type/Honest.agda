-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Honest — completeness of the honesty deciders
-- (`Once.Spec.Type.Honest`): an honest type is decided honest.
------------------------------------------------------------------------

module Once.Type.Honest where

open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Type.Grade
open import Once.Spec.Type
open import Once.Spec.Type.Poly
open import Once.Spec.Type.Honest

------------------------------------------------------------------------
-- Completeness of the deciders: an honest type is decided honest.
------------------------------------------------------------------------

open import Data.Product using (∃-syntax)

private
  both-c : ∀ {A B : Set} {ma : Maybe A} {mb : Maybe B}
         → ∃[ a ] ma ≡ just a → ∃[ b ] mb ≡ just b → ∃[ h ] both ma mb ≡ just h
  both-c (a , refl) (b , refl) = (a , b) , refl

  either-l : ∀ {A B : Set} {ma : Maybe A} {mb : Maybe B}
           → ∃[ a ] ma ≡ just a → ∃[ h ] either ma mb ≡ just h
  either-l (a , refl) = inj₁ a , refl

  either-r : ∀ {A B : Set} (ma : Maybe A) {mb : Maybe B}
           → ∃[ b ] mb ≡ just b → ∃[ h ] either ma mb ≡ just h
  either-r (just a) _          = inj₁ a , refl
  either-r nothing  (b , refl) = inj₂ b , refl

notEmpty?-complete : ∀ (T : Type) → NotEmpty T → ∃[ h ] notEmpty? T ≡ just h
notEmpty?-complete Unit    tt       = tt , refl
notEmpty?-complete Void    ()
notEmpty?-complete Int     tt       = tt , refl
notEmpty?-complete Float   tt       = tt , refl
notEmpty?-complete (A * B) (a , b)  = both-c (notEmpty?-complete A a) (notEmpty?-complete B b)
notEmpty?-complete (A + B) (inj₁ a) = either-l (notEmpty?-complete A a)
notEmpty?-complete (A + B) (inj₂ b) = either-r (notEmpty? A) (notEmpty?-complete B b)
notEmpty?-complete (_ ⇒[ _ ] _) ()
notEmpty?-complete (μ-type _)   ()
notEmpty?-complete (ν-type _ _) ()
notEmpty?-complete (rigid _ _)  ()

notSingleton?-complete : ∀ (T : Type) → NotSingleton T → ∃[ h ] notSingleton? T ≡ just h
notSingleton?-complete Unit    ()
notSingleton?-complete Void    tt             = tt , refl
notSingleton?-complete Int     tt             = tt , refl
notSingleton?-complete Float   tt             = tt , refl
notSingleton?-complete (A * B) (inj₁ a)       = either-l (notSingleton?-complete A a)
notSingleton?-complete (A * B) (inj₂ b)       = either-r (notSingleton? A) (notSingleton?-complete B b)
notSingleton?-complete (A + B) (inj₁ (a , b)) = either-l (both-c (notEmpty?-complete A a) (notEmpty?-complete B b))
notSingleton?-complete (A + B) (inj₂ (a , b)) =
  either-r (both (notEmpty? A) (notEmpty? B)) (both-c (notSingleton?-complete A a) (notSingleton?-complete B b))
notSingleton?-complete (_ ⇒[ _ ] _) ()
notSingleton?-complete (μ-type _)   ()
notSingleton?-complete (ν-type _ _) ()
notSingleton?-complete (rigid _ _)  ()

dataCod?-complete : ∀ (π : Purity) (B : Type) → DataCod π B → ∃[ h ] dataCod? π B ≡ just h
dataCod?-complete pure B h       = notEmpty?-complete B h
dataCod?-complete eff  B (a , b) = both-c (notEmpty?-complete B a) (notSingleton?-complete B b)
dataCod?-complete prod B ()
dataCod?-complete eff⁺ B (a , b) = both-c (notEmpty?-complete B a) (notSingleton?-complete B b)

effectful?-complete : ∀ (π : Purity) → Effectful π → ∃[ h ] effectful? π ≡ just h
effectful?-complete eff  tt = tt , refl
effectful?-complete eff⁺ tt = tt , refl

oneCall?-complete : ∀ (π : Purity) → OneCall π → ∃[ h ] oneCall? π ≡ just h
oneCall?-complete pure tt = tt , refl
oneCall?-complete eff  tt = tt , refl
oneCall?-complete prod ()
oneCall?-complete eff⁺ tt = tt , refl

honestCod?-complete : ∀ (π : Purity) (B : Type) → HonestCod π B → ∃[ h ] honestCod? π B ≡ just h
honestCod?-complete π Unit                    h    = effectful?-complete π h
honestCod?-complete π Void                    h    = effectful?-complete π h
honestCod?-complete π (A ⇒[ mk-kind q π′ ] B) h    = honestCod?-complete π′ B h
honestCod?-complete π (A * B)                 h    = dataCod?-complete π (A * B) h
honestCod?-complete π (A + B)                 h    = dataCod?-complete π (A + B) h
honestCod?-complete π (μ-type _)              ()
honestCod?-complete π (ν-type _ _)            ()
honestCod?-complete π Int                     h    = oneCall?-complete π h
honestCod?-complete π Float                   h    = oneCall?-complete π h
honestCod?-complete π (rigid _ _)             ()

honest?-complete : ∀ {T : Type} → HonestFFI T → ∃[ h ] honest? T ≡ just h
honest?-complete {Unit} ()
honest?-complete {Void} ()
honest?-complete {A ⇒[ mk-kind q π ] B} h = honestCod?-complete π B h
honest?-complete {A * B}      h  = notEmpty?-complete (A * B) h
honest?-complete {A + B}      h  = notEmpty?-complete (A + B) h
honest?-complete {μ-type _}   ()
honest?-complete {ν-type _ _} ()
honest?-complete {Int}        tt = tt , refl
honest?-complete {Float}      tt = tt , refl
honest?-complete {rigid _ _}  ()
