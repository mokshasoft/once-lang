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
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Type

-- Plan 0.113 B2: HALTING and EMITTING are properties UP TO ISOMORPHISM — a codomain
-- that is EMPTY halts (initial object), one that is a SINGLETON owes no answer
-- (terminal object). The contract (`Spec.Contract.contract-eff`) and every layer
-- after it decide by the syntactic `B ≡ Void` / `B ≡ Unit`. That is correct only on
-- a SKELETON: an honest declaration writes an empty codomain as `Void` and a
-- singleton one as `Unit`. Otherwise `Void * Int` would be an "answers" contract
-- whose answer type is empty — no implementation of the signature exists, and the
-- correctness theorem is vacuous for the program.
--
-- Over the first-order codomains an FFI signature can have (`IsConcrete`: the ABI),
-- both are structural. Anything else (an arrow inside data, `μ`, `ν`, `rigid`) is
-- not first-order data: `⊥`, i.e. not an honest codomain.
NotEmpty : Type → Set
NotEmpty Unit    = ⊤
NotEmpty Void    = ⊥
NotEmpty Int     = ⊤
NotEmpty Float   = ⊤
NotEmpty (A * B) = NotEmpty A × NotEmpty B
NotEmpty (A + B) = NotEmpty A ⊎ NotEmpty B
NotEmpty (_ ⇒[ _ ] _) = ⊥
NotEmpty (μ-type _)   = ⊥
NotEmpty (ν-type _ _) = ⊥
NotEmpty (rigid _ _)  = ⊥

-- `|A + B| ≠ 1` iff both summands are inhabited, or neither is a singleton.
NotSingleton : Type → Set
NotSingleton Unit    = ⊥
NotSingleton Void    = ⊤
NotSingleton Int     = ⊤
NotSingleton Float   = ⊤
NotSingleton (A * B) = NotSingleton A ⊎ NotSingleton B
NotSingleton (A + B) = (NotEmpty A × NotEmpty B) ⊎ (NotSingleton A × NotSingleton B)
NotSingleton (_ ⇒[ _ ] _) = ⊥
NotSingleton (μ-type _)   = ⊥
NotSingleton (ν-type _ _) = ⊥
NotSingleton (rigid _ _)  = ⊥

-- A data codomain at grade `π` (not `Unit`/`Void`, not an arrow): a pure one must be
-- inhabited (a value contract); an effectful one must be neither empty nor a
-- singleton — those ARE `Void` / `Unit` and must be written so.
DataCod : Purity → Type → Set
DataCod pure B = NotEmpty B
DataCod eff  B = NotEmpty B × NotSingleton B

-- The codomain `B` of an arrow at grade `π`.
HonestCod : Purity → Type → Set
HonestCod π Unit                       = π ≡ eff
HonestCod π Void                       = π ≡ eff
HonestCod π (A ⇒[ mk-kind q π′ ] B)    = HonestCod π′ B
HonestCod π (A * B)                    = DataCod π (A * B)
HonestCod π (A + B)                    = DataCod π (A + B)
HonestCod π (μ-type _)                 = ⊥   -- B2: not first-order data
HonestCod π (ν-type _ _)               = ⊥
HonestCod π Int                        = ⊤
HonestCod π Float                      = ⊤
HonestCod π (rigid _ _)                = ⊥   -- D243: an FFI signature is ground

-- A constant is a pure value: it must be inhabited.
HonestFFI : Type → Set
HonestFFI Unit                    = ⊥
HonestFFI Void                    = ⊥
HonestFFI (A ⇒[ mk-kind q π ] B)  = HonestCod π B
HonestFFI (A * B)                 = NotEmpty (A * B)
HonestFFI (A + B)                 = NotEmpty (A + B)
HonestFFI (μ-type _)              = ⊥
HonestFFI (ν-type _ _)            = ⊥
HonestFFI Int                     = ⊤
HonestFFI Float                   = ⊤
HonestFFI (rigid _ _)             = ⊥   -- D243: an FFI signature is ground

------------------------------------------------------------------------
-- Deciders (implementation; the elaborator checks a reference with them)
------------------------------------------------------------------------

isEff? : (π : Purity) → Maybe (π ≡ eff)
isEff? pure = nothing
isEff? eff  = just refl

-- Two witnesses, or the first that exists (no `with`: proofs follow by cases).
both : ∀ {A B : Set} → Maybe A → Maybe B → Maybe (A × B)
both (just a) (just b) = just (a , b)
both (just _) nothing  = nothing
both nothing  _        = nothing

either : ∀ {A B : Set} → Maybe A → Maybe B → Maybe (A ⊎ B)
either (just a) _        = just (inj₁ a)
either nothing  (just b) = just (inj₂ b)
either nothing  nothing  = nothing

notEmpty? : (T : Type) → Maybe (NotEmpty T)
notEmpty? Unit         = just tt
notEmpty? Void         = nothing
notEmpty? Int          = just tt
notEmpty? Float        = just tt
notEmpty? (A * B)      = both (notEmpty? A) (notEmpty? B)
notEmpty? (A + B)      = either (notEmpty? A) (notEmpty? B)
notEmpty? (_ ⇒[ _ ] _) = nothing
notEmpty? (μ-type _)   = nothing
notEmpty? (ν-type _ _) = nothing
notEmpty? (rigid _ _)  = nothing

notSingleton? : (T : Type) → Maybe (NotSingleton T)
notSingleton? Unit         = nothing
notSingleton? Void         = just tt
notSingleton? Int          = just tt
notSingleton? Float        = just tt
notSingleton? (A * B)      = either (notSingleton? A) (notSingleton? B)
notSingleton? (A + B)      = either (both (notEmpty? A) (notEmpty? B)) (both (notSingleton? A) (notSingleton? B))
notSingleton? (_ ⇒[ _ ] _) = nothing
notSingleton? (μ-type _)   = nothing
notSingleton? (ν-type _ _) = nothing
notSingleton? (rigid _ _)  = nothing

dataCod? : (π : Purity) (B : Type) → Maybe (DataCod π B)
dataCod? pure B = notEmpty? B
dataCod? eff  B = both (notEmpty? B) (notSingleton? B)

honestCod? : (π : Purity) (B : Type) → Maybe (HonestCod π B)
honestCod? π Unit                     = isEff? π
honestCod? π Void                     = isEff? π
honestCod? π (A ⇒[ mk-kind q π′ ] B)  = honestCod? π′ B
honestCod? π (A * B)                  = dataCod? π (A * B)
honestCod? π (A + B)                  = dataCod? π (A + B)
honestCod? π (μ-type _)               = nothing
honestCod? π (ν-type _ _)             = nothing
honestCod? π Int                      = just tt
honestCod? π Float                    = just tt
honestCod? π (rigid _ _)              = nothing

honest? : (T : Type) → Maybe (HonestFFI T)
honest? Unit                    = nothing
honest? Void                    = nothing
honest? (A ⇒[ mk-kind q π ] B)  = honestCod? π B
honest? (A * B)                 = notEmpty? (A * B)
honest? (A + B)                 = notEmpty? (A + B)
honest? (μ-type _)              = nothing
honest? (ν-type _ _)            = nothing
honest? Int                     = just tt
honest? Float                   = just tt
honest? (rigid _ _)             = nothing

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

honestCod?-complete : ∀ (π : Purity) (B : Type) → HonestCod π B → ∃[ h ] honestCod? π B ≡ just h
honestCod?-complete π Unit                    refl = refl , refl
honestCod?-complete π Void                    refl = refl , refl
honestCod?-complete π (A ⇒[ mk-kind q π′ ] B) h    = honestCod?-complete π′ B h
honestCod?-complete π (A * B)                 h    = dataCod?-complete π (A * B) h
honestCod?-complete π (A + B)                 h    = dataCod?-complete π (A + B) h
honestCod?-complete π (μ-type _)              ()
honestCod?-complete π (ν-type _ _)            ()
honestCod?-complete π Int                     tt   = tt , refl
honestCod?-complete π Float                   tt   = tt , refl
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
