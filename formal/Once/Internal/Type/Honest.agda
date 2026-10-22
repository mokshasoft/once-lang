-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Type.Honest — SPEC. An FFI declaration's type does not hide an effect
-- (D231: `pure` means no side effects).
--
-- A SigOp's effect is read off its codomain (D225): returning `Unit` EMITS,
-- returning `Void` HALTS. So an FFI arrow into `Unit`/`Void` must be
-- effectful, and a bare constant of type `Unit`/`Void` — a nullary effect,
-- whose every REFERENCE would emit — is not a declaration at all: effects live
-- on arrows (D032), so it is written `Act Unit Unit`. D318 item 5: a declaration
-- is FIRST ORDER — a constant, a pure function, or an operation declared at
-- `Act` (used at `Eff` by subtyping); an `Eff` or a curried declaration is not.
------------------------------------------------------------------------

module Once.Internal.Type.Honest where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Spec.Type using (μ; ν)
open import Once.Spec.Type using (var; Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Internal.Type.Poly

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
NotEmpty (μ _)   = ⊥
NotEmpty (ν _ _) = ⊥
NotEmpty (var ())

-- `|A + B| ≠ 1` iff both summands are inhabited, or neither is a singleton.
NotSingleton : Type → Set
NotSingleton Unit    = ⊥
NotSingleton Void    = ⊤
NotSingleton Int     = ⊤
NotSingleton Float   = ⊤
NotSingleton (A * B) = NotSingleton A ⊎ NotSingleton B
NotSingleton (A + B) = (NotEmpty A × NotEmpty B) ⊎ (NotSingleton A × NotSingleton B)
NotSingleton (_ ⇒[ _ ] _) = ⊥
NotSingleton (μ _)   = ⊥
NotSingleton (ν _ _) = ⊥
NotSingleton (var ())

-- A data codomain at grade `π` (not `Unit`/`Void`, not an arrow): a pure one must be
-- inhabited (a value contract); an effectful one must be neither empty nor a
-- singleton — those ARE `Void` / `Unit` and must be written so.
DataCod : Purity → Type → Set
DataCod pure B = NotEmpty B
DataCod eff  B = NotEmpty B × NotSingleton B
DataCod act  B = NotEmpty B × NotSingleton B

-- An effectful grade of one call: the codomain may be `Unit` (it emits) or
-- `Void` (it halts). A foreign operation is ONE call at every effectful
-- grade: at `act` a one-node tree of `T` (D313), at `eff` its embedding into
-- `T∞` (D317).
Effectful : Purity → Set
Effectful eff  = ⊤
Effectful act  = ⊤
Effectful pure = ⊥

-- The codomain `B` of an arrow at grade `π`.
HonestCod : Purity → Type → Set
HonestCod π Unit                       = Effectful π
HonestCod π Void                       = Effectful π
HonestCod π (_ ⇒[ _ ] _)               = ⊥   -- D318: first order
HonestCod π (A * B)                    = DataCod π (A * B)
HonestCod π (A + B)                    = DataCod π (A + B)
HonestCod π (μ _)                 = ⊥   -- B2: not first-order data
HonestCod π (ν _ _)               = ⊥
HonestCod π Int                        = ⊤
HonestCod π Float                      = ⊤
HonestCod π (var ())

-- A constant is a pure value: it must be inhabited.
HonestFFI : Type → Set
HonestFFI Unit                    = ⊥
HonestFFI Void                    = ⊥
HonestFFI (A ⇒[ mk-kind q    pure ] B) = HonestCod pure B
HonestFFI (A ⇒[ mk-kind Many act  ] B) = HonestCod act B   -- D318: an operation, at `Act`
HonestFFI (A ⇒[ mk-kind Zero act  ] B) = ⊥
HonestFFI (A ⇒[ mk-kind One  act  ] B) = ⊥
HonestFFI (A ⇒[ mk-kind q    eff  ] B) = ⊥
HonestFFI (A * B)                 = NotEmpty (A * B)
HonestFFI (A + B)                 = NotEmpty (A + B)
HonestFFI (μ _)              = ⊥
HonestFFI (ν _ _)            = ⊥
HonestFFI Int                     = ⊤
HonestFFI Float                   = ⊤
HonestFFI (var ())

------------------------------------------------------------------------
-- Deciders (implementation; the elaborator checks a reference with them)
------------------------------------------------------------------------

isEff? : (π : Purity) → Maybe (π ≡ eff)
isEff? pure = nothing
isEff? eff  = just refl
isEff? act  = nothing

effectful? : (π : Purity) → Maybe (Effectful π)
effectful? eff  = just tt
effectful? act  = just tt
effectful? pure = nothing

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
notEmpty? (μ _)   = nothing
notEmpty? (ν _ _) = nothing
notEmpty? (var ())

notSingleton? : (T : Type) → Maybe (NotSingleton T)
notSingleton? Unit         = nothing
notSingleton? Void         = just tt
notSingleton? Int          = just tt
notSingleton? Float        = just tt
notSingleton? (A * B)      = either (notSingleton? A) (notSingleton? B)
notSingleton? (A + B)      = either (both (notEmpty? A) (notEmpty? B)) (both (notSingleton? A) (notSingleton? B))
notSingleton? (_ ⇒[ _ ] _) = nothing
notSingleton? (μ _)   = nothing
notSingleton? (ν _ _) = nothing
notSingleton? (var ())

dataCod? : (π : Purity) (B : Type) → Maybe (DataCod π B)
dataCod? pure B = notEmpty? B
dataCod? eff  B = both (notEmpty? B) (notSingleton? B)
dataCod? act  B = both (notEmpty? B) (notSingleton? B)

honestCod? : (π : Purity) (B : Type) → Maybe (HonestCod π B)
honestCod? π Unit                     = effectful? π
honestCod? π Void                     = effectful? π
honestCod? π (_ ⇒[ _ ] _)             = nothing
honestCod? π (A * B)                  = dataCod? π (A * B)
honestCod? π (A + B)                  = dataCod? π (A + B)
honestCod? π (μ _)               = nothing
honestCod? π (ν _ _)             = nothing
honestCod? π Int                      = just tt
honestCod? π Float                    = just tt
honestCod? π (var ())

honest? : (T : Type) → Maybe (HonestFFI T)
honest? Unit                    = nothing
honest? Void                    = nothing
honest? (A ⇒[ mk-kind q    pure ] B) = honestCod? pure B
honest? (A ⇒[ mk-kind Many act  ] B) = honestCod? act B
honest? (A ⇒[ mk-kind Zero act  ] B) = nothing
honest? (A ⇒[ mk-kind One  act  ] B) = nothing
honest? (A ⇒[ mk-kind q    eff  ] B) = nothing
honest? (A * B)                 = notEmpty? (A * B)
honest? (A + B)                 = notEmpty? (A + B)
honest? (μ _)              = nothing
honest? (ν _ _)            = nothing
honest? Int                     = just tt
honest? Float                   = just tt
honest? (var ())

