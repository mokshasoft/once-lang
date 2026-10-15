{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Signature — the program's SIGNATURE Σ and its functor H_Σ.
--
-- A program is compiled against the declarations of the Interpretations it
-- uses (D061): each is a name with a first-order type —
--   * a CONSTANT of a base type, or a PURE arrow between base types: a value
--     the Interpretation provides;
--   * an EFFECTFUL arrow between base types: an OPERATION. Applying it is one
--     observable EVENT; the world answers it, except at an empty answer type
--     (`void`), where the program halts.
--
-- The operations define one functor,
--
--     H_Σ X = Σ (o : operation) ⟦arg o⟧ × (⟦ans o⟧ → X)
--
-- (`Layer`): one call and what to continue with from its answer. `T` and `T∞`
-- (`Spec.Effect`) are its free monad and its free completely iterative monad.
------------------------------------------------------------------------

module Once.Spec.Signature where

open import Data.Empty using (⊥)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Once.Spec.Grade using (ArrowKind; mk-kind; Quantity; Zero; One; Many; Purity; pure; act; eff⁺; eff)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Word using (Carrier)
import Once.Spec.Type as T

------------------------------------------------------------------------
-- Base types: what an operation takes and answers
------------------------------------------------------------------------

data BTy : Set where
  unit void int float : BTy
  _*_ _+_             : BTy → BTy → BTy

infixr 40 _+_
infixr 50 _*_

-- A base type is a type.
⌜_⌝ : ∀ {m} → BTy → T.Ty m
⌜ unit ⌝    = T.Unit
⌜ void ⌝    = T.Void
⌜ int ⌝     = T.Int
⌜ float ⌝   = T.Float
⌜ a * b ⌝   = ⌜ a ⌝ T.* ⌜ b ⌝
⌜ a + b ⌝   = ⌜ a ⌝ T.+ ⌜ b ⌝

-- Its values. An `Int` or a `Float` is a natural number: a word of the
-- target's width (`Spec.Word`), a bit pattern of its float format.
⟦_⟧ᵇ : BTy → Set
⟦ unit ⟧ᵇ  = ⊤
⟦ void ⟧ᵇ  = ⊥
⟦ int ⟧ᵇ   = Carrier
⟦ float ⟧ᵇ = Carrier
⟦ a * b ⟧ᵇ = ⟦ a ⟧ᵇ × ⟦ b ⟧ᵇ
⟦ a + b ⟧ᵇ = ⟦ a ⟧ᵇ ⊎ ⟦ b ⟧ᵇ

-- Inhabited.
NotEmpty : BTy → Set
NotEmpty unit    = ⊤
NotEmpty void    = ⊥
NotEmpty int     = ⊤
NotEmpty float   = ⊤
NotEmpty (a * b) = NotEmpty a × NotEmpty b
NotEmpty (a + b) = NotEmpty a ⊎ NotEmpty b

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

data DeclType : Set where
  constant : BTy → DeclType
  arrow    : BTy → ArrowKind → BTy → DeclType

record Decl : Set where
  constructor _∶_
  field
    name : CanonicalName
    type : DeclType
open Decl

Signature : Set
Signature = List Decl

-- A declaration's type.
⌜_⌝ᵈ : ∀ {m} → DeclType → T.Ty m
⌜ constant b ⌝ᵈ  = ⌜ b ⌝
⌜ arrow a k b ⌝ᵈ = ⌜ a ⌝ T.⇒[ k ] ⌜ b ⌝

-- Not a singleton: `|b| ≠ 1`.
NotSingleton : BTy → Set
NotSingleton unit    = ⊥
NotSingleton void    = ⊤
NotSingleton int     = ⊤
NotSingleton float   = ⊤
NotSingleton (a * b) = NotSingleton a ⊎ NotSingleton b
NotSingleton (a + b) = (NotEmpty a × NotEmpty b) ⊎ (NotSingleton a × NotSingleton b)

-- What an operation answers: `unit` (it emits), `void` (it halts), or data
-- that is neither empty nor a singleton — those ARE `void` and `unit` and are
-- written so.
EffCod : BTy → Set
EffCod unit    = ⊤
EffCod void    = ⊤
EffCod int     = ⊤
EffCod float   = ⊤
EffCod (a * b) = NotEmpty (a * b) × NotSingleton (a * b)
EffCod (a + b) = NotEmpty (a + b) × NotSingleton (a + b)

-- An HONEST declaration hides no effect and can be implemented: a value is
-- inhabited and is not `Unit` (a constant or pure arrow into `Unit` or `Void`
-- would be a hidden effect — it is written effectful); an operation answers
-- as `EffCod` says.
WellFormedDecl : DeclType → Set
WellFormedDecl (constant b)                 = NotEmpty b × b ≢ unit
WellFormedDecl (arrow a (mk-kind q pure) b) = NotEmpty b × b ≢ unit
WellFormedDecl (arrow a (mk-kind q act) b)  = EffCod b
WellFormedDecl (arrow a (mk-kind q eff⁺) b) = EffCod b
WellFormedDecl (arrow a (mk-kind q eff) b)  = EffCod b

data WellFormed : Signature → Set where
  []  : WellFormed Data.List.[]
  _∷_ : ∀ {d Σ} → WellFormedDecl (type d) → WellFormed Σ → WellFormed (d Data.List.∷ Σ)

------------------------------------------------------------------------
-- The operations, and the functor H_Σ
------------------------------------------------------------------------

-- An argument used zero times is not passed: the call takes `unit`.
argAt : Quantity → BTy → BTy
argAt Zero a = unit
argAt One  a = a
argAt Many a = a

data Effectful : Purity → Set where
  e-act : Effectful act
  e-g   : Effectful eff⁺
  e-eff : Effectful eff

-- An operation of Σ: one of its effectful arrows.
record Op (Σ : Signature) : Set where
  constructor op
  field
    {opName} : CanonicalName
    {dom}    : BTy
    {q}      : Quantity
    {π}      : Purity
    {ans}    : BTy
    declared : (opName ∶ arrow dom (mk-kind q π) ans) ∈ Σ
    effectful : Effectful π
open Op

arg : ∀ {Σ} → Op Σ → BTy
arg o = argAt (q o) (dom o)

-- H_Σ: one call, and what to continue with from its answer.
data Layer (Σ : Signature) (X : Set) : Set where
  call : (o : Op Σ) → ⟦ arg o ⟧ᵇ → (⟦ ans o ⟧ᵇ → X) → Layer Σ X

------------------------------------------------------------------------
-- What is observed: one call (D058, D114)
------------------------------------------------------------------------

record Event : Set where
  constructor event
  field
    ev-name : CanonicalName
    ev-arg  : BTy
    ev-val  : ⟦ ev-arg ⟧ᵇ

eventOf : ∀ {Σ} (o : Op Σ) → ⟦ arg o ⟧ᵇ → Event
eventOf o a = event (opName o) (arg o) a
