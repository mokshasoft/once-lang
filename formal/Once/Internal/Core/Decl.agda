-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Core.Decl — an FFI declaration's type as the Spec's
-- `DeclType`.
--
-- The checker keeps a program's signature as ground types (`ISig`); the
-- Spec's core names an external operation by a `DeclType` (`sigop c t`, typed
-- `⌜ t ⌝ᵈ`). An honest, concrete FFI type is exactly a declaration's
-- (`⌜declS⌝`), read at any number of type variables.
------------------------------------------------------------------------

module Once.Internal.Core.Decl where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_)
open import Once.Internal.Contract using (ISig)
open import Once.Internal.Name using (showCanonical)
open import Once.Spec.Grade using (mk-kind; pure; act; eff; Zero; One; Many)
open import Once.Spec.Type using (Type; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)
import Once.Spec.Signature as S
open S using (BTy; DeclType; constant; value; operation; ⌜_⌝; ⌜_⌝ᵈ; Signature; _∶_)
open import Once.Internal.Type using (wk₀)
open import Once.Internal.Type.WellFormed using (IsBaseType; IsConcrete; con-base; con-fun;
  base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum)
open import Once.Internal.Type.Honest using (HonestFFI)

-- A base type's code (the rest never reaches a declaration).
toB : Type → BTy
toB Unit         = S.unit
toB Void         = S.void
toB Int          = S.int
toB Float        = S.float
toB (A * B)      = toB A S.* toB B
toB (A + B)      = toB A S.+ toB B
toB (_ ⇒[ _ ] _) = S.unit
toB (μ _)        = S.unit
toB (ν _ _)      = S.unit
toB (var ())

-- A declaration's type: a pure arrow is a function, an acting one an
-- operation, anything else a constant.
declS : Type → DeclType
declS (A ⇒[ mk-kind q pure ] B) = value (toB A) q (toB B)
declS (A ⇒[ mk-kind q act ] B)  = operation (toB A) q (toB B)
declS (A ⇒[ mk-kind q eff ] B)  = operation (toB A) q (toB B)
declS Unit                       = constant (toB Unit)
declS Void                       = constant (toB Void)
declS Int                        = constant (toB Int)
declS Float                      = constant (toB Float)
declS (A * B)                    = constant (toB (A * B))
declS (A + B)                    = constant (toB (A + B))
declS (μ F)                      = constant (toB (μ F))
declS (ν F φ)                    = constant (toB (ν F φ))
declS (var ())

⌜toB⌝ : ∀ {m} {A : Type} → IsBaseType A → ⌜ toB A ⌝ ≡ wk₀ {m} A
⌜toB⌝ base-Unit        = refl
⌜toB⌝ base-Void        = refl
⌜toB⌝ base-Int         = refl
⌜toB⌝ base-Float       = refl
⌜toB⌝ (base-Prod a b)  = cong₂ _*_ (⌜toB⌝ a) (⌜toB⌝ b)
⌜toB⌝ (base-Sum a b)   = cong₂ _+_ (⌜toB⌝ a) (⌜toB⌝ b)

-- An honest, concrete FFI type is its declaration's.
⌜declS⌝ : ∀ {m} {T : Type} → IsConcrete T → HonestFFI T → ⌜ declS T ⌝ᵈ ≡ wk₀ {m} T
⌜declS⌝ {T = A ⇒[ mk-kind q pure ] B} (con-fun a b) h = cong₂ (λ x y → x ⇒[ mk-kind q pure ] y) (⌜toB⌝ a) (⌜toB⌝ b)
⌜declS⌝ {T = A ⇒[ mk-kind Many act ] B} (con-fun a b) h = cong₂ (λ x y → x ⇒[ mk-kind Many act ] y) (⌜toB⌝ a) (⌜toB⌝ b)
⌜declS⌝ {T = A ⇒[ mk-kind Zero act ] B} (con-fun a b) ()
⌜declS⌝ {T = A ⇒[ mk-kind One act ] B} (con-fun a b) ()
⌜declS⌝ {T = A ⇒[ mk-kind q eff ] B} (con-fun a b) ()
⌜declS⌝ (con-base base-Unit) ()
⌜declS⌝ (con-base base-Void) ()
⌜declS⌝ (con-base base-Int) h = refl
⌜declS⌝ (con-base base-Float) h = refl
⌜declS⌝ (con-base b@(base-Prod _ _)) h = ⌜toB⌝ b
⌜declS⌝ (con-base b@(base-Sum _ _)) h = ⌜toB⌝ b

------------------------------------------------------------------------
-- The other way: a Spec signature as the checker's (`ISig`)
------------------------------------------------------------------------

toISig : Signature → ISig
toISig []              = []
toISig ((c ∶ t) ∷ Σ′) = (showCanonical c , ⌜ t ⌝ᵈ) ∷ toISig Σ′

∈-toISig : ∀ {Σ c t} → (c ∶ t) ∈ Σ → (showCanonical c , ⌜ t ⌝ᵈ) ∈ toISig Σ
∈-toISig {(c′ ∶ t′) ∷ _} (here refl) = here refl
∈-toISig {_ ∷ _}         (there m)   = there (∈-toISig m)

-- A declaration's type is concrete.
⌜⌝-base : ∀ b → IsBaseType ⌜ b ⌝
⌜⌝-base S.unit    = base-Unit
⌜⌝-base S.void    = base-Void
⌜⌝-base S.int     = base-Int
⌜⌝-base S.float   = base-Float
⌜⌝-base (a S.* b) = base-Prod (⌜⌝-base a) (⌜⌝-base b)
⌜⌝-base (a S.+ b) = base-Sum (⌜⌝-base a) (⌜⌝-base b)

⌜⌝ᵈ-concrete : ∀ t → IsConcrete ⌜ t ⌝ᵈ
⌜⌝ᵈ-concrete (constant b)      = con-base (⌜⌝-base b)
⌜⌝ᵈ-concrete (value a q b)     = con-fun (⌜⌝-base a) (⌜⌝-base b)
⌜⌝ᵈ-concrete (operation a q b) = con-fun (⌜⌝-base a) (⌜⌝-base b)
