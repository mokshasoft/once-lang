-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MeaningRelation — the FUNEXT-FREE observational logical
-- relation on the monadic value domain `⟦_⟧ᴰ` (Plan 0.58, OCP-0006).
--
-- `bridgeᵈ` (direct meaning `⟦_⟧ᵈ` ≈ SD∘realize) can't be a raw `≡` — at
-- arrow types the two sides agree only as FUNCTIONS of their argument, which
-- would need funext. Instead we relate computations observationally:
--
--   RelT A t₁ t₂  = at every budget `n`, the SAME event trace AND related values
--   RelV (A⇒B) f g = related inputs ↦ related outputs   (a Π, NOT a funext `≡`)
--   RelV (first-order A) x y = x ≡ y
--
-- The fundamental lemma (`MeaningBridge`) then shows `⟦deriv⟧ᶜ` and
-- `SD.⟦realize deriv⟧ˢ` are `RelT`-related; at `main : EffUU` applied to `tt`
-- this yields the plain `Behavior` equality `bridgeᵈ` needs — funext-free.
------------------------------------------------------------------------

open import Once.Float.Dyadic using (FloatFormat)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.MeaningRelation (fmt : FloatFormat) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.List using (_++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer;
                             _*_; _+_; _⇒[_]_; μ-type; ν-type)
open import Once.Denotation.TraceMonad using (T; projTrace; valueT; returnT; _>>=T_)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)

------------------------------------------------------------------------
-- The relation, by recursion on the type. `RelV` on values, `RelT` on
-- computations (mutual: `RelV` at arrows quantifies over `RelT` outputs).
------------------------------------------------------------------------

RelV : ∀ (A : Type) → ⟦ A ⟧ᴰ → ⟦ A ⟧ᴰ → Set
RelT : ∀ (A : Type) → T ⟦ A ⟧ᴰ → T ⟦ A ⟧ᴰ → Set

-- A computation relation: equal event traces + related values at EVERY budget.
RelT A t₁ t₂ = ∀ n → (projTrace t₁ n ≡ projTrace t₂ n)
                   × RelV A (valueT t₁ n) (valueT t₂ n)

-- First-order (pure `Val`) payloads: observational = propositional equality.
RelV Unit        _ _ = ⊤
RelV Void        ()
RelV Int         x y = x ≡ y
RelV Float       x y = x ≡ y
RelV Str         x y = x ≡ y
RelV Buffer      x y = x ≡ y
RelV (μ-type F)  x y = x ≡ y
RelV (ν-type F)  x y = x ≡ y
RelV (A * B) (a₁ , b₁) (a₂ , b₂) = RelV A a₁ a₂ × RelV B b₁ b₂
RelV (A + B) (inj₁ a₁) (inj₁ a₂) = RelV A a₁ a₂
RelV (A + B) (inj₂ b₁) (inj₂ b₂) = RelV B b₁ b₂
RelV (A + B) (inj₁ _)  (inj₂ _)  = ⊥
RelV (A + B) (inj₂ _)  (inj₁ _)  = ⊥
-- The arrow: related arguments map to related computations. This is the
-- funext-free heart — a Π over related inputs, not an equality of functions.
RelV (A ⇒[ k ] B) f g = ∀ {a b} → RelV A a b → RelT B (f a) (g b)

------------------------------------------------------------------------
-- Monad lemmas — the two combinators `⟦_⟧ᶜ`/SD are built from (`returnT`,
-- `_>>=T_`). Both hold DEFINITIONALLY from `_>>=T_`'s `++`-of-traces.
------------------------------------------------------------------------

-- `returnT` has empty trace and carries its value, so related values give
-- related pure computations.
RelT-return : ∀ {A} {x y : ⟦ A ⟧ᴰ} → RelV A x y → RelT A (returnT x) (returnT y)
RelT-return rv n = refl , rv

-- Bind preserves the relation: related computations sequenced with related
-- continuations stay related. `_>>=T_` concatenates the two traces, so the
-- trace equality is `cong₂ _++_` of the two halves.
RelT-bind : ∀ {A B} {t₁ t₂ : T ⟦ A ⟧ᴰ} {f g : ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ}
          → RelT A t₁ t₂
          → (∀ {a b} → RelV A a b → RelT B (f a) (g b))
          → RelT B (t₁ >>=T f) (t₂ >>=T g)
RelT-bind rt rk n =
  let (tr-eq  , v-rel)  = rt n
      (tr-eq' , v-rel') = rk v-rel n
  in cong₂ _++_ tr-eq tr-eq' , v-rel'
