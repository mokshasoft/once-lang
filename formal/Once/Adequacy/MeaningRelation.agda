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

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.MeaningRelation (fmt : TargetNum) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _∸_)
open import Data.List using (_++_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; subst)

open import Once.Type using (Type; Unit; Void; Int; Float;
                             _*_; _+_; _⇒[_]_; μ-type; ν-type;
                             mk-kind; Zero; One; Many)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; RelT′; rel-ret; RelT′-bind)
open import Once.Res using (Res; stopped; returns; Res-rel; rel-stopped; rel-returns)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.ValueDomainLaws using (_∼ᵈ_)

------------------------------------------------------------------------
-- The relation, by recursion on the type. `RelV` on values, `RelT` on
-- computations (mutual: `RelV` at arrows quantifies over `RelT` outputs).
------------------------------------------------------------------------

RelV : ∀ (A : Type) → ⟦ A ⟧ᴰ → ⟦ A ⟧ᴰ → Set
RelT : ∀ (A : Type) → T ⟦ A ⟧ᴰ → T ⟦ A ⟧ᴰ → Set

-- A computation relation (plan 0.105): related TREES — the same calls with
-- the same arguments, continuing relatedly at every answer, halting alike, and
-- returning related values (`RelT′`). The old budget-indexed form (equal trace
-- prefixes at every budget, related results) is its observational
-- consequence (`RelT′-events`, `RelT′-result`).
RelT A t₁ t₂ = RelT′ (RelV A) t₁ t₂

-- First-order (pure `Val`) payloads: observational = propositional equality.
RelV Unit        _ _ = ⊤
RelV Void        ()
RelV Int         x y = x ≡ y
RelV Float       x y = x ≡ y
RelV (μ-type F)  x y = x ≡ y
-- SPIKE (4th ν defect): the observational relation at a COINDUCTIVE type is
-- BISIMILARITY, not propositional equality. `anaᵈ-∼` proves this one directly
-- and coinductively; it is only the conversion to `≡` that needs the
-- `bisimᵈ-to-eq` axiom.
RelV (ν-type F _)  x y = x ∼ᵈ y
RelV (A * B) (a₁ , b₁) (a₂ , b₂) = RelV A a₁ a₂ × RelV B b₁ b₂
RelV (A + B) (inj₁ a₁) (inj₁ a₂) = RelV A a₁ a₂
RelV (A + B) (inj₂ b₁) (inj₂ b₂) = RelV B b₁ b₂
RelV (A + B) (inj₁ _)  (inj₂ _)  = ⊥
RelV (A + B) (inj₂ _)  (inj₁ _)  = ⊥
-- The arrow: related arguments map to related computations. This is the
-- funext-free heart — a Π over related inputs, not an equality of functions.
--
-- D143: split on the quantity. At `Zero` the meaning takes NO argument (its
-- domain is `⊤`), so relatedness is just relatedness of the two thunks' bodies
-- — there is no input to quantify over.
RelV (A ⇒[ mk-kind Zero π ] B) f g = RelT B (f tt) (g tt)
RelV (A ⇒[ mk-kind One  π ] B) f g = ∀ {a b} → RelV A a b → RelT B (f a) (g b)
RelV (A ⇒[ mk-kind Many π ] B) f g = ∀ {a b} → RelV A a b → RelT B (f a) (g b)

------------------------------------------------------------------------
-- Monad lemmas — the two combinators `⟦_⟧ᶜ`/SD are built from (`returnT`,
-- `_>>=T_`). Both hold DEFINITIONALLY from `_>>=T_`'s `++`-of-traces.
------------------------------------------------------------------------

-- `returnT` has empty trace and carries its value, so related values give
-- related pure computations.
RelT-return : ∀ {A} {x y : ⟦ A ⟧ᴰ} → RelV A x y → RelT A (returnT x) (returnT y)
RelT-return rv = rel-ret rv

-- Bind preserves the relation: related computations sequenced with related
-- continuations stay related — the tree relation's own bind law.
RelT-bind : ∀ {A B} {t₁ t₂ : T ⟦ A ⟧ᴰ} {f g : ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ}
          → RelT A t₁ t₂
          → (∀ {a b} → RelV A a b → RelT B (f a) (g b))
          → RelT B (t₁ >>=T f) (t₂ >>=T g)
RelT-bind {A} {B} rt rk = RelT′-bind (RelV A) (RelV B) rt (λ a b r → rk r)
