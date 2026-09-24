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

open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer;
                             _*_; _+_; _⇒[_]_; μ-type; ν-type;
                             mk-kind; Zero; One; Many)
open import Once.Denotation.TraceMonad using (T; projTrace; valueT; stoppedT; returnT; _>>=T_; bindRes-rel)
open import Once.Res using (Res; stopped; returns; Res-rel)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.ValueDomainLaws using (_∼ᵈ_)

------------------------------------------------------------------------
-- The relation, by recursion on the type. `RelV` on values, `RelT` on
-- computations (mutual: `RelV` at arrows quantifies over `RelT` outputs).
------------------------------------------------------------------------

RelV : ∀ (A : Type) → ⟦ A ⟧ᴰ → ⟦ A ⟧ᴰ → Set
RelT : ∀ (A : Type) → T ⟦ A ⟧ᴰ → T ⟦ A ⟧ᴰ → Set

-- A computation relation: equal event traces at EVERY budget, and related
-- RESULTS.
--
-- plan 0.97 made this a TRIPLE — trace, stop flag, value — because `_>>=T_`'s
-- trace was a `join-es` of the two and `RelT-bind` could not conclude the
-- composite traces agreed without the flag. plan 0.98: the flag and the value
-- were always ONE fact, "did this return, and with what", and `Res-rel` is
-- that fact. Two related computations stop together or return related values;
-- there is no state in which one has a value and the other does not, which is
-- exactly what the triple could express and should not have been able to.
RelT A t₁ t₂ = ∀ n → (projTrace t₁ n ≡ projTrace t₂ n)
                   × Res-rel (RelV A) (T.resT t₁) (T.resT t₂)

-- First-order (pure `Val`) payloads: observational = propositional equality.
RelV Unit        _ _ = ⊤
RelV Void        ()
RelV Int         x y = x ≡ y
RelV Float       x y = x ≡ y
RelV Str         x y = x ≡ y
RelV Buffer      x y = x ≡ y
RelV (μ-type F)  x y = x ≡ y
-- SPIKE (4th ν defect): the observational relation at a COINDUCTIVE type is
-- BISIMILARITY, not propositional equality. `anaᵈ-∼` proves this one directly
-- and coinductively; it is only the conversion to `≡` that needs the
-- `bisimᵈ-to-eq` axiom.
RelV (ν-type F)  x y = x ∼ᵈ y
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
RelT-return rv n = refl , rv

-- Bind preserves the relation: related computations sequenced with related
-- continuations stay related. `_>>=T_` concatenates the two traces, so the
-- trace equality is `cong₂ _++_` of the two halves.
--
-- The two sides run their continuations at their OWN remaining budgets
-- (`_>>=T_` threads). Those budgets are computed from the two head traces,
-- which the relation already equates — so `keq` transports the right half
-- from the left's budget to its own. Nothing new is assumed: the budget
-- agreement IS the trace agreement.
RelT-bind : ∀ {A B} {t₁ t₂ : T ⟦ A ⟧ᴰ} {f g : ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ}
          → RelT A t₁ t₂
          → (∀ {a b} → RelV A a b → RelT B (f a) (g b))
          → RelT B (t₁ >>=T f) (t₂ >>=T g)
-- plan 0.98: the whole body is `bindRes-rel`. 0.97 had to thread the value
-- out of the head (`valueT t₁ n`) in order to APPLY the continuation, and then
-- transport the result along the budget equation — three components moved by
-- hand. Splitting on the head's RESULT instead means the value is bound by the
-- constructor: the stopped case has no continuation to mention at all, and the
-- returning case is the one that carries the budget transport.
RelT-bind {A} {B} {t₁} {t₂} {f} {g} rt rk n =
  bindRes-rel (RelV A) (RelV B) (T.trT t₁) (T.trT t₂) (T.resT t₁) (T.resT t₂)
              f g n (proj₁ (rt n)) (proj₂ (rt n)) (λ r j → rk r j)
