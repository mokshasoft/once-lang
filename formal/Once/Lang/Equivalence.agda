-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Equivalence — when two meanings are the same (plan 0.116 D0).
--
-- SPEC. Two meanings are the same when NO FINITE OBSERVATION tells them apart
-- — the notion the correctness statement already uses for a program's
-- behaviour (it compares every finite prefix of the trace, never two infinite
-- objects). By type:
--   * a base value (`Int`, `Float`, a `μ` value) is observed whole: `≡`;
--   * a pair componentwise, a sum by its side and its content;
--   * an arrow by its results at arguments that are the same (at every depth);
--   * a computation by its events, in order, and its result, to every finite
--     DEPTH `n`: its first `n` nodes — the same call with the same argument,
--     and equivalent continuations at every answer; or the same halt; or
--     equivalent results. Every grade's computation is read as a tree of the
--     completely iterative monad (`toT∞`, D311, D312), so a computation that
--     runs forever is observed as one that returns: by its finite prefixes;
--   * a stream (`ν`) to every finite DEPTH `n`: its first `n` layers.
-- A meaning at `ν` is codata, so `≡` cannot compare two streams that behave
-- identically but are built differently; every finite observation can.
--
-- Plan 0.116's coherence and plan 0.112 F's laws are stated with it.
------------------------------------------------------------------------

module Once.Lang.Equivalence where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Lang.Type.Grade using (Purity; pure; act; eff⁺; eff; mk-kind; Zero; One; Many)
open import Once.Lang.Guarded using (ν⁺; forget⁺)
open Once.Lang.Guarded.ν⁺ using (force⁺)
open import Once.Lang.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; rigid)
open import Once.Lang.Meaning using (T; M; ⟦_⟧ᵛ; toT∞)
open import Once.Lang.Iterative using (T∞; NodeEq; ν∞)
open Once.Lang.Iterative.T∞ using (force)
open Once.Lang.Iterative.ν∞ using (force∞)
open import Once.Lang.Trace using (ret; call; halt)
open import Once.Lang.Graded using (νᵖ; module νᵖ)
open import Once.Lang.Stream using (νᵈ; module νᵈ)
open νᵈ using (forceᵈ)
open import Once.Lang.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open νᵖ using (forceᵖ)

------------------------------------------------------------------------
-- Computations: the same events in the same order, equivalent results.
------------------------------------------------------------------------

data TreeEq {X : Set} (R : X → X → Set) : T X → T X → Set where
  ret≈  : ∀ {x y} → R x y → TreeEq R (ret x) (ret y)
  call≈ : ∀ {o a k k′} → (∀ b → TreeEq R (k b) (k′ b)) → TreeEq R (call o a k) (call o a k′)
  halt≈ : ∀ {o a} → TreeEq R (halt o a) (halt o a)

-- A tree of the completely iterative monad to depth `n`: its first `n` nodes.
TreeEqN : ∀ {X : Set} → ℕ → (X → X → Set) → T∞ X → T∞ X → Set
TreeEqN zero    R _ _  = ⊤
TreeEqN (suc n) R m m′ = NodeEq R (TreeEqN n R) (force m) (force m′)

------------------------------------------------------------------------
-- One layer of a stream: its constant parts (base values) equal, its
-- recursive positions related by `R`.
------------------------------------------------------------------------

LayerEq : ∀ (G : SFunctor) {X : Set} → (X → X → Set) → ⟦ G ⟧SF X → ⟦ G ⟧SF X → Set
LayerEq (SK B)   R x y = x ≡ y
LayerEq SId      R x y = R x y
LayerEq (G S⊕ H) R (inj₁ x) (inj₁ y) = LayerEq G R x y
LayerEq (G S⊕ H) R (inj₂ x) (inj₂ y) = LayerEq H R x y
LayerEq (G S⊕ H) R (inj₁ _) (inj₂ _) = ⊥
LayerEq (G S⊕ H) R (inj₂ _) (inj₁ _) = ⊥
LayerEq (G S⊗ H) R (x , x′) (y , y′) = LayerEq G R x y × LayerEq H R x′ y′

-- Streams to depth `n`: the first `n` layers agree.
νᵖ-upto : ∀ (H : SFunctor) → ℕ → νᵖ H → νᵖ H → Set
νᵖ-upto H zero    _ _ = ⊤
νᵖ-upto H (suc n) v w = LayerEq H (νᵖ-upto H n) (forceᵖ v) (forceᵖ w)

νᵈ-upto : ∀ (H : SFunctor) → ℕ → νᵈ H → νᵈ H → Set
νᵈ-upto H zero    _ _ = ⊤
νᵈ-upto H (suc n) v w = TreeEq (LayerEq H (νᵈ-upto H n)) (forceᵈ v) (forceᵈ w)

ν⁺-upto : ∀ (H : SFunctor) → ℕ → ν⁺ H → ν⁺ H → Set
ν⁺-upto H zero    _ _ = ⊤
ν⁺-upto H (suc n) v w = TreeEqN (suc n) (LayerEq H (ν⁺-upto H n)) (forget⁺ (force⁺ v)) (forget⁺ (force⁺ w))

ν∞-upto : ∀ (H : SFunctor) → ℕ → ν∞ H → ν∞ H → Set
ν∞-upto H zero    _ _ = ⊤
ν∞-upto H (suc n) v w = TreeEqN (suc n) (LayerEq H (ν∞-upto H n)) (force∞ v) (force∞ w)

------------------------------------------------------------------------
-- Values and computations of a type, observed to depth `n`.
------------------------------------------------------------------------

Obs  : ℕ → (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᵛ → Set
ObsM : ℕ → (π : Purity) (A : Type) → M π ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ → Set

ObsM n π A m m′ = TreeEqN n (Obs n A) (toT∞ π m) (toT∞ π m′)

Obs n Unit        _ _ = ⊤
Obs n Void        _ _ = ⊤
Obs n Int         x y = x ≡ y
Obs n Float       x y = x ≡ y
Obs n (μ-type F)  x y = x ≡ y
Obs n (rigid _ _) _ _ = ⊤
Obs n (A * B) (a , b) (a′ , b′) = Obs n A a a′ × Obs n B b b′
Obs n (A + B) (inj₁ a) (inj₁ a′) = Obs n A a a′
Obs n (A + B) (inj₂ b) (inj₂ b′) = Obs n B b b′
Obs n (A + B) (inj₁ _) (inj₂ _)  = ⊥
Obs n (A + B) (inj₂ _) (inj₁ _)  = ⊥
Obs n (A ⇒[ mk-kind Zero π ] B) f g = ObsM n π B (f tt) (g tt)
Obs n (A ⇒[ mk-kind One  π ] B) f g = ∀ a a′ → (∀ m → Obs m A a a′) → ObsM n π B (f a) (g a′)
Obs n (A ⇒[ mk-kind Many π ] B) f g = ∀ a a′ → (∀ m → Obs m A a a′) → ObsM n π B (f a) (g a′)
Obs n (ν-type F pure) v w = νᵖ-upto _ n v w
Obs n (ν-type F act)  v w = νᵈ-upto _ n v w
Obs n (ν-type F eff)  v w = ν∞-upto _ n v w
Obs n (ν-type F eff⁺) v w = ν⁺-upto _ n v w

------------------------------------------------------------------------
-- The equivalence: every finite observation agrees.
------------------------------------------------------------------------

-- `Same A x y`: no finite observation tells the values `x`, `y` of type `A`
-- apart; `SameM π A m m′` for computations at grade `π`.
Same : (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᵛ → Set
Same A x y = ∀ n → Obs n A x y

SameM : (π : Purity) (A : Type) → M π ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ → Set
SameM π A m m′ = ∀ n → ObsM n π A m m′
