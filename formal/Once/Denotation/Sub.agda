-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.Sub — what a subtyping derivation MEANS (plan 0.99, D226).
--
-- Each `p : A <: B` denotes a conversion `⟦ p ⟧<: : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ`. `Void`
-- converts by `¡` (there is nothing to convert); an arrow converts its argument
-- backwards and its RESULT forwards under `fmap∞`, which leaves the trace alone;
-- the grade is erased, as `⟦_⟧ᴰ` erases it.
--
-- Coherence has two halves. `Once.Internal.Laws.SubLaws.<:-unique` says each `A <: B` has
-- one derivation. This module says the admissible structure means what it
-- should: `<:-refl` denotes the identity and `<:-trans` denotes composition. So
-- any chain of conversions means the single direct one.
--
-- `void-middle` is plan 0.94 §4's case: `compose f g` with `g` ending in `Void`
-- is typeable at EVERY middle type, and every choice means the same thing —
-- indeed it does not depend on `f` at all, because a computation into `Void`
-- can only have HALTED (a tree into `Void` has no `ret` leaf).
------------------------------------------------------------------------

module Once.Denotation.Sub where

open import Once.Spec.Type using (Ty)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Spec.Grade using (Zero; One; Many; mk-kind)
open import Once.Spec.Type using (Type; _⇒[_]_; Void)
import Once.Spec.Type as ST
open import Once.Internal.Type.Sub
open import Once.Spec.Sub using (sub-*; sub-+)
open import Once.Spec.Sub using (_<:_; _<:ᶜ_; _⊔_≔_; sub-*; sub-+; subᶜ-*; subᶜ-+; sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν; subᶜ-void; subᶜ-var; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Type.Sub
open import Once.Internal.Laws.SubLaws
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
-- `fmap∞` is a functor and congruent: the tree's laws (plan 0.105).
open import Once.Internal.Iterative using (T∞; fmap∞)

------------------------------------------------------------------------
-- The conversion a derivation denotes.
------------------------------------------------------------------------

⟦_⟧<: : ∀ {m} {A B : Ty m} → A <: B → ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ
⟦ sub-void   ⟧<: ()
⟦ sub-unit   ⟧<: x = x
⟦ sub-int    ⟧<: x = x
⟦ sub-float  ⟧<: x = x
⟦ sub-arr {q = Zero} a b _ ⟧<: f = λ u → fmap∞ ⟦ b ⟧<: (f u)
⟦ sub-arr {q = One}  a b _ ⟧<: f = λ x → fmap∞ ⟦ b ⟧<: (f (⟦ a ⟧<: x))
⟦ sub-arr {q = Many} a b _ ⟧<: f = λ x → fmap∞ ⟦ b ⟧<: (f (⟦ a ⟧<: x))
⟦ sub-* a b ⟧<: (x , y) = ⟦ a ⟧<: x , ⟦ b ⟧<: y
⟦ sub-+ a b ⟧<: (inj₁ x) = inj₁ (⟦ a ⟧<: x)
⟦ sub-+ a b ⟧<: (inj₂ y) = inj₂ (⟦ b ⟧<: y)
⟦ sub-μ ⟧<: x = x
⟦ sub-ν _ ⟧<: x = x

------------------------------------------------------------------------
-- Coherence, semantic half: reflexivity is the identity …
------------------------------------------------------------------------

-- plan 0.119 D5: the coercions' laws hold up to the IR's value relation
-- (`ValueRel.RelD`): an arrow's coercion maps a run, and runs are compared
-- step for step, never by `≡`.
open import Once.Denotation.ValueRel using (RelD; RelS-fmap; RelS-fmapˡ)
open import Data.Unit using (tt)

<:-refl-rel : ∀ {m} (A : Ty m) {x y : ⟦ A ⟧ᴰ} → RelD A x y → RelD A (⟦ <:-refl A ⟧<: x) y
<:-refl-rel ST.Unit   r = r
<:-refl-rel ST.Void   {()}
<:-refl-rel ST.Int    r = r
<:-refl-rel ST.Float  r = r
<:-refl-rel (A ⇒[ mk-kind Zero π ] B) r = RelS-fmapˡ r (<:-refl-rel B)
<:-refl-rel (A ⇒[ mk-kind One π ] B)  r = λ ra → RelS-fmapˡ (r (<:-refl-rel A ra)) (<:-refl-rel B)
<:-refl-rel (A ⇒[ mk-kind Many π ] B) r = λ ra → RelS-fmapˡ (r (<:-refl-rel A ra)) (<:-refl-rel B)
<:-refl-rel (A ST.* B) {x₁ , x₂} {y₁ , y₂} (r₁ , r₂) = <:-refl-rel A r₁ , <:-refl-rel B r₂
<:-refl-rel (A ST.+ B) {inj₁ x} {inj₁ y} r = <:-refl-rel A r
<:-refl-rel (A ST.+ B) {inj₂ x} {inj₂ y} r = <:-refl-rel B r
<:-refl-rel (A ST.+ B) {inj₁ _} {inj₂ _} ()
<:-refl-rel (A ST.+ B) {inj₂ _} {inj₁ _} ()
<:-refl-rel (ST.μ F) r = r
<:-refl-rel (ST.ν F _) r = r
<:-refl-rel (ST.var _) {()}
