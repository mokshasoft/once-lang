-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.Sub — what a subtyping derivation MEANS (plan 0.99, D226).
--
-- Each `p : A <: B` denotes a conversion `⟦ p ⟧<: : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ`. `Void`
-- converts by `¡` (there is nothing to convert); an arrow converts its argument
-- backwards and its RESULT forwards under `fmapT`, which leaves the trace alone;
-- the grade is erased, as `⟦_⟧ᴰ` erases it.
--
-- Coherence has two halves. `Once.Type.Sub.<:-unique` says each `A <: B` has
-- one derivation. This module says the admissible structure means what it
-- should: `<:-refl` denotes the identity and `<:-trans` denotes composition. So
-- any chain of conversions means the single direct one.
--
-- `void-middle` is plan 0.94 §4's case: `compose f g` with `g` ending in `Void`
-- is typeable at EVERY middle type, and every choice means the same thing —
-- indeed it does not depend on `f` at all, because a computation into `Void`
-- can only have STOPPED.
------------------------------------------------------------------------

module Once.Denotation.Sub where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Type using (Type; Zero; One; Many; mk-kind; _⇒[_]_; Void)
open import Once.Type.Sub
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonad using (T; mkT; fmapT; _>>=T_)
open import Once.Res using (stopped; returns; mapRes-id; mapRes-∘; mapRes-cong)
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- `fmapT` is a functor, and congruent. Each is one `Res` law under `mkT`.
------------------------------------------------------------------------

fmapT-id : ∀ {X} (m : T X) → fmapT (λ x → x) m ≡ m
fmapT-id (mkT tr r) = cong (mkT tr) (mapRes-id r)

fmapT-∘ : ∀ {X Y Z} (g : Y → Z) (f : X → Y) (m : T X)
        → fmapT g (fmapT f m) ≡ fmapT (λ x → g (f x)) m
fmapT-∘ g f (mkT tr r) = cong (mkT tr) (mapRes-∘ g f r)

fmapT-cong : ∀ {X Y} {f g : X → Y} → (∀ x → f x ≡ g x) → (m : T X) → fmapT f m ≡ fmapT g m
fmapT-cong h (mkT tr r) = cong (mkT tr) (mapRes-cong h r)

------------------------------------------------------------------------
-- The conversion a derivation denotes.
------------------------------------------------------------------------

⟦_⟧<: : ∀ {A B} → A <: B → ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ
⟦ sub-void   ⟧<: ()
⟦ sub-unit   ⟧<: x = x
⟦ sub-int    ⟧<: x = x
⟦ sub-float  ⟧<: x = x
⟦ sub-str    ⟧<: x = x
⟦ sub-buffer ⟧<: x = x
⟦ sub-arr {q = Zero} a b _ ⟧<: f = λ u → fmapT ⟦ b ⟧<: (f u)
⟦ sub-arr {q = One}  a b _ ⟧<: f = λ x → fmapT ⟦ b ⟧<: (f (⟦ a ⟧<: x))
⟦ sub-arr {q = Many} a b _ ⟧<: f = λ x → fmapT ⟦ b ⟧<: (f (⟦ a ⟧<: x))
⟦ sub-prod a b ⟧<: (x , y) = ⟦ a ⟧<: x , ⟦ b ⟧<: y
⟦ sub-sum a b ⟧<: (inj₁ x) = inj₁ (⟦ a ⟧<: x)
⟦ sub-sum a b ⟧<: (inj₂ y) = inj₂ (⟦ b ⟧<: y)
⟦ sub-μ ⟧<: x = x
⟦ sub-ν ⟧<: x = x

------------------------------------------------------------------------
-- Coherence, semantic half: reflexivity is the identity …
------------------------------------------------------------------------

<:-refl-id : ∀ A (x : ⟦ A ⟧ᴰ) → ⟦ <:-refl A ⟧<: x ≡ x
<:-refl-id Type.Unit   x = refl
<:-refl-id Type.Void   ()
<:-refl-id Type.Int    x = refl
<:-refl-id Type.Float  x = refl
<:-refl-id Type.Str    x = refl
<:-refl-id Type.Buffer x = refl
<:-refl-id (A ⇒[ mk-kind Zero π ] B) f = extensionality λ u →
  trans (fmapT-cong (<:-refl-id B) (f u)) (fmapT-id (f u))
<:-refl-id (A ⇒[ mk-kind One π ] B) f = extensionality λ x →
  trans (cong (λ y → fmapT ⟦ <:-refl B ⟧<: (f y)) (<:-refl-id A x))
        (trans (fmapT-cong (<:-refl-id B) (f x)) (fmapT-id (f x)))
<:-refl-id (A ⇒[ mk-kind Many π ] B) f = extensionality λ x →
  trans (cong (λ y → fmapT ⟦ <:-refl B ⟧<: (f y)) (<:-refl-id A x))
        (trans (fmapT-cong (<:-refl-id B) (f x)) (fmapT-id (f x)))
<:-refl-id (A Type.* B) (x , y) = cong₂ _,_ (<:-refl-id A x) (<:-refl-id B y)
<:-refl-id (A Type.+ B) (inj₁ x) = cong inj₁ (<:-refl-id A x)
<:-refl-id (A Type.+ B) (inj₂ y) = cong inj₂ (<:-refl-id B y)
<:-refl-id (Type.μ-type F) x = refl
<:-refl-id (Type.ν-type F) x = refl

------------------------------------------------------------------------
-- … and transitivity is composition.
------------------------------------------------------------------------

<:-trans-∘ : ∀ {A B C} (p : A <: B) (q : B <: C) (x : ⟦ A ⟧ᴰ)
           → ⟦ <:-trans p q ⟧<: x ≡ ⟦ q ⟧<: (⟦ p ⟧<: x)
<:-trans-∘ sub-void   q ()
<:-trans-∘ sub-unit   q x = refl
<:-trans-∘ sub-int    q x = refl
<:-trans-∘ sub-float  q x = refl
<:-trans-∘ sub-str    q x = refl
<:-trans-∘ sub-buffer q x = refl
<:-trans-∘ (sub-arr {q = Zero} a b _) (sub-arr a′ b′ _) f = extensionality λ u →
  trans (fmapT-cong (<:-trans-∘ b b′) (f u)) (sym (fmapT-∘ ⟦ b′ ⟧<: ⟦ b ⟧<: (f u)))
<:-trans-∘ (sub-arr {q = One} a b _) (sub-arr a′ b′ _) f = extensionality λ x →
  trans (cong (λ y → fmapT ⟦ <:-trans b b′ ⟧<: (f y)) (<:-trans-∘ a′ a x))
        (trans (fmapT-cong (<:-trans-∘ b b′) (f (⟦ a ⟧<: (⟦ a′ ⟧<: x))))
               (sym (fmapT-∘ ⟦ b′ ⟧<: ⟦ b ⟧<: (f (⟦ a ⟧<: (⟦ a′ ⟧<: x))))))
<:-trans-∘ (sub-arr {q = Many} a b _) (sub-arr a′ b′ _) f = extensionality λ x →
  trans (cong (λ y → fmapT ⟦ <:-trans b b′ ⟧<: (f y)) (<:-trans-∘ a′ a x))
        (trans (fmapT-cong (<:-trans-∘ b b′) (f (⟦ a ⟧<: (⟦ a′ ⟧<: x))))
               (sym (fmapT-∘ ⟦ b′ ⟧<: ⟦ b ⟧<: (f (⟦ a ⟧<: (⟦ a′ ⟧<: x))))))
<:-trans-∘ (sub-prod a b) (sub-prod a′ b′) (x , y) =
  cong₂ _,_ (<:-trans-∘ a a′ x) (<:-trans-∘ b b′ y)
<:-trans-∘ (sub-sum a b) (sub-sum a′ b′) (inj₁ x) = cong inj₁ (<:-trans-∘ a a′ x)
<:-trans-∘ (sub-sum a b) (sub-sum a′ b′) (inj₂ y) = cong inj₂ (<:-trans-∘ b b′ y)
<:-trans-∘ sub-μ q x = refl
<:-trans-∘ sub-ν q x = refl

------------------------------------------------------------------------
-- Plan 0.94 §4: the middle type through `Void` is irrelevant.
--
-- `compose f g` with `g : A ⇒ Void` checks at ANY middle `B`, by converting
-- `g`'s result `Void <: B`. Whatever `B` and `f` are, the composite means `g`'s
-- own result converted straight to `C`: a computation into `Void` can only have
-- stopped, so the bind never reaches `f`.
------------------------------------------------------------------------

void-middle : ∀ {B C : Type} (f : ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ) (m : T ⟦ Void ⟧ᴰ)
            → (fmapT ⟦ sub-void {B} ⟧<: m >>=T f) ≡ fmapT ⟦ sub-void {C} ⟧<: m
void-middle f (mkT tr stopped)      = refl
void-middle f (mkT tr (returns ()))
