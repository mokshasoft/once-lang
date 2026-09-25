-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.CoerceIR — the IR a subtyping conversion compiles to (plan 0.99).
--
-- `coeIR p` is the STRUCTURAL conversion: `initial` out of `Void`, the identity
-- on base types, and under a type former the former's functorial action (a
-- closure is re-wrapped: argument backwards, result forwards).
--
-- The IR is UNGRADED (`⌊_⌋` erases the arrow's purity), so a derivation with no
-- genuine `Void` conversion in it — `VoidFree` — relates two types with the SAME
-- IR type (`erase-eq`), and needs no code at all. `runCoe` emits nothing for
-- those: `subst … refl f` is `f` for every concrete derivation, so a grade-only
-- conversion (the former `arr'`) compiles to exactly the IR it compiled to
-- before. Only a derivation that converts out of `Void` pays for `coeIR`.
--
-- Why a DECIDED predicate and not a `Coe` type with an identity constructor:
-- splitting on such a constructor makes Agda unify `⌊ A ⌋` with `⌊ B ⌋`, which
-- it cannot do through a defined function. A decision is split on instead.
------------------------------------------------------------------------

module Once.Surface.CoerceIR where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Type as T using (Type; Quantity; Zero; One; Many)
open import Once.Type.Sub
open import Once.IR

------------------------------------------------------------------------
-- The structural conversion.
------------------------------------------------------------------------

-- A closure converted: the argument backwards, the result forwards.
wrapArr : ∀ {X X′ Y Y′} → IR X′ X → IR Y Y′ → IR (X ⇛ Y) (X′ ⇛ Y′)
wrapArr f g = curry (g ∘ (apply ∘ ⟨ fst , f ∘ snd ⟩))

-- An erased (`Zero`) arrow takes no argument, so only its result converts.
wrapArr₀ : ∀ {Y Y′} → IR Y Y′ → IR (Unit ⇛ Y) (Unit ⇛ Y′)
wrapArr₀ g = curry (g ∘ apply)

coeIR : ∀ {A B} → A <: B → IR ⌊ A ⌋ ⌊ B ⌋
coeIR sub-void   = initial
coeIR sub-unit   = id
coeIR sub-int    = id
coeIR sub-float  = id
coeIR sub-str    = id
coeIR sub-buffer = id
coeIR (sub-arr {q = Zero} a b _) = wrapArr₀ (coeIR b)
coeIR (sub-arr {q = One}  a b _) = wrapArr (coeIR a) (coeIR b)
coeIR (sub-arr {q = Many} a b _) = wrapArr (coeIR a) (coeIR b)
coeIR (sub-prod a b) = ⟨ coeIR a ∘ fst , coeIR b ∘ snd ⟩
coeIR (sub-sum a b)  = case (inl ∘ coeIR a) (inr ∘ coeIR b)
coeIR sub-μ = id
coeIR sub-ν = id

------------------------------------------------------------------------
-- Void-free derivations relate types with the same IR type.
------------------------------------------------------------------------

data VoidFree : ∀ {A B} → A <: B → Set where
  vf-void   : VoidFree (sub-void {T.Void})
  vf-unit   : VoidFree sub-unit
  vf-int    : VoidFree sub-int
  vf-float  : VoidFree sub-float
  vf-str    : VoidFree sub-str
  vf-buffer : VoidFree sub-buffer
  vf-arr    : ∀ {A A′ B B′ q π π′} {a : A′ <: A} {b : B <: B′} {g : π ⊑π π′}
            → VoidFree a → VoidFree b → VoidFree (sub-arr {q = q} a b g)
  vf-prod   : ∀ {A A′ B B′} {a : A <: A′} {b : B <: B′}
            → VoidFree a → VoidFree b → VoidFree (sub-prod a b)
  vf-sum    : ∀ {A A′ B B′} {a : A <: A′} {b : B <: B′}
            → VoidFree a → VoidFree b → VoidFree (sub-sum a b)
  vf-μ      : ∀ {F} → VoidFree (sub-μ {F})
  vf-ν      : ∀ {F} → VoidFree (sub-ν {F})

private
  two : ∀ {P Q R : Set} → (P → Q → R) → (R → P) → (R → Q) → Dec P → Dec Q → Dec R
  two k π₁ π₂ (yes p) (yes q) = yes (k p q)
  two k π₁ π₂ (no ¬p) _       = no λ r → ¬p (π₁ r)
  two k π₁ π₂ (yes _) (no ¬q) = no λ r → ¬q (π₂ r)

  arr-a : ∀ {A A′ B B′ q π π′} {a : A′ <: A} {b : B <: B′} {g : π ⊑π π′}
        → VoidFree (sub-arr {q = q} a b g) → VoidFree a
  arr-a (vf-arr va _) = va
  arr-b : ∀ {A A′ B B′ q π π′} {a : A′ <: A} {b : B <: B′} {g : π ⊑π π′}
        → VoidFree (sub-arr {q = q} a b g) → VoidFree b
  arr-b (vf-arr _ vb) = vb
  prod-a : ∀ {A A′ B B′} {a : A <: A′} {b : B <: B′} → VoidFree (sub-prod a b) → VoidFree a
  prod-a (vf-prod va _) = va
  prod-b : ∀ {A A′ B B′} {a : A <: A′} {b : B <: B′} → VoidFree (sub-prod a b) → VoidFree b
  prod-b (vf-prod _ vb) = vb
  sum-a : ∀ {A A′ B B′} {a : A <: A′} {b : B <: B′} → VoidFree (sub-sum a b) → VoidFree a
  sum-a (vf-sum va _) = va
  sum-b : ∀ {A A′ B B′} {a : A <: A′} {b : B <: B′} → VoidFree (sub-sum a b) → VoidFree b
  sum-b (vf-sum _ vb) = vb

voidFree? : ∀ {A B} (p : A <: B) → Dec (VoidFree p)
voidFree? (sub-void {T.Void})         = yes vf-void
voidFree? (sub-void {T.Unit})         = no λ ()
voidFree? (sub-void {T.Int})          = no λ ()
voidFree? (sub-void {T.Float})        = no λ ()
voidFree? (sub-void {T.Str})          = no λ ()
voidFree? (sub-void {T.Buffer})       = no λ ()
voidFree? (sub-void {_ T.* _})        = no λ ()
voidFree? (sub-void {_ T.+ _})        = no λ ()
voidFree? (sub-void {_ T.⇒[ _ ] _})  = no λ ()
voidFree? (sub-void {T.μ-type _})     = no λ ()
voidFree? (sub-void {T.ν-type _})     = no λ ()
voidFree? sub-unit   = yes vf-unit
voidFree? sub-int    = yes vf-int
voidFree? sub-float  = yes vf-float
voidFree? sub-str    = yes vf-str
voidFree? sub-buffer = yes vf-buffer
voidFree? (sub-arr a b g) = two vf-arr arr-a arr-b (voidFree? a) (voidFree? b)
voidFree? (sub-prod a b)  = two vf-prod prod-a prod-b (voidFree? a) (voidFree? b)
voidFree? (sub-sum a b)   = two vf-sum sum-a sum-b (voidFree? a) (voidFree? b)
voidFree? sub-μ = yes vf-μ
voidFree? sub-ν = yes vf-ν

-- For every CONCRETE derivation this reduces to `refl`.
erase-eq : ∀ {A B} (p : A <: B) → VoidFree p → ⌊ A ⌋ ≡ ⌊ B ⌋
erase-eq _ vf-void   = refl
erase-eq _ vf-unit   = refl
erase-eq _ vf-int    = refl
erase-eq _ vf-float  = refl
erase-eq _ vf-str    = refl
erase-eq _ vf-buffer = refl
erase-eq (sub-arr {q = Zero} a b _) (vf-arr va vb) = cong (Unit ⇛_) (erase-eq b vb)
erase-eq (sub-arr {q = One}  a b _) (vf-arr va vb) = cong₂ _⇛_ (sym (erase-eq a va)) (erase-eq b vb)
erase-eq (sub-arr {q = Many} a b _) (vf-arr va vb) = cong₂ _⇛_ (sym (erase-eq a va)) (erase-eq b vb)
erase-eq (sub-prod a b) (vf-prod va vb) = cong₂ _*_ (erase-eq a va) (erase-eq b vb)
erase-eq (sub-sum a b)  (vf-sum va vb)  = cong₂ _+_ (erase-eq a va) (erase-eq b vb)
erase-eq _ vf-μ = refl
erase-eq _ vf-ν = refl

------------------------------------------------------------------------
-- What `elaborate (coerce p e)` emits.
------------------------------------------------------------------------

runCoe-dec : ∀ {Z A B} (p : A <: B) → Dec (VoidFree p) → IR Z ⌊ A ⌋ → IR Z ⌊ B ⌋
runCoe-dec p (yes vf) f = subst (IR _) (erase-eq p vf) f
runCoe-dec p (no _)   f = coeIR p ∘ f

runCoe : ∀ {Z A B} → A <: B → IR Z ⌊ A ⌋ → IR Z ⌊ B ⌋
runCoe p f = runCoe-dec p (voidFree? p) f
