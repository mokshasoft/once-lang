-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.CoerceIR — the IR a subtyping conversion compiles to (plan 0.99).
--
-- The IR is UNGRADED (`⌊_⌋` erases the arrow's purity), so a conversion that
-- only raises grades is the identity on IR types. `Coe X Y` keeps that fact as
-- a constructor, `idC`, instead of emitting `id ∘ …`: a grade-only coercion — the
-- former `arr'` — compiles to exactly the IR it compiled to before, and only a
-- real `Void` conversion emits code (`initial`, under a closure when it sits in
-- an arrow's codomain).
------------------------------------------------------------------------

module Once.Surface.CoerceIR where

open import Once.Type as T using (Type; Quantity; Zero; One; Many)
open import Once.Type.Sub
open import Once.IR

------------------------------------------------------------------------
-- A conversion is either the identity (the two IR types coincide) or a
-- morphism.
------------------------------------------------------------------------

data Coe : IRTy → IRTy → Set where
  idC : ∀ {X} → Coe X X
  fnC : ∀ {X Y} → IR X Y → Coe X Y

toIR : ∀ {X Y} → Coe X Y → IR X Y
toIR idC     = id
toIR (fnC f) = f

-- Post-compose a conversion. `idC` adds NOTHING — `runC idC e` IS `e`.
runC : ∀ {Z X Y} → Coe X Y → IR Z X → IR Z Y
runC idC     e = e
runC (fnC f) e = f ∘ e

------------------------------------------------------------------------
-- The constructors' actions.
------------------------------------------------------------------------

-- `Void` into anything: `initial`, except into `Void` itself.
voidC : ∀ (B : Type) → Coe Void ⌊ B ⌋
voidC T.Unit          = fnC initial
voidC T.Void          = idC
voidC T.Int           = fnC initial
voidC T.Float         = fnC initial
voidC T.Str           = fnC initial
voidC T.Buffer        = fnC initial
voidC (A T.* B)       = fnC initial
voidC (A T.+ B)       = fnC initial
voidC (A T.⇒[ k ] B)  = fnC initial
voidC (T.μ-type F)    = fnC initial
voidC (T.ν-type F)    = fnC initial

-- A closure converted: the argument backwards, the result forwards.
wrapArr : ∀ {X X′ Y Y′} → IR X′ X → IR Y Y′ → IR (X ⇛ Y) (X′ ⇛ Y′)
wrapArr f g = curry (g ∘ (apply ∘ ⟨ fst , f ∘ snd ⟩))

-- An erased (`Zero`) arrow takes no argument, so only its result converts.
arrC : ∀ (q : Quantity) {X X′ Y Y′} → Coe X′ X → Coe Y Y′
     → Coe (eraseArrow q X Y) (eraseArrow q X′ Y′)
arrC Zero ca        idC     = idC
arrC Zero ca        (fnC g) = fnC (curry (g ∘ apply))
arrC One  idC       idC     = idC
arrC One  idC       (fnC g) = fnC (wrapArr id g)
arrC One  (fnC f)   cb      = fnC (wrapArr f (toIR cb))
arrC Many idC       idC     = idC
arrC Many idC       (fnC g) = fnC (wrapArr id g)
arrC Many (fnC f)   cb      = fnC (wrapArr f (toIR cb))

prodC : ∀ {X X′ Y Y′} → Coe X X′ → Coe Y Y′ → Coe (X * Y) (X′ * Y′)
prodC idC     idC     = idC
prodC idC     (fnC g) = fnC ⟨ fst , g ∘ snd ⟩
prodC (fnC f) cb      = fnC ⟨ f ∘ fst , toIR cb ∘ snd ⟩

sumC : ∀ {X X′ Y Y′} → Coe X X′ → Coe Y Y′ → Coe (X + Y) (X′ + Y′)
sumC idC     idC     = idC
sumC idC     (fnC g) = fnC (case inl (inr ∘ g))
sumC (fnC f) cb      = fnC (case (inl ∘ f) (inr ∘ toIR cb))

------------------------------------------------------------------------
-- The conversion a derivation compiles to.
------------------------------------------------------------------------

coeIR : ∀ {A B} → A <: B → Coe ⌊ A ⌋ ⌊ B ⌋
coeIR (sub-void {B}) = voidC B
coeIR sub-unit   = idC
coeIR sub-int    = idC
coeIR sub-float  = idC
coeIR sub-str    = idC
coeIR sub-buffer = idC
coeIR (sub-arr {q = q} a b _) = arrC q (coeIR a) (coeIR b)
coeIR (sub-prod a b) = prodC (coeIR a) (coeIR b)
coeIR (sub-sum a b)  = sumC (coeIR a) (coeIR b)
coeIR sub-μ = idC
coeIR sub-ν = idC
