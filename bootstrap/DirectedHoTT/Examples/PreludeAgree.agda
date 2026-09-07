------------------------------------------------------------------------
-- DirectedHoTT · EXAMPLES — THE PRELUDE'S EQUALITY **IS** THE BUILTIN ONE.
--
-- ★★★ THE FACT AXIS 0 EXISTS TO ESTABLISH, MADE CHECKABLE.  Before
--   2026-09-07 this tree held TWO `_≡_`s: 235 modules used the
--   hand-rolled one from `normalizer.Syntax.Types`, while
--   `Metatheory/FormerCensus` and `Examples/Knot/Census` used
--   `Agda.Builtin.Equality` because REFLECTION needs the builtin.  Those
--   two straddled the split and compiled only because they never stated
--   an equation relating the two worlds — an induction with one half in
--   each does not go through.
--
-- ★ `DirectedHoTT.Prelude` re-exports the STANDARD LIBRARY's `_≡_`, and
--   the stdlib's `_≡_` IS `Agda.Builtin.Equality._≡_`.  So the split is
--   not narrowed, it is GONE: the census modules and the kernel now speak
--   the same equality.  The four lemmas below are that claim; they are
--   `refl`/identity by construction, and the POINT is that they
--   TYPECHECK.
--
-- ⚠ WHY AN EXAMPLE AND NOT A COMMENT.  `LESSONS.md`: a fact nothing
--   checks is a fact that rots.  If someone re-points the prelude at a
--   hand-rolled equality, THIS module goes red — and nothing else in the
--   tree would, because every other module is internally consistent
--   either way.  That is exactly the failure mode axis 0 closed, so it is
--   the one that needs a standing control.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.PreludeAgree where

open import DirectedHoTT.Prelude using ( _≡_; refl )
open import Agda.Builtin.Equality using () renaming ( _≡_ to _≡ᵇ_ ; refl to reflᵇ )
open import DirectedHoTT.Spec.Syntax using ( RTm; var; Var; vz; ε; _∙ )

-- The two equalities are interchangeable in BOTH directions — i.e. they
-- are the same inductive family, not merely equivalent ones.
tree→builtin : {A : Set} {x y : A} → x ≡ y → x ≡ᵇ y
tree→builtin p = p

builtin→tree : {A : Set} {x y : A} → x ≡ᵇ y → x ≡ y
builtin→tree p = p

-- ...and the constructors agree too.
refl-agrees : {A : Set} {x : A} → (refl {x = x}) ≡ᵇ reflᵇ
refl-agrees = reflᵇ

-- At a REAL kernel type: the shape a reflection-side census needs when it
-- wants to state an equation about kernel syntax.  This is what could not
-- be written before.
kernel-eq : var (vz {ε}) ≡ᵇ var (vz {ε})
kernel-eq = refl
