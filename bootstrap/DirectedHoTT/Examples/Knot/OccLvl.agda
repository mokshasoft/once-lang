------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ A de BRUIJN INDEX, AT A LEVEL.
--
--     lvl : Var Γ → ℕ
--
-- ★ `Knot/Occ`'s header fixes the convention: "a `vz` at depth `nsuc m`
--   IS the variable at level `m`".  So `vz`'s level is the depth of the
--   context UNDER the binder, and `vs` LEAVES THE LEVEL ALONE.
--
-- ★★ THAT SECOND CLAUSE IS THE WHOLE REASON `occK` IS INDEXED BY A LEVEL
--   RATHER THAN AN INDEX.  `occTy x (Π A B) = occTy x A ∨ occTy (vs x) B`
--   recurses under a binder, and `lvl (vs x) = lvl x` BY DEFINITION — so
--   the object-level call needs no shift.  With indices that row would
--   owe a shift lemma, and `Knot/Occ`'s `cVar-vs` would need a method of
--   its own instead of falling out of the generic fold.
--
-- ⚠ THE CONVENTION IS PINNED BY THE `refl`s BELOW, and that is not
--   decoration: reverse it (level = index) and every row still
--   type-checks — the statement is simply FALSE, and only the
--   `cVar-vz` row would ever notice.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.OccLvl where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; Var; vz; vs )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )

lvl : {Γ : Cx} → Var Γ → ℕ
lvl {Γ ∙} vz     = len Γ
lvl {Γ ∙} (vs x) = lvl x

-- in a context of depth 3: `vz` is level 2, `vs (vs vz)` is level 0
_ : lvl {ε ∙ ∙ ∙} vz ≡ suc (suc zero)
_ = refl

_ : lvl {ε ∙ ∙ ∙} (vs vz) ≡ suc zero
_ = refl

_ : lvl {ε ∙ ∙ ∙} (vs (vs vz)) ≡ zero
_ = refl
