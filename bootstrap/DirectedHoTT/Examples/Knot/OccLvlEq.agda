------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `lvl` IS INJECTIVE ON `Var Γ`.
--
--     eqv-lvl : (x y : Var Γ) → eqv x y ≡ eqℕ (lvl x) (lvl y)
--
-- ★★★ THIS IS WHAT MAKES THE LEVEL ENCODING FAITHFUL, and it is the
--   only real mathematical content in `occK`'s adequacy.  `Knot/Occ`'s
--   `occVz` decides variable equality by comparing LEVELS with
--   `eqNatTm`; that is correct exactly because distinct variables of one
--   context have distinct levels, which is this theorem.
--
-- ⚠ SEPARATE FROM `Knot/OccLvl` ON PURPOSE.  `OccLvl` is `lvl` plus
--   three `refl` convention checks and imports nothing but `Spec/Syntax`
--   and `Knot/Sorts`.  The proofs here need `eqℕ`, `eqv` and two
--   arithmetic lemmas; keeping them apart leaves `lvl`'s own module
--   cheap for everything that only needs the definition.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.OccLvlEq where

open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong; trans )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; Var; vz; vs )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; eqv )
open import DirectedHoTT.Lib.IFold using ( eqℕ )
-- ⚠ REUSED, NOT REDEFINED.  `+suc` is already in `Lib/IMeths` (and again
--   in `Metatheory/TySub`); `+-zeroʳ` in `Lib/NatMaxNum`.  A third copy
--   was written here and deleted.
open import DirectedHoTT.Lib.IMeths using ( +suc )
open import DirectedHoTT.Lib.NatMaxNum using ( +-zeroʳ )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )
open import DirectedHoTT.Examples.Knot.OccLvl using ( lvl )

eqℕ-refl : (n : ℕ) → eqℕ n n ≡ true
eqℕ-refl zero    = refl
eqℕ-refl (suc n) = eqℕ-refl n

-- ★ a number is never equal to itself plus a POSITIVE slack
eqℕ-gt : (n m : ℕ) → eqℕ (suc (n + m)) n ≡ false
eqℕ-gt zero    m = refl
eqℕ-gt (suc n) m = eqℕ-gt n m

eqℕ-lt : (n m : ℕ) → eqℕ n (suc (n + m)) ≡ false
eqℕ-lt zero    m = refl
eqℕ-lt (suc n) m = eqℕ-lt n m

------------------------------------------------------------------------
-- ★★★ THE BOUND — a variable's level is below its context's length.
--
-- ⚠⚠ THE NARROW FORM DOES NOT GO THROUGH.  `eqℕ (len Γ) (lvl y) ≡ false`
--   fails at `y = vs y'`: the goal is about `len (Γ ∙) = suc (len Γ)`
--   while the IH is about `len Γ`, and nothing bridges them.  Carrying a
--   SLACK `m` makes the `vs` case exactly the IH at `suc m`.
--
-- ⚠ And `_+_` recurses on its FIRST argument, so `len Γ + suc m` is
--   stuck and stepping the slack costs a `+suc` rewrite — the same
--   recursion-direction tax `Lib/NatMaxNum` pays three times.
------------------------------------------------------------------------
lvl-bound : {Γ : Cx} (y : Var Γ) (m : ℕ) → eqℕ (len Γ + m) (lvl y) ≡ false
lvl-bound {Γ ∙} vz     m = eqℕ-gt (len Γ) m
lvl-bound {Γ ∙} (vs y) m =
  trans (cong (λ z → eqℕ z (lvl y)) (sym (+suc (len Γ) m)))
        (lvl-bound y (suc m))

lvl-bound' : {Γ : Cx} (y : Var Γ) (m : ℕ) → eqℕ (lvl y) (len Γ + m) ≡ false
lvl-bound' {Γ ∙} vz     m = eqℕ-lt (len Γ) m
lvl-bound' {Γ ∙} (vs y) m =
  trans (cong (eqℕ (lvl y)) (sym (+suc (len Γ) m)))
        (lvl-bound' y (suc m))

lvl-neq : {Γ : Cx} (y : Var Γ) → eqℕ (len Γ) (lvl y) ≡ false
lvl-neq {Γ} y = trans (cong (λ z → eqℕ z (lvl y)) (sym (+-zeroʳ (len Γ))))
                      (lvl-bound y zero)

lvl-neq' : {Γ : Cx} (y : Var Γ) → eqℕ (lvl y) (len Γ) ≡ false
lvl-neq' {Γ} y = trans (cong (eqℕ (lvl y)) (sym (+-zeroʳ (len Γ))))
                       (lvl-bound' y zero)

------------------------------------------------------------------------
-- ★★★ THE THEOREM.  Comparing LEVELS decides variable equality.
------------------------------------------------------------------------
eqv-lvl : {Γ : Cx} (x y : Var Γ) → eqv x y ≡ eqℕ (lvl x) (lvl y)
eqv-lvl {Γ ∙} vz     vz     = sym (eqℕ-refl (len Γ))
eqv-lvl {Γ ∙} vz     (vs y) = sym (lvl-neq y)
eqv-lvl {Γ ∙} (vs x) vz     = sym (lvl-neq' x)
eqv-lvl {Γ ∙} (vs x) (vs y) = eqv-lvl x y
