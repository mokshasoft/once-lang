------------------------------------------------------------------------
-- OCP-0009 · LIB — `max` ON `Nat`, FROM MONUS.
--
--     max a b = a + (b ∸ a)
--
-- ★ TWO LINES, because both halves already exist.  ⚠ `Lib/Max` is NOT
--   this: that module is the MAXIMALITY predicate of a divisor (gcd's
--   spec), which shares only the word.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.NatMax where
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; Nat )
open import DirectedHoTT.Spec.Typing using ( Ctx; ⌊_⌋; _⊢_∷_ )
open import DirectedHoTT.Lib.Nat   using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Monus using ( monusTm; ⊢monus )

maxTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
maxTm a b = plusTm a (monusTm b a)

⊢max : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
       Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ maxTm a b ∷ Nat
⊢max da db = ⊢plus da (⊢monus db da)
