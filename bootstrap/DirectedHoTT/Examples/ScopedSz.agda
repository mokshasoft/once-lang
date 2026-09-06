------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ `Lib/ISz` AT A SECOND DESCRIPTION.
--
-- `Lib/ISz` was written for the 53-constructor knot, but nothing in it
-- mentions the knot: `szMeths : IDesc → RTm Γ` is generic in the
-- description AND in the index type.  This file is the check that that
-- is true rather than merely plausible — the same library, at
-- `Examples/Scoped`'s three-constructor syntax, whose index is
-- `El ⌜Nat⌝` and not a pair.
--
-- ⚠ IT DOES NOT REPRODUCE `Scoped.msize` ON THE NOSE, and the difference
--   is worth knowing.  The library's fold emits a trailing empty sum, so
--   `lam`'s method is `suc (f + 0)` where the hand-written one is
--   `suc f`.  Same value, one redundant `plusTm _ nzero` per
--   constructor — which costs REDUCTION steps, not type-checking, and
--   so will show up in the agreement proof rather than here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.ScopedSz where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; Nat; El; ⌜Nat⌝; ielim )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ty-El; ty-Nat; ⊢⌜Nat⌝
        ; ⊢ielim; imethsTy )
open import DirectedHoTT.Lib.IPay using ( spl-nil )
open import DirectedHoTT.Lib.ISz using ( szMeths; ⊢szMeths )
open import DirectedHoTT.Examples.Scoped using ( TmD; TmWf; INat; Tm )

szMethsTm : {Γ : Cx} → RTm Γ
szMethsTm = szMeths TmD

⊢szMethsTm : {Γ : Ctx} → Γ ⊢ szMethsTm ∷ imethsTy TmD INat Nat TmD
⊢szMethsTm = ⊢szMeths TmD INat zero TmD TmWf TmWf spl-nil (ty-El ⊢⌜Nat⌝)

-- ★ `size` for the scoped λ-calculus, from the SAME library that does
--   the 53-constructor knot.
szTmScoped : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
szTmScoped n t = ielim TmD n szMethsTm t

⊢szTmScoped : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
              Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n → Γ ⊢ szTmScoped n t ∷ Nat
⊢szTmScoped dn dt = ⊢ielim TmWf ty-Nat dn ⊢szMethsTm dt
