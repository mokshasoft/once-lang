------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — `depth` FOR THE SCOPED SYNTAX, from `Lib/IDepth`.
--
-- ⚠ THE SAME FILE AS `Examples/ScopedSz` WITH ONE IMPORT CHANGED.  That
--   is the claim `Lib/IFold` was factored out to support, discharged: two
--   measures over the same description differ in an ALGEBRA, not in any
--   per-constructor work.
--
-- ★ AND `depth` IS NOT A TOY ALTERNATIVE TO `sz`.  Where a constructor
--   BRANCHES the two disagree — `app`'s size SUMS its children, its depth
--   MAXES them — so a depth bound is "this term fits in k nested
--   constructors" where a size bound is "it has k nodes".  For a syntax
--   the first is usually the measure you actually want.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.ScopedDepth where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; Nat; El; ⌜Nat⌝; ielim )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ty-El; ty-Nat; ⊢⌜Nat⌝
        ; ⊢ielim; imethsTy )
open import DirectedHoTT.Lib.IPay using ( spl-nil )
open import DirectedHoTT.Lib.IDepth using ( dpMeths; ⊢dpMeths )
open import DirectedHoTT.Examples.Scoped using ( TmD; TmWf; INat; Tm )

dpMethsTm : {Γ : Cx} → RTm Γ
dpMethsTm = dpMeths TmD

⊢dpMethsTm : {Γ : Ctx} → Γ ⊢ dpMethsTm ∷ imethsTy TmD INat Nat TmD
⊢dpMethsTm = ⊢dpMeths TmD INat zero TmD TmWf TmWf spl-nil (ty-El ⊢⌜Nat⌝)

-- ★ `depth : Tm n → Nat`, at the object level.
dpTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
dpTm n t = ielim TmD n dpMethsTm t

⊢dpTm : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n → Γ ⊢ dpTm n t ∷ Nat
⊢dpTm dn dt = ⊢ielim TmWf ty-Nat dn ⊢dpMethsTm dt
