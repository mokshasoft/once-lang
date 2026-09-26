------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — `depth` FOR THE SCOPED SYNTAX: the same fold as
-- `Examples/Scoped.size` at a different ALGEBRA (`Lib/TelFold.depthAlg`).
--
-- ★ That is the claim the fold was factored out to support: two measures
--   over the same description differ in an algebra, not in any
--   per-constructor work.  And `depth` is not a toy alternative to
--   `size` — where a constructor BRANCHES the two disagree (`app`'s size
--   SUMS its children, its depth MAXES them), and for a syntax the depth
--   is usually the measure you want.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.ScopedDepth where
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; Nat; El; ⌜Nat⌝; ielim )
open import DirectedHoTT.Spec.Typing using ( Ctx; ⌊_⌋; _⊢_∷_; ty-Nat; ⊢⌜Nat⌝; ⊢ielim )
open import DirectedHoTT.Lib.Sugar using ( methₗ )
open import DirectedHoTT.Lib.TelFold using ( depthAlg; foldMs; ⊢foldE )
open import DirectedHoTT.Examples.Scoped using ( TmTs; TmD; ⊢TmD; TmOK; Tm )

dpTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
dpTm n t = ielim TmD n (methₗ (foldMs depthAlg TmTs)) t

⊢dpTm : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n → Γ ⊢ dpTm n t ∷ Nat
⊢dpTm dn dt = ⊢ielim ⊢⌜Nat⌝ ⊢TmD ty-Nat (⊢foldE depthAlg ⊢⌜Nat⌝ TmOK) dn dt
