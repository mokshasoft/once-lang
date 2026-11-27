{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Scope using ( Cx )
open import DirectedHoTT.Spec.Syntax using ( Defs; RTm; ⌜base⌝ )
module tmp.ExpProbe (𝒮 : Defs) where
open import DirectedHoTT.Spec.Reduction 𝒮
open import DirectedHoTT.Prelude using ( ⊥ )
private variable Γ : Cx
nostep : {C : RTm Γ} → ⌜base⌝ ⟶ C → ⊥
nostep (⟶head ())
nostep (⟶cong ())
