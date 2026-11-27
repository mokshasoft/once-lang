{-# OPTIONS --safe #-}
module tmp.GenSynNeg where
open import DirectedHoTT.Prelude using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax using ( Var; vz; vs; _∙; ε )
open import tmp.GenSyn
open import tmp.GenSynFrag
open Trav K
-- the positive twin: the bound variable survives substitution
good : sub {Γ = ε ∙} (λ _ → ref 1) (lam (var vz)) ≡ lam (var vz)
good = refl
-- FALSE: claims the bound variable is replaced; must fail on CONVERSION
bad : sub {Γ = ε ∙} (λ _ → ref 1) (lam (var vz)) ≡ lam (ref 1)
bad = refl
