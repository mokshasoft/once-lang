{-# OPTIONS --safe #-}
-- ExistLiftPos + a Π clause in ⊩₀ (the real model has one; the recorded
-- spike did not).  If this is rejected, the existential ILift is not
-- strictly positive against the real `_⊩₀∋_`.
module tmp.ExistLiftPiCtl
  (RTm RTy : Set)
  (SN : RTm → Set)
  (IMu Unit : RTy)
  (Pi : RTy → RTy → RTy)
  (ap fst' snd' app' : RTm → RTm)
  where

open import Agda.Builtin.Sigma using ( Σ; _,_ )

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

data ICon : Set where
  iι : ICon
  iρ : ICon → ICon
  iκ : RTy → ICon → ICon

data ⊩₀_ : RTy → Set
_⊩₀∋_ : {A : RTy} → ⊩₀ A → RTm → Set
data IMuMem : RTm → Set
ILift : ICon → RTm → Set

data ⊩₀_ where
  ⊩₀Unit : ⊩₀ Unit
  ⊩₀IMu  : ⊩₀ IMu
  ⊩₀Π    : {F G : RTy} → (⊩F : ⊩₀ F) → ((u : RTm) → ⊩F ⊩₀∋ u → ⊩₀ G) → ⊩₀ (Pi F G)

⊩₀Unit ⊩₀∋ t = SN t
⊩₀IMu  ⊩₀∋ t = SN t × IMuMem t
⊩₀Π ⊩F ⊩G ⊩₀∋ t = SN t × ((u : RTm) (r : ⊩F ⊩₀∋ u) → (⊩G u r) ⊩₀∋ app' t)

data IMuMem where
  imm-ne   : {t : RTm} → SN t → IMuMem t
  imm-icon : (C : ICon) {p : RTm} → ILift C p → IMuMem (ap p)

ILift iι       t = SN t
ILift (iρ C)   t = SN t × ((SN (fst' t) × IMuMem (fst' t)) × ILift C (snd' t))
ILift (iκ A C) t = SN t × (SN (fst' t) × ILift C (snd' t))
