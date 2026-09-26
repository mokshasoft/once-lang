{-# OPTIONS --safe #-}
-- ★ The VALID-ENVIRONMENT interpretation of a constructor telescope, with
--   the REAL relation's shape (the lesson of `ExistLiftPi`: include every
--   clause that can reach the new occurrence):
--     · `⊩₀` has a Π clause — `⊩₀∋` to the LEFT of an arrow;
--     · `IMuMem` takes PREDICATES, never `⊩₀` witnesses, and `_⊩₀∋_`'s
--       IMu clause mentions `IMuMem` (the real cycle);
--     · the witnesses live in `IKInterp`, INSIDE the ⊩₀ block, demanded
--       only at VALID environments — each tail's validity is extended by
--       the head's OWN membership, as `⊩₀Π` demands its codomain only at
--       members of its domain.
module tmp.ValidEnvPos
  (RTm RTy Env ⊤ : Set)
  (SN : RTm → Set)
  (IMu Unit : RTy)
  (Pi : RTy → RTy → RTy)
  (El : Env → RTy)                 -- a κ field's type AT an environment
  (ext : Env → RTm → Env)
  (ap fst' snd' app' : RTm → RTm)
  where

open import Agda.Builtin.Sigma using ( Σ; _,_ )

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

data ICon : Set where
  iι : ICon
  iρ : ICon → ICon
  iκ : ICon → ICon

-- the tail's validity: extended by the head's membership
extV : {V : Env → Set} → ((σ : Env) → V σ → RTm → Set) → Env → Set
extV {V} Q σ' = Σ Env (λ σ → Σ (V σ) (λ h → Σ RTm (λ v → Q σ h v)))

-- ★ predicates, for IMuMem — NOT mutual with ⊩₀
data IKPred : (Env → Set) → ICon → Set₁ where
  ikp-ι : {V : Env → Set} → IKPred V iι
  ikp-ρ : {V : Env → Set} {C : ICon} → IKPred V C → IKPred V (iρ C)
  ikp-κ : {V : Env → Set} {C : ICon} →
          (Q : (σ : Env) → V σ → RTm → Set) → IKPred (extV Q) C → IKPred V (iκ C)

ILift : {V : Env → Set} (C : ICon) → IKPred V C → (RTm → Set) →
        (σ : Env) → V σ → RTm → Set
ILift iι       ikp-ι         P σ h t = SN t
ILift (iρ C)   (ikp-ρ kp)    P σ h t = SN t × ((SN (fst' t) × P (fst' t)) × ILift C kp P σ h (snd' t))
ILift (iκ C)   (ikp-κ Q kp)  P σ h t =
  SN t × Σ (Q σ h (fst' t)) (λ q → ILift C kp P (ext σ (fst' t)) (σ , (h , (fst' t , q))) (snd' t))

data IMuMem {V : Env → Set} (C : ICon) (dp : IKPred V C) (σ : Env) (h : V σ) : RTm → Set where
  imm-ne   : {t : RTm} → SN t → IMuMem C dp σ h t
  imm-icon : {p : RTm} → ILift C dp (IMuMem C dp σ h) σ h p → IMuMem C dp σ h (ap p)

data ⊩₀_ : RTy → Set
_⊩₀∋_ : {A : RTy} → ⊩₀ A → RTm → Set
data IKInterp : (Env → Set) → ICon → Set
ikpredsOf : {V : Env → Set} {C : ICon} → IKInterp V C → IKPred V C

data ⊩₀_ where
  ⊩₀Unit : ⊩₀ Unit
  ⊩₀Π    : {F G : RTy} → (⊩F : ⊩₀ F) → ((u : RTm) → ⊩F ⊩₀∋ u → ⊩₀ G) → ⊩₀ (Pi F G)
  ⊩₀IMu  : {C : ICon} (σ : Env) → IKInterp (λ _ → ⊤) C → ⊩₀ IMu

data IKInterp where
  iki-ι : {V : Env → Set} → IKInterp V iι
  iki-ρ : {V : Env → Set} {C : ICon} → IKInterp V C → IKInterp V (iρ C)
  iki-κ : {V : Env → Set} {C : ICon} →
          (w : (σ : Env) → V σ → ⊩₀ (El σ)) →
          IKInterp (extV (λ σ h v → (w σ h) ⊩₀∋ v)) C →
          IKInterp V (iκ C)

ikpredsOf iki-ι        = ikp-ι
ikpredsOf (iki-ρ ki)   = ikp-ρ (ikpredsOf ki)
ikpredsOf (iki-κ w ki) = ikp-κ (λ σ h v → (w σ h) ⊩₀∋ v) (ikpredsOf ki)

⊩₀Unit ⊩₀∋ t = SN t
⊩₀Π ⊩F ⊩G ⊩₀∋ t = SN t × ((u : RTm) (r : ⊩F ⊩₀∋ u) → (⊩G u r) ⊩₀∋ app' t)
⊩₀IMu {C} σ ki ⊩₀∋ t = SN t × Σ ⊤ (λ h → IMuMem C (ikpredsOf ki) σ h t)
