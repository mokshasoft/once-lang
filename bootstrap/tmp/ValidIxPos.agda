{-# OPTIONS --safe #-}
-- ★ INDEX-DEPENDENT interpretation over VALID indices, respecting the
--   model's law (gates 6/6b, ExistLiftPi): nothing INSIDE the ⊩₀ block may
--   reach `_⊩₀∋_` from a datatype that `_⊩₀∋_` mentions.  So:
--     · `IKPredAt` (predicates) and `IMuMem` are defined BEFORE the block,
--       parameterised by an abstract index-validity `V` — they never see ⊩₀;
--     · inside the block, `IKInterp` stores WITNESSES with ⊩₀Σ/⊩₀Π-style
--       tails: a κ field's interpretation HERE, the tail only over its
--       MEMBERS; a recursive field carries its index's VALIDITY;
--     · `⊩₀IMu` stores the index type's interpretation ⊩I (small index) and
--       a FUNCTION from valid indices to per-index witnesses;
--     · `_⊩₀∋_`'s IMu clause instantiates IMuMem at `V = ⊩I ⊩₀∋_`.
--   The Π clause is included (the lesson of ExistLiftPi).
module tmp.ValidIxPos
  (RTm RTy : Set)
  (SN : RTm → Set)
  (Unit Ix : RTy)
  (IMuT : RTm → RTy)
  (Pi : RTy → RTy → RTy)
  (Env : Set) (root : RTm → Env) (ext : Env → RTm → Env)
  (ElAt : Env → RTy)              -- a κ field's type at an environment
  (jAt  : Env → RTm)              -- a recursive field's index at an environment
  (icon' fst' snd' app' : RTm → RTm)
  where

open import Agda.Builtin.Sigma using ( Σ; _,_ )

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

data ICon : Set where
  iι : ICon
  iρ : ICon → ICon
  iκ : ICon → ICon

-- ── BEFORE the block: predicates only ─────────────────────────────────
data IKPredAt (V : RTm → Set) : Env → ICon → Set₁ where
  ikp-ι : {σ : Env} → IKPredAt V σ iι
  ikp-ρ : {σ : Env} {C : ICon} → V (jAt σ) →
          ((v : RTm) → IKPredAt V (ext σ v) C) → IKPredAt V σ (iρ C)
  ikp-κ : {σ : Env} {C : ICon} → (Q : RTm → Set) →
          ((v : RTm) → Q v → IKPredAt V (ext σ v) C) → IKPredAt V σ (iκ C)

ILift : {V : RTm → Set} {σ : Env} {C : ICon} → IKPredAt V σ C →
        ((j : RTm) → V j → RTm → Set) → RTm → Set
ILift ikp-ι P t = SN t
ILift (ikp-ρ vj k) P t =
  SN t × ((SN (fst' t) × P _ vj (fst' t)) × ILift (k (fst' t)) P (snd' t))
ILift (ikp-κ Q k) P t =
  SN t × Σ (Q (fst' t)) (λ r → ILift (k (fst' t) r) P (snd' t))

data IMuMem (V : RTm → Set) (C : ICon)
            (kp : (i : RTm) → V i → IKPredAt V (root i) C) : (i : RTm) → V i → RTm → Set where
  imm-ne   : {i : RTm} {vi : V i} {t : RTm} → SN t → IMuMem V C kp i vi t
  imm-icon : {i : RTm} {vi : V i} {p : RTm} →
             ILift (kp i vi) (IMuMem V C kp) p → IMuMem V C kp i vi (icon' p)

-- ── THE BLOCK: witnesses ──────────────────────────────────────────────
data ⊩₀_ : RTy → Set
_⊩₀∋_ : {A : RTy} → ⊩₀ A → RTm → Set
data IKInterp (⊩I : ⊩₀ Ix) : Env → ICon → Set
ikpredsOf : {⊩I : ⊩₀ Ix} {σ : Env} {C : ICon} →
            IKInterp ⊩I σ C → IKPredAt (⊩I ⊩₀∋_) σ C

data ⊩₀_ where
  ⊩₀Unit : ⊩₀ Unit
  ⊩₀Ix   : ⊩₀ Ix
  ⊩₀Π    : {F G : RTy} → (⊩F : ⊩₀ F) → ((u : RTm) → ⊩F ⊩₀∋ u → ⊩₀ G) → ⊩₀ (Pi F G)
  ⊩₀IMu  : {i : RTm} {C : ICon} (⊩I : ⊩₀ Ix) →
           ((j : RTm) → ⊩I ⊩₀∋ j → IKInterp ⊩I (root j) C) → ⊩₀ (IMuT i)

data IKInterp ⊩I where
  iki-ι : {σ : Env} → IKInterp ⊩I σ iι
  iki-ρ : {σ : Env} {C : ICon} → ⊩I ⊩₀∋ jAt σ →
          ((v : RTm) → IKInterp ⊩I (ext σ v) C) → IKInterp ⊩I σ (iρ C)
  iki-κ : {σ : Env} {C : ICon} → (w : ⊩₀ (ElAt σ)) →
          ((v : RTm) → w ⊩₀∋ v → IKInterp ⊩I (ext σ v) C) → IKInterp ⊩I σ (iκ C)

ikpredsOf iki-ι         = ikp-ι
ikpredsOf (iki-ρ vj k)  = ikp-ρ vj (λ v → ikpredsOf (k v))
ikpredsOf (iki-κ w k)   = ikp-κ (w ⊩₀∋_) (λ v r → ikpredsOf (k v r))

⊩₀Unit ⊩₀∋ t = SN t
⊩₀Ix   ⊩₀∋ t = SN t
⊩₀Π ⊩F ⊩G ⊩₀∋ t = SN t × ((u : RTm) (r : ⊩F ⊩₀∋ u) → (⊩G u r) ⊩₀∋ app' t)
-- ⚠ the ambient index must itself be VALID for the membership to be stated
⊩₀IMu {i = i} {C = C} ⊩I ki ⊩₀∋ t =
  SN t × Σ (⊩I ⊩₀∋ i) (λ vi → IMuMem (⊩I ⊩₀∋_) C (λ j vj → ikpredsOf (ki j vj)) i vi t)
