{-# OPTIONS --safe #-}
-- SPIKE-LEVITATION S0 — STRATIFICATION.  Descriptions are TERMS; their
-- meaning is their MEMBERSHIP in the LARGE type `IDescT` (level 1), which
-- may store ⊩₀ witnesses; the small `IMu D i` is interpreted in the ⊩₀ block
-- from a LEVEL-0 COPY (`IKInterp`), with a separate NEUTRAL clause.
-- Every clause that can reach a new occurrence is included: Π at BOTH levels
-- (∋ to the left of an arrow), neutral cases, member-indexed tails.
module tmp.LevS0Ctl
  (RTm RTy : Set)
  (SN Ne : RTm → Set)
  (_⟶*_ : RTm → RTm → Set)
  (Unit U : RTy) (El : RTm → RTy) (Pi : RTy → RTy → RTy)
  (IMuT : RTm → RTm → RTy)            -- IMu D i
  (IDescT : RTm → RTy)                -- descriptions with index code cI
  -- description terms
  (dnil : RTm) (dcons : RTm → RTm → RTm)
  (dι : RTm) (dσ : RTm → RTm → RTm) (dρ : RTm → RTm → RTm)
  (app' fst' snd' icon' : RTm → RTm) (app2 : RTm → RTm → RTm)
  (lookupC : RTm → RTm → RTm)         -- the k-th constructor of D
  where

open import Agda.Builtin.Sigma using ( Σ; _,_ )

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

-- ═══ LEVEL 0 ═══
data ⊩₀_ : RTy → Set
_⊩₀∋_ : {A : RTy} → ⊩₀ A → RTm → Set
data IKInterp {cI : RTm} (⊩I : ⊩₀ (El cI)) : RTm → Set
ILiftW : {cI : RTm} {⊩I : ⊩₀ (El cI)} {C : RTm} → IKInterp ⊩I C → ((j : RTm) → ⊩I ⊩₀∋ j → RTm → Set) → RTm → Set
data IMuMemW {cI : RTm} (⊩I : ⊩₀ (El cI)) (D : RTm)
             (ki : (j : RTm) → ⊩I ⊩₀∋ j → (k : RTm) → IKInterp ⊩I (lookupC D j)) : (i : RTm) → ⊩I ⊩₀∋ i → RTm → Set

data ⊩₀_ where
  ⊩₀Unit : ⊩₀ Unit
  ⊩₀El   : {c : RTm} → Ne c → ⊩₀ (El c)                -- neutral small type
  ⊩₀Π    : {F G : RTy} → (⊩F : ⊩₀ F) → ((u : RTm) → ⊩F ⊩₀∋ u → ⊩₀ G) → ⊩₀ (Pi F G)
  -- ★ a family over a CANONICAL-ENOUGH description: the index type's
  --   interpretation and, for every VALID index and every tag, the level-0
  --   telescope interpretation of that constructor.
  ⊩₀IMu  : {D i cI : RTm} (⊩I : ⊩₀ (El cI)) →
           ((j : RTm) → ⊩I ⊩₀∋ j → (k : RTm) → IKInterp ⊩I (lookupC D j)) →
           ⊩₀ (IMuT D i)
  -- ★ a family over a NEUTRAL description: nothing to interpret.
  ⊩₀IMuNe : {D i : RTm} → Ne D → ⊩₀ (IMuT D i)

data IKInterp ⊩I where
  iki-ne : {C : RTm} → Ne C → IKInterp ⊩I C
  iki-ι  : {C : RTm} → C ⟶* dι → IKInterp ⊩I C
  iki-ρ  : {C j C' : RTm} → C ⟶* dρ j C' → ⊩I ⊩₀∋ j → IKInterp ⊩I C' → IKInterp ⊩I C
  iki-σ  : {C S b : RTm} → C ⟶* dσ S b → (w : ⊩₀ (El S)) →
           ((v : RTm) → w ⊩₀∋ v → IKInterp ⊩I (app2 b v)) → IKInterp ⊩I C

ILiftW (iki-ne n) P t = SN t
ILiftW (iki-ι r) P t = SN t
ILiftW (iki-ρ {j = j} r vj k) P t = SN t × ((SN (fst' t) × P j vj (fst' t)) × ILiftW k P (snd' t))
ILiftW (iki-σ r w k) P t = SN t × Σ (w ⊩₀∋ fst' t) (λ q → ILiftW (k (fst' t) q) P (snd' t))

data IMuMemW ⊩I D ki where
  imm-ne   : {i : RTm} {vi : ⊩I ⊩₀∋ i} {t : RTm} → SN t → IMuMemW ⊩I D ki i vi t
  imm-icon : {i : RTm} {vi : ⊩I ⊩₀∋ i} {k p : RTm} →
             ILiftW (ki i vi k) (IMuMemW ⊩I D ki) p → IMuMemW ⊩I D ki i vi (icon' p)

⊩₀Unit ⊩₀∋ t = SN t
⊩₀El n ⊩₀∋ t = SN t
⊩₀Π ⊩F ⊩G ⊩₀∋ t = SN t × ((u : RTm) (r : ⊩F ⊩₀∋ u) → (⊩G u r) ⊩₀∋ app' t)
⊩₀IMu {D = D} {i = i} ⊩I ki ⊩₀∋ t =
  SN t × Σ (⊩I ⊩₀∋ i) (λ vi → IMuMemW ⊩I D ki i vi t)
⊩₀IMuNe n ⊩₀∋ t = SN t

-- ═══ LEVEL 1 (⊩₀ is complete; ⊩₀ witnesses may be STORED freely) ═══
data ⊩₁_ : RTy → Set
_⊩₁∋_ : {A : RTy} → ⊩₁ A → RTm → Set
-- the MEMBERSHIP of a description in `IDescT cI`: canonical or neutral,
-- constructor by constructor, codes carrying their ⊩₀ interpretations.
data ConMem {cI : RTm} (⊩I : ⊩₀ (El cI)) : RTm → Set where
  cm-ne : {C : RTm} → Ne C → ConMem ⊩I C
  cm-ι  : {C : RTm} → C ⟶* dι → ConMem ⊩I C
  cm-ρ  : {C j C' : RTm} → C ⟶* dρ j C' → ⊩I ⊩₀∋ j → ConMem ⊩I C' → ConMem ⊩I C
  cm-σ  : {C S b : RTm} → C ⟶* dσ S b → (w : ⊩₀ (El S)) →
          ((v : RTm) → w ⊩₀∋ v → ConMem ⊩I (app2 b v)) → ConMem ⊩I C

data ⊩₁_ where
  ⊩₁U     : ⊩₁ U
  ⊩₁Π     : {F G : RTy} → (⊩F : ⊩₁ F) → ((u : RTm) → ⊩F ⊩₁∋ u → ⊩₁ G) → ⊩₁ (Pi F G)
  ⊩₁IDesc : {cI : RTm} → ⊩₀ (El cI) → ⊩₁ (IDescT cI)

⊩₁U ⊩₁∋ c = SN c × (⊩₀ (El c))
⊩₁Π ⊩F ⊩G ⊩₁∋ t = SN t × ((u : RTm) (r : ⊩F ⊩₁∋ u) → (⊩G u r) ⊩₁∋ app' t)
-- ★ a member description: at every VALID index, every constructor is a member
⊩₁IDesc ⊩I ⊩₁∋ D = SN D × ((j : RTm) → ⊩I ⊩₀∋ j → (k : RTm) → ConMem ⊩I (lookupC D j))

-- ═══ THE BRIDGE: a member description's meaning, copied down to level 0 ═══
toIK : {cI : RTm} {⊩I : ⊩₀ (El cI)} {C : RTm} → ConMem ⊩I C → IKInterp ⊩I C
toIK (cm-ne n)      = iki-ne n
toIK (cm-ι r)       = iki-ι r
toIK (cm-ρ r vj k)  = iki-ρ r vj (toIK k)
toIK (cm-σ r w k)   = iki-σ r w (λ v q → toIK (k v q))

-- ⇒ what `fund`'s `ty-IMu`/`⊢⌜IMu⌝` case would do with `⊢ D ∷ IDescT cI`:
imuSem : {cI D i : RTm} (⊩I : ⊩₀ (El cI)) → (⊩₁IDesc ⊩I) ⊩₁∋ D → ⊩₀ (IMuT D i)
imuSem ⊩I (sn , m) = ⊩₀IMu ⊩I (λ j vj k → toIK (m j vj k))
