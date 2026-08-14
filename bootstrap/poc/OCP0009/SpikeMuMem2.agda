------------------------------------------------------------------------
-- OCP-0009 — ★ GATE 6b: THE KNOT, WITH `⊩₀Π` PRESENT.
--
-- ⚠⚠⚠ GATE 6 WAS REFUTED BY THE KERNEL, AND THE REASON IS A SPIKE DEFECT.
--
--   Gate 6 modelled `⊩₀` with only `base`, `Unit`, `Mu`.  It had NO
--   `⊩₀Π` — and `⊩₀Π` is the constructor that carries
--
--       ((u : RTm Γ) → ⊩F ⊩₀∋ u → ⊩₀ …)
--                      ^^^^^^^^^ MEMBERSHIP, LEFT OF AN ARROW
--
--   i.e. the one NEGATIVE occurrence of `_⊩₀∋_` in the whole datatype.
--   Gate 6's existential `Mem₀ A t = Σ (⊩₀ A) (λ w → w ⊩₀∋ t)` closed a
--   cycle through it:
--
--     MuMem ▸ Lift ▸ Mem₀ ▸ ⊩₀ ▸ ⊩₀Π(negative) ▸ _⊩₀∋_ ▸ ⊩₀Mu ▸ MuMem
--
--   The kernel rejects it: `NotStrictlyPositive`.
--
--   ⇒ I SIMPLIFIED AWAY THE EXACT CONSTRUCTOR THAT BREAKS THE DESIGN, and
--     then drew a PLANNING conclusion from the simplified model ("§4 stays
--     deferred").  A spike must keep every feature the property under test
--     could interact with — for POSITIVITY that means every constructor of
--     the datatype, especially the ones with function-space premises.
--
-- ★★ THE FIX UNDER TEST — the kernel's OWN idiom.  `⊩₀Π` does not LOOK UP
--   `⊩₀ F`; it CARRIES it.  So `⊩₀Mu` should carry its `dκ` fields'
--   interpretations too, and `MuMem`/`Lift` should read them from there
--   instead of reaching back through `⊩₀`.  Then `Mem₀` disappears and
--   the cycle never forms.
--
--   ⇒ this makes DESCRIPTION WELL-FORMEDNESS SEMANTIC and a PREREQUISITE
--     (PLAN §4 moves before §5) — the opposite of gate 6's conclusion.
--
-- Q28  ★★★ with `⊩₀Π` PRESENT, does carrying the κ-interpretations pass
--      POSITIVITY where the existential did not?
-- Q29  ★★ does it still terminate, and do neutrals/expansion still fit?
-- Q30  ★ is it still non-vacuous at a `dκ` field and at a NESTED `Mu`?
--
-- Self-contained: no imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeMuMem2 where

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

infixr 4 _,_

record _×_ (A B : Set) : Set where
  constructor _⋆_
  field
    π₁ : A
    π₂ : B

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------------------
-- syntax
------------------------------------------------------------------------

data Desc : Set
data DCon : Set
data RTy : Set
data RTm : Set

data RTy where
  base : RTy
  Unit : RTy
  Pi   : RTy → RTy → RTy            -- ★ NON-dependent Π is enough: what
                                    --   matters is the FUNCTION-SPACE
                                    --   premise in ⊩₀Pi below
  Mu   : Desc → RTy

data RTm where
  ne   : RTm
  unit : RTm
  pr   : RTm → RTm → RTm
  con  : ℕ → RTm → RTm
  ap   : RTm → RTm → RTm
  red  : RTm → RTm

data DCon where
  dι : DCon
  dρ : DCon → DCon
  dκ : RTy → DCon → DCon

data Desc where
  dnil : Desc
  _◃_  : DCon → Desc → Desc

infixr 5 _◃_

lookupD : Desc → ℕ → DCon
lookupD dnil    _       = dι
lookupD (C ◃ D) zero    = C
lookupD (C ◃ D) (suc k) = lookupD D k

data SNRed : RTm → RTm → Set where
  snr : (t : RTm) → SNRed (red t) t

data SNe : RTm → Set where
  sne-ne : SNe ne

data SN : RTm → Set where
  sn-ne   : {t : RTm} → SNe t → SN t
  sn-unit : SN unit
  sn-pr   : {a b : RTm} → SN a → SN b → SN (pr a b)
  sn-con  : {k : ℕ} {p : RTm} → SN p → SN (con k p)
  sn-exp  : {t t' : RTm} → SNRed t t' → SN t' → SN t

data BaseMem : RTm → Set where
  bm-ne  : BaseMem ne
  bm-exp : {t t' : RTm} → SNRed t t' → BaseMem t' → BaseMem t

------------------------------------------------------------------------
-- ★★★ THE KNOT, design (a): the WITNESS CARRIES its κ-interpretations.
------------------------------------------------------------------------

mutual
  data ⊩₀_ : RTy → Set where
    ⊩₀base : ⊩₀ base
    ⊩₀Unit : ⊩₀ Unit
    -- ⚠⚠ THE CONSTRUCTOR GATE 6 OMITTED.  `⊩₀Pi` carries a function whose
    --    DOMAIN is a membership — the one negative occurrence of `_⊩₀∋_`,
    --    and the reason gate 6's existential was rejected.
    ⊩₀Pi   : {F G : RTy} → (⊩F : ⊩₀ F) →
             ((u : RTm) → ⊩F ⊩₀∋ u → ⊩₀ G) → ⊩₀ (Pi F G)
    -- ★ and `Mu` CARRIES its description's κ-interpretations, exactly as
    --   `⊩₀Pi` carries `⊩F`.  No reaching back through `⊩₀`.
    ⊩₀Mu   : (D : Desc) → DInterp D → ⊩₀ (Mu D)

  -- the κ-interpretations of ONE constructor's field list
  data KInterp : DCon → Set where
    ki-ι : KInterp dι
    ki-ρ : {C : DCon} → KInterp C → KInterp (dρ C)
    ki-κ : {A : RTy} {C : DCon} → ⊩₀ A → KInterp C → KInterp (dκ A C)

  -- …and of a whole description
  data DInterp : Desc → Set where
    di-nil  : DInterp dnil
    di-cons : {C : DCon} {E : Desc} →
              KInterp C → DInterp E → DInterp (C ◃ E)

  _⊩₀∋_ : {A : RTy} → ⊩₀ A → RTm → Set
  ⊩₀base       ⊩₀∋ t = SN t × BaseMem t
  ⊩₀Unit       ⊩₀∋ t = SN t
  ⊩₀Pi ⊩F ⊩G   ⊩₀∋ t = SN t × ((u : RTm) (r : ⊩F ⊩₀∋ u) → (⊩G u r) ⊩₀∋ ap t u)
  ⊩₀Mu D di    ⊩₀∋ t = SN t × MuMem D di t

  -- ★ `Lift` now reads the κ-witness FROM the `KInterp` it is handed —
  --   no ambient-relation parameter, hence no `Mem₀`, hence no cycle.
  Lift : (C : DCon) → KInterp C → (RTm → Set) → RTm → Set
  Lift dι       ki-ι        P ne        = ⊥
  Lift dι       ki-ι        P unit      = ⊤
  Lift dι       ki-ι        P (pr _ _)  = ⊥
  Lift dι       ki-ι        P (con _ _) = ⊥
  Lift dι       ki-ι        P (ap _ _)  = ⊥
  Lift dι       ki-ι        P (red _)   = ⊥
  Lift (dρ C)   (ki-ρ ki)   P (pr x r)  = P x × Lift C ki P r
  Lift (dρ C)   (ki-ρ ki)   P ne        = ⊥
  Lift (dρ C)   (ki-ρ ki)   P unit      = ⊥
  Lift (dρ C)   (ki-ρ ki)   P (con _ _) = ⊥
  Lift (dρ C)   (ki-ρ ki)   P (ap _ _)  = ⊥
  Lift (dρ C)   (ki-ρ ki)   P (red _)   = ⊥
  Lift (dκ A C) (ki-κ w ki) P (pr x r)  = (w ⊩₀∋ x) × Lift C ki P r
  Lift (dκ A C) (ki-κ w ki) P ne        = ⊥
  Lift (dκ A C) (ki-κ w ki) P unit      = ⊥
  Lift (dκ A C) (ki-κ w ki) P (con _ _) = ⊥
  Lift (dκ A C) (ki-κ w ki) P (ap _ _)  = ⊥
  Lift (dκ A C) (ki-κ w ki) P (red _)   = ⊥

  lookupI : {D : Desc} → DInterp D → (k : ℕ) → KInterp (lookupD D k)
  lookupI di-nil          _       = ki-ι
  lookupI (di-cons ki _)  zero    = ki
  lookupI (di-cons _  dj) (suc k) = lookupI dj k

  data MuMem (D : Desc) (di : DInterp D) : RTm → Set where
    mm-ne  : {t : RTm} → SNe t → MuMem D di t
    mm-con : (k : ℕ) (p : RTm) →
             Lift (lookupD D k) (lookupI di k) (MuMem D di) p →
             MuMem D di (con k p)
    mm-exp : {t t' : RTm} → SNRed t t' → MuMem D di t' → MuMem D di t
