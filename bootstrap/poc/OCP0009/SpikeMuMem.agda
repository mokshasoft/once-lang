------------------------------------------------------------------------
-- OCP-0009 — ★ GATE 6: THE `MuMem` KNOT, AT THE KERNEL'S ACTUAL SHAPE.
--
-- ⚠⚠ WHY A NEW GATE.  Gate 4 (`SpikeDescSigma`) and the merge
--   (`SpikeIDescSigma`) DID untie a three-way knot — but not this one.
--   They modelled the logical relation as a FUNCTION on types:
--
--       ⊩ : Ty → Tm → Set                      (the spikes)
--
--   The kernel has a DATATYPE plus a membership function that recurses on
--   the WITNESS:
--
--       data ⊩₀_ : RTy Γ → Set                 (NbEPDirDBLR)
--       _⊩₀∋_   : ⊩₀ A → RTm Γ → Set
--
--   So `Lift`'s "ambient relation" argument — which the spikes passed as a
--   plain function — HAS NO DIRECT COUNTERPART.  Membership at a `dκ`
--   field's type needs a witness, and where that witness comes from is
--   exactly the question the earlier gates did not ask.
--
-- ★★ THE DESIGN UNDER TEST: package it EXISTENTIALLY.
--
--       Mem₀ A t = Σ (⊩₀ A) (λ w → w ⊩₀∋ t)
--
--   "t is in the relation at A, for SOME witness".  That is a FUNCTION on
--   types again, so `Lift` can take it — and it is sound because the
--   kernel already proves witness-IRRELEVANCE (`irrel₀`): any two
--   witnesses at the same type agree on membership.
--
--   ⇒ if this passes, the kernel's `⊩₀Mu` needs no new well-formedness
--     plumbing, and PLAN §4 stays deferred.
--
-- Q25  ★★★ does `⊩₀` + `MuMem` + `Lift` + `Mem₀` pass POSITIVITY, with
--      `Mem₀` mentioning `⊩₀` and `⊩₀Mu`'s membership being `MuMem`?
-- Q26  ★★ does membership still TERMINATE, recursing on the witness while
--      `Lift` walks the description?
-- Q27  ★ do NEUTRALS and HEAD EXPANSION fit (the spikes' `⊩` had no
--      `SNe`/`SNRed`), i.e. does `MuMem` really mirror `NatMem`?
--
-- Self-contained: no imports.  `SN`/`SNe`/`SNRed` are stubbed to the
-- SHAPE the kernel gives them — that is all the knot can see.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeMuMem where

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

infixr 4 _,_

record _×_ (A B : Set) : Set where
  constructor _⋆_
  field
    π₁ : A
    π₂ : B
open _×_

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------------------
-- the syntax, cut to what the knot can see
------------------------------------------------------------------------

data Desc : Set
data DCon : Set
data RTy : Set
data RTm : Set

data RTy where
  base : RTy
  Unit : RTy
  Mu   : Desc → RTy

data RTm where
  ne   : RTm                    -- stands for any neutral
  unit : RTm
  pr   : RTm → RTm → RTm
  con  : ℕ → RTm → RTm
  red  : RTm → RTm              -- stands for any redex

-- ★ CLOSED descriptions, as in the kernel.
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

-- the SN layer, at the shape the kernel gives it
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

------------------------------------------------------------------------
-- ★★★ THE KNOT.
--
--   Lift  ── takes ──▶ P (recursive) and R (ambient), BOTH as plain
--                      functions — that is what keeps it declarable first
--   ⊩₀    ── a DATATYPE, as in the kernel
--   _⊩₀∋_ ── membership, by recursion on the WITNESS
--   MuMem ── mutual with both, via `Lift`
--   Mem₀  ── the existential package that turns `⊩₀`+`∋` back into a
--            FUNCTION so `Lift` can take it
------------------------------------------------------------------------

-- ★ parameterised in BOTH relations, so it mentions neither by name and
--   can be defined BEFORE the block that ties them.
Lift : DCon → (RTm → Set) → (RTy → RTm → Set) → RTm → Set
Lift dι       P R ne        = ⊥
Lift dι       P R unit      = ⊤
Lift dι       P R (pr _ _)  = ⊥
Lift dι       P R (con _ _) = ⊥
Lift dι       P R (red _)   = ⊥
Lift (dρ C)   P R ne        = ⊥
Lift (dρ C)   P R unit      = ⊥
Lift (dρ C)   P R (pr x r)  = P x × Lift C P R r        -- recursive field
Lift (dρ C)   P R (con _ _) = ⊥
Lift (dρ C)   P R (red _)   = ⊥
Lift (dκ A C) P R ne        = ⊥
Lift (dκ A C) P R unit      = ⊥
Lift (dκ A C) P R (pr x r)  = R A x × Lift C P R r      -- ★ AMBIENT
Lift (dκ A C) P R (con _ _) = ⊥
Lift (dκ A C) P R (red _)   = ⊥

data BaseMem : RTm → Set where
  bm-ne  : BaseMem ne
  bm-exp : {t t' : RTm} → SNRed t t' → BaseMem t' → BaseMem t

mutual
  -- the kernel's shape: a DATATYPE, not a function
  data ⊩₀_ : RTy → Set where
    ⊩₀base : ⊩₀ base
    ⊩₀Unit : ⊩₀ Unit
    ⊩₀Mu   : (D : Desc) → ⊩₀ (Mu D)

  -- membership recurses on the WITNESS
  _⊩₀∋_ : {A : RTy} → ⊩₀ A → RTm → Set
  ⊩₀base   ⊩₀∋ t = SN t × BaseMem t
  ⊩₀Unit   ⊩₀∋ t = SN t
  ⊩₀Mu D   ⊩₀∋ t = SN t × MuMem D t

  -- ★★ the EXISTENTIAL package — a FUNCTION on types again, which is
  --    what lets `Lift` take the ambient relation.  Sound because the
  --    kernel proves witness-irrelevance (`irrel₀`).
  Mem₀ : RTy → RTm → Set
  Mem₀ A t = Σ (⊩₀ A) (λ w → w ⊩₀∋ t)

  -- ★★★ and the knot itself.  ⚠ mirrors `NatMem` exactly: neutral,
  --     constructor, head-expansion.
  data MuMem (D : Desc) : RTm → Set where
    mm-ne  : {t : RTm} → SNe t → MuMem D t
    mm-con : (k : ℕ) (p : RTm) →
             Lift (lookupD D k) (MuMem D) Mem₀ p →
             MuMem D (con k p)
    mm-exp : {t t' : RTm} → SNRed t t' → MuMem D t' → MuMem D t

------------------------------------------------------------------------
-- ★ NON-VACUITY.  A knot that typechecks and has NO INHABITANTS would be
--   the same trap as a vacuously-discharged theorem.  So: build members,
--   including at a `dκ` field — the one the ambient relation is for.
------------------------------------------------------------------------

-- ℕ = zero (no fields) | suc (one recursive field)
NatD : Desc
NatD = dι ◃ dρ dι ◃ dnil

`zero : RTm
`zero = con zero unit

`suc : RTm → RTm
`suc n = con (suc zero) (pr n unit)

mem-zero : MuMem NatD `zero
mem-zero = mm-con zero unit tt

mem-suc : {n : RTm} → MuMem NatD n → MuMem NatD (`suc n)
mem-suc m = mm-con (suc zero) _ (m ⋆ tt)

-- and the two cases the earlier gates' `⊩` could not express at all
mem-ne : MuMem NatD ne
mem-ne = mm-ne sne-ne

mem-red : MuMem NatD (red `zero)
mem-red = mm-exp (snr `zero) mem-zero

-- ★★ THE ONE THAT MATTERS: a `dκ` field, whose membership goes through
--    the AMBIENT relation — i.e. through `Mem₀`, i.e. through the knot.
TreeD : Desc
TreeD = dκ base dι ◃ dρ (dρ dι) ◃ dnil

`leaf : RTm → RTm
`leaf v = con zero (pr v unit)

mem-leaf : {v : RTm} → SN v → BaseMem v → MuMem TreeD (`leaf v)
mem-leaf sv bv = mm-con zero _ ((⊩₀base , (sv ⋆ bv)) ⋆ tt)
--                              ^^^^^^^^^^^^^^^^^^^^ the existential
--                              package: a WITNESS plus membership at it

`node : RTm → RTm → RTm
`node l r = con (suc zero) (pr l (pr r unit))

mem-node : {l r : RTm} → MuMem TreeD l → MuMem TreeD r →
           MuMem TreeD (`node l r)
mem-node ml mr = mm-con (suc zero) _ (ml ⋆ (mr ⋆ tt))

-- ★ and a NESTED datatype: a `dκ` whose field type is another `Mu`.
WrapD : Desc
WrapD = dκ (Mu NatD) dι ◃ dnil

mem-wrap : {t : RTm} → SN t → MuMem NatD t → MuMem WrapD (con zero (pr t unit))
mem-wrap st mt = mm-con zero _ ((⊩₀Mu NatD , (st ⋆ mt)) ⋆ tt)
