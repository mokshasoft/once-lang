------------------------------------------------------------------------
-- OCP-0009 — ★ GATE 6c: THE KNOT, design (f) — CARRY THE PREDICATE.
--
-- ⚠ HISTORY.  Gate 6 (`SpikeMuMem`) packaged membership EXISTENTIALLY and
--   was refuted; gate 6b (`SpikeMuMem2`) had `⊩₀Mu` CARRY the κ-witnesses
--   and was ALSO refuted.  6b's error is the informative one:
--
--     MuMem occurs in _⊩₀∋_'s 4th clause (⊩₀Mu)
--     _⊩₀∋_ occurs LEFT OF AN ARROW in _⊩₀∋_'s 3rd clause  ← ⊩₀Pi
--     _⊩₀∋_ occurs in the 13th clause                      ← Lift's dκ case
--
--   i.e. `_⊩₀∋_` is INHERENTLY negative-recursive at Π.  That is fine for a
--   FUNCTION (Agda accepts `_⊩₀∋_` itself), but ANY DATATYPE mutual with it
--   inherits the negativity.  Carrying the witness does not help, because
--   `Lift` must still APPLY it.
--
--   ⇒ the constraint is structural: `MuMem` must not mention `_⊩₀∋_` AT ALL.
--     That is exactly why the kernel's `NatMem` works — it is standalone.
--
-- ★★ THE DESIGN UNDER TEST (f).  `KPred` carries the κ-field's membership
--   PREDICATE (`RTm → Set`) rather than a `⊩₀` witness.  Then `Lift` and
--   `MuMem` mention no part of the logical relation, and LEAVE THE MUTUAL
--   BLOCK ENTIRELY — defined BEFORE `⊩₀`.  The knot does not get worked
--   around; it dissolves.
--
--   Price: `KPred : Set₁`, hence `⊩₀ : RTy → Set₁`.  This is NOT barred —
--   `SCOPE-INDUCTIVE.md`'s `Set₁` row is about the DESCRIPTION GRAMMAR
--   (full `IDesc`'s `σ : (S : Set) → …`), a property of the OBJECT language,
--   not a ban on the metalanguage.  Object-level expressiveness is FULL:
--   `dκ` stays unrestricted.
--
-- ★★★ AND THE RISK, stated up front so it is not discovered by omission.
--   An UNCONSTRAINED `DPred` lets `⊩₀Mu` carry nonsense predicates, which
--   breaks `irrel₀` (witness irrelevance — two witnesses at one type must
--   agree on membership; the kernel USES it).  So the predicates must be
--   tied back to genuine witnesses by `KOk`/`DOk` — and `ko-κ`'s INDEX
--   mentions `_⊩₀∋_` again:
--
--       ko-κ : (w : ⊩₀ A) → KOk kp → KOk (kp-κ (λ t → w ⊩₀∋ t) kp)
--                                            ^^^^^^^^^^ in an INDEX
--
--   Indices are usually positivity-benign.  "Usually" is precisely the
--   reasoning that produced gate 6's wrong conclusion, so it is TESTED.
--
-- Q31 ★★★ does (f) pass POSITIVITY, with `⊩₀Pi` PRESENT and `KOk` tying
--     the predicates back to witnesses?
-- Q32 ★★ does it still TERMINATE?
-- Q33 ★★ non-vacuous — at a `dκ` field, at a NESTED `Mu`, and ★ at a
--     `dκ` whose field type is a Π (the negative constructor itself)?
-- Q34 ★★★ does `irrel₀` SURVIVE at `Mu`?  (f)'s carried predicate is what
--     puts it at risk, and the kernel USES `irrel₀`.
--
-- ✅ ALL FOUR GREEN.  Q31/Q32 first try; Q34 needs no `Lift`-as-datatype —
--    Agda tracks `π₁ l < mm-con k p l` through the computed type.
--
-- ⛔ WHAT THIS GATE DOES NOT COVER, so the clearance is not over-read:
--   · `IrrelAt` is a HYPOTHESIS here.  It is what the kernel already proves
--     for `base`/`Unit`/`Π`; the port must discharge it for real, and the
--     `Mu` case of `irrel₀` then feeds ITSELF via `irrelMu` — a knot the
--     spike does not tie because its `IrrelAt` is external.
--   · the `⊩₁` (type-level) counterpart is untouched.
--   · a JUNK-predicate guard was run out-of-tree and correctly REJECTED
--     (`SN t × BaseMem t != ⊤`), confirming `DOk` actually constrains.
--
-- Self-contained: no imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeMuMem3 where

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

record ⊤ : Set where
  constructor tt

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
-- syntax
------------------------------------------------------------------------

data Desc : Set
data DCon : Set
data RTy : Set
data RTm : Set

data RTy where
  base : RTy
  Unit : RTy
  Pi   : RTy → RTy → RTy       -- ★ non-dependent Π suffices: what matters
                               --   is the FUNCTION-SPACE premise in ⊩₀Pi
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

------------------------------------------------------------------------
-- the SN layer, at the shape the kernel gives it
--
-- ⚠ `SNe`/`BaseMem` are RICHER than gates 6/6b's, on purpose: Q33's Π-field
--   member needs `ap` of a neutral to BE neutral, which the one-constructor
--   stub could not express.  A stub must be able to express the witnesses
--   the gate claims to build.
------------------------------------------------------------------------

data SNRed : RTm → RTm → Set where
  snr : (t : RTm) → SNRed (red t) t

data SN : RTm → Set
data SNe : RTm → Set

data SNe where
  sne-ne : SNe ne
  sne-ap : {t u : RTm} → SNe t → SN u → SNe (ap t u)

data SN where
  sn-ne   : {t : RTm} → SNe t → SN t
  sn-unit : SN unit
  sn-pr   : {a b : RTm} → SN a → SN b → SN (pr a b)
  sn-con  : {k : ℕ} {p : RTm} → SN p → SN (con k p)
  sn-exp  : {t t' : RTm} → SNRed t t' → SN t' → SN t

data BaseMem : RTm → Set where
  bm-ne  : {t : RTm} → SNe t → BaseMem t
  bm-exp : {t t' : RTm} → SNRed t t' → BaseMem t' → BaseMem t

------------------------------------------------------------------------
-- ★★★ (f): THE CARRIED PREDICATES.  These mention NOTHING of `⊩₀`, so
--   everything below lives OUTSIDE the mutual block.
------------------------------------------------------------------------

data KPred : DCon → Set₁ where
  kp-ι : KPred dι
  kp-ρ : {C : DCon} → KPred C → KPred (dρ C)
  kp-κ : {A : RTy} {C : DCon} → (RTm → Set) → KPred C → KPred (dκ A C)

data DPred : Desc → Set₁ where
  dp-nil  : DPred dnil
  dp-cons : {C : DCon} {E : Desc} → KPred C → DPred E → DPred (C ◃ E)

lookupP : {D : Desc} → DPred D → (k : ℕ) → KPred (lookupD D k)
lookupP dp-nil          _       = kp-ι
lookupP (dp-cons kp _)  zero    = kp
lookupP (dp-cons _  dp) (suc k) = lookupP dp k

-- ★ `Lift` reads the κ-slot's predicate straight out of the `KPred`.
Lift : (C : DCon) → KPred C → (RTm → Set) → RTm → Set
Lift dι       kp-ι          P ne        = ⊥
Lift dι       kp-ι          P unit      = ⊤
Lift dι       kp-ι          P (pr _ _)  = ⊥
Lift dι       kp-ι          P (con _ _) = ⊥
Lift dι       kp-ι          P (ap _ _)  = ⊥
Lift dι       kp-ι          P (red _)   = ⊥
Lift (dρ C)   (kp-ρ kp)     P (pr x r)  = P x × Lift C kp P r
Lift (dρ C)   (kp-ρ kp)     P ne        = ⊥
Lift (dρ C)   (kp-ρ kp)     P unit      = ⊥
Lift (dρ C)   (kp-ρ kp)     P (con _ _) = ⊥
Lift (dρ C)   (kp-ρ kp)     P (ap _ _)  = ⊥
Lift (dρ C)   (kp-ρ kp)     P (red _)   = ⊥
Lift (dκ A C) (kp-κ Q kp)   P (pr x r)  = Q x × Lift C kp P r   -- ★ CARRIED
Lift (dκ A C) (kp-κ Q kp)   P ne        = ⊥
Lift (dκ A C) (kp-κ Q kp)   P unit      = ⊥
Lift (dκ A C) (kp-κ Q kp)   P (con _ _) = ⊥
Lift (dκ A C) (kp-κ Q kp)   P (ap _ _)  = ⊥
Lift (dκ A C) (kp-κ Q kp)   P (red _)   = ⊥

-- ★★ and `MuMem` — a STANDALONE datatype, exactly like the kernel's
--    `NatMem`.  No mutual block, no `⊩₀`, nothing to be negative about.
data MuMem (D : Desc) (dp : DPred D) : RTm → Set where
  mm-ne  : {t : RTm} → SNe t → MuMem D dp t
  mm-con : (k : ℕ) (p : RTm) →
           Lift (lookupD D k) (lookupP dp k) (MuMem D dp) p →
           MuMem D dp (con k p)
  mm-exp : {t t' : RTm} → SNRed t t' → MuMem D dp t' → MuMem D dp t

------------------------------------------------------------------------
-- ★★★ THE RELATION.  `⊩₀Pi` is PRESENT — the constructor gate 6 omitted.
--   `KOk`/`DOk` tie the carried predicates back to genuine witnesses, so
--   `irrel₀` stays reachable.  `ko-κ` puts `_⊩₀∋_` in an INDEX.
------------------------------------------------------------------------

mutual
  data ⊩₀_ : RTy → Set₁ where
    ⊩₀base : ⊩₀ base
    ⊩₀Unit : ⊩₀ Unit
    ⊩₀Pi   : {F G : RTy} → (⊩F : ⊩₀ F) →
             ((u : RTm) → ⊩F ⊩₀∋ u → ⊩₀ G) → ⊩₀ (Pi F G)
    ⊩₀Mu   : (D : Desc) (dp : DPred D) → DOk dp → ⊩₀ (Mu D)

  data KOk : {C : DCon} → KPred C → Set₁ where
    ko-ι : KOk kp-ι
    ko-ρ : {C : DCon} {kp : KPred C} → KOk kp → KOk (kp-ρ kp)
    ko-κ : {A : RTy} {C : DCon} {kp : KPred C} →
           (w : ⊩₀ A) → KOk kp → KOk (kp-κ {A = A} (λ t → w ⊩₀∋ t) kp)

  data DOk : {D : Desc} → DPred D → Set₁ where
    do-nil  : DOk dp-nil
    do-cons : {C : DCon} {E : Desc} {kp : KPred C} {dp : DPred E} →
              KOk kp → DOk dp → DOk (dp-cons kp dp)

  _⊩₀∋_ : {A : RTy} → ⊩₀ A → RTm → Set
  ⊩₀base       ⊩₀∋ t = SN t × BaseMem t
  ⊩₀Unit       ⊩₀∋ t = SN t
  ⊩₀Pi ⊩F ⊩G   ⊩₀∋ t = SN t × ((u : RTm) (r : ⊩F ⊩₀∋ u) → (⊩G u r) ⊩₀∋ ap t u)
  ⊩₀Mu D dp ok ⊩₀∋ t = SN t × MuMem D dp t
  --          ^^ ★ membership IGNORES the proof — `MuMem` needs only `dp`.
  --             That is the whole point: no dependency on the relation.

------------------------------------------------------------------------
-- ★ Q33 — NON-VACUITY.  A knot that typechecks with no inhabitants is the
--   same trap as a vacuously-discharged theorem.
------------------------------------------------------------------------

-- ℕ = zero | suc _
NatD : Desc
NatD = dι ◃ dρ dι ◃ dnil

natDP : DPred NatD
natDP = dp-cons kp-ι (dp-cons (kp-ρ kp-ι) dp-nil)

natOk : DOk natDP
natOk = do-cons ko-ι (do-cons (ko-ρ ko-ι) do-nil)

`zero : RTm
`zero = con zero unit

`suc : RTm → RTm
`suc n = con (suc zero) (pr n unit)

mem-zero : MuMem NatD natDP `zero
mem-zero = mm-con zero unit tt

mem-suc : {n : RTm} → MuMem NatD natDP n → MuMem NatD natDP (`suc n)
mem-suc m = mm-con (suc zero) _ (m ⋆ tt)

mem-ne : MuMem NatD natDP ne
mem-ne = mm-ne sne-ne

mem-red : MuMem NatD natDP (red `zero)
mem-red = mm-exp (snr `zero) mem-zero

-- ★★ a `dκ` field — membership goes through the CARRIED predicate, and
--    `ko-κ`'s index forces it to be a real witness's membership.
TreeD : Desc
TreeD = dκ base dι ◃ dρ (dρ dι) ◃ dnil

treeDP : DPred TreeD
treeDP = dp-cons (kp-κ (λ t → ⊩₀base ⊩₀∋ t) kp-ι)
                 (dp-cons (kp-ρ (kp-ρ kp-ι)) dp-nil)

treeOk : DOk treeDP
treeOk = do-cons (ko-κ ⊩₀base ko-ι) (do-cons (ko-ρ (ko-ρ ko-ι)) do-nil)

`leaf : RTm → RTm
`leaf v = con zero (pr v unit)

mem-leaf : {v : RTm} → SN v → BaseMem v → MuMem TreeD treeDP (`leaf v)
mem-leaf sv bv = mm-con zero _ ((sv ⋆ bv) ⋆ tt)

`node : RTm → RTm → RTm
`node l r = con (suc zero) (pr l (pr r unit))

mem-node : {l r : RTm} → MuMem TreeD treeDP l → MuMem TreeD treeDP r →
           MuMem TreeD treeDP (`node l r)
mem-node ml mr = mm-con (suc zero) _ (ml ⋆ (mr ⋆ tt))

-- ★★ NESTED: a `dκ` whose field type is another `Mu`.
WrapD : Desc
WrapD = dκ (Mu NatD) dι ◃ dnil

natW : ⊩₀ (Mu NatD)
natW = ⊩₀Mu NatD natDP natOk

wrapDP : DPred WrapD
wrapDP = dp-cons (kp-κ (λ t → natW ⊩₀∋ t) kp-ι) dp-nil

wrapOk : DOk wrapDP
wrapOk = do-cons (ko-κ natW ko-ι) do-nil

mem-wrap : {t : RTm} → SN t → MuMem NatD natDP t →
           MuMem WrapD wrapDP (con zero (pr t unit))
mem-wrap st mt = mm-con zero _ ((st ⋆ mt) ⋆ tt)

-- ★★★ THE ONE GATES 6/6b COULD NOT POSE AT ALL: a `dκ` whose field type is
--     a Π — so the member's κ-slot obligation is discharged AT THE NEGATIVE
--     CONSTRUCTOR.  If (f) were secretly vacuous at function fields, this is
--     where it would show.
FunD : Desc
FunD = dκ (Pi base base) dι ◃ dnil

piW : ⊩₀ (Pi base base)
piW = ⊩₀Pi ⊩₀base (λ u r → ⊩₀base)

funDP : DPred FunD
funDP = dp-cons (kp-κ (λ t → piW ⊩₀∋ t) kp-ι) dp-nil

funOk : DOk funDP
funOk = do-cons (ko-κ piW ko-ι) do-nil

-- a genuine member of `piW`: the neutral, applied stays neutral
piW-ne : piW ⊩₀∋ ne
piW-ne = sn-ne sne-ne
       ⋆ (λ u r → sn-ne (sne-ap sne-ne (π₁ r)) ⋆ bm-ne (sne-ap sne-ne (π₁ r)))

mem-fun : MuMem FunD funDP (con zero (pr ne unit))
mem-fun = mm-con zero _ (piW-ne ⋆ tt)

------------------------------------------------------------------------
-- ★★★ Q34 — `irrel₀` AT `Mu`.  THE RISK (f) CREATES, discharged here.
--
--   (f) lets `⊩₀Mu` carry a `DPred`, so two witnesses at ONE type could in
--   principle carry DIFFERENT predicates and disagree on membership — which
--   would break `irrel₀`, WHICH THE KERNEL USES.  `DOk` is what stops that:
--   `ko-κ` pins every κ-slot to `λ t → w ⊩₀∋ t` for some real `w : ⊩₀ A`,
--   so two `DOk`s over one `D` differ ONLY by the choice of witness — and
--   `IrrelAt` (the ambient irrelevance the kernel already proves for the
--   pre-existing formers) collapses exactly that difference.
--
--   ⚠ Proved BEFORE the kernel port, not after: this is the one property
--     whose failure would make the `Set₁` port wasted work.
------------------------------------------------------------------------

lookupOk : {D : Desc} {dp : DPred D} → DOk dp → (k : ℕ) → KOk (lookupP dp k)
lookupOk do-nil         _       = ko-ι
lookupOk (do-cons o _)  zero    = o
lookupOk (do-cons _ dk) (suc k) = lookupOk dk k

-- the ambient irrelevance, taken as a HYPOTHESIS: it is what the kernel
-- already has for `base`/`Unit`/`Π`, and is not this gate's business.
IrrelAt : Set₁
IrrelAt = {A : RTy} (w₁ w₂ : ⊩₀ A) (t : RTm) → w₁ ⊩₀∋ t → w₂ ⊩₀∋ t

mutual
  irrelMu : IrrelAt → {D : Desc} {dp₁ dp₂ : DPred D} →
            DOk dp₁ → DOk dp₂ → {t : RTm} →
            MuMem D dp₁ t → MuMem D dp₂ t
  irrelMu ir d₁ d₂ (mm-ne s)      = mm-ne s
  irrelMu ir d₁ d₂ (mm-exp r m)   = mm-exp r (irrelMu ir d₁ d₂ m)
  irrelMu ir d₁ d₂ (mm-con k p l) =
    mm-con k p (liftIrrel ir d₁ d₂ (lookupOk d₁ k) (lookupOk d₂ k) p l)

  -- ★ recurses on the `KOk` (i.e. on the DCon); the κ case is the ONLY
  --   place the ambient hypothesis is used — exactly where (f) put the risk.
  liftIrrel : IrrelAt → {D : Desc} {dp₁ dp₂ : DPred D} →
              DOk dp₁ → DOk dp₂ →
              {C : DCon} {kp₁ kp₂ : KPred C} → KOk kp₁ → KOk kp₂ →
              (p : RTm) →
              Lift C kp₁ (MuMem D dp₁) p → Lift C kp₂ (MuMem D dp₂) p
  liftIrrel ir d₁ d₂ ko-ι ko-ι unit      l = tt
  liftIrrel ir d₁ d₂ ko-ι ko-ι ne        l = ⊥-elim l
  liftIrrel ir d₁ d₂ ko-ι ko-ι (pr _ _)  l = ⊥-elim l
  liftIrrel ir d₁ d₂ ko-ι ko-ι (con _ _) l = ⊥-elim l
  liftIrrel ir d₁ d₂ ko-ι ko-ι (ap _ _)  l = ⊥-elim l
  liftIrrel ir d₁ d₂ ko-ι ko-ι (red _)   l = ⊥-elim l
  liftIrrel ir d₁ d₂ (ko-ρ o₁) (ko-ρ o₂) (pr x r) l =
    irrelMu ir d₁ d₂ (π₁ l) ⋆ liftIrrel ir d₁ d₂ o₁ o₂ r (π₂ l)
  liftIrrel ir d₁ d₂ (ko-ρ o₁) (ko-ρ o₂) ne        l = ⊥-elim l
  liftIrrel ir d₁ d₂ (ko-ρ o₁) (ko-ρ o₂) unit      l = ⊥-elim l
  liftIrrel ir d₁ d₂ (ko-ρ o₁) (ko-ρ o₂) (con _ _) l = ⊥-elim l
  liftIrrel ir d₁ d₂ (ko-ρ o₁) (ko-ρ o₂) (ap _ _)  l = ⊥-elim l
  liftIrrel ir d₁ d₂ (ko-ρ o₁) (ko-ρ o₂) (red _)   l = ⊥-elim l
  liftIrrel ir d₁ d₂ (ko-κ w₁ o₁) (ko-κ w₂ o₂) (pr x r) l =
    ir w₁ w₂ x (π₁ l) ⋆ liftIrrel ir d₁ d₂ o₁ o₂ r (π₂ l)
  --  ^^^^^^^^^^^^^^^ THE κ SLOT: two witnesses, one type, collapsed
  liftIrrel ir d₁ d₂ (ko-κ w₁ o₁) (ko-κ w₂ o₂) ne        l = ⊥-elim l
  liftIrrel ir d₁ d₂ (ko-κ w₁ o₁) (ko-κ w₂ o₂) unit      l = ⊥-elim l
  liftIrrel ir d₁ d₂ (ko-κ w₁ o₁) (ko-κ w₂ o₂) (con _ _) l = ⊥-elim l
  liftIrrel ir d₁ d₂ (ko-κ w₁ o₁) (ko-κ w₂ o₂) (ap _ _)  l = ⊥-elim l
  liftIrrel ir d₁ d₂ (ko-κ w₁ o₁) (ko-κ w₂ o₂) (red _)   l = ⊥-elim l

