------------------------------------------------------------------------
-- OCP-0009 — ★ GATES 3+4 MERGED: THE FORM THE KERNEL WOULD USE.
--
-- Gate 3 was INDEXED without `κ`; gate 4 had `κ` and the mutual KNOT
-- without indexing.  `SCOPE-INDUCTIVE.md` §3d records the merge as
-- untested and as the remaining shape risk.  This is the merge.
--
-- ★ WHY IT IS NOT AUTOMATIC.  Gate 4's knot ties a DATATYPE (`MuMem`) to a
--   FUNCTION (`⊩`) through a third function (`Lift`).  Indexing turns
--   `MuMem` into a FAMILY and makes `Lift` apply its predicate at a
--   COMPUTED index — so the knot now has to close over an index that is
--   being computed inside it.  Either half was fine alone; that says
--   nothing about both.
--
--   ⚠ And `mu` must now carry the INDEX as well as the description
--     (`mu : Desc → I → Ty`), so `Ty` mentions `I` — which is why the
--     whole core is parameterised by the index set rather than quantifying
--     over it, keeping everything in `Set`.
--
-- Q15  ★★ does the knot still pass POSITIVITY once `MuMem` is a family and
--      `Lift` applies its predicate at a computed index?
-- Q16  ★★ does elimination still pass TERMINATION with BOTH the index
--      threaded and the `κ` case crossing to the ambient relation?
-- Q17  ★★★ does `RTm`'s OWN SHAPE instantiate it — `var` (a non-recursive
--      field), `lam` (binding), `app` — at one description?
--
-- Self-contained: no imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeIDescSigma where

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

infixr 4 _,_

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

id : {A : Set} → A → A
id x = x

------------------------------------------------------------------------
-- object-language terms, index-independent
------------------------------------------------------------------------

data Tm : Set where
  ne   : Tm
  unit : Tm
  pr   : Tm → Tm → Tm
  con  : ℕ → Tm → Tm
  red  : Tm → Tm

data _⟶_ : Tm → Tm → Set where
  β : (t : Tm) → red t ⟶ t

data BaseMem : Tm → Set where
  bm-ne   : BaseMem ne
  bm-unit : BaseMem unit
  bm-exp  : {t t' : Tm} → t ⟶ t' → BaseMem t' → BaseMem t

------------------------------------------------------------------------
-- ★ THE CORE, parameterised by the INDEX SET.
--
-- ⚠ A parameter rather than a quantified argument on purpose: `Ty` has to
--   mention `I` (in `mu : Desc → I → Ty`), and quantifying would push the
--   whole block to `Set₁`.
------------------------------------------------------------------------

module Core (I : Set) where

  mutual
    data Ty : Set where
      base : Ty
      mu   : Desc → I → Ty          -- ★ a datatype AT an index is a type

    data Con : Set where
      ι : Con                       -- done; targets the ambient index
      ρ : (I → I) → Con → Con       -- recursive field at a COMPUTED index
      κ : Ty → Con → Con            -- non-recursive field of object type

    data Desc : Set where
      []  : Desc
      _∷_ : Con → Desc → Desc

  infixr 5 _∷_

  lookup : Desc → ℕ → Maybe Con
  lookup []      _       = nothing
  lookup (C ∷ D) zero    = just C
  lookup (C ∷ D) (suc k) = lookup D k

  -- ★ parameterised in BOTH relations, and now carrying the index too
  Lift : Con → (I → Tm → Set) → (Ty → Tm → Set) → I → Tm → Set
  Lift ι       P R i ne        = ⊥
  Lift ι       P R i unit      = ⊤
  Lift ι       P R i (pr _ _)  = ⊥
  Lift ι       P R i (con _ _) = ⊥
  Lift ι       P R i (red _)   = ⊥
  Lift (ρ f C) P R i ne        = ⊥
  Lift (ρ f C) P R i unit      = ⊥
  Lift (ρ f C) P R i (pr x r)  = P (f i) x × Lift C P R i r   -- ★ computed index
  Lift (ρ f C) P R i (con _ _) = ⊥
  Lift (ρ f C) P R i (red _)   = ⊥
  Lift (κ A C) P R i ne        = ⊥
  Lift (κ A C) P R i unit      = ⊥
  Lift (κ A C) P R i (pr x r)  = R A x × Lift C P R i r       -- ★ ambient relation
  Lift (κ A C) P R i (con _ _) = ⊥
  Lift (κ A C) P R i (red _)   = ⊥

  ----------------------------------------------------------------------
  -- ★★ Q15 — THE KNOT, WITH THE INDEX.
  ----------------------------------------------------------------------

  mutual
    ⊩ : Ty → Tm → Set
    ⊩ base     t = BaseMem t
    ⊩ (mu D i) t = MuMem D i t

    data MuMem (D : Desc) : I → Tm → Set where
      mm-ne  : {i : I} → MuMem D i ne
      mm-con : {i : I} (k : ℕ) (C : Con) (p : Tm) → lookup D k ≡ just C →
               Lift C (MuMem D) ⊩ i p → MuMem D i (con k p)
      mm-exp : {i : I} {t t' : Tm} → t ⟶ t' → MuMem D i t' → MuMem D i t

  ----------------------------------------------------------------------
  -- ★★ Q16 — elimination, index threaded AND crossing to the ambient
  --    relation at every `κ`.
  ----------------------------------------------------------------------

  mutual
    elimMem : {D : Desc} {Q : I → Tm → Set} →
              ({i : I} → Q i ne) →
              ({i : I} {t t' : Tm} → t ⟶ t' → Q i t' → Q i t) →
              ({i : I} (k : ℕ) (C : Con) (p : Tm) → lookup D k ≡ just C →
                 Lift C Q ⊩ i p → Q i (con k p)) →
              {i : I} (t : Tm) → MuMem D i t → Q i t
    elimMem qn qe qc .ne        mm-ne              = qn
    elimMem qn qe qc .(con k p) (mm-con k C p e l) =
      qc k C p e (elimLift qn qe qc C _ p l)
    elimMem qn qe qc t          (mm-exp r m)       =
      qe r (elimMem qn qe qc _ m)

    elimLift : {D : Desc} {Q : I → Tm → Set} →
               ({i : I} → Q i ne) →
               ({i : I} {t t' : Tm} → t ⟶ t' → Q i t' → Q i t) →
               ({i : I} (k : ℕ) (C : Con) (p : Tm) → lookup D k ≡ just C →
                  Lift C Q ⊩ i p → Q i (con k p)) →
               (C : Con) (i : I) (p : Tm) →
               Lift C (MuMem D) ⊩ i p → Lift C Q ⊩ i p
    elimLift qn qe qc ι       i ne        ()
    elimLift qn qe qc ι       i unit      tt        = tt
    elimLift qn qe qc ι       i (pr _ _)  ()
    elimLift qn qe qc ι       i (con _ _) ()
    elimLift qn qe qc ι       i (red _)   ()
    elimLift qn qe qc (ρ f C) i ne        ()
    elimLift qn qe qc (ρ f C) i unit      ()
    elimLift qn qe qc (ρ f C) i (pr x r)  (mx , mr) =
      elimMem qn qe qc x mx , elimLift qn qe qc C i r mr
    elimLift qn qe qc (ρ f C) i (con _ _) ()
    elimLift qn qe qc (ρ f C) i (red _)   ()
    elimLift qn qe qc (κ A C) i ne        ()
    elimLift qn qe qc (κ A C) i unit      ()
    elimLift qn qe qc (κ A C) i (pr x r)  (rx , mr) =
      rx , elimLift qn qe qc C i r mr             -- ★ handed back unchanged
    elimLift qn qe qc (κ A C) i (con _ _) ()
    elimLift qn qe qc (κ A C) i (red _)   ()

------------------------------------------------------------------------
-- ★★★ Q17 — `RTm`'s OWN SHAPE, at one description.
--
--   var : Var Γ  → RTm Γ        ← a NON-RECURSIVE field        (κ)
--   lam : RTm (Γ ∙) → RTm Γ     ← BINDING: field index ≠ target (ρ suc)
--   app : RTm Γ → RTm Γ → RTm Γ ← two fields at the target      (ρ id)
--
-- Indexed by context DEPTH, which is `Cx`'s essential content here.
------------------------------------------------------------------------

open Core ℕ

LamD : Desc
LamD = κ base ι           -- var, carrying its index as a `base` value
     ∷ ρ suc ι            -- lam ★ binding
     ∷ ρ id (ρ id ι)      -- app
     ∷ []

`var : Tm → Tm
`var v = con zero (pr v unit)

`lam : Tm → Tm
`lam t = con (suc zero) (pr t unit)

`app : Tm → Tm → Tm
`app f a = con (suc (suc zero)) (pr f (pr a unit))

-- ★ the non-recursive field crosses to the AMBIENT relation
mem-var : {n : ℕ} {v : Tm} → BaseMem v → MuMem LamD n (`var v)
mem-var bv = mm-con zero (κ base ι) _ refl (bv , tt)

-- ★★ THE ONE THAT MATTERS: premise at `suc n`, conclusion at `n`
mem-lam : {n : ℕ} {t : Tm} → MuMem LamD (suc n) t → MuMem LamD n (`lam t)
mem-lam m = mm-con (suc zero) (ρ suc ι) _ refl (m , tt)

mem-app : {n : ℕ} {f a : Tm} →
          MuMem LamD n f → MuMem LamD n a → MuMem LamD n (`app f a)
mem-app mf ma = mm-con (suc (suc zero)) (ρ id (ρ id ι)) _ refl (mf , ma , tt)

-- `λ. (var ∘ var)` — closed at depth 0, body at depth 1, and the body's
-- leaves are non-recursive fields
example : MuMem LamD zero (`lam (`app (`var unit) (`var unit)))
example = mem-lam (mem-app (mem-var bm-unit) (mem-var bm-unit))

------------------------------------------------------------------------
-- ★★ AND A NESTED DATATYPE AT AN INDEX — the knot and the index at once.
--   `wrap : RTm n → Wrap n`, i.e. a `κ` whose type is `mu LamD n`.
------------------------------------------------------------------------

WrapD : ℕ → Desc
WrapD n = κ (mu LamD n) ι ∷ []

`wrap : Tm → Tm
`wrap t = con zero (pr t unit)

mem-wrap : {n : ℕ} {t : Tm} → MuMem LamD n t → MuMem (WrapD n) n (`wrap t)
mem-wrap mt = mm-con zero (κ (mu LamD _) ι) _ refl (mt , tt)

example-nested : MuMem (WrapD zero) zero (`wrap (`lam (`var unit)))
example-nested = mem-wrap (mem-lam (mem-var bm-unit))

------------------------------------------------------------------------
-- ★★ and the elimination instantiates, at both descriptions.
------------------------------------------------------------------------

data Shape : Tm → Set where
  sh-ne  : Shape ne
  sh-red : (t : Tm) → Shape (red t)
  sh-con : (k : ℕ) (p : Tm) → Shape (con k p)

ShapeAt : ℕ → Tm → Set
ShapeAt _ t = Shape t

classify : {n : ℕ} (t : Tm) → MuMem LamD n t → ShapeAt n t
classify =
  elimMem sh-ne (λ { (β t) _ → sh-red t }) (λ k C p _ _ → sh-con k p)

classify-nested : {n : ℕ} (t : Tm) → MuMem (WrapD n) n t → ShapeAt n t
classify-nested =
  elimMem sh-ne (λ { (β t) _ → sh-red t }) (λ k C p _ _ → sh-con k p)
