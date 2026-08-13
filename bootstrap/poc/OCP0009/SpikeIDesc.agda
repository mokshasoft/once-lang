------------------------------------------------------------------------
-- OCP-0009 — ★ GATE 3: INDEXED DESCRIPTIONS.
--
-- Gates 1 (`SpikeDesc`) and 2 (`SpikeDescTm`) cleared the logical-relation
-- shape, but both were NON-INDEXED.  The dogfooding target is
-- `RTm : Cx → Set`, and `SCOPE-INDUCTIVE.md` records indexing as the
-- biggest remaining unknown.
--
-- ★★ WHAT INDEXING ACTUALLY REQUIRES, and it is less than full `IDesc`.
--   The essential content is that a constructor's recursive field may sit
--   at a DIFFERENT index from its target — that is precisely what BINDING
--   is:
--
--       lam : RTm (Γ ∙) → RTm Γ        field at `Γ ∙`, target `Γ`
--       app : RTm Γ → RTm Γ → RTm Γ    fields at the target index
--
--   So `ρ` must carry an index FUNCTION, not a fixed index:
--
--       ρ : (I → I) → Con I → Con I
--
--   ⇒ `lam` is `ρ (_∙) ι` and `app` is `ρ id (ρ id ι)`.
--
--   ★ AND THAT KEEPS `Con` SMALL.  `(I → I)` is a `Set` when `I` is, so
--     `Con I : Set` — no jump to `Set₁`, which full `IDesc`'s
--     `σ : (S : Set) → (S → IDesc I) → IDesc I` would force.
--
-- THE THREE QUESTIONS:
--   Q8   ★ does the nesting survive when the predicate becomes an INDEXED
--        family `I → Tm → Set` and `Lift` applies it at a COMPUTED index?
--   Q9   ★★ does the elimination still pass TERMINATION with the index
--        threaded through both members of the mutual block?
--   Q10  does a genuinely BINDING datatype instantiate it — a constructor
--        whose field index differs from its target?
--
-- ⛔ WHAT THIS STILL DOES NOT COVER: `σ` — a constructor carrying a VALUE
--   the rest of the description depends on.  `RTm`'s `var : Var Γ → RTm Γ`
--   needs it, and in a syntactic setting it is genuinely harder, because
--   the carried value is an open TERM whose value is not known.  Recorded,
--   not solved.
--
-- Self-contained: no imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeIDesc where

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
-- INDEXED DESCRIPTIONS.  ★ `ρ` carries an index FUNCTION — that is the
-- whole difference from gate 2, and it is what binding needs.
------------------------------------------------------------------------

data Con (I : Set) : Set where
  ι : Con I                        -- done; targets the ambient index
  ρ : (I → I) → Con I → Con I      -- a recursive field at `f i`, then more

data Desc (I : Set) : Set where
  []  : Desc I
  _∷_ : Con I → Desc I → Desc I

infixr 5 _∷_

lookup : {I : Set} → Desc I → ℕ → Maybe (Con I)
lookup []      _       = nothing
lookup (C ∷ D) zero    = just C
lookup (C ∷ D) (suc k) = lookup D k

------------------------------------------------------------------------
-- object-language terms — unchanged from gate 2
------------------------------------------------------------------------

data Tm : Set where
  ne   : Tm
  unit : Tm
  pr   : Tm → Tm → Tm
  con  : ℕ → Tm → Tm
  red  : Tm → Tm

data _⟶_ : Tm → Tm → Set where
  β : (t : Tm) → red t ⟶ t

------------------------------------------------------------------------
-- ★ Q8 — the lifting, now INDEXED.  The predicate is `I → Tm → Set` and
--   each recursive field is required at the COMPUTED index `f i`.
------------------------------------------------------------------------

Lift : {I : Set} → Con I → (I → Tm → Set) → I → Tm → Set
Lift ι       P i ne        = ⊥
Lift ι       P i unit      = ⊤
Lift ι       P i (pr _ _)  = ⊥
Lift ι       P i (con _ _) = ⊥
Lift ι       P i (red _)   = ⊥
Lift (ρ f C) P i ne        = ⊥
Lift (ρ f C) P i unit      = ⊥
Lift (ρ f C) P i (pr x r)  = P (f i) x × Lift C P i r    -- ★ the computed index
Lift (ρ f C) P i (con _ _) = ⊥
Lift (ρ f C) P i (red _)   = ⊥

-- ★★ THE GATE.  `MuMem D : I → Tm → Set` is now a FAMILY, used nested
--    inside its own declaration through the function-defined `Lift`.
data MuMem {I : Set} (D : Desc I) : I → Tm → Set where
  mm-ne  : {i : I} → MuMem D i ne
  mm-con : {i : I} (k : ℕ) (C : Con I) (p : Tm) → lookup D k ≡ just C →
           Lift C (MuMem D) i p → MuMem D i (con k p)
  mm-exp : {i : I} {t t' : Tm} → t ⟶ t' → MuMem D i t' → MuMem D i t

------------------------------------------------------------------------
-- ★★ Q9 — elimination, with the index threaded through the mutual block.
------------------------------------------------------------------------

mutual
  elimMem : {I : Set} {D : Desc I} {Q : I → Tm → Set} →
            ({i : I} → Q i ne) →
            ({i : I} {t t' : Tm} → t ⟶ t' → Q i t' → Q i t) →
            ({i : I} (k : ℕ) (C : Con I) (p : Tm) → lookup D k ≡ just C →
               Lift C Q i p → Q i (con k p)) →
            {i : I} (t : Tm) → MuMem D i t → Q i t
  elimMem qn qe qc .ne        mm-ne              = qn
  elimMem qn qe qc .(con k p) (mm-con k C p e l) =
    qc k C p e (elimLift qn qe qc C _ p l)
  elimMem qn qe qc t          (mm-exp r m)       =
    qe r (elimMem qn qe qc _ m)

  elimLift : {I : Set} {D : Desc I} {Q : I → Tm → Set} →
             ({i : I} → Q i ne) →
             ({i : I} {t t' : Tm} → t ⟶ t' → Q i t' → Q i t) →
             ({i : I} (k : ℕ) (C : Con I) (p : Tm) → lookup D k ≡ just C →
                Lift C Q i p → Q i (con k p)) →
             (C : Con I) (i : I) (p : Tm) →
             Lift C (MuMem D) i p → Lift C Q i p
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

------------------------------------------------------------------------
-- ★ Q10 — A GENUINELY BINDING DATATYPE.
--
--   A mini λ-syntax indexed by context DEPTH, which is `RTm`'s own shape:
--
--       lam : Tm (suc n) → Tm n      ← ★ field index ≠ target index
--       app : Tm n → Tm n → Tm n
------------------------------------------------------------------------

LamD : Desc ℕ
LamD = ρ suc ι            -- lam
     ∷ ρ id (ρ id ι)      -- app
     ∷ []

`lam : Tm → Tm
`lam t = con zero (pr t unit)

`app : Tm → Tm → Tm
`app f a = con (suc zero) (pr f (pr a unit))

-- ★★ THE ONE THAT MATTERS: the premise is at `suc n`, the conclusion at
--    `n`.  That is binding, expressed by the description alone.
mem-lam : {n : ℕ} {t : Tm} → MuMem LamD (suc n) t → MuMem LamD n (`lam t)
mem-lam m = mm-con zero (ρ suc ι) _ refl (m , tt)

mem-app : {n : ℕ} {f a : Tm} →
          MuMem LamD n f → MuMem LamD n a → MuMem LamD n (`app f a)
mem-app mf ma = mm-con (suc zero) (ρ id (ρ id ι)) _ refl (mf , ma , tt)

mem-ne : {n : ℕ} → MuMem LamD n ne
mem-ne = mm-ne

mem-red : {n : ℕ} {t : Tm} → MuMem LamD n t → MuMem LamD n (red t)
mem-red m = mm-exp (β _) m

-- a closed term at depth 0 whose body lives at depth 1
example : MuMem LamD zero (`lam (`app ne ne))
example = mem-lam (mem-app mem-ne mem-ne)

------------------------------------------------------------------------
-- ★★ AND THE ELIMINATION INSTANTIATES, non-degenerately: every member
--    has one of the three head shapes, at every index.
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
