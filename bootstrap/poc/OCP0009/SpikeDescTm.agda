------------------------------------------------------------------------
-- OCP-0009 — ★ THE SECOND GATE: DESCRIPTIONS OVER *TERMS*.
--
-- `SpikeDesc` cleared the shape in the METALANGUAGE, where `μ D` is an
-- Agda datatype so its elements ARE description-shaped.  Over `RTm` they
-- are not, and `SCOPE-INDUCTIVE.md` §3 records the question that leaves:
--
--   ⇒ how does an object-language CONSTRUCTOR TERM carry its fields, so
--     that `Lift` can walk them against the description — and does the
--     logical relation still work once NEUTRALS and EXPANSION are back?
--
-- ★★ THE DESIGN UNDER TEST — sum-of-products with a NUMERAL TAG.
--
--     Con   one constructor's fields:  `ι` (done) | `ρ C` (a recursive
--           field, then more)
--     Desc  a datatype IS a list of `Con`s
--     term  `con i p` — a TAG `i` selecting the constructor, and a
--           payload `p` built from `unit`/`pr`
--
--   ⚠⚠ AND THAT IS WHY IT AVOIDS COPRODUCTS.  `SpikeDesc` used `δ`
--     (choice) inside the description, whose object-language reading is
--     `inl`/`inr` — and the kernel has NO coproduct, a gap
--     `ARCHITECTURE.md` leans on (⊢lexrec takes two recursor arguments
--     rather than a disjunction precisely to avoid needing one).  Moving
--     the choice OUT of the type and INTO the term as a tag needs only
--     `Nat` and a pair, both of which the kernel already has.
--
--   ⇒ if this passes, the axis is ONE cascade, not two.
--
-- ⚠ Restriction bought with it, and it is the right one: choice may only
--   appear at the TOP of a description.  That is exactly "sum of
--   products", i.e. what a datatype declaration is; a field that is
--   itself a choice belongs to a nested datatype.
--
-- THE THREE QUESTIONS:
--   Q5  ★ does `Lift` — walking a `Con` against a PAYLOAD TERM — survive
--       being nested inside `MuMem`, now WITH `mm-ne` and `mm-exp`?
--   Q6  ★★ does an elimination by recursion on the MEMBERSHIP proof pass
--       TERMINATION, when the recursive sub-proofs are reached only by
--       UNFOLDING `Lift` into a product?
--   Q7  does a concrete datatype (ℕ) instantiate it, non-vacuously?
--
-- Self-contained: no imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeDescTm where

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

------------------------------------------------------------------------
-- DESCRIPTIONS — sum of products.  ⚠ the choice is the LIST, not a former.
------------------------------------------------------------------------

data Con : Set where
  ι : Con              -- no more fields
  ρ : Con → Con        -- a recursive field, then more

data Desc : Set where
  []  : Desc
  _∷_ : Con → Desc → Desc

infixr 5 _∷_

lookup : Desc → ℕ → Maybe Con
lookup []      _       = nothing
lookup (C ∷ D) zero    = just C
lookup (C ∷ D) (suc i) = lookup D i

------------------------------------------------------------------------
-- OBJECT-LANGUAGE TERMS.  Minimal, but carrying the two things that made
-- the metalanguage spike unfaithful: NEUTRALS and a REDUCTION.
------------------------------------------------------------------------

data Tm : Set where
  ne   : Tm            -- stands for any neutral
  unit : Tm            -- the empty payload
  pr   : Tm → Tm → Tm  -- payload cons
  con  : ℕ → Tm → Tm   -- ★ TAG + payload
  red  : Tm → Tm       -- stands for any redex

data _⟶_ : Tm → Tm → Set where
  β : (t : Tm) → red t ⟶ t

------------------------------------------------------------------------
-- ★ Q5 — the predicate lifting, walking a `Con` against a PAYLOAD TERM.
--
-- ⚠ Every clause is explicit rather than a catch-all, so the termination
--   checker in Q6 can unfold it without guessing.
------------------------------------------------------------------------

Lift : Con → (Tm → Set) → Tm → Set
Lift ι     P ne        = ⊥
Lift ι     P unit      = ⊤
Lift ι     P (pr _ _)  = ⊥
Lift ι     P (con _ _) = ⊥
Lift ι     P (red _)   = ⊥
Lift (ρ C) P ne        = ⊥
Lift (ρ C) P unit      = ⊥
Lift (ρ C) P (pr x r)  = P x × Lift C P r
Lift (ρ C) P (con _ _) = ⊥
Lift (ρ C) P (red _)   = ⊥

-- ★★ THE GATE.  `Lift C (MuMem D)` is a FUNCTION-defined lifting used
--    NESTED inside the relation's own declaration — now alongside a
--    neutral case and an expansion case, which is what `NbEPDirDBLR`'s
--    `NatMem` actually looks like.
data MuMem (D : Desc) : Tm → Set where
  mm-ne  : MuMem D ne
  mm-con : (i : ℕ) (C : Con) (p : Tm) → lookup D i ≡ just C →
           Lift C (MuMem D) p → MuMem D (con i p)
  mm-exp : {t t' : Tm} → t ⟶ t' → MuMem D t' → MuMem D t

------------------------------------------------------------------------
-- ★★ Q6 — ELIMINATION BY RECURSION ON THE MEMBERSHIP PROOF.
--
-- This is `fund`'s shape: a predicate `Q` closed under the three ways a
-- term can be a member, and the conclusion for every member.  ⚠ The
-- recursive sub-proofs live INSIDE `Lift C (MuMem D) p`, reachable only
-- by unfolding `Lift` into a product — so this is where the termination
-- checker has to do the work.
------------------------------------------------------------------------

mutual
  elimMem : {D : Desc} {Q : Tm → Set} →
            Q ne →
            ({t t' : Tm} → t ⟶ t' → Q t' → Q t) →
            ((i : ℕ) (C : Con) (p : Tm) → lookup D i ≡ just C →
               Lift C Q p → Q (con i p)) →
            (t : Tm) → MuMem D t → Q t
  elimMem qn qe qc .ne          mm-ne             = qn
  elimMem qn qe qc .(con i p)   (mm-con i C p e l) =
    qc i C p e (elimLift qn qe qc C p l)
  elimMem qn qe qc t            (mm-exp r m)       =
    qe r (elimMem qn qe qc _ m)

  elimLift : {D : Desc} {Q : Tm → Set} →
             Q ne →
             ({t t' : Tm} → t ⟶ t' → Q t' → Q t) →
             ((i : ℕ) (C : Con) (p : Tm) → lookup D i ≡ just C →
                Lift C Q p → Q (con i p)) →
             (C : Con) (p : Tm) → Lift C (MuMem D) p → Lift C Q p
  elimLift qn qe qc ι     ne        ()
  elimLift qn qe qc ι     unit      tt        = tt
  elimLift qn qe qc ι     (pr _ _)  ()
  elimLift qn qe qc ι     (con _ _) ()
  elimLift qn qe qc ι     (red _)   ()
  elimLift qn qe qc (ρ C) ne        ()
  elimLift qn qe qc (ρ C) unit      ()
  elimLift qn qe qc (ρ C) (pr x r)  (mx , mr) =
    elimMem qn qe qc x mx , elimLift qn qe qc C r mr
  elimLift qn qe qc (ρ C) (con _ _) ()
  elimLift qn qe qc (ρ C) (red _)   ()

------------------------------------------------------------------------
-- ★ Q7 — a CONCRETE datatype, so none of the above is vacuous.
--   ℕ = two constructors: `zero` (no fields), `suc` (one recursive field).
------------------------------------------------------------------------

NatD : Desc
NatD = ι ∷ ρ ι ∷ []

`zero : Tm
`zero = con zero unit

`suc : Tm → Tm
`suc n = con (suc zero) (pr n unit)

-- both really are members
mem-zero : MuMem NatD `zero
mem-zero = mm-con zero ι unit refl tt

mem-suc : {n : Tm} → MuMem NatD n → MuMem NatD (`suc n)
mem-suc m = mm-con (suc zero) (ρ ι) _ refl (m , tt)

-- ★ and so is a neutral, and a redex over a member — the two cases the
--   metalanguage spike could not express at all
mem-ne : MuMem NatD ne
mem-ne = mm-ne

mem-red : MuMem NatD (red `zero)
mem-red = mm-exp (β `zero) mem-zero

------------------------------------------------------------------------
-- ★★ AND `elimMem` INSTANTIATES.  `Q t = ⊤` is degenerate on purpose:
--    what is being tested is that the ELIMINATION SHAPE goes through, not
--    the predicate.  A real `fund` supplies a real `Q`.
------------------------------------------------------------------------

trivial : Tm → Set
trivial _ = ⊤

all-trivial : (t : Tm) → MuMem NatD t → trivial t
all-trivial = elimMem tt (λ _ _ → tt) (λ _ _ _ _ _ → tt)

-- ★ a NON-degenerate one: every member is either neutral, a redex, or a
--   `con` — i.e. the relation really does classify head shapes.
data Shape : Tm → Set where
  sh-ne  : Shape ne
  sh-red : (t : Tm) → Shape (red t)
  sh-con : (i : ℕ) (p : Tm) → Shape (con i p)

classify : (t : Tm) → MuMem NatD t → Shape t
classify =
  elimMem sh-ne (λ { (β t) _ → sh-red t }) (λ i C p _ _ → sh-con i p)
