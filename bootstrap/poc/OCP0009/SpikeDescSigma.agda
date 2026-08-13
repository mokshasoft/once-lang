------------------------------------------------------------------------
-- OCP-0009 — ★ GATE 4: NON-RECURSIVE FIELDS, AND THE MUTUAL KNOT.
--
-- Gates 1–3 cleared the LR shape including binding.  The last shape
-- question `SCOPE-INDUCTIVE.md` records is `σ` — a constructor carrying a
-- VALUE the description then depends on.
--
-- ★★ FIRST, THE QUESTION GOT SMALLER, and that is a finding in itself.
--   Full `IDesc` needs `σ : (S : Set) → (S → IDesc I) → IDesc I` because
--   a constructor's later fields may depend on an earlier one's VALUE, and
--   because the target index must be BOUND (`cons : A → Vec n → Vec (suc n)`
--   binds `n`).  Neither arises for a SYNTAX:
--
--     * `RTm`'s constructors relate `Γ` to `Γ` or `Γ ∙` — never downward —
--       so gate 3's "target = ambient index, `ρ` computes the field index"
--       covers every one of them, and nothing needs binding;
--     * no `RTm` constructor's field SHAPE depends on an earlier field's
--       VALUE.  Checked against all 25.
--
--   ⇒ what is actually needed is not dependent `σ` but a NON-DEPENDENT
--     non-recursive field:  `κ : Ty → Con → Con`.
--
-- ★★★ AND THAT IS WHERE THE REAL DIFFICULTY IS.  A field of type `A` must
--   be a member of the AMBIENT logical relation at `A` — so `Lift` has to
--   invoke `⊩`, `⊩` unfolds at `mu D` to `MuMem D`, and `MuMem`'s own
--   declaration mentions `Lift`.  A THREE-WAY KNOT between two functions
--   and a datatype:
--
--       Lift ── calls ──▶ ⊩ ── unfolds to ──▶ MuMem ── declared with ──▶ Lift
--
--   Q11  ★ do `Ty`, `Con`, `Desc` form a legal MUTUAL block, given `Ty`
--        contains `mu D` and `Con` contains `κ A`?
--   Q12  ★★ does the knot pass POSITIVITY — `MuMem` (data) mutual with
--        `⊩` (function), with `Lift` mentioning both?
--   Q13  ★★★ does elimination still pass TERMINATION across the knot?
--   Q14  does a datatype with a NON-RECURSIVE field instantiate it, and
--        does a NESTED datatype (a field whose type is another `mu`)?
--
-- ⚠ NOT COMBINED WITH GATE 3.  This spike is non-indexed, to isolate the
--   knot.  Gates 3 and 4 together are untested and that is the remaining
--   shape risk.
--
-- Self-contained: no imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeDescSigma where

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

------------------------------------------------------------------------
-- ★ Q11 — TYPES AND DESCRIPTIONS ARE MUTUAL.
--   `Ty` contains `mu D`; `Con` contains `κ A`; so the three are one block.
------------------------------------------------------------------------

mutual
  data Ty : Set where
    base : Ty
    mu   : Desc → Ty       -- ★ a datatype IS a type

  data Con : Set where
    ι : Con
    ρ : Con → Con          -- a RECURSIVE field
    κ : Ty → Con → Con     -- ★ a NON-RECURSIVE field, of object type `Ty`

  data Desc : Set where
    []  : Desc
    _∷_ : Con → Desc → Desc

infixr 5 _∷_

lookup : Desc → ℕ → Maybe Con
lookup []      _       = nothing
lookup (C ∷ D) zero    = just C
lookup (C ∷ D) (suc k) = lookup D k

------------------------------------------------------------------------
-- object-language terms
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
-- ★ `Lift` stays PARAMETERISED in BOTH relations.  That is what keeps the
--   knot legal: it mentions neither `MuMem` nor `⊩` by name, so it can be
--   defined before the block that ties them.
------------------------------------------------------------------------

Lift : Con → (Tm → Set) → (Ty → Tm → Set) → Tm → Set
Lift ι       P R ne        = ⊥
Lift ι       P R unit      = ⊤
Lift ι       P R (pr _ _)  = ⊥
Lift ι       P R (con _ _) = ⊥
Lift ι       P R (red _)   = ⊥
Lift (ρ C)   P R ne        = ⊥
Lift (ρ C)   P R unit      = ⊥
Lift (ρ C)   P R (pr x r)  = P x × Lift C P R r          -- recursive field
Lift (ρ C)   P R (con _ _) = ⊥
Lift (ρ C)   P R (red _)   = ⊥
Lift (κ A C) P R ne        = ⊥
Lift (κ A C) P R unit      = ⊥
Lift (κ A C) P R (pr x r)  = R A x × Lift C P R r        -- ★ AMBIENT relation
Lift (κ A C) P R (con _ _) = ⊥
Lift (κ A C) P R (red _)   = ⊥

------------------------------------------------------------------------
-- ★★ Q12 — THE KNOT.  `⊩` is a FUNCTION on types; `MuMem` is a DATATYPE;
--    each mentions the other.
------------------------------------------------------------------------

data BaseMem : Tm → Set where
  bm-ne   : BaseMem ne
  bm-unit : BaseMem unit
  bm-exp  : {t t' : Tm} → t ⟶ t' → BaseMem t' → BaseMem t

mutual
  ⊩ : Ty → Tm → Set
  ⊩ base   t = BaseMem t
  ⊩ (mu D) t = MuMem D t

  data MuMem (D : Desc) : Tm → Set where
    mm-ne  : MuMem D ne
    mm-con : (k : ℕ) (C : Con) (p : Tm) → lookup D k ≡ just C →
             Lift C (MuMem D) ⊩ p → MuMem D (con k p)
    mm-exp : {t t' : Tm} → t ⟶ t' → MuMem D t' → MuMem D t

------------------------------------------------------------------------
-- ★★★ Q13 — ELIMINATION ACROSS THE KNOT.
--
-- ⚠ The `κ` case hands back the ambient membership UNCHANGED — the
--   eliminator does not recurse into it.  That is correct and is what
--   keeps termination in reach: a non-recursive field is not a recursive
--   position, so no IH is owed there.
------------------------------------------------------------------------

mutual
  elimMem : {D : Desc} {Q : Tm → Set} →
            Q ne →
            ({t t' : Tm} → t ⟶ t' → Q t' → Q t) →
            ((k : ℕ) (C : Con) (p : Tm) → lookup D k ≡ just C →
               Lift C Q ⊩ p → Q (con k p)) →
            (t : Tm) → MuMem D t → Q t
  elimMem qn qe qc .ne        mm-ne              = qn
  elimMem qn qe qc .(con k p) (mm-con k C p e l) =
    qc k C p e (elimLift qn qe qc C p l)
  elimMem qn qe qc t          (mm-exp r m)       =
    qe r (elimMem qn qe qc _ m)

  elimLift : {D : Desc} {Q : Tm → Set} →
             Q ne →
             ({t t' : Tm} → t ⟶ t' → Q t' → Q t) →
             ((k : ℕ) (C : Con) (p : Tm) → lookup D k ≡ just C →
                Lift C Q ⊩ p → Q (con k p)) →
             (C : Con) (p : Tm) →
             Lift C (MuMem D) ⊩ p → Lift C Q ⊩ p
  elimLift qn qe qc ι       ne        ()
  elimLift qn qe qc ι       unit      tt        = tt
  elimLift qn qe qc ι       (pr _ _)  ()
  elimLift qn qe qc ι       (con _ _) ()
  elimLift qn qe qc ι       (red _)   ()
  elimLift qn qe qc (ρ C)   ne        ()
  elimLift qn qe qc (ρ C)   unit      ()
  elimLift qn qe qc (ρ C)   (pr x r)  (mx , mr) =
    elimMem qn qe qc x mx , elimLift qn qe qc C r mr
  elimLift qn qe qc (ρ C)   (con _ _) ()
  elimLift qn qe qc (ρ C)   (red _)   ()
  elimLift qn qe qc (κ A C) ne        ()
  elimLift qn qe qc (κ A C) unit      ()
  elimLift qn qe qc (κ A C) (pr x r)  (rx , mr) =
    rx , elimLift qn qe qc C r mr                  -- ★ handed back unchanged
  elimLift qn qe qc (κ A C) (con _ _) ()
  elimLift qn qe qc (κ A C) (red _)   ()

------------------------------------------------------------------------
-- ★ Q14 — INSTANCES.
--
--   `Tree`  leaf : base → Tree          ← a NON-RECURSIVE field
--           node : Tree → Tree → Tree
--
--   `Wrap`  wrap : Tree → Wrap          ← ★ a NESTED datatype: the field's
--                                         type is another `mu`
------------------------------------------------------------------------

TreeD : Desc
TreeD = κ base ι          -- leaf, carrying one `base` value
      ∷ ρ (ρ ι)           -- node, two recursive fields
      ∷ []

`leaf : Tm → Tm
`leaf v = con zero (pr v unit)

`node : Tm → Tm → Tm
`node l r = con (suc zero) (pr l (pr r unit))

mem-leaf : {v : Tm} → BaseMem v → MuMem TreeD (`leaf v)
mem-leaf bv = mm-con zero (κ base ι) _ refl (bv , tt)

mem-node : {l r : Tm} → MuMem TreeD l → MuMem TreeD r → MuMem TreeD (`node l r)
mem-node ml mr = mm-con (suc zero) (ρ (ρ ι)) _ refl (ml , mr , tt)

-- ★★ THE NESTED ONE: a datatype whose field's type is another datatype.
WrapD : Desc
WrapD = κ (mu TreeD) ι ∷ []

`wrap : Tm → Tm
`wrap t = con zero (pr t unit)

mem-wrap : {t : Tm} → MuMem TreeD t → MuMem WrapD (`wrap t)
mem-wrap mt = mm-con zero (κ (mu TreeD) ι) _ refl (mt , tt)

-- a concrete inhabitant of the nested type
example : MuMem WrapD (`wrap (`node (`leaf unit) ne))
example = mem-wrap (mem-node (mem-leaf bm-unit) mm-ne)

------------------------------------------------------------------------
-- ★★ AND THE ELIMINATION INSTANTIATES across the knot.
------------------------------------------------------------------------

data Shape : Tm → Set where
  sh-ne  : Shape ne
  sh-red : (t : Tm) → Shape (red t)
  sh-con : (k : ℕ) (p : Tm) → Shape (con k p)

classify : (t : Tm) → MuMem TreeD t → Shape t
classify =
  elimMem sh-ne (λ { (β t) _ → sh-red t }) (λ k C p _ _ → sh-con k p)

classify-nested : (t : Tm) → MuMem WrapD t → Shape t
classify-nested =
  elimMem sh-ne (λ { (β t) _ → sh-red t }) (λ k C p _ _ → sh-con k p)
