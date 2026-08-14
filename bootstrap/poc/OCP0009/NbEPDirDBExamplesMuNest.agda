------------------------------------------------------------------------
-- OCP-0009 · INDUCTIVE TYPES — ★ NESTED DATATYPES, end to end.
--
-- ⚠⚠ WHAT THIS FILE IS FOR.  `⌜Mu⌝` was added for exactly one capability,
--   and a green kernel does not by itself demonstrate it: a description
--   whose `dκ` FIELD IS ANOTHER DATATYPE.  Gate 6c (`SpikeMuMem3`) posed
--   that case semantically as `WrapD`; the kernel could not express it
--   until now, because `dwf-κ` demands the field be `El c` for a CLOSED
--   CODE and there was no code for `Mu`.
--
--   So this is the acceptance test for the whole ⌜Mu⌝ increment.  If it
--   type-checks, nesting is real; if it were merely "green", nothing here
--   would compile.
--
-- ★ THE CHAIN, and every link is a REAL derivation, not a postulate:
--
--     ⊢⌜Mu⌝ natWf      : ◇ ⊢ ⌜Mu⌝ NatD ∷ U       -- ℕ is a CODE
--     dwf-κ … above …  : DConWf (dκ (El (⌜Mu⌝ NatD)) dι)
--     wrapWf           : DescWf WrapD             -- so Wrap is well-formed
--     ty-Mu wrapWf     : Γ ⊢ty Mu WrapD           -- …and is a TYPE
--     ⊢con wrapWf …    : ◇ ⊢ `wrap `zero ∷ Mu WrapD   -- …and is INHABITED
--
--   The last line is the point: a closed inhabitant of a datatype one of
--   whose fields is a different datatype.
--
-- ⚠ `--safe`, no postulates, no holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesMuNest where

open import Agda.Builtin.Nat using ( zero; suc )
open import normalizer.Syntax.Types using ( _≡_; refl )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; RTy; RTm; El; Mu; U; Unit; Σ'; Π
        ; Desc; DCon; dι; dρ; dκ; dnil; _◃_; ⌜Mu⌝
        ; con; unit; pair; fst; lam; app; elim; payTy; lookupD
        ; sel; ihs; fields
        ; _∈D_; hereD; thereD )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; ⌊_⌋; _⊢_∷_; _⊢ty_
        ; DConWf; dwf-ι; dwf-ρ; dwf-κ; DescWf; dwf-nil; dwf-cons
        ; ty-Mu; ⊢con; ⊢⌜Mu⌝; ⊢unit; ⊢pair; ty-Unit
        ; ⊢conv; _≅ᵀ_; credᵀ; csymᵀ; El-⌜Mu⌝
        ; ⊢elim; ⊢lam; ty-Σ; ty-El; methsTy
        ; _⟶_; _⟶*_; done; step; ι-elim; β; βfst; ξ-appˡ )

------------------------------------------------------------------------
-- 1. ℕ as a description — the INNER datatype.
------------------------------------------------------------------------

NatD : Desc
NatD = dι ◃ dρ dι ◃ dnil

-- ⚠ no `dκ` anywhere in `NatD`, so its well-formedness needs no codes.
natWf : DescWf NatD
natWf = dwf-cons dwf-ι (dwf-cons (dwf-ρ dwf-ι) dwf-nil)

-- ★ …and THIS is what ⌜Mu⌝ bought: `Mu NatD` is now a SMALL type, i.e.
--   it has a code, so it can appear as a `dκ` field below.
`ℕcode : RTm ε
`ℕcode = ⌜Mu⌝ NatD

⊢ℕcode : ◇ ⊢ `ℕcode ∷ U
⊢ℕcode = ⊢⌜Mu⌝ natWf

`zero : RTm ⌊ ◇ ⌋
`zero = con zero unit

⊢zero : ◇ ⊢ `zero ∷ Mu NatD
⊢zero = ⊢con natWf hereD ⊢unit

------------------------------------------------------------------------
-- 2. ★★★ THE NESTED DESCRIPTION.  One constructor, one field, and that
--    field's type is ANOTHER DATATYPE.
------------------------------------------------------------------------

WrapD : Desc
WrapD = dκ (El `ℕcode) dι ◃ dnil

-- ★ the well-formedness that was UNREACHABLE before ⌜Mu⌝ existed: the
--   κ-slot is discharged by a genuine `◇ ⊢ c ∷ U` whose code is `⌜Mu⌝`.
wrapWf : DescWf WrapD
wrapWf = dwf-cons (dwf-κ `ℕcode ⊢ℕcode dwf-ι) dwf-nil

-- …so `Mu WrapD` is a type.
ty-Wrap : ◇ ⊢ty Mu WrapD
ty-Wrap = ty-Mu wrapWf

------------------------------------------------------------------------
-- 3. AN INHABITANT.  `wrap zero : Wrap`.
--
-- ⚠ the payload's type is `payTy WrapD (lookupD WrapD 0)`, which computes
--   to `Σ' (εwkTy (El `ℕcode)) Unit` — the field, then the `dι` tail.  The
--   `⊢pair` below is what forces the FIELD to be a genuine `Mu NatD`
--   inhabitant, so this derivation could not exist without step 1.
------------------------------------------------------------------------

`wrap : RTm ⌊ ◇ ⌋ → RTm ⌊ ◇ ⌋
`wrap n = con zero (pair n unit)

-- ★★ THE ONE STEP THAT IS NOT BOOKKEEPING.  The field's declared type is
--   the CODE'S DECODE, `El (⌜Mu⌝ NatD)`, which REDUCES to `Mu NatD` but is
--   not syntactically it — so the inhabitant must cross by CONVERSION, and
--   `El-⌜Mu⌝` is exactly the rule that licenses the crossing.  This line is
--   where `⌜Mu⌝` actually does its work.
⊢zeroAsField : ◇ ⊢ `zero ∷ El `ℕcode
⊢zeroAsField = ⊢conv ⊢zero (csymᵀ (credᵀ El-⌜Mu⌝))

-- ⚠ `⊢pair`'s type premise lives in the EXTENDED context (under the field
--   binder), which is why `ty-Unit` is given there and not at ◇.
⊢wrap-zero : ◇ ⊢ `wrap `zero ∷ Mu WrapD
⊢wrap-zero = ⊢con wrapWf hereD (⊢pair ty-Unit ⊢zeroAsField ⊢unit)

------------------------------------------------------------------------
-- 3b. ★★★ ELIMINATING A NESTED VALUE — and watching it COMPUTE.
--
-- ⚠ THE ACCOUNTING THAT MATTERS HERE: a `dκ` field owes NO INDUCTION
--   HYPOTHESIS.  `ihTy WrapD (dκ A dι) q M` computes to `ihTy WrapD dι …`
--   = `Unit`, and `ihs` correspondingly yields `unit` — the nested ℕ is a
--   PARAMETER, not a recursive occurrence, so the method receives the
--   payload and an EMPTY IH tuple.  Getting that wrong in either `ihs` or
--   `ihTy` alone would desynchronise them and nothing below would type.
------------------------------------------------------------------------

-- the motive: constant `Unit` (enough to exercise the machinery without
-- dragging in motive-dependency, which `⊢natrec` already covers)
MotU : RTy (⌊ ◇ ⌋ ∙)
MotU = Unit

-- the single method: takes the payload, takes the (empty) IH tuple, and
-- returns `unit`.
methWrap : RTm ⌊ ◇ ⌋
methWrap = lam (lam unit)

⊢payloadTy : ◇ ⊢ty Σ' (El `ℕcode) Unit
⊢payloadTy = ty-Σ (ty-El ⊢ℕcode) ty-Unit

⊢methWrap : ◇ ⊢ methWrap ∷ Π (Σ' (El `ℕcode) Unit) (Π Unit Unit)
⊢methWrap = ⊢lam ⊢payloadTy (⊢lam ty-Unit ⊢unit)

-- the method TUPLE — right-nested, so `sel 0` is `fst`.
msWrap : RTm ⌊ ◇ ⌋
msWrap = pair methWrap unit

⊢msWrap : ◇ ⊢ msWrap ∷ methsTy WrapD MotU WrapD
⊢msWrap = ⊢pair ty-Unit ⊢methWrap ⊢unit

-- ★ the eliminator at a NESTED datatype, fully typed.
⊢elimWrap : ◇ ⊢ elim WrapD msWrap (`wrap `zero) ∷ Unit
⊢elimWrap = ⊢elim wrapWf ty-Unit ⊢msWrap ⊢wrap-zero

-- ★★ …and it COMPUTES.  ι fires on the `con` scrutinee, `sel 0` projects
--    the method, then two β's consume the payload and the empty IH tuple.
--    Each step is a REAL constructor of `_⟶_`; nothing is postulated.
elimWrap-computes : elim WrapD msWrap (`wrap `zero) ⟶* unit
elimWrap-computes =
  step (ι-elim WrapD msWrap zero (pair `zero unit))
  (step (ξ-appˡ (ξ-appˡ (βfst methWrap unit)))
  (step (ξ-appˡ (β (lam unit) (pair `zero unit)))
  (step (β unit unit)
   done)))

------------------------------------------------------------------------
-- 4. ★ WHAT THIS DOES **NOT** SHOW, recorded so the demonstration is not
--    over-read.
--
--   · It exhibits ONE nesting level.  Nothing here proves an arbitrary
--     depth, though nothing obstructs it either: `⌜Mu⌝ WrapD` is itself a
--     code, so `dκ (El (⌜Mu⌝ WrapD))` is the next rung.
--   · The motive is CONSTANT.  A dependent motive over a nested scrutinee
--     is not exercised here; `⊢natrec`'s case in `Fund` is where motive
--     dependency is actually stressed.
------------------------------------------------------------------------

-- the next rung, to show the construction genuinely iterates
`Wrapcode : RTm ε
`Wrapcode = ⌜Mu⌝ WrapD

⊢Wrapcode : ◇ ⊢ `Wrapcode ∷ U
⊢Wrapcode = ⊢⌜Mu⌝ wrapWf

Wrap²D : Desc
Wrap²D = dκ (El `Wrapcode) dι ◃ dnil

wrap²Wf : DescWf Wrap²D
wrap²Wf = dwf-cons (dwf-κ `Wrapcode ⊢Wrapcode dwf-ι) dwf-nil

ty-Wrap² : ◇ ⊢ty Mu Wrap²D
ty-Wrap² = ty-Mu wrap²Wf
