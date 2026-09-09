------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ WHICH CHILDREN `occK` MAY DESCEND INTO.
--
-- `Lib/IOcc` picks with `Lib/IFold.scopeAt`: descend into a child whose
-- index MENTIONS the ambient index variable, skip one PINNED TO A
-- LITERAL.  This module is the claim that that test is the right one
-- for `KnotD`, checked rather than argued.
--
-- ★★★ WHY THE TEST EXISTS.  `occK` compares raw LEVELS, and
-- `enVar {Γ ∙} vz = Var-vzK (num (len Γ))` with `len ε = 0`.  So a
-- variable bound INSIDE a closed piece of syntax encodes to the level-0
-- node an ambient free variable also occupies:
--
--     dκ : RTy ε → DCon → DCon         -- a CLOSED type …
--     leaky = Π Nat (El (var vz))      -- … that binds its own variable
--     occTy vz (Mu (dκ leaky dι ◃ dnil)) ≡ false   -- but occK said 1
--
-- A fold that descends there cannot be faithful to `Spec/Variance.occTy`,
-- which — correctly — never traverses a description.  `OCC-ATTEMPTS.md`
-- §35 has the full account.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.PickScope where

open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; ICon; IDesc; iι; iρ; iκ; inil; _◂_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )
open import DirectedHoTT.Lib.IFold using ( Maybeℕ; noℕ; someℕ; depthAt; scopeAt )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )

------------------------------------------------------------------------
-- 1. THE COUNTS.  A cheap shadow, but a falsifiable one.
------------------------------------------------------------------------
skipCon : {Δ : Cx} → ICon Δ → ℕ
skipCon iι       = zero
skipCon (iκ κ C) = skipCon C
skipCon (iρ j C) with scopeAt {𝔹} true j
... | false = suc (skipCon C)
... | true  = skipCon C

keepCon : {Δ : Cx} → ICon Δ → ℕ
keepCon iι       = zero
keepCon (iκ κ C) = keepCon C
keepCon (iρ j C) with scopeAt {𝔹} true j
... | false = keepCon C
... | true  = suc (keepCon C)

skipD : IDesc → ℕ
skipD inil    = zero
skipD (C ◂ E) = skipCon C + skipD E

keepD : IDesc → ℕ
keepD inil    = zero
keepD (C ◂ E) = keepCon C + keepD E

-- ★ FOUR of the knot's 82 recursive children restart a scope.
knot-skips : skipD KnotD ≡ 4
knot-skips = refl

knot-keeps : keepD KnotD ≡ 78
knot-keeps = refl

------------------------------------------------------------------------
-- 2. ★★★ AND *WHICH* FOUR — the check that matters.
--
-- ⚠ A COUNT IS THE CHEAP SHADOW: it cannot tell a skipped child from a
--   different skipped child, so it would survive picking the wrong four.
--   The ROW INDICES pin them.  Cf. `Knot/Census`, and the standing
--   lesson that a check whose expected value the producer computes is
--   not a check — this list is hand-written from the TYPING RULES:
--
--     10  cTy-IMu      a1 ∷ K (pair sTy   (num 0))  -- IMu's index type
--     39  cTm-cIMu     a1 ∷ K (pair sTy   (num 0))  -- ⌜IMu⌝'s, likewise
--     45  cDCon-kap    a0 ∷ K (pair sTy   (num 0))  -- dκ's field type
--     47  cIDesc-cons  a0 ∷ K (pair sICon (num 1))  -- a desc's ICon
------------------------------------------------------------------------
-- ⚠ NOT `[]`/`_∷_`: those are already in scope from the imports and
--   Agda resolves the literal list against the wrong one.
data RowL : Set where
  rnil  : RowL
  rcons : ℕ → RowL → RowL

-- rows carrying at least one skipped child, in description order
skipRows : ℕ → IDesc → RowL
skipRows i inil    = rnil
skipRows i (C ◂ E) with skipCon C
... | zero  = skipRows (suc i) E
... | suc _ = rcons i (skipRows (suc i) E)

knot-skip-rows : skipRows 0 KnotD
               ≡ rcons 10 (rcons 39 (rcons 45 (rcons 47 rnil)))
knot-skip-rows = refl

------------------------------------------------------------------------
-- 3. ⬜ WHAT IS STILL OWED, stated so it is not mistaken for done.
--
-- The above says WHICH children the fold skips.  It does NOT say that
-- those are exactly the children `Spec/Variance.occTy`/`occTm` decline
-- to recurse into — that correspondence is what actually licenses
-- `occK`'s adequacy, and it is discharged row by row by the `agree-ty` /
-- `agree-tm` induction, not here.
--
-- ⇒ this module rules out the defect it was written for; it does not
--   prove faithfulness.
------------------------------------------------------------------------
