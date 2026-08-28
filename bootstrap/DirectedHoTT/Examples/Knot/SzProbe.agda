------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ⬜ SPIKE: does the SAME-SORT predicate reproduce
-- the meta-level `szb`'s counts on the real table?
--
-- The `sz` agreement `szTm ⌈t⌉ ⟶* ⌜ sz t ⌝` fails because `szb` folds
-- over `RTm` ALONE — the other sorts are separate Agda types and it
-- treats them as ATOMS — while `Lib/IFold` traverses all seven at once.
-- ⚠ Measured 28/28 outside Agda: `szb`'s count is exactly the number of
-- SAME-SORT `iρ` fields.
--
-- ★ THIS FILE CHECKS THAT CLAIM **INSIDE** AGDA, against the generated
--   table, so it is a theorem rather than a script's opinion.  Each line
--   is `countSame <row> ≡ <what szb counts>`, by `refl`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SzProbe where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc )
open import DirectedHoTT.Spec.Syntax using ( nzero; fst; var; vz; RTm; ε; _∙ )
open import DirectedHoTT.Spec.Variance using ( true )
open import DirectedHoTT.Lib.IFold using ( countSame; rowSort; Maybeℕ; someℕ )
open import DirectedHoTT.Lib.ISz using ( szSum )
open import DirectedHoTT.Lib.ISzSort using ( szsSum )
open import DirectedHoTT.Examples.Knot.Desc
  using ( cTm-var; cTm-lam; cTm-app; cTm-cMu; cTm-elim; cTm-ielim
        ; cTm-cIMu; cTm-con; cTm-icon; cTm-natrec; cTm-ordtr )

------------------------------------------------------------------------
-- 1. ★ THE ROW'S OWN SORT IS READABLE FROM ITS TAG FORD.
--
-- ⚠ This is the half that had no precedent: `Lib/IWk` decides SHAPES and
--   never needed to read a literal back out.  `sTm` is 1.
------------------------------------------------------------------------

_ : rowSort cTm-app ≡ someℕ 1
_ = refl

------------------------------------------------------------------------
-- 2. ★★★ AND THE COUNTS AGREE WITH `szb`, ROW BY ROW.
--
--   `Metatheory/Canonicity`:        vs `countSame`:
--     szb (var x)        = zero          0   ← the `Var` child is CROSS-SORT
--     szb (lam t)        = sz t          1
--     szb (app f a)      = sz f + sz a   2
--     szb (⌜Mu⌝ D)       = zero          0   ← the `Desc` is CROSS-SORT
--     szb (elim D ms t)  = sz ms + sz t  2   ← 3 `iρ`, one cross-sort
--     szb (ielim D i ms t) = 3 subterms  3   ← 4 `iρ`, one cross-sort
--     szb (⌜IMu⌝ D I i)  = sz i          1   ← 3 `iρ`, two cross-sort
--     szb (con k p)      = sz p          1
--     szb (icon k p)     = sz p          1
--     szb (natrec z w n) = 3 subterms    3
--     szb (ordtr a t u p q) = 5 subterms 5
------------------------------------------------------------------------

_ : countSame cTm-var    ≡ 0
_ = refl
_ : countSame cTm-lam    ≡ 1
_ = refl
_ : countSame cTm-app    ≡ 2
_ = refl
_ : countSame cTm-cMu    ≡ 0
_ = refl
_ : countSame cTm-elim   ≡ 2
_ = refl
_ : countSame cTm-ielim  ≡ 3
_ = refl
_ : countSame cTm-cIMu   ≡ 1
_ = refl
_ : countSame cTm-con    ≡ 1
_ = refl
_ : countSame cTm-icon   ≡ 1
_ = refl
_ : countSame cTm-natrec ≡ 3
_ = refl
_ : countSame cTm-ordtr  ≡ 5
_ = refl

------------------------------------------------------------------------
-- 3. ★★★ AND THE GENERALISATION IS STRICT — CHECKED, NOT ASSUMED.
--
-- ⚠ THE SWEEP DOES NOT SHOW THIS.  `Lib/ISz` and `Lib/IDepth` still
--   TYPE-CHECK after `Lib/IFold` gained its `pick` parameter, but
--   neither of them asserts a computed value, so "all green" is
--   consistent with the count-all fold now emitting a different term.
--   These three lines are about the TERMS.
------------------------------------------------------------------------

-- ⚠ PINNED.  Left as `var vz` the fold's `Γ` is a meta with nothing to
--   solve it — the statement never mentions the context otherwise.
ih0 : RTm (ε ∙)
ih0 = var vz

-- (i) on a row whose every child is same-sort, the two folds are the
--     SAME TERM — so `pick` cost the old customers nothing.
_ : szSum true cTm-app ih0 ≡ szsSum (rowSort cTm-app) cTm-app ih0
_ = refl

-- (ii) and they part company exactly where a child is CROSS-SORT.
--      `cTm-var`'s one recursive field lands in `Var`, not `Tm`.
_ : szsSum (rowSort cTm-var) cTm-var ih0 ≡ nzero
_ = refl

_ : szSum true cTm-var ih0 ≡ fst ih0
_ = refl
