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
  using ( cTm-var; cTm-lam; cTm-absurd; cTm-app; cTm-pair
        ; cTm-fst; cTm-snd; cTm-cbase; cTm-cNat; cTm-cUnit
        ; cTm-cMu; cTm-cPi; cTm-cSg; cTm-cHom; cTm-hrefl
        ; cTm-tr; cTm-ap; cTm-cId; cTm-idrefl; cTm-jsub
        ; cTm-unit; cTm-nzero; cTm-nsuc; cTm-ordtr; cTm-natrec
        ; cTm-con; cTm-elim; cTm-icon; cTm-ielim; cTm-cIMu )

------------------------------------------------------------------------
-- 1. ★ THE ROW'S OWN SORT IS READABLE FROM ITS TAG FORD.
--
-- ⚠ This is the half that had no precedent: `Lib/IWk` decides SHAPES and
--   never needed to read a literal back out.  `sTm` is 1.
------------------------------------------------------------------------

_ : rowSort cTm-app ≡ someℕ 1
_ = refl

------------------------------------------------------------------------
-- 2. ★★★ AND THE COUNTS AGREE WITH `szb`, ROW BY ROW — ALL **30** OF THEM.
--
-- ⚠ THE COUNT IS THE CLAIM.  `Metatheory/Canonicity`'s `szb` has exactly
--   30 clauses and the table has exactly 30 `cTm-` rows; every one is
--   below.  A probe over a SUBSET would pass just as green while saying
--   nothing about the rows it skipped — and the interesting rows here
--   are precisely the irregular ones.
--
--     szb (var)    = zero                   0   ← the `Var` child is CROSS-SORT
--     szb (lam)    = sz t                   1
--     szb (absurd) = sz c + sz e            2
--     szb (app)    = sz f + sz a            2
--     szb (pair)   = sz a + sz b            2
--     szb (fst)    = sz p                   1
--     szb (snd)    = sz p                   1
--     szb (cbase)  = zero                   0   ← no fields
--     szb (cNat)   = zero                   0   ← no fields
--     szb (cUnit)  = zero                   0   ← no fields
--     szb (cMu)    = zero                   0   ← the `Desc` is CROSS-SORT
--     szb (cPi)    = sz c + sz d            2
--     szb (cSg)    = sz c + sz d            2
--     szb (cHom)   = sz c + sz a + sz b     3
--     szb (hrefl)  = sz c + sz t            2
--     szb (tr)     = sz d + sz p + sz e     3
--     szb (ap)     = sz c + sz b + sz p     3
--     szb (cId)    = sz c + sz a + sz b     3
--     szb (idrefl) = sz c + sz t            2
--     szb (jsub)   = sz d + sz p + sz e     3
--     szb (unit)   = zero                   0   ← no fields
--     szb (nzero)  = zero                   0   ← no fields
--     szb (nsuc)   = sz n                   1
--     szb (ordtr)  = 5 subterms             5
--     szb (natrec) = sz z + sz w + sz n     3
--     szb (con)    = sz p                   1   ← the tag `k` is a κ, not a child
--     szb (elim)   = sz ms + sz t           2   ← 3 `iρ`, one CROSS-SORT
--     szb (icon)   = sz p                   1
--     szb (ielim)  = sz i + sz ms + sz t    3   ← 4 `iρ`, one CROSS-SORT
--     szb (cIMu)   = sz i                   1   ← 3 `iρ`, two CROSS-SORT
------------------------------------------------------------------------

_ : countSame cTm-var    ≡ 0
_ = refl
_ : countSame cTm-lam    ≡ 1
_ = refl
_ : countSame cTm-absurd ≡ 2
_ = refl
_ : countSame cTm-app    ≡ 2
_ = refl
_ : countSame cTm-pair   ≡ 2
_ = refl
_ : countSame cTm-fst    ≡ 1
_ = refl
_ : countSame cTm-snd    ≡ 1
_ = refl
_ : countSame cTm-cbase  ≡ 0
_ = refl
_ : countSame cTm-cNat   ≡ 0
_ = refl
_ : countSame cTm-cUnit  ≡ 0
_ = refl
_ : countSame cTm-cMu    ≡ 0
_ = refl
_ : countSame cTm-cPi    ≡ 2
_ = refl
_ : countSame cTm-cSg    ≡ 2
_ = refl
_ : countSame cTm-cHom   ≡ 3
_ = refl
_ : countSame cTm-hrefl  ≡ 2
_ = refl
_ : countSame cTm-tr     ≡ 3
_ = refl
_ : countSame cTm-ap     ≡ 3
_ = refl
_ : countSame cTm-cId    ≡ 3
_ = refl
_ : countSame cTm-idrefl ≡ 2
_ = refl
_ : countSame cTm-jsub   ≡ 3
_ = refl
_ : countSame cTm-unit   ≡ 0
_ = refl
_ : countSame cTm-nzero  ≡ 0
_ = refl
_ : countSame cTm-nsuc   ≡ 1
_ = refl
_ : countSame cTm-ordtr  ≡ 5
_ = refl
_ : countSame cTm-natrec ≡ 3
_ = refl
_ : countSame cTm-con    ≡ 1
_ = refl
_ : countSame cTm-elim   ≡ 2
_ = refl
_ : countSame cTm-icon   ≡ 1
_ = refl
_ : countSame cTm-ielim  ≡ 3
_ = refl
_ : countSame cTm-cIMu   ≡ 1
_ = refl

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
