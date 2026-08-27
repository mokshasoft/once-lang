------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ⚠ DOES `Lib/IWk`'s CLASSIFIER ACTUALLY CLASSIFY
-- THE KNOT?  A probe, run before the typing lemma is written.
--
-- ★ WHY BEFORE.  `Lib/IWk`'s whole claim is that the per-field rule is
--   DECIDED from the description rather than supplied per row.  If the
--   decision procedure says `nothing` on a row that ought to be in
--   scope, the classification is wrong and no amount of proof work
--   fixes it.  Cheap, and decisive.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.WkProbe where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax using ( vz; _◂_; inil )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Lib.IWk
  using ( WkCon; WkDesc; decCon; decDesc; wkdLen; wkdRest
        ; Maybe; just; nothing; Chk; tt )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD
        ; cTy-Nat; cTy-Pi; cTy-IMu
        ; cTm-lam; cTm-app; cTm-natrec; cTm-con; cTm-ielim
        ; cDesc-cons; cDCon-kap; cIDesc-cons; cICon-rho
        ; cVar-vz; cVar-vs )

------------------------------------------------------------------------
-- 1. ★ IN SCOPE — one per shape the table has.
--
-- Each line type-checks only if `decCon` returned a `just`: `Chk`
-- reduces to `⊤` on a `just` and to `⊥` on a `nothing`.
------------------------------------------------------------------------

_ : Chk (decCon vz cTy-Nat)      -- ford-only
_ = tt
_ : Chk (decCon vz cTy-Pi)       -- two riding fields, one under a binder
_ = tt
_ : Chk (decCon vz cTm-lam)      -- the binder, index `suc ⟨d⟩`
_ = tt
_ : Chk (decCon vz cTm-app)      -- two fields at the ambient
_ = tt
_ : Chk (decCon vz cTm-natrec)   -- a field at `suc (suc ⟨d⟩)`
_ = tt
_ : Chk (decCon vz cTm-con)      -- a `κ ⌜Nat⌝` field beside a riding one
_ = tt
_ : Chk (decCon vz cTm-ielim)    -- four fields
_ = tt
_ : Chk (decCon vz cDesc-cons)   -- cross-sort, both riding
_ = tt
_ : Chk (decCon vz cDCon-kap)    -- ★ a PINNED field beside a riding one
_ = tt
_ : Chk (decCon vz cTy-IMu)      -- ★ a field pinned at `pair sTy 0`
_ = tt
_ : Chk (decCon vz cIDesc-cons)  -- ★ pinned at a NON-ZERO literal
_ = tt
_ : Chk (decCon vz cICon-rho)    -- riding, at `suc ⟨d⟩`
_ = tt

------------------------------------------------------------------------
-- 2. ⚠ OUT OF SCOPE, AND DETECTED — the two DEPTH-FORDED rows.
--
-- ★★ THIS IS THE POINT OF THE PROBE.  Their κ constrains `snd ⟨i⟩`, so
--   passing the witness through is WRONG and the classifier must refuse
--   rather than mis-classify.  It refuses.
------------------------------------------------------------------------

vz-out : decCon vz cVar-vz ≡ nothing
vz-out = refl

vs-out : decCon vz cVar-vs ≡ nothing
vs-out = refl

------------------------------------------------------------------------
-- 3. ★★★ AND THE MEASUREMENT: **51 OF THE 53 ROWS ARE CLASSIFIED**, and
--    the classifier stops exactly where it should.
--
-- ⚠ THIS IS THE NUMBER TO ASSERT, not the fact that it type-checks.
--   `decDesc` is TOTAL — it stops rather than failing — so "it compiled"
--   says nothing about how far it got.  A row that silently stopped
--   being classifiable would shorten this and nothing else would notice.
--   Pinning it makes the coverage a CHECKED claim.
--
-- ⇒ 51 computed rows, and a 2-method tail the caller supplies.  That is
--   the same split `Knot/Ctors` (51 generated) and `Knot/Build` (2
--   hand-written `Var` rows) already use — and for the same reason,
--   which is what makes it a design rather than a coincidence.
------------------------------------------------------------------------

knot-classified : wkdLen (decDesc KnotD) ≡ 51
knot-classified = refl

-- ⚠ AND THE STOP IS AT THE RIGHT PLACE.  `wkdLen` alone would be
--   satisfied by classifying some OTHER 51; §2 pins which two are left,
--   and these two are the last two rows of the table.

------------------------------------------------------------------------
-- 4. ★★ AND NO COVERAGE IS LOST — the leftover is EXACTLY the two rows
--    that were refused, and nothing else.
--
-- ⚠ WHY THIS NEEDS SAYING.  `decDesc` stops at the FIRST row it cannot
--   classify, so a classifiable row sitting AFTER an unclassifiable one
--   would simply not be computed.  ⚠ That is a COVERAGE loss, not an
--   unsoundness and not a restriction on what may be written — the
--   caller supplies the whole leftover either way and nothing is
--   forbidden.  But it is invisible unless measured.
--
-- ⇒ pinning `wkdRest` measures it: the leftover is the two `Var` rows,
--   so the stop costs nothing here.  Reorder the table and this line
--   fails, which is the point.
------------------------------------------------------------------------

knot-rest : wkdRest (decDesc KnotD) ≡ (cVar-vz ◂ (cVar-vs ◂ inil))
knot-rest = refl
