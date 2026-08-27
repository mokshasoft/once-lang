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
open import DirectedHoTT.Spec.Syntax using ( vz )
open import DirectedHoTT.Lib.IWk
  using ( WkCon; decCon; decDesc; Maybe; just; nothing; Chk; tt )
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
-- 3. ⇒ AND SO THE WHOLE KNOT IS OUT, which is the finding.
--
-- `iwkMeths` needs a method for EVERY row, so `WkDesc KnotD` cannot be
-- computed while `Var`'s two rows are in the list.  ⇒ `Lib/IWk` needs a
-- per-row ESCAPE HATCH — a `WkDesc` constructor taking a HAND-WRITTEN
-- method — and `KnotD` is then 51 computed rows plus 2 given ones.
--
-- ⚠ THAT IS THE SPLIT THE TREE ALREADY USES: `Knot/Ctors` generates 51
--   smart constructors and `Knot/Build` hand-writes the two `Var` rows,
--   for exactly this reason (they Ford the DEPTH).  It is not
--   half-generalization: the enumeration is 2 rows, not 53, and the 51
--   stay computed with the description a variable.
------------------------------------------------------------------------

knot-out : decDesc KnotD ≡ nothing
knot-out = refl
