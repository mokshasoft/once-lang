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
open import DirectedHoTT.Spec.Syntax
  using ( vz; _◂_; inil; Cx; RTm; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢fst; ⊢snd; ⊢nsuc; imethTy )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Lib.IWk
  using ( WkCon; WkDesc; decCon; decDesc; wkdLen; wkdRest
        ; iwkMethod; ⊢iwkMethod; Mot; sh
        ; Maybe; just; nothing; Chk; tt; get )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; ⊢IPair; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Wf
  using ( KnotWf; cTm-lamWf; cDCon-kapWf )
open import DirectedHoTT.Examples.Knot.Tags
  using ( tagTy-Nat; tagTm-lam; tagDCon-kap; memTm-lam; memDCon-kap )
open import DirectedHoTT.Examples.Knot.WkRows
  using ( wkTyNat; wkTmLam; wkDkap )
open import DirectedHoTT.Examples.Knot.Wk using ( ⊢shIPair )
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

------------------------------------------------------------------------
-- 5. ★★★ AND THE GENERIC METHOD **IS** THE HAND-WRITTEN ONE.
--
-- `Examples/Knot/WkRows` wrote four methods by hand, one per row shape.
-- `Lib/IWk` computes them from the description.  ⚠ Nothing so far said
-- the two agree — the generic one could have been well typed and a
-- DIFFERENT term.
--
-- ⇒ they are equal by `refl`, at both shapes that have a hand-written
--   counterpart with no depth ford.  That is the control that ties the
--   library to its spike, and it is why `WkRows` was kept rather than
--   deleted once `Lib/IWk` existed.
------------------------------------------------------------------------

clsNat : WkCon vz cTy-Nat
clsNat = get (decCon vz cTy-Nat) tt

clsLam : WkCon vz cTm-lam
clsLam = get (decCon vz cTm-lam) tt

clsKap : WkCon vz cDCon-kap
clsKap = get (decCon vz cDCon-kap) tt

nat-agrees : {Γ : Cx} → iwkMethod {Γ = Γ} tagTy-Nat clsNat ≡ wkTyNat {Γ}
nat-agrees = refl

lam-agrees : {Γ : Cx} → iwkMethod {Γ = Γ} tagTm-lam clsLam ≡ wkTmLam {Γ}
lam-agrees = refl

-- ★ the row the per-field rule is ABOUT: one field takes the IH, its
--   sibling takes the original field, and the computed method makes the
--   same two choices the hand-written one did.
kap-agrees : {Γ : Cx} → iwkMethod {Γ = Γ} tagDCon-kap clsKap ≡ wkDkap {Γ}
kap-agrees = refl

------------------------------------------------------------------------
-- 6. ★★ …AND IT TYPES, at the real description.
--
-- ⚠ `⊢sh` is the hypothesis `Lib/IFold` had no analogue of: the result
--   sits at `sh ⟨i⟩`, so `⊢icon` must TYPE that index.  At `I = Σ' Nat
--   Nat` it is three constructors.
------------------------------------------------------------------------

-- ⚠ `⊢shIPair` now lives in `Knot/Wk`.  It was here, which made a real
--   module depend on this ASSERTIONS module — a probe should be a leaf.

⊢genLam : {Γ : Ctx} →
          Γ ⊢ iwkMethod tagTm-lam clsLam
            ∷ imethTy KnotD IPair tagTm-lam cTm-lam (Mot KnotD IPair)
⊢genLam = ⊢iwkMethod KnotD IPair tagTm-lam clsLam KnotWf cTm-lamWf
                     memTm-lam refl ⊢IPair ⊢shIPair

⊢genKap : {Γ : Ctx} →
          Γ ⊢ iwkMethod tagDCon-kap clsKap
            ∷ imethTy KnotD IPair tagDCon-kap cDCon-kap (Mot KnotD IPair)
⊢genKap = ⊢iwkMethod KnotD IPair tagDCon-kap clsKap KnotWf cDCon-kapWf
                     memDCon-kap refl ⊢IPair ⊢shIPair
