------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ THE HEAD REDUCTION OF AN `ielim`, ONCE.
--
--     ihead-red : sel k ms ⟶* mth →
--                 app (app (app mth i) p) (iihs D ms (isingle i) C p) ⟶* u →
--                 ielim D i ms (icon k p) ⟶* u
--
-- ★★★ EVERY ADEQUACY PROOF IN THE TREE STARTS WITH THIS STEP, AND EACH
--   ONE HAD WRITTEN IT OUT AGAIN.  Before this module there were exactly
--   three, one per adequacy proof that exists:
--
--       `Knot/SzAgree.head-red`      at `szsMethsK`
--       `Knot/RenRed.ren-head-red`   at `renMethsK`
--       `Knot/SubRed.sub-head-red`   at `subMethsK`
--
--   The last two are the SAME LEMMA twice, differing only in
--   `renDescK`/`subDescK`, `renGiveK`/`giveK`, `wOf`/`wOfS` and the
--   method tuple.  This module is the step they share.
--
-- ★ WHY IT FACTORS AT ALL: `ι-ielim` fires on ANY method tuple, and
--   `ifields D i ms σ C m p` is DEFINITIONALLY
--   `app (app (app m i) p) (iihs D ms σ C p)` (`Spec/Syntax:1233`).  So
--   the only program-specific ingredient is the reduction that turns
--   `sel k ms` into that program's `k`-th method — and THAT is already
--   generic: `Lib/IMeths.methsAt-sel` / `methsFrom-sel` for a
--   hand-built tuple, `Lib/IFold.ifMeths-sel` for a folded one.
--   ⇒ take it as a PARAMETER and nothing program-specific is left.
--
-- ⚠ SO THE PREMISE IS `sel k ms ⟶* mth`, NOT `k ∈ID D`.  Membership is
--   how each client PROVES the premise, not what this step needs; asking
--   for the witness instead would pin the lemma to one tuple-shape and
--   re-introduce exactly what it exists to remove.
--
-- ★ SCOPE: this is the HEAD step only — selecting the row's method and
--   handing back the applied form.  What each client then does with the
--   payload and the IH tuple is its own content: see `Knot/SzAgree`'s
--   header for the two-peels-at-different-depths hazard, which this
--   module deliberately does not try to share.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IHeadRed where

open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; IDesc; ICon; icon; ielim; sel; app; iihs; isingle
        ; ilookupD )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; _⟶_; step; done; ι-ielim )
-- ⚠ `_»_` is NOT imported: it is a LOCAL infix alias for `⟶*-trans`,
--   redefined in 10+ Knot modules.  A library lemma must not depend
--   on a notation its clients happen to have spelled out.
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ; ⟶*-trans )

private variable Γ : Cx

-- ★ `D`, `ms`, `k`, `i`, `p` are EXPLICIT: every call site names them
--   anyway, and leaving them implicit makes the metas depend on the
--   client's `iihs` argument, which is exactly the position
--   `pin-implicits-on-defined-set-types` warns about.
-- ⚠ THE `ICon` IS NOT FREE: `ι-ielim` hands back `ilookupD D k`, so the
--   row's constructor is DETERMINED by `D` and `k`.  Taking it as a
--   parameter type-checks the signature and then fails at the body —
--   the lemma has one shape, not a family of them.
ihead-red : (D : IDesc) (ms : RTm Γ) (k : ℕ) {mth : RTm Γ}
            (i p : RTm Γ) {u : RTm Γ} →
            sel k ms ⟶* mth →
            app (app (app mth i) p) (iihs D ms (isingle i) (ilookupD D k) p)
              ⟶* u →
            ielim D i ms (icon k p) ⟶* u
ihead-red D ms k i p sel-red h =
  step (ι-ielim D i ms k p)
       (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ sel-red))) h)
