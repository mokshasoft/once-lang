------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ THE HEAD REDUCTION OF AN `ielim`, ONCE.
--
--     ihead-red : Nth ms k m →
--                 app (app (app m i) p) (dih D (methₗ ms) D (tag k , p)) ⟶* u →
--                 ielim D i (methₗ ms) (conₗ k p) ⟶* u
--
-- ★★ LEVITATION: the head step is `Lib/Sugar.ιₗ` — ι, two β, the split,
--   the tag selection — and the IH is the kernel's `dih`, not a tuple.
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
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; ielim; app; dih; pair )
open import DirectedHoTT.Spec.Typing using ( _⟶*_ )
-- ⚠ `_»_` is NOT imported: it is a LOCAL infix alias for `⟶*-trans`,
--   redefined in 10+ Knot modules.  A library lemma must not depend
--   on a notation its clients happen to have spelled out.
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans )
open import DirectedHoTT.Lib.Sugar using ( Cons; Nth; methₗ; conₗ; tag; ιₗ )

private variable
  Γ : Cx
  c : ℕ

-- ★ `D`, `ms`, `k`, `i`, `p` are EXPLICIT: every call site names them
--   anyway, and leaving them implicit makes the metas depend on the
--   client's continuation, which is exactly the position
--   `pin-implicits-on-defined-set-types` warns about.
ihead-red : (D : RTm Γ) (ms : Cons Γ c) (k : ℕ) {m : RTm Γ}
            (i p : RTm Γ) {u : RTm Γ} →
            Nth ms k m →
            app (app (app m i) p) (dih D (methₗ ms) (app D i) (pair (tag k) p)) ⟶* u →
            ielim D i (methₗ ms) (conₗ k p) ⟶* u
ihead-red D ms k i p nt h = ⟶*-trans (ιₗ nt) h
