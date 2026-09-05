------------------------------------------------------------------------
-- DirectedHoTT · NEGATIVE — ⛔⛔ `wkK`: THE **WRONG** WEAKENING, PARKED.
--
-- ⛔ DO NOT USE THIS.  `wkK` is NOT `renTm vs`.  It keeps the de Bruijn
--   index where `renTm vs` shifts it, so the two agree only on terms with
--   no free variables — and the encoding of an open term has them.
--   `Knot/WkSub.wkAtK` (and its `wkTyK`/`wkTmK` instances) is the correct
--   translation, and it has an ADEQUACY PROOF (`Knot/SubSpec.wkTmK-agree`,
--   via `ren-agree`) which `wkK` cannot even have — see below.
--
-- ★★★ WHY IT IS KEPT AT ALL.  It is the subject of `PLAN-RENAMING.md`,
--   whose sharpest finding (§15.1) is about THIS function:
--
--     "there is no `app wkK x` to reduce: `wkK` is an `ielim`, and its
--      renaming exists only as the SHAPE of `Lib/IWk`'s 53 derived
--      methods.  ⇒ the defect was not that the law went unproved; it was
--      that the law was UNSTATABLE."
--
--   A wrong definition that cannot even be given a specification is worth
--   keeping as a specimen.  Deleting it would delete the evidence.
--
-- ⚠ SIX BUGS CAME FROM IT — `PLAN-RENAMING.md` §7 — and all six were the
--   same class: `renTm vs`/`renTy vs` in the source, `wkK` in the
--   encoding.  Step 4 retired the last four applications
--   (`Knot/PayTy` ×2, `Knot/IPayTyRho`, `Knot/IPayTyKap`).
--
-- ⚠⚠ AND IT IS **SPLIT OUT, NOT MOVED WHOLESALE**.  `Knot/Wk` also holds
--   `⊢MotK` (used 9× by `Knot/PwBody`) and `⊢shIPair` (2× by
--   `Knot/WkProbe`) — live infrastructure that merely shared a file with
--   the failed attempt.  Moving the module would have broken a live one,
--   and since `Negative/` is neither swept nor covered by `Trust/`, that
--   breakage would not have surfaced until someone ran `--negative`.
--
-- ⚠ `Negative/` IS NOT BUILT by `tools/sweep.sh` (use `--negative`) and is
--   excluded from `Trust/`, so nothing here is under `--safe` enforcement.
--   That is correct for parked work and is why nothing live may depend on
--   it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.WkK where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Lib.ICast using ( muFwd )
open import DirectedHoTT.Spec.Typing
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; ren-ty )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy )
open import DirectedHoTT.Lib.IWk
open import DirectedHoTT.Lib.IPay using ( Split; spl-nil )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; ⊢IPair; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import Agda.Builtin.Nat using ( suc )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz; tagVar-vs )
open import DirectedHoTT.Examples.Knot.WkRows
open import DirectedHoTT.Examples.Knot.Wk using ( ⊢MotK; wkMethsK; ⊢wkMethsK )


-- ★★★ OBJECT-LEVEL WEAKENING FOR THE KNOT.
wkK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkK i t = ielim KnotD i wkMethsK t

⊢wkK : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
       Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ t ∷ K i → Γ ⊢ wkK i t ∷ K (sh i)
⊢wkK {i = i} di dt =
  ⊢-cast (cong (λ z → K (sh z)) (wk-single i))
         (⊢ielim KnotWf ⊢MotK di ⊢wkMethsK dt)

------------------------------------------------------------------------
-- ★★★ `wkK` AT AN EXPLICIT `(sort , depth)` — the two β-steps, once.
--
-- ⚠⚠ `⊢wkK` lands at `sh i`, and `sh i = pair (fst i) (nsuc (snd i))`
--   (`Lib/IWk`).  At a concrete `i = pair s n` that is
--   `pair (fst (pair s n)) (nsuc (snd (pair s n)))` — two `⟶` STEPS
--   away from `pair s (nsuc n)`, not definitionally equal to it.  Every
--   caller therefore pays the SAME pair of conversions.
--
-- ★ THREE CUSTOMERS ALREADY: `tools/gen-knot.py` hard-codes it as the
--   `WK` post (`muFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _))) (muFwd (ξ-pairˡ
--   (βfst _ _)) …)`), `Knot/Nrs` writes it out, and `Knot/PayTy` needs
--   it for `Σ'`'s second component.  ⇒ lifted here, beside `wkK`, rather
--   than copied a fourth time.
------------------------------------------------------------------------

⊢wkKat : {Γ : Ctx} {s n t : RTm ⌊ Γ ⌋} →
         Γ ⊢ s ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ t ∷ K (pair s n) →
         Γ ⊢ wkK (pair s n) t ∷ K (pair s (nsuc n))
⊢wkKat ds dn dt =
  muFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
    (muFwd (ξ-pairˡ (βfst _ _)) (⊢wkK (⊢ixP ds dn) dt))
