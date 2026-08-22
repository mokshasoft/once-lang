------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — `amrec` AT A CLOSED CARRIER.
--
-- ★ At `◇` the unfolding's premise is FREE: `amrec-unfold-z`/`-s` are
--   conditional on the measure reaching a numeral, and at a closed carrier
--   that is a THEOREM (`natEval`), so the library discharges it and the
--   caller just cases on the answer.
--
-- ⚠⚠ WHY THIS IS ITS OWN MODULE, AND IT IS A COST BOUNDARY, NOT A TOPIC
--   BOUNDARY.  `natEval` runs through canonicity and drags
--   `…Canon → …Fund → …FundSem`/`…FundSN` behind it.  While these 43 lines
--   sat in `…LibAmrec`, that module's 31 importers each paid ~5.5 MB of
--   interface for a theorem none of them used — 18–23% of their closure
--   (`PERF-2026-08-21.md` §2).  Anything that needs canonicity belongs on
--   this side of the line; keep `…LibAmrec` free of it.
--
-- ⚠ The boundary is CANONICITY, not normalisation: `wnorm` works at any
--   context, `canNat` is closed-only.  Two lemmas, two domains — the
--   conditional form in `…LibAmrec` is the correct one whenever anything
--   is open, not a weaker fallback.
--
-- ⬜ `AmTΠ◇` HAS NO CLIENT.  It is unexercised library surface and by the
--   standing rule (`libraries-exercised-by-examples`) it needs one or a
--   stated reason.  Flagged at the move rather than quietly relocated;
--   `measure-evals` below IS exercised, by `…ExamplesPairLib`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.AmrecClosed where
open import DirectedHoTT.Spec.Syntax
  using ( ε; _∙; RTy; RTm; U; Nat; natrec; app; subTm; extS )
open import DirectedHoTT.Spec.Typing
  using ( ◇; _▹_; single; _⊢_∷_; _⊢ty_; _⟶*_ )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢[] )
open import DirectedHoTT.Lib.Strong using ( reflTm )
open import DirectedHoTT.Lib.NatVal using ( NatVal; nv-zero; nv-suc )
open import DirectedHoTT.Lib.NatEval using ( natEval )
open import DirectedHoTT.Lib.Amrec using ( aStepT; module AmTΠ )

------------------------------------------------------------------------
-- ★★ AT A CLOSED CARRIER, THE UNFOLDING'S PREMISE IS FREE.
--
-- `amrec-unfold-z`/`-s` are conditional on the measure reaching a numeral.
-- That premise is real information at an OPEN context — there the measure
-- normalises to a NEUTRAL containing the free variable, and no library can
-- supply it.  At `◇` it is a THEOREM (`natEval`), so the library discharges
-- it and the caller just cases on the answer.
--
-- ⚠ The boundary is CANONICITY, not normalisation: `wnorm` works at any
--   context, `canNat` is closed-only.  Two lemmas, two domains — the
--   conditional form is the correct one whenever anything is open, not a
--   weaker fallback.
------------------------------------------------------------------------

measure-evals : (A : RTy ε) (m : RTm (ε ∙)) → (◇ ▹ A) ⊢ m ∷ Nat →
                (x : RTm ε) → ◇ ⊢ x ∷ A → NatVal (subTm (single x) m)
measure-evals A m dm x dx = natEval (⊢[] dm dx)

------------------------------------------------------------------------
-- ★★ AND THE TWO HALVES, COMPOSED.  At a closed carrier a caller touches
--    neither `NatVal` nor the conditional lemmas: it hands over `x` and
--    its derivation and gets the reduction.
--
-- ⚠ Still one step short of the ideal D7 shape — this reaches the
--   AUXILIARY's branch, not the user's step; two more βs would take it to
--   `app (app stp x) ⟨ih⟩`.  Flagged rather than claimed.
------------------------------------------------------------------------

module AmTΠ◇ (A : RTy ε) (cM m : RTm (ε ∙)) (stp : RTm ε)
             (dA   : ◇ ⊢ty A)
             (dcM  : (◇ ▹ A) ⊢ cM ∷ U)
             (dm   : (◇ ▹ A) ⊢ m ∷ Nat)
             (dstp : ◇ ⊢ stp ∷ aStepT A cM m)
             where

  open AmTΠ ◇ A cM m stp dA dcM dm dstp public

  data Unfold (x : RTm ε) : Set where
    unf-z : app amrecTm x
          ⟶* app (app (subTm (single x) aZBr) x) (reflTm (subTm (single x) m))
          → Unfold x
    unf-s : (k : RTm ε) →
            app amrecTm x
          ⟶* app (app (subTm (single (natrec (subTm (single x) aZBr)
                                             (subTm (extS (extS (single x))) aSBr)
                                             k))
                              (subTm (extS (single k))
                                     (subTm (extS (extS (single x))) aSBr)))
                      x)
                 (reflTm (subTm (single x) m))
          → Unfold x

  -- ★ the premise is gone: canonicity supplies it.
  amrec-unfold : (x : RTm ε) → ◇ ⊢ x ∷ A → Unfold x
  amrec-unfold x dx with measure-evals A m dm x dx
  ... | nv-zero r  = unf-z (amrec-unfold-z x r)
  ... | nv-suc k r = unf-s k (amrec-unfold-s x k r)
