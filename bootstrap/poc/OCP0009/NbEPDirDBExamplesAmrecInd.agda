------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — `amrec-ind` IS CALLABLE.  THE LIBRARY'S EXERCISER.
--
-- ⚠ EVERY LIBRARY IS EXERCISED BY AN EXAMPLE, NEVER BY A SPIKE (standing
--   rule, 2026-08-21).  A green `--safe` library proves its definitions
--   typecheck; it does not prove a client can CALL them.  This file is that
--   guarantee for `…LibAmrecInd`, and it fails loudly if the interface moves.
--
-- ⚠⚠ COVERAGE IS PER BRANCH, AND THIS FILE DOES NOT YET HAVE IT.  What is
--   below is the SATISFIABILITY check — deliberately the weakest interesting
--   one.  The branch-level exercise (an `IndStep` that actually USES its
--   `IndPW` hypothesis) is gap B layer 2, `…ExamplesGcdDvd`.
--
-- ⚠⚠ WHAT THIS DOES AND DOES NOT SHOW.  `…SpikeAmrecInd` proves
--   `amrecInd`, whose premises are `StepExt` and `IndStep`.  Green says
--   the DEFINITION typechecks; it does not say the premises can be met at
--   a call site with the types lining up.  That is the failure mode
--   `lexrec` died of (`lexrec-branches-done-assembly-open`: the Γ₅ form's
--   premise is unsatisfiable, and the module was green throughout).
--
--   So: discharge `IndStep` at the trivially-true motive and CALL the
--   combinator.  If the seven-premise interface did not compose, this
--   would not typecheck.
--
-- ⚠ IT DOES **NOT** SHOW THE COMBINATOR IS USEFUL.  The step below ignores
--   its `IndPW` hypothesis, because exercising `IndPW` needs a carrier
--   whose measure genuinely DECREASES — i.e. a real client.  ⭐ And that
--   is not a gap in this check, it is the reason the success criterion was
--   fixed in advance: all three of `gcd ∣ a`, `gcd ∣ b`, and maximality
--   must go THROUGH `amrec-ind`.  This file rules out one failure mode; it
--   does not stand in for that judgement.
--
-- ★ WHY `⌜Unit⌝` IS THE RIGHT TRIVIAL MOTIVE.  It is a CLOSED code, so
--   every renaming and substitution in `PAtR` collapses DEFINITIONALLY and
--   the step's goal reduces to `El ⌜Unit⌝`.  A motive that merely happened
--   to be provable would have tested the peels instead of the interface.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesAmrecInd where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; RTm; El; U; Nat; unit; ⌜Unit⌝ )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_
        ; ⊢unit; ⊢conv; ⊢⌜Unit⌝; csymᵀ; credᵀ; El-⌜Unit⌝ )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( aStepT; Prv; prv; StepExt )
open import poc.OCP0009.NbEPDirDBLibAmrecInd
  using ( IndStep; module Concl )

module Sat (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
           (dA   : Δ ⊢ty A)
           (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
           (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
           (dstp : Δ ⊢ stp ∷ aStepT A cM m)
           (ext  : StepExt Δ A cM m stp)
           where

  open Concl Δ A cM m stp dA dcM dm dstp
    using ( AmrecInd; amrecInd )

  ------------------------------------------------------------------------
  -- ★ THE STEP PREMISE, DISCHARGED — and it is one line, because the
  --   motive is closed.  ⚠ `pw` is bound and ignored ON PURPOSE; see the
  --   header.
  ------------------------------------------------------------------------

  trivStep : IndStep Δ A cM m stp ⌜Unit⌝
  trivStep ρ⊢ a ih da dih pw =
    prv unit (⊢conv ⊢unit (csymᵀ (credᵀ El-⌜Unit⌝)))

  ------------------------------------------------------------------------
  -- ★★ …AND THE COMBINATOR, CALLED.  Every premise of `amrecInd` is met
  --   here by a term written above, so the interface composes.
  ------------------------------------------------------------------------

  called : AmrecInd ⌜Unit⌝
  called = amrecInd ext

  sat : {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Prv Δ (El ⌜Unit⌝)
  sat dx = called ⊢⌜Unit⌝ trivStep dx
