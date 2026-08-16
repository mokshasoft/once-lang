------------------------------------------------------------------------
-- OCP-0009 — gcd's `StepExt`: THE CALLER'S HALF OF GAP A.
--
-- ★ WHAT THIS IS FOR.  `NbEPDirDBLibAmrec.irr-ind`/`amrec-unfold-Id` are
--   CONDITIONAL on `StepExt Δ A cM m stp` — "the step does not look at
--   WHICH ih it is given, only at what the ih computes".  The library half
--   is done; this module discharges the hypothesis for `gcdStp`, which is
--   the last thing between the tree and gap A (defining equations 3/4 at
--   VARIABLES rather than numerals).
--
-- ⚠ IT IS NOT ONE INSTANTIATION.  `StepExt` quantifies over an ARBITRARY
--   carrier `a` and `irr-ind` consumes it at a VARIABLE, but `gcdStp`
--   reduces only at a constructor-headed carrier: at a neutral `a` all
--   three scrutinees (`snd a`, `fst a`, `a ∸ b`) are stuck.  There is no
--   funext in this kernel, so the two stuck neutrals cannot be related by a
--   congruence.  The route is to SPLIT: `natrec` proves `P(t)` for a
--   neutral `t` perfectly well, so abstract each scrutinee out of the goal
--   and recurse on it.  Three nested splits, four leaves — two IH-free
--   (both sides literally equal) and two using the pointwise hypothesis
--   once each, at `(PAIRᶻ , CERTᶻ)` resp. `(PAIRˢ , CERTˢ)`.
--
-- ⚠⚠ AND THE SPLIT MOTIVES CARRY AN ORDER HYPOTHESIS.  A `natrec` on
--   `snd a` hands its successor branch a fresh `n'`; it does NOT hand over
--   the equation `snd a = nsuc n'`.  So the leaf's certificate, which
--   `⊢CERTᶻ` states at `plusTm (nsuc k') (nsuc n')`, cannot be re-stated at
--   `μ a = plusTm (fst a) (snd a)` where the pointwise hypothesis wants it.
--   The fix is to split under `M z = Π (Hom Nat z (w t)) …` and instantiate
--   at the scrutinee with `⊢le-refl`, so each branch RECEIVES
--   `nsuc n' ≤ snd a`.  Splits 1 and 2 only; split 3's motive is constant.
--   (Same failure mode as the one that made `amrec-unfold-Id` necessary: a
--   case split gives you branches, never an equation about the scrutinee.)
--
-- ★ STATUS.  Under construction — see the section markers.  Everything
--   above `THE PIECES` is built and green.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdStepExt where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; sym )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs; RTm; Ren; renTm; extR )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep using ( gcdStp )

------------------------------------------------------------------------
-- ★ RENAMING-INVARIANCE OF THE STEP.
--
-- `StepExt` is CONTEXT-POLYMORPHIC: it states its conclusion about
-- `renTm ρ stp` at an arbitrary weakening `ρ` of the ambient context, so
-- every leaf below has to know that `gcdStp` is unmoved by one.  `gcdStp`
-- is closed, but "closed" is not a judgement this syntax has — what makes
-- it work is finer and cheaper: every variable in `gcdStp` sits under
-- strictly more binders than its own index, so each `extR` peels one `vs`
-- and `ρ` is never reached.  That is a COMPUTATION, not an induction.
--
-- ⚠ The `w (w a)` inside `monusLtTm` would NOT collapse for an abstract
--   `a` (`renTm` does not fuse definitionally), but gcd instantiates it at
--   a concrete variable, where it does.
------------------------------------------------------------------------

ren-gcdStp : {Γ Δ : Cx} (ρ : Ren Γ Δ) → renTm ρ gcdStp ≡ gcdStp
ren-gcdStp ρ = refl
