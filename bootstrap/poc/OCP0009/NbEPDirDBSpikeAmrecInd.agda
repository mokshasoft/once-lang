------------------------------------------------------------------------
-- OCP-0009 — `amrec-ind`, ATTEMPT 1: STATE IT BEFORE PROVING IT.
--
-- ★ WHY THIS ORDER.  Gap A's expensive failures came from committing to a
--   SHAPE and then fighting it — 52 attempts, seven on one derivation.  So
--   write the statement, check it is WELL-FORMED, and only then prove it.
--   A malformed statement is cheap to find here and expensive to find with
--   a half-built proof on top of it.
--
-- ★★ THE MOTIVE IS A CODE IN **TWO** SLOTS, and both are forced:
--
--       ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U
--          ↑ the ARGUMENT      ↑ the RESULT
--
--   `gcd (a,b) ∣ a` mentions the input pair AND the output, so a motive
--   over the result alone cannot state gap B's obligation.  And it must be
--   a CODE, not an `RTy`, because `⊢jsub` transports code families — the
--   constraint that forced certificate irrelevance in `amrec-unfold-Id`.
--   ⚠ `dvdT` clears it: `⊢dvdCode` is green.
--
-- ⚠ SLOT ORDER IS NOT FREE.  `single` fills the TOP slot, so the RESULT
--   must be substituted first and the ARGUMENT second.  Writing it the
--   other way round needs a substitution-composition lemma for no gain.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBSpikeAmrecInd where

open import normalizer.Syntax.Types using ( _≡_; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; RTm; El; U; Nat; Hom; Π; var; vz; app; nsuc
        ; subTm; subTy; renTy; renTm; Ren; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; ⊢app; ty-El )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast; ⊢[]; Ren⊢ )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; wᶠ; wᶠ¹-single )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( aStepT; Prv; module AmTΠ )

module Stmt (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
            (dA   : Δ ⊢ty A)
            (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
            (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
            (dstp : Δ ⊢ stp ∷ aStepT A cM m)
            where

  open AmTΠ Δ A cM m stp dA dcM dm dstp using ( amrecTm; ⊢amrecΠ )

  ------------------------------------------------------------------------
  -- ★ THE RECURSIVE VALUE, AT THE BOUND ARGUMENT.  `amrec` applied to the
  --   `A`-slot's own variable — this is what the motive's result slot gets
  --   filled with.
  ------------------------------------------------------------------------

  valAt : RTm (⌊ Δ ⌋ ∙)
  valAt = app (w amrecTm) (var vz)

  ⊢valAt : (Δ ▹ A) ⊢ valAt ∷ El cM
  ⊢valAt = ⊢-cast (cong El (wᶠ¹-single cM)) (⊢app (⊢wk ⊢amrecΠ) (⊢var here))

  ------------------------------------------------------------------------
  -- ★★ THE GOAL TYPE: `P` at the argument `x` and the value `amrec x`.
  ------------------------------------------------------------------------

  IndAt : RTm ((⌊ Δ ⌋ ∙) ∙) → RTm ⌊ Δ ⌋ → RTy ⌊ Δ ⌋
  IndAt P x = El (subTm (single x) (subTm (single valAt) P))

  -- ★ …and it IS a type, whenever `P` is a code and `x` an element.
  ⊢IndAt : {P : RTm ((⌊ Δ ⌋ ∙) ∙)} →
           ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
           {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A →
           Δ ⊢ty IndAt P x
  ⊢IndAt dP dx = ty-El (⊢[] (⊢[] dP ⊢valAt) dx)

------------------------------------------------------------------------
-- ★★★ THE MOTIVE, APPLIED — under an ambient renaming.
--
-- Every premise below states `P` at some (argument, result) pair in some
-- context reached by a renaming, so this is factored once.
--
-- ⚠ SLOT ORDER, again: `single` fills the TOP slot, so the RESULT goes in
--   first and the ARGUMENT second.  Same convention as `IndAt`.
------------------------------------------------------------------------

-- ⚠ `val` IS WEAKENED ON THE WAY IN, and the reason is the slot order.
--   Filling the RESULT slot happens while the ARGUMENT is still bound, so
--   the substituted value must live one context deeper.  The outer
--   `single y` then cancels the weakening (`wk-single`) and lands `val`
--   back where it was written.
--   ⭐ `IndAt`'s `valAt` needs no such weakening — it is written AT
--   `⌊ Δ ⌋ ∙` already, as `app (w amrecTm) (var vz)`.
PAtR : {Γ Γ' : Cx} (ρ : Ren Γ Γ') (P : RTm ((Γ ∙) ∙)) (y val : RTm Γ') → RTm Γ'
PAtR ρ P y val =
  subTm (single y) (subTm (single (w val)) (renTm (extR (extR ρ)) P))

------------------------------------------------------------------------
-- ★★★ THE INDUCTION HYPOTHESIS, POINTWISE — `P` holds of EVERY recursive
--   call the handle `ih` can make.
--
-- ⚠ DOUBLY RENAMING-INDEXED, exactly like `StepPW`, and for the same
--   reason: the caller instantiates it under further binders, so a
--   `Θ`-only statement is not general enough.  The coherence condition
--   `ϑ ∘ ρ ≡ ρ'` is what lets the two renamings be related at all.
--   ⭐ Recorded 2026-08-16 as "StepExt's premise must be renaming-indexed";
--   the same applies here and is cheaper to get right the first time.
------------------------------------------------------------------------

IndPW : (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙))
        (P : RTm ((⌊ Δ ⌋ ∙) ∙))
        (Θ : Ctx) (ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋) (a ih : RTm ⌊ Θ ⌋) → Set
IndPW Δ A cM m P Θ ρ a ih =
  {Θ' : Ctx} {ϑ : Ren ⌊ Θ ⌋ ⌊ Θ' ⌋} {ρ' : Ren ⌊ Δ ⌋ ⌊ Θ' ⌋} →
  Ren⊢ Θ Θ' ϑ → (∀ v → ϑ (ρ v) ≡ ρ' v) →
  (y q : RTm ⌊ Θ' ⌋) →
  Θ' ⊢ y ∷ renTy ρ' A →
  Θ' ⊢ q ∷ Hom Nat (nsuc (subTm (single y) (renTm (extR ρ') m)))
                   (renTm ϑ (subTm (single a) (renTm (extR ρ) m))) →
  Prv Θ' (El (PAtR ρ' P y (app (app (renTm ϑ ih) y) q)))

------------------------------------------------------------------------
-- ★★★★ THE STEP PREMISE — the caller's half, and the ONLY thing a client
--   of `amrec-ind` should have to discharge.
--
--   "if `P` holds of every recursive call, it holds of the step's result"
--
-- ★ COMPARE `StepExt`, which says the step RESPECTS pointwise equality of
--   handles.  This says it PRESERVES a predicate.  Same shape, different
--   payload — which is the evidence that the shape is the right one.
------------------------------------------------------------------------

IndStep : (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
          (P : RTm ((⌊ Δ ⌋ ∙) ∙)) → Set
IndStep Δ A cM m stp P =
  {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
  (a ih : RTm ⌊ Θ ⌋) →
  Θ ⊢ a ∷ renTy ρ A →
  Θ ⊢ ih ∷ aIHTat (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                  (subTm (single a) (renTm (extR ρ) m)) →
  IndPW Δ A cM m P Θ ρ a ih →
  Prv Θ (El (PAtR ρ P a (app (app (renTm ρ stp) a) ih)))

------------------------------------------------------------------------
-- ★★★★★ …AND THE COMBINATOR'S FULL TYPE.
--
-- Stated as a `Set` so the SPECIFICATION can be checked well-formed
-- before any of it is proved, and so a client can take it as a PARAMETER
-- and be written against it while the proof is still open.  (`--safe`
-- forbids `postulate`, which is the usual way to do this; a parameter is
-- the honest substitute and is strictly better — it cannot leak into
-- anything that does not ask for it.)
--
-- ⚠ WHAT IS AND IS NOT ESTABLISHED HERE.  This is a well-formed STATEMENT
--   and nothing more.  No instance exists, so nothing below is yet
--   evidence that any function has the property — exactly the status
--   `StepExt` had before `…GcdStepExtA` discharged it.
------------------------------------------------------------------------

module Concl (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
             (dA   : Δ ⊢ty A)
             (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
             (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
             (dstp : Δ ⊢ stp ∷ aStepT A cM m)
             where

  open Stmt Δ A cM m stp dA dcM dm dstp using ( IndAt )

  AmrecInd : RTm ((⌊ Δ ⌋ ∙) ∙) → Set
  AmrecInd P =
    ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
    IndStep Δ A cM m stp P →
    {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A →
    Prv Δ (IndAt P x)
