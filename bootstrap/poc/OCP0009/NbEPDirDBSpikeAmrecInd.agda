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

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; RTm; El; U; Nat; Hom; Π; var; vz; vs; Var; app; nsuc; nzero; natrec
        ; subTm; subTy; renTy; renTm; Ren; extR; extS; renTy-renTy )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢app; ty-El; ty-Π; ty-Hom; ty-Nat )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ⊢[]; Ren⊢; Ren⊢-ext; ren-lemma; ren-ty
        ; Sub⊢; Sub⊢-ext; ⊢single; sub-lemma )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; wᶠ; wᶠ¹-single; ⊢wkᶠ )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( aStepT; Prv; wR; module AmTΠ )

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

-- ⚠⚠ THE ARGUMENT SLOT MUST BE FILLED **FIRST**, AND THE REASON IS A
--   DEPENDENCY, not a convention.  The RESULT slot's type is `El cM`,
--   which DEPENDS on the argument slot.  So substituting the result first
--   is type-correct only when the value is written as a function of the
--   argument VARIABLE — and an arbitrary `val` is not.
--
--   ⭐ `IndAt` gets away with the other order precisely because its
--   `valAt = app (w amrecTm) (var vz)` IS such a function.  That is a
--   special case, not the general rule, and reading it as the rule was
--   attempt 1's mistake: the wrong order still checks as a TERM operation
--   (attempt 3 was green) and only fails when a TYPING is demanded of it.
--
-- ⇒ `extS (single y)` fills the argument and keeps the result slot open;
--   `single val` then closes it, at the now-instantiated type `El cM[y]`.
PAtR : {Γ Γ' : Cx} (ρ : Ren Γ Γ') (P : RTm ((Γ ∙) ∙)) (y val : RTm Γ') → RTm Γ'
PAtR ρ P y val =
  subTm (single val) (subTm (extS (single y)) (renTm (extR (extR ρ)) P))

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

------------------------------------------------------------------------
-- ★★★ AND THE TYPING THAT DECIDES THE ORDER.  If `PAtR` is well-ordered
--   this goes through; if not, no arrangement of casts saves it, because
--   the mismatch is a genuine dependency.
------------------------------------------------------------------------

module Typing (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
              (dA   : Δ ⊢ty A)
              (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
              (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
              (dstp : Δ ⊢ stp ∷ aStepT A cM m)
              where

  ⊢PAtR : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
          {P : RTm ((⌊ Δ ⌋ ∙) ∙)} →
          ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
          {y val : RTm ⌊ Θ ⌋} →
          Θ ⊢ y ∷ renTy ρ A →
          Θ ⊢ val ∷ El (subTm (single y) (renTm (extR ρ) cM)) →
          Θ ⊢ PAtR ρ P y val ∷ U
  ⊢PAtR ρ⊢ dP dy dval =
    ⊢[] (sub-lemma (ren-lemma dP (Ren⊢-ext (Ren⊢-ext ρ⊢)))
                   (Sub⊢-ext (⊢single dy)))
        dval

  open AmTΠ Δ A cM m stp dA dcM dm dstp using ( amrecTm; ⊢amrecΠ )

  ------------------------------------------------------------------------
  -- ★★★★ THE BOUNDED STATEMENT — what the `natrec` on the measure bound
  --   actually inducts over:
  --
  --     "for every `x : A` with `μ x ≤ n`,  P holds at (x, amrec x)"
  --
  --   It lives at `Δ ▹ Nat`, the bound being that `Nat`.  Inside the two
  --   `Π`s the slots read  [0]=c  [1]=x  [2]=n.
  --
  -- ⚠ `μ x` is `wᶠ m`, NOT a substitution.  `m`'s own slot 0 IS the
  --   `A`-argument, and `wᶠ` inserts the BOUND at slot 1 while leaving that
  --   argument where it is — so the measure lands on `x` with no
  --   substitution at all.
  ------------------------------------------------------------------------

  ρ₃ : Ren ⌊ Δ ⌋ ⌊ ((Δ ▹ Nat) ▹ renTy vs A) ▹ Hom Nat (wᶠ m) (var (vs vz)) ⌋
  ρ₃ v = vs (vs (vs v))

  IndB : RTm ((⌊ Δ ⌋ ∙) ∙) → RTy (⌊ Δ ⌋ ∙)
  IndB P =
    Π (renTy vs A)
      (Π (Hom Nat (wᶠ m) (var (vs vz)))
         (El (PAtR ρ₃ P (var (vs vz))
                (app (renTm ρ₃ amrecTm) (var (vs vz))))))

  -- ★ the ambient renaming, typed: three weakenings off `Δ`.
  ρ₃⊢ : Ren⊢ Δ (((Δ ▹ Nat) ▹ renTy vs A) ▹ Hom Nat (wᶠ m) (var (vs vz))) ρ₃
  ρ₃⊢ = wR (wR there)

  ⊢IndB : {P : RTm ((⌊ Δ ⌋ ∙) ∙)} →
          ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
          (Δ ▹ Nat) ⊢ty IndB P
  ⊢IndB dP =
    ty-Π (ren-ty dA there)
      (ty-Π (ty-Hom ty-Nat (⊢wkᶠ dm) (⊢var (there here)))
         (ty-El (⊢PAtR ρ₃⊢ dP dy (⊢app (ren-lemma ⊢amrecΠ ρ₃⊢) dy))))
    where
      -- ⚠ THE VARIABLE'S TYPE IS THE COMPOSITE, NOT THE CONTEXT'S.
      --   `⊢var (there here)` yields `renTy vs (renTy vs (renTy vs A))`,
      --   while `⊢PAtR` and `⊢app` both want `renTy ρ₃ A`.  Equal only up
      --   to `renTy-renTy`, twice — the same fusion `wR` does internally
      --   with `∋-cast`.
      dyEq : renTy vs (renTy vs (renTy vs A)) ≡ renTy ρ₃ A
      dyEq = trans (cong (renTy vs) (renTy-renTy A)) (renTy-renTy A)

      dy = ⊢-cast dyEq (⊢var (there here))


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
