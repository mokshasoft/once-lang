------------------------------------------------------------------------
-- OCP-0009 — GATE SPIKE: lexrec's TYPE LAYER under the families
-- interface, ahead of re-porting any branch.
--
-- ★ THE QUESTION THIS EXISTS TO ANSWER.  Option C's lexrec died at branch
--   (S,S): `LexCSS1` and `LexCSS2` each OOM at the 5.5 GB cap, both halves,
--   even under `+RTS -c`.  That was the codes-and-functions interface.
--   Families removes every `app` from the types and collapses the fitting
--   to one lemma per spine, so the elaborated terms should be markedly
--   smaller.  Does (S,S) fit?
--
-- ⚠ THIS FILE IS THE TYPE LAYER ONLY — no branch, no derivation.  It is
--   step 1 of the gate: establish that lexrec's four types EXIST under
--   families and see how much `LibRec` already supplies, before spending
--   anything on a branch.
--
-- ★ AND THE FIRST ANSWER IS FREE: `rec₁`'s type IS `aIHT`, the measure
--   recursor's IH, verbatim.  Only `rec₂` (two descents) and `lStepT` are
--   new, which is the concrete form of "these are one abstraction".
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeLexT where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType using ( Ctx; _▹_; ⌊_⌋; single; nrs )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; cong₃; cong₄; cong₅; cong₆; sub-w; sub-w²; ren-w
        ; wk-singleTy; wᶠ-single; ren-wTy; ren-wᶠ )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat; aIHT )

------------------------------------------------------------------------
-- ★ rec₁ is aIHT.  Nothing to define.
--
--     rec₁ = (y : A) → μ₁ y < μ₁ x → P y   =   aIHT A cM m₁
------------------------------------------------------------------------

rec1T : {Γ : Cx} (A : RTy Γ) (cM m₁ : RTm (Γ ∙)) → RTy (Γ ∙)
rec1T = aIHT

------------------------------------------------------------------------
-- rec₂ — `(y : A) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y`.
--
-- TWO descents, so two `Hom` binders; the second measure and the motive
-- each pick up one more weakening as they pass the first.
------------------------------------------------------------------------

rec2Tat' : {Γ : Cx} (A : RTy Γ) (m₁ b₁ : RTm (Γ ∙))
           (m₂ b₂ : RTm ((Γ ∙) ∙)) (cm : RTm (((Γ ∙) ∙) ∙)) → RTy Γ
rec2Tat' A m₁ b₁ m₂ b₂ cm =
  Π A (Π (Hom Nat m₁ b₁) (Π (Hom Nat (nsuc m₂) b₂) (El cm)))

-- at an EXPLICIT pair of bounds (D8: the bounds must be nameable)
rec2Tat : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) (μ₁x μ₂x : RTm Γ) → RTy Γ
rec2Tat A cM m₁ m₂ μ₁x μ₂x =
  rec2Tat' A m₁ (w μ₁x) (w m₂) (w (w μ₂x)) (w (w cM))

-- …and at the binder where the carrier variable IS `x`, so the bounds are
-- the measure families themselves.
rec2T : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) → RTy (Γ ∙)
rec2T A cM m₁ m₂ =
  rec2Tat (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) m₁ m₂

------------------------------------------------------------------------
-- the step — `(x : A) → rec₁ → rec₂ → P x`
------------------------------------------------------------------------

lStepT' : {Γ : Cx} (A : RTy Γ) (r₁ : RTy (Γ ∙)) (r₂ : RTy ((Γ ∙) ∙))
          (cm : RTm (((Γ ∙) ∙) ∙)) → RTy Γ
lStepT' A r₁ r₂ cm = Π A (Π r₁ (Π r₂ (El cm)))

lStepT : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) → RTy Γ
lStepT A cM m₁ m₂ =
  lStepT' A (rec1T A cM m₁) (renTy vs (rec2T A cM m₁ m₂)) (w (w cM))

------------------------------------------------------------------------
-- the doubly-bounded auxiliary's body — `(x : A) → μ₁ x ≤ n₁ → μ₂ x ≤ n₂
-- → P x`.  This is `aAuxB` with a second bound.
------------------------------------------------------------------------

auxB' : {Γ : Cx} (A : RTy Γ) (m₁ b₁ : RTm (Γ ∙))
        (m₂ b₂ : RTm ((Γ ∙) ∙)) (cm : RTm (((Γ ∙) ∙) ∙)) → RTy Γ
auxB' A m₁ b₁ m₂ b₂ cm =
  Π A (Π (Hom Nat m₁ b₁) (Π (Hom Nat m₂ b₂) (El cm)))

auxB : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) (n₁ n₂ : RTm Γ) → RTy Γ
auxB A cM m₁ m₂ n₁ n₂ =
  auxB' A m₁ (w n₁) (w m₂) (w (w n₂)) (w (w cM))

-- ★ the naturality: only the two BOUNDS can move, exactly as for `aAuxB`.
auxB-sub : {Γ Δ : Cx} {σ : Sub Γ Δ} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙))
           (n₁ n₂ : RTm Γ) →
           subTy σ (auxB A cM m₁ m₂ n₁ n₂)
         ≡ auxB (subTy σ A) (subTm (extS σ) cM) (subTm (extS σ) m₁)
                (subTm (extS σ) m₂) (subTm σ n₁) (subTm σ n₂)
auxB-sub {σ = σ} A cM m₁ m₂ n₁ n₂ =
  cong₆ auxB' refl refl (sub-w n₁)
        (sub-w {σ = extS σ} m₂)
        (sub-w² {σ = σ} n₂)
        (sub-w² {σ = extS σ} cM)
