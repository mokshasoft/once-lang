------------------------------------------------------------------------
-- OCP-0009 · LIB — ★ `⊢ty` FOR AN INDEXED PAYLOAD, GENERICALLY.
--
-- The missing twin of `Metatheory/SubjectReduction.iihTy-wf`: that one
-- says the IH TUPLE's type is well formed, this one says the PAYLOAD's
-- is.  Both are one induction over the `ICon`.
--
-- ⚠ WHY IT IS NEEDED, and it is a COST result, not a gap.  A method of
--   `imethTy` binds the payload, so writing one requires `⊢ty` of the
--   payload type.  Doing that CONCRETELY — a hand-built `ty-Σ` chain
--   that Agda must then unify against the computed `ipayTy` — is what
--   makes `Examples/Knot/Sz` blow up: measured, a 2-field row costs 1s,
--   a 3-field row 9s, and `ordtr` (SIX fields) exhausts a 7.7 GB box on
--   its own.  Handing Agda a derivation whose type is ALREADY
--   `ipayTy D I σ C` removes the unification entirely.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IPay where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; Unit; Σ'; El; IMu
        ; ICon; IDesc; iι; iρ; iκ; ipayTy; Sub; extS; subTm; subTy
        ; εwkTy; εwk-sub )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢ty_; ty-Unit; ty-Σ; ty-El; ty-IMu
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ; IDescWf )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( Sub⊢; Sub⊢-ext; sub-lemma; ⊢-cast )

ipayTy-wf : {Γ Θ : Ctx} (D : IDesc) (I : RTy ε)
            (σ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋) (C : ICon ⌊ Θ ⌋) →
            IDescWf I D → IConWf D I Θ C → Sub⊢ Θ Γ σ →
            Γ ⊢ty ipayTy D I σ C
ipayTy-wf D I σ iι wD wC hσ = ty-Unit
ipayTy-wf D I σ (iρ j C) wD (iwf-ρ .j dj wC) hσ =
  ty-Σ (ty-IMu wD (⊢-cast (εwk-sub σ I) (sub-lemma dj hσ)))
       (ipayTy-wf D I (extS σ) C wD wC (Sub⊢-ext hσ))
ipayTy-wf D I σ (iκ κ C) wD (iwf-κ .κ _ dcode wC) hσ =
  ty-Σ (ty-El (sub-lemma dcode hσ))
       (ipayTy-wf D I (extS σ) C wD wC (Sub⊢-ext hσ))
