-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the hand-written typing rows, decoded
-- (PLAN-FAITHFUL F6): `⊢ref` (`Knot/RefJudge`).  Same discipline as the
-- generated rows (`JudgeDecodeTm`): each row along its own constructor's
-- reduction.
--
--   ⊢ref    (PLAN-REF K4) the side condition decoded to `d <ˢ (Defs.size 𝒮)`
--           (`homLt`), the Ford closed against the declared type looked up
--           in the quoted signature (`typesQ-at`) and `εwk-agree-ty`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PwCore as Core₀
module DirectedHoTT.Examples.Knot.JudgeDecodeHand (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ; ⟶*-trans; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-natrecⁿ; ⟶*-dρʲ )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.LogicalRelation 𝒮 using ( IsNormal )
open import DirectedHoTT.Metatheory.Canonicity 𝒮 wf using ( sz )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Cons; []; _∷_; conₗ; atᶜ; v₀; _,ₚ_; nth-z; nth-s )
open import DirectedHoTT.Lib.SynRed 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( prj-tup )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Decode 𝒮 wf
open import DirectedHoTT.Lib.PatDecode 𝒮 wf
open import DirectedHoTT.Lib.Size 𝒮 wf using ( _<_; <ˡ; <ʳ )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( quoteCtx; cε; El-⌜Ty⌝ )
open import DirectedHoTT.Examples.Knot.Unquote 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( rows )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; tmIx )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( w1; w2 )
open import DirectedHoTT.Examples.Knot.Judge 𝒮 wf core using ( D⊢ )
open import DirectedHoTT.Examples.Knot.RefJudge 𝒮 wf core using ( T⊢ref; T⊢refT; T⊢refT-sub )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( sigT; boundT; typesQ )
open import DirectedHoTT.Examples.Knot.QuoteSig 𝒮 wf using ( q𝒮; t𝒮; homLt; typesQ-at )
open import DirectedHoTT.Lib.Strong 𝒮 (Defs.size 𝒮) using ( El-homNat )
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( εwkK )
open import DirectedHoTT.Examples.Knot.OpAgree 𝒮 wf using ( εwk-agree-ty )
open import DirectedHoTT.Examples.Knot.JudgeDecodeBase 𝒮 wf core

------------------------------------------------------------------------
-- ⊢ref : d <ˢ (Defs.size 𝒮) → Γ ⊢ ref d ∷ εwkTy (type 𝒮 d)
------------------------------------------------------------------------

jdref : {N : ℕ} → IHTy N → IHTm N → (Γ : Ctx) (d : ℕ) (A : RTy ⌊ Γ ⌋) {w : RTm ε} → sz w < N →
        ◇ ⊢ w ∷ El (dpay JT (D⊢ t𝒮) ⌜ T⊢ref t𝒮 (dep ⌊ Γ ⌋) (pair (quoteℕ d) unit) (pair (quoteCtx Γ) (quoteTy A)) ⌝ᵗ) →
        IsNormal w → Γ ⊢ ref d ∷ A
jdref _ _ Γ d A {w} _ dq nq =
  pay-σ dq done nq
  ▷ λ { (h , (_ , (_ , ((dH , dR) , (_ , nR))))) →
  pay-σ dR (step (β _ h) (subst (λ z → z ⟶* _) (sym (EQ h)) done)) nR
  ▷ λ { (_ , (_ , (_ , ((dF , _) , (nF , _))))) →
  quoteTy-inj A (εwkTy (Defs.type 𝒮 d))
    (nf-≅ (quoteTy-normal {Γ = ⌊ Γ ⌋} A) (quoteTy-normal {Γ = ⌊ Γ ⌋} (εwkTy (Defs.type 𝒮 d)))
      (ctrn (csym (cred (βsnd g X))) (ctrn (idrefl-decᶜ dF nF) (⟶*→≅ TR))))
  ▷ λ eqT → subst (λ z → Γ ⊢ ref d ∷ z) (sym eqT) (⊢ref (homLt d (Defs.size 𝒮) (⊢conv dH (red→≅ᵀ HR)))) } }
  where
    j g X n' c : RTm ε
    j = dep ⌊ Γ ⌋
    g = quoteCtx Γ
    X = quoteTy A
    n' = fst (pair (quoteℕ d) unit)
    c = pair g X
    EQ : (h : RTm ε) → subTm (single h) ⌜ T⊢refT (w1 t𝒮) (w1 j) (w1 n') (w1 (snd c)) ⌝ᵗ ≡ ⌜ T⊢refT t𝒮 j n' (snd c) ⌝ᵗ
    EQ h = trans (T⊢refT-sub (single h) (w1 t𝒮) (w1 j) (w1 n') (w1 (snd c)))
                 (cong₄ (λ a b x y → ⌜ T⊢refT a b x y ⌝ᵗ) (wk-cancel-tm h t𝒮) (wk-cancel-tm h j) (wk-cancel-tm h n') (wk-cancel-tm h (snd c)))
    nR' : n' ⟶* num d
    nR' = step (βfst (quoteℕ d) unit) (subst (λ z → quoteℕ d ⟶* z) (quoteℕ-num d) done)
    -- the side condition at numerals: the name out of the payload, the bound out of the parameter
    HR : El (⌜Hom⌝ ⌜Nat⌝ (nsuc n') (boundT t𝒮)) ⟶ᵀ* Hom Nat (nsuc (num d)) (num (Defs.size 𝒮))
    HR = ⟶ᵀ*-trans (El-homNat _ _) (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (⟶*-nsuc nR')) (⟶ᵀ*-Homʳ (step (βsnd q𝒮 (num (Defs.size 𝒮))) done)))
    -- the declared type: the signature out of the parameter, then the lookup, computed
    TR : εwkK 0 j (typesQ (sigT t𝒮) n') ⟶* quoteTy (εwkTy {⌊ Γ ⌋} (Defs.type 𝒮 d))
    TR = ⟶*-trans (⟶*-natrecᶻ (⟶*-trans (⟶*-appˡ (⟶*-fst (⟶*-snd (step (βfst q𝒮 (num (Defs.size 𝒮))) done))))
                                (⟶*-trans (⟶*-appʳ nR') (typesQ-at 𝒮 d))))
                  (εwk-agree-ty ⌊ Γ ⌋ (Defs.type 𝒮 d))
