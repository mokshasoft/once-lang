-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the hand-written typing rows, decoded
-- (PLAN-FAITHFUL F6): `⊢ref` (`Knot/RefJudge`).  Same discipline as the
-- generated rows (`JudgeDecodeTm`): each row along its own constructor's
-- reduction.
--
--   ⊢ref    the definition's type unquoted, its typing decoded at `◇`,
--           the Ford closed against `εwk-agree-ty`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.JudgeDecodeHand (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ; ⟶*-trans; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-natrecⁿ; ⟶*-dρʲ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.LogicalRelation 𝒮 using ( IsNormal )
open import DirectedHoTT.Metatheory.Canonicity 𝒮 wf using ( sz )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Cons; []; _∷_; conₗ; atᶜ; v₀; _,ₚ_; nth-z; nth-s )
open import DirectedHoTT.Lib.SynRed 𝒮 𝓃 ok using ( prj-tup )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
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
open import DirectedHoTT.Examples.Knot.Judge 𝒮 wf using ( D⊢ )
open import DirectedHoTT.Examples.Knot.RefJudge 𝒮 wf using ( T⊢ref; T⊢ref⁽1⁾; T⊢ref⁽1⁾-sub )
open import DirectedHoTT.Examples.Knot.Ref 𝒮 wf using ( bodyOf )
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( εwkK )
open import DirectedHoTT.Examples.Knot.OpAgree 𝒮 wf using ( εwk-agree-ty )
open import DirectedHoTT.Examples.Knot.JudgeDecodeBase 𝒮 wf

------------------------------------------------------------------------
-- ⊢ref : ◇ ⊢ b ∷ A₀ → Γ ⊢ ref d b ∷ εwkTy A₀
------------------------------------------------------------------------

private
  cong₃' : {A B C D : Set} (f : A → B → C → D) {a a' : A} {b b' : B} {x x' : C} →
           a ≡ a' → b ≡ b' → x ≡ x' → f a b x ≡ f a' b' x'
  cong₃' f refl refl refl = refl

jdref : {N : ℕ} → IHTy N → IHTm N → (Γ : Ctx) (d : ℕ) (b : RTm ε) (A : RTy ⌊ Γ ⌋) {w : RTm ε} → sz w < N →
        ◇ ⊢ w ∷ El (dpay JT D⊢ ⌜ T⊢ref (dep ⌊ Γ ⌋) (pair (quoteℕ d) (pair (quoteTm b) unit)) (pair (quoteCtx Γ) (quoteTy A)) ⌝ᵗ) →
        IsNormal w → Γ ⊢ ref d b ∷ A
jdref ihTy ihTm Γ d b A {w} hq dq nq =
  pay-σ dq done nq
  ▷ λ { (a , (b₁ , (eq₀ , ((da , db₁) , (na , nb₁))))) →
  unqTy {Γ = ε} (⊢conv da (credᵀ El-⌜Ty⌝)) na
  ▷ λ { (A₀ , eqA) →
  pay-ρ (⊢-cast (cong (λ Z → El (dpay JT D⊢ Z)) (EQ a)) (⊢conv db₁ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ a) done)))))) done nb₁
  ▷ λ { (r , (b₂ , (eq₁ , ((dr , db₂) , (nr , nb₂))))) →
  pay-σ db₂ done nb₂
  ▷ λ { (_ , (_ , (_ , ((dF , _) , (nF , _))))) →
  ihTm ◇ b A₀ (<ˡ eq₁ (<ʳ eq₀ hq))
       (subst (λ z → ◇ ⊢ r ∷ IMu JT D⊢ (tmIx nzero cε (quoteTm b) z)) eqA
         (⊢conv dr (tmIx≅ done (prj-tup {ws = quoteℕ d ∷ quoteTm b ∷ []} unit (atᶜ 1)) done))) nr
  ▷ λ D →
  quoteTy-inj A (εwkTy A₀)
    (nf-≅ (quoteTy-normal {Γ = ⌊ Γ ⌋} A) (quoteTy-normal {Γ = ⌊ Γ ⌋} (εwkTy A₀))
      (ctrn (csym (cred (βsnd g X)))
        (ctrn (subst (λ z → snd c ≅ εwkK 0 j z) eqA (idrefl-decᶜ dF nF)) (⟶*→≅ (εwk-agree-ty ⌊ Γ ⌋ A₀)))))
  ▷ λ eqT → subst (λ z → Γ ⊢ ref d b ∷ z) (sym eqT) (⊢ref D) } } } }
  where
    j g X p c : RTm ε
    j = dep ⌊ Γ ⌋
    g = quoteCtx Γ
    X = quoteTy A
    p = pair (quoteℕ d) (pair (quoteTm b) unit)
    c = pair g X
    EQ : (a : RTm ε) → subTm (single a) ⌜ T⊢ref⁽1⁾ (w1 j) (w1 (bodyOf p)) (w1 (snd c)) v₀ ⌝ᵗ ≡ ⌜ T⊢ref⁽1⁾ j (bodyOf p) (snd c) a ⌝ᵗ
    EQ a = trans (T⊢ref⁽1⁾-sub (single a) (w1 j) (w1 (bodyOf p)) (w1 (snd c)) v₀)
                 (cong₃' (λ J B C → ⌜ T⊢ref⁽1⁾ J B C a ⌝ᵗ) (wk-cancel-tm a j) (wk-cancel-tm a (bodyOf p)) (wk-cancel-tm a (snd c)))
