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
module DirectedHoTT.Examples.Knot.JudgeDecodeHand where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ; ⟶*-trans; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-natrecⁿ; ⟶*-dρʲ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal )
open import DirectedHoTT.Metatheory.Canonicity using ( sz )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; atᶜ; v₀; _,ₚ_; nth-z; nth-s )
open import DirectedHoTT.Lib.SynRed using ( prj-tup )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Decode
open import DirectedHoTT.Lib.PatDecode
open import DirectedHoTT.Lib.Size using ( _<_; <ˡ; <ʳ )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Ctx using ( quoteCtx; cε; El-⌜Ty⌝ )
open import DirectedHoTT.Examples.Knot.Unquote
open import DirectedHoTT.Examples.Knot.Lookup using ( rows )
open import DirectedHoTT.Examples.Knot.JudgeIx using ( JT; tmIx )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w2 )
open import DirectedHoTT.Examples.Knot.Judge using ( D⊢ )
open import DirectedHoTT.Examples.Knot.RefJudge using ( T⊢ref; T⊢ref⁽1⁾; T⊢ref⁽1⁾-sub )
open import DirectedHoTT.Examples.Knot.Ref using ( bodyOf )
open import DirectedHoTT.Examples.Knot.Ren using ( εwkK )
open import DirectedHoTT.Examples.Knot.OpAgree using ( εwk-agree-ty )
open import DirectedHoTT.Examples.Knot.JudgeDecodeBase

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
