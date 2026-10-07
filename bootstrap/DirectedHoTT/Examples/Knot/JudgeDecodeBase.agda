-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the typing judgements' decoders, the shared part
-- (PLAN-FAITHFUL F6).
--
-- A typing premise's subject is often NOT a subterm of the conclusion's
-- (⊢lam's `⊢ty A`, the endpoint premises of ⊢tr/⊢ap/⊢jsub, ⊢conv), so the
-- decoders recurse on the INHABITANT's size: a premise is a strict
-- subterm of the inhabitant.  A row decoder is not recursive itself — it
-- takes the induction hypotheses `IHTy N`/`IHTm N` for every inhabitant
-- below the bound `N`; `JudgeDecode` ties the knot with `Acc` (`Lib/Size`).
--
-- Here: the hypotheses' types, the index conversions a premise needs
-- (the Knot index reduces to the quoted Spec index by the F3 agreements),
-- and the `⊢conv` row — ONE row, the same at every term head (`TCVat`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.JudgeDecodeBase (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ; ⟶ᵀ*-IMu; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-trans )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.LogicalRelation 𝒮 using ( IsNormal )
open import DirectedHoTT.Metatheory.Canonicity 𝒮 wf using ( sz )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Cons; []; _∷_; conₗ; v₀; v₁; v₂; v₃; _,ₚ_ )
open import DirectedHoTT.Lib.NatNum 𝒮 𝓃 using ( num )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynRed 𝒮 𝓃 ok using ( mono-by; σₗ; _∷ʳ_; []ʳ )
open import DirectedHoTT.Lib.Decode 𝒮 wf
open import DirectedHoTT.Lib.Size 𝒮 wf using ( _<_; <ˡ; <ʳ )
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( quoteCtx; El-⌜Ty⌝ )
open import DirectedHoTT.Examples.Knot.Unquote 𝒮 wf using ( hdTm; pfTm; quote-hdTm; unqTy )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; tyIx; tmIx )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( w1 )
open import DirectedHoTT.Examples.Knot.Judge 𝒮 wf using ( D⊢ )
open import DirectedHoTT.Examples.Knot.JudgeConv 𝒮 wf using ( TCV; TCV-sub; TCVat )
open import DirectedHoTT.Examples.Knot.Conv 𝒮 wf using ( ⌜≅ᵀ⌝; ⌜≅ᵀ⌝-sub; El-⌜≅ᵀ⌝; K≅ᵀ )
open import DirectedHoTT.Examples.Knot.ConvDecode 𝒮 wf using ( decConvT )

------------------------------------------------------------------------
-- 1. The induction hypotheses: every inhabitant below `N` decodes.
------------------------------------------------------------------------

IHTy : ℕ → Set
IHTy N = (Γ : Ctx) (A : RTy ⌊ Γ ⌋) {r : RTm ε} → sz r < N →
         ◇ ⊢ r ∷ IMu JT D⊢ (tyIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTy A)) → IsNormal r → Γ ⊢ty A

IHTm : ℕ → Set
IHTm N = (Γ : Ctx) (t : RTm ⌊ Γ ⌋) (A : RTy ⌊ Γ ⌋) {r : RTm ε} → sz r < N →
         ◇ ⊢ r ∷ IMu JT D⊢ (tmIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTm t) (quoteTy A)) → IsNormal r → Γ ⊢ t ∷ A

------------------------------------------------------------------------
-- 2. A premise's Knot index reduces to the quoted Spec index (F3).
------------------------------------------------------------------------

-- tmIx j g t A = pair (pair (tag 1) j) (pair t (pair g A))
tmIx≅ : {j g g' t t' A A' : RTm ε} → g ⟶* g' → t ⟶* t' → A ⟶* A' →
        IMu JT D⊢ (tmIx j g t A) ≅ᵀ IMu JT D⊢ (tmIx j g' t' A')
tmIx≅ rg rt rA = red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-trans (⟶*-pairˡ rt) (⟶*-pairʳ (⟶*-trans (⟶*-pairˡ rg) (⟶*-pairʳ rA))))))

-- tyIx j g A = pair (pair (tag 0) j) (pair A (pair g unit))
tyIx≅ : {j g g' A A' : RTm ε} → g ⟶* g' → A ⟶* A' →
        IMu JT D⊢ (tyIx j g A) ≅ᵀ IMu JT D⊢ (tyIx j g' A')
tyIx≅ rg rA = red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-trans (⟶*-pairˡ rA) (⟶*-pairʳ (⟶*-pairˡ rg)))))

-- a numeral is a quoted number
num-quoteℕ : (m : ℕ) → num {ε} m ≡ quoteℕ m
num-quoteℕ zero    = refl
num-quoteℕ (suc m) = cong nsuc (num-quoteℕ m)

------------------------------------------------------------------------
-- 3. ★ The `⊢conv` row, at every term head: `(A₀ , r , e)` — a type, a
--    typing at it, a conversion to the target.
------------------------------------------------------------------------

private
  cv2-cong : (J J' G G' T T' A : RTm ε) (C C' : RTm ε) → J ≡ J' → G ≡ G' → T ≡ T' → C ≡ C' →
             dρ (tmIx J G T A) (dσ C (lam dι)) ≡ dρ (tmIx J' G' T' A) (dσ C' (lam dι))
  cv2-cong J J' G G' T T' A C C' refl refl refl refl = refl

dconv : {N : ℕ} → IHTm N → (Γ : Ctx) (t : RTm ⌊ Γ ⌋) (A : RTy ⌊ Γ ⌋) {q : RTm ε} → sz q < N →
        ◇ ⊢ q ∷ El (dpay JT D⊢ ⌜ TCVat (hdTm t) (dep ⌊ Γ ⌋) (pfTm t) (pair (quoteCtx Γ) (quoteTy A)) ⌝ᵗ) → IsNormal q →
        Γ ⊢ t ∷ A
dconv {N} ih Γ t A {q} hq dq nq =
  pay-σ (⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R)))) done nq
  ▷ λ { (a , (b , (eq , ((da , db) , (na , nb))))) →
  unqTy {Γ = ⌊ Γ ⌋} (⊢conv da (credᵀ El-⌜Ty⌝)) na
  ▷ λ { (A₀ , eqA) →
  pay-ρ (⊢-cast (cong (λ Z → El (dpay JT D⊢ Z)) (EQ a)) (⊢conv db (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ a) done)))))) done nb
  ▷ λ { (r , (b' , (eq' , ((dr , db') , (nr , nb'))))) →
  pay-σ db' done nb'
  ▷ λ { (e , (_ , (_ , ((de , _) , (ne , _))))) →
  ⊢conv (ih Γ t A₀ (<ˡ eq' (<ʳ eq hq))
           (subst (λ z → ◇ ⊢ r ∷ IMu JT D⊢ (tmIx j g z (quoteTy A₀))) (sym (quote-hdTm t))
             (subst (λ z → ◇ ⊢ r ∷ IMu JT D⊢ (tmIx j g T z)) eqA dr)) nr)
        (decConvT A₀ A (subst (λ z → ◇ ⊢ e ∷ K≅ᵀ j z X) eqA (⊢conv de El-⌜≅ᵀ⌝)) ne) } } } }
  where
    j g T X c : RTm ε
    j = dep ⌊ Γ ⌋
    g = quoteCtx Γ
    T = conₗ (hdTm t) (pfTm t)
    X = quoteTy A
    c = pair g X
    R : ⌜ TCV j (fst c) T (snd c) ⌝ᵗ ⟶* ⌜ TCV j g T X ⌝ᵗ
    R = mono-by {Δ = ε} {n = 4} {as = j ∷ fst c ∷ T ∷ snd c ∷ []} {as' = j ∷ g ∷ T ∷ X ∷ []}
          ⌜ TCV v₀ v₁ v₂ v₃ ⌝ᵗ
          (TCV-sub (σₗ (j ∷ fst c ∷ T ∷ snd c ∷ [])) v₀ v₁ v₂ v₃)
          (TCV-sub (σₗ (j ∷ g ∷ T ∷ X ∷ [])) v₀ v₁ v₂ v₃)
          (done ∷ʳ step (βfst g X) done ∷ʳ done ∷ʳ step (βsnd g X) done ∷ʳ []ʳ)
    EQ : (a : RTm ε) → subTm (single a) ⌜ tρ (tmIx (w1 j) (w1 g) (w1 T) v₀) (tσ (⌜≅ᵀ⌝ (w1 j) v₀ (w1 X)) tι) ⌝ᵗ
                       ≡ ⌜ tρ (tmIx j g T a) (tσ (⌜≅ᵀ⌝ j a X) tι) ⌝ᵗ
    EQ a = cv2-cong _ _ _ _ _ _ a _ _ (wk-cancel-tm a j) (wk-cancel-tm a g) (wk-cancel-tm a T)
             (trans (⌜≅ᵀ⌝-sub (single a) (w1 j) v₀ (w1 X)) (cong₂ (λ x y → ⌜≅ᵀ⌝ x a y) (wk-cancel-tm a j) (wk-cancel-tm a X)))
