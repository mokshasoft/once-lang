-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ THE CONVERSIONS ARE EXACT (PLAN-FAITHFUL F6):
-- the converse of `ConvAgree`.  A closed normal inhabitant of
-- `K≅ ⌜Γ⌝ ⌜t⌝ ⌜u⌝` is one of the four rows of the parametric fibre
-- (`Knot/Conv`), and each row is a Spec rule:
--
--     cred  — the σ-field decodes by `decRed`
--     crfl  — the Ford: `nf-≅` + quote injectivity
--     csym  — the ρ-field, by recursion
--     ctrn  — the middle σ-field unquoted, both ρ-fields by recursion
--
-- The subject does not shrink (ctrn's middle term is arbitrary), so the
-- recursion is on FUEL: the inhabitant's size (`sz`), which every peel
-- (`rows-dec`, `pay-σ`, `pay-ρ`) shrinks — `Lib/SynUnq`'s `szp`/`szˡ`/`szʳ`.
-- Chained with `▷` (no `with`: with-over-knot-contexts-ooms).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.ConvDecode (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.LogicalRelation 𝒮 using ( IsNormal )
open import DirectedHoTT.Metatheory.Canonicity 𝒮 wf using ( sz; _≤_; ≤-refl )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Cons; []; _∷_; conₗ; v₀; _,ₚ_; nth-z; nth-s )
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.Decode 𝒮 wf
open import DirectedHoTT.Lib.Size 𝒮 wf using ( szp; szˡ; szʳ )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( ⌜Ty⌝; El-⌜Ty⌝ )
open import DirectedHoTT.Examples.Knot.Unquote 𝒮 wf
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( ⌜Tm⌝; El-⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( w1 )
open import DirectedHoTT.Examples.Knot.RedIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Red 𝒮 wf using ( ⌜⟶⌝; El-⌜⟶⌝ )
open import DirectedHoTT.Examples.Knot.RedT 𝒮 wf using ( ⌜⟶ᵀ⌝; El-⌜⟶ᵀ⌝ )
open import DirectedHoTT.Examples.Knot.Conv 𝒮 wf
open import DirectedHoTT.Examples.Knot.RedDecode 𝒮 wf using ( decRed )
open import DirectedHoTT.Examples.Knot.RedTDecode 𝒮 wf using ( decRedT )

------------------------------------------------------------------------
-- 1. t ≅ u
------------------------------------------------------------------------

private
  -- the four rows, at the quoted subject `T` and target `c`
  R≅₀ R≅₁ R≅₂ R≅₃ : RTm ε → RTm ε → RTm ε → RTm ε
  R≅₀ j T c = dσ (⌜⟶⌝ j T c) (lam dι)
  R≅₁ j T c = dσ (⌜Id⌝ (⌜Tm⌝ j) T c) (lam dι)
  R≅₂ j T c = dρ (ix≅ j c T) dι
  R≅₃ j T c = dσ (⌜Tm⌝ j) (lam (dρ (ix≅ (w1 j) (w1 T) v₀) (dρ (ix≅ (w1 j) v₀ (w1 c)) dι)))

  Pay≅ : (RTm ε → RTm ε → RTm ε → RTm ε) → {Γ : Cx} → RTm Γ → RTm Γ → RTm ε → Set
  Pay≅ R {Γ} t u q = ◇ ⊢ q ∷ El (dpay Convₘ.J ≅F.DF (R (dep Γ) (quoteTm t) (quoteTm u)))

  -- a σ-row's payload at the quoted subject, back from the head view
  back : (R : RTm ε → RTm ε → RTm ε → RTm ε) {Γ : Cx} (t u : RTm Γ) {q : RTm ε} →
         ◇ ⊢ q ∷ El (dpay Convₘ.J ≅F.DF (R (dep Γ) (conₗ (hdTm t) (pfTm t)) (quoteTm u))) → Pay≅ R t u q
  back R {Γ} t u {q} dq = subst (λ z → ◇ ⊢ q ∷ El (dpay Convₘ.J ≅F.DF (R (dep Γ) z (quoteTm u)))) (sym (quote-hdTm t)) dq

  no0 : {A : Set} {q : RTm ε} → sz q ≤ zero → A
  no0 ()

  -- the ρ-field under the middle binder, instantiated
  mid : (j T v : RTm ε) → subTm (single v) (ix≅ (w1 j) (w1 T) v₀) ≡ ix≅ j T v
  mid j T v = cong₂ (λ a b → ix≅ a b v) (wk-cancel-tm v j) (wk-cancel-tm v T)

  mid' : (j c v : RTm ε) → subTm (single v) (ix≅ (w1 j) v₀ (w1 c)) ≡ ix≅ j v c
  mid' j c v = cong₂ (λ a b → ix≅ a v b) (wk-cancel-tm v j) (wk-cancel-tm v c)

decConvF : (f : ℕ) {Γ : Cx} (t u : RTm Γ) {k : RTm ε} → sz k ≤ f →
           ◇ ⊢ k ∷ K≅ (dep Γ) (quoteTm t) (quoteTm u) → IsNormal k → t ≅ u

-- ⚠ every peel that precedes a recursive call is a CLAUSE of a helper (the
--   peel passed as an argument): a recursive call under a `▷` lambda is
--   invisible to the termination checker
private
  row₀ : {Γ : Cx} (t u : RTm Γ) {q : RTm ε} → Pay≅ R≅₀ t u q → IsNormal q → t ≅ u
  row₀ t u dq nq =
    pay-σ dq done nq
    ▷ λ { (_ , (_ , (_ , ((da , _) , (na , _))))) → cred (decRed t (⊢conv da El-⌜⟶⌝) na) }

  row₁ : {Γ : Cx} (t u : RTm Γ) {q : RTm ε} → Pay≅ R≅₁ t u q → IsNormal q → t ≅ u
  row₁ t u dq nq =
    pay-σ dq done nq
    ▷ λ { (_ , (_ , (_ , ((da , _) , (na , _))))) →
          subst (λ z → t ≅ z) (quoteTm-inj t u (nf-≅ (quoteTm-normal t) (quoteTm-normal u) (idrefl-decᶜ da na))) crfl }

  -- csym: the ρ-field
  row₂ : (f : ℕ) {Γ : Cx} (t u : RTm Γ) {q : RTm ε} → sz q ≤ suc f →
         PayΡ Convₘ.J ≅F.DF (ix≅ (dep Γ) (quoteTm u) (quoteTm t)) dι q → t ≅ u
  row₂ f t u h (r , (b , (refl , ((dr , _) , (nr , _))))) = csym (decConvF f u t (szˡ r b h) dr nr)

  -- ctrn: the middle term (unquoted), then the two ρ-fields
  row₃ : (f : ℕ) {Γ : Cx} (t u : RTm Γ) {q : RTm ε} → sz q ≤ suc f →
         PayΣ Convₘ.J ≅F.DF (⌜Tm⌝ (dep Γ)) (lam (dρ (ix≅ (w1 (dep Γ)) (w1 (quoteTm t)) v₀) (dρ (ix≅ (w1 (dep Γ)) v₀ (w1 (quoteTm u))) dι))) q → t ≅ u
  row₃ᶜ : (f : ℕ) {Γ : Cx} (t u : RTm Γ) {v b : RTm ε} → sz b ≤ f →
          Σ (RTm Γ) (λ V → v ≡ quoteTm V) →
          PayΡ Convₘ.J ≅F.DF (subTm (single v) (ix≅ (w1 (dep Γ)) (w1 (quoteTm t)) v₀)) (subTm (single v) (dρ (ix≅ (w1 (dep Γ)) v₀ (w1 (quoteTm u))) dι)) b →
          t ≅ u
  row₃ᵈ : (f : ℕ) {Γ : Cx} (t u V : RTm Γ) {r₀ b : RTm ε} → sz r₀ ≤ f → sz b ≤ f →
          ◇ ⊢ r₀ ∷ K≅ (dep Γ) (quoteTm t) (quoteTm V) → IsNormal r₀ →
          PayΡ Convₘ.J ≅F.DF (ix≅ (dep Γ) (quoteTm V) (quoteTm u)) dι b → t ≅ u

  row₃ f {Γ} t u h (v , (b , (refl , ((dv , db) , (nv , nb))))) =
    row₃ᶜ f t u (szʳ v b h) (unqTm {Γ = Γ} (⊢conv dv (credᵀ El-⌜Tm⌝)) nv)
      (pay-ρ (⊢conv db (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ v) done))))) done nb)

  row₃ᶜ zero    t u () _ _
  row₃ᶜ (suc f) {Γ} t u {v} h (V , refl) (r₀ , (b' , (refl , ((dr₀ , db') , (nr₀ , nb'))))) =
    row₃ᵈ f t u V (szˡ r₀ b' h) (szʳ r₀ b' h)
      (⊢-cast (cong (λ z → IMu Convₘ.J ≅F.DF z) (mid (dep Γ) (quoteTm t) v)) dr₀) nr₀
      (pay-ρ (⊢-cast (cong (λ z → El (dpay Convₘ.J ≅F.DF (dρ z dι))) (mid' (dep Γ) (quoteTm u) v)) db') done nb')

  row₃ᵈ zero    t u V h₀ () dr₀ nr₀ _
  row₃ᵈ (suc f) t u V h₀ h dr₀ nr₀ (r₁ , (b , (refl , ((dr₁ , _) , (nr₁ , _))))) =
    ctrn (decConvF (suc f) t V h₀ dr₀ nr₀) (decConvF f V u (szˡ r₁ b h) dr₁ nr₁)

  -- the four rows
  rows≅ : (f : ℕ) {Γ : Cx} (t u : RTm Γ) {k : RTm ε} → sz k ≤ suc f →
          RowsDec Convₘ.J ≅F.DF (R≅₀ (dep Γ) (conₗ (hdTm t) (pfTm t)) (quoteTm u) ∷ R≅₁ (dep Γ) (conₗ (hdTm t) (pfTm t)) (quoteTm u)
                                 ∷ R≅₂ (dep Γ) (conₗ (hdTm t) (pfTm t)) (quoteTm u) ∷ R≅₃ (dep Γ) (conₗ (hdTm t) (pfTm t)) (quoteTm u) ∷ []) k →
          t ≅ u
  rows≅ f t u h (_ , (_ , (_ , (nth-z , (_ , (dq , nq)))))) = row₀ t u (back R≅₀ t u dq) nq
  rows≅ f t u h (_ , (_ , (_ , (nth-s nth-z , (_ , (dq , nq)))))) = row₁ t u (back R≅₁ t u dq) nq
  rows≅ zero t u h (_ , (_ , (q , (nth-s (nth-s nth-z) , (refl , _))))) = no0 {q = q} (szp 2 q h)
  rows≅ (suc f) t u h (_ , (_ , (q , (nth-s (nth-s nth-z) , (refl , (dq , nq)))))) =
    row₂ f t u (szp 2 q h) (pay-ρ (back R≅₂ t u dq) done nq)
  rows≅ zero t u h (_ , (_ , (q , (nth-s (nth-s (nth-s nth-z)) , (refl , _))))) = no0 {q = q} (szp 3 q h)
  rows≅ (suc f) t u h (_ , (_ , (q , (nth-s (nth-s (nth-s nth-z)) , (refl , (dq , nq)))))) =
    row₃ f t u (szp 3 q h) (pay-σ (back R≅₃ t u dq) done nq)

decConvF zero    t u () dk nk
decConvF (suc f) {Γ} t u {k} h dk nk =
  rows≅ f t u h
    (rows-dec {I = Convₘ.J} {D = ≅F.DF} {i = ix≅ (dep Γ) T c} {m = 4}
              {Cs = R≅₀ (dep Γ) T c ∷ R≅₁ (dep Γ) T c ∷ R≅₂ (dep Γ) T c ∷ R≅₃ (dep Γ) T c ∷ []}
       (≅F.fibF {s = 1} {k = hdTm t} {j = dep Γ} {p = pfTm t} {c = c} (atᵍ 1) (nhTm t))
       (subst (λ z → ◇ ⊢ k ∷ K≅ (dep Γ) z c) (quote-hdTm t) dk) nk)
  where
    T c : RTm ε
    T = conₗ (hdTm t) (pfTm t)
    c = quoteTm u

decConv : {Γ : Cx} (t u : RTm Γ) {k : RTm ε} → ◇ ⊢ k ∷ K≅ (dep Γ) (quoteTm t) (quoteTm u) → IsNormal k → t ≅ u
decConv t u {k} dk nk = decConvF (sz k) t u ≤-refl dk nk

------------------------------------------------------------------------
-- 2. A ≅ᵀ B
------------------------------------------------------------------------

private
  -- the four rows, at the quoted subject `T` and target `c`
  R≅ᵀ₀ R≅ᵀ₁ R≅ᵀ₂ R≅ᵀ₃ : RTm ε → RTm ε → RTm ε → RTm ε
  R≅ᵀ₀ j T c = dσ (⌜⟶ᵀ⌝ j T c) (lam dι)
  R≅ᵀ₁ j T c = dσ (⌜Id⌝ (⌜Ty⌝ j) T c) (lam dι)
  R≅ᵀ₂ j T c = dρ (ix≅ᵀ j c T) dι
  R≅ᵀ₃ j T c = dσ (⌜Ty⌝ j) (lam (dρ (ix≅ᵀ (w1 j) (w1 T) v₀) (dρ (ix≅ᵀ (w1 j) v₀ (w1 c)) dι)))

  Pay≅ᵀ : (RTm ε → RTm ε → RTm ε → RTm ε) → {Γ : Cx} → RTy Γ → RTy Γ → RTm ε → Set
  Pay≅ᵀ R {Γ} t u q = ◇ ⊢ q ∷ El (dpay ConvTₘ.J ≅ᵀF.DF (R (dep Γ) (quoteTy t) (quoteTy u)))

  -- a σ-row's payload at the quoted subject, backᵀ from the head view
  backᵀ : (R : RTm ε → RTm ε → RTm ε → RTm ε) {Γ : Cx} (t u : RTy Γ) {q : RTm ε} →
         ◇ ⊢ q ∷ El (dpay ConvTₘ.J ≅ᵀF.DF (R (dep Γ) (conₗ (hdTy t) (pfTy t)) (quoteTy u))) → Pay≅ᵀ R t u q
  backᵀ R {Γ} t u {q} dq = subst (λ z → ◇ ⊢ q ∷ El (dpay ConvTₘ.J ≅ᵀF.DF (R (dep Γ) z (quoteTy u)))) (sym (quote-hdTy t)) dq

  no0ᵀ : {A : Set} {q : RTm ε} → sz q ≤ zero → A
  no0ᵀ ()

  -- the ρ-field under the middle binder, instantiated
  midᵀ : (j T v : RTm ε) → subTm (single v) (ix≅ᵀ (w1 j) (w1 T) v₀) ≡ ix≅ᵀ j T v
  midᵀ j T v = cong₂ (λ a b → ix≅ᵀ a b v) (wk-cancel-tm v j) (wk-cancel-tm v T)

  midᵀ' : (j c v : RTm ε) → subTm (single v) (ix≅ᵀ (w1 j) v₀ (w1 c)) ≡ ix≅ᵀ j v c
  midᵀ' j c v = cong₂ (λ a b → ix≅ᵀ a v b) (wk-cancel-tm v j) (wk-cancel-tm v c)

decConvTF : (f : ℕ) {Γ : Cx} (t u : RTy Γ) {k : RTm ε} → sz k ≤ f →
           ◇ ⊢ k ∷ K≅ᵀ (dep Γ) (quoteTy t) (quoteTy u) → IsNormal k → t ≅ᵀ u

-- ⚠ every peel that precedes a recursive call is a CLAUSE of a helper (the
--   peel passed as an argument): a recursive call under a `▷` lambda is
--   invisible to the termination checker
private
  rowᵀ₀ : {Γ : Cx} (t u : RTy Γ) {q : RTm ε} → Pay≅ᵀ R≅ᵀ₀ t u q → IsNormal q → t ≅ᵀ u
  rowᵀ₀ t u dq nq =
    pay-σ dq done nq
    ▷ λ { (_ , (_ , (_ , ((da , _) , (na , _))))) → credᵀ (decRedT t (⊢conv da El-⌜⟶ᵀ⌝) na) }

  rowᵀ₁ : {Γ : Cx} (t u : RTy Γ) {q : RTm ε} → Pay≅ᵀ R≅ᵀ₁ t u q → IsNormal q → t ≅ᵀ u
  rowᵀ₁ t u dq nq =
    pay-σ dq done nq
    ▷ λ { (_ , (_ , (_ , ((da , _) , (na , _))))) →
          subst (λ z → t ≅ᵀ z) (quoteTy-inj t u (nf-≅ (quoteTy-normal t) (quoteTy-normal u) (idrefl-decᶜ da na))) crflᵀ }

  -- csym: the ρ-field
  rowᵀ₂ : (f : ℕ) {Γ : Cx} (t u : RTy Γ) {q : RTm ε} → sz q ≤ suc f →
         PayΡ ConvTₘ.J ≅ᵀF.DF (ix≅ᵀ (dep Γ) (quoteTy u) (quoteTy t)) dι q → t ≅ᵀ u
  rowᵀ₂ f t u h (r , (b , (refl , ((dr , _) , (nr , _))))) = csymᵀ (decConvTF f u t (szˡ r b h) dr nr)

  -- ctrn: the middle term (unquoted), then the two ρ-fields
  rowᵀ₃ : (f : ℕ) {Γ : Cx} (t u : RTy Γ) {q : RTm ε} → sz q ≤ suc f →
         PayΣ ConvTₘ.J ≅ᵀF.DF (⌜Ty⌝ (dep Γ)) (lam (dρ (ix≅ᵀ (w1 (dep Γ)) (w1 (quoteTy t)) v₀) (dρ (ix≅ᵀ (w1 (dep Γ)) v₀ (w1 (quoteTy u))) dι))) q → t ≅ᵀ u
  rowᵀ₃ᶜ : (f : ℕ) {Γ : Cx} (t u : RTy Γ) {v b : RTm ε} → sz b ≤ f →
          Σ (RTy Γ) (λ V → v ≡ quoteTy V) →
          PayΡ ConvTₘ.J ≅ᵀF.DF (subTm (single v) (ix≅ᵀ (w1 (dep Γ)) (w1 (quoteTy t)) v₀)) (subTm (single v) (dρ (ix≅ᵀ (w1 (dep Γ)) v₀ (w1 (quoteTy u))) dι)) b →
          t ≅ᵀ u
  rowᵀ₃ᵈ : (f : ℕ) {Γ : Cx} (t u V : RTy Γ) {r₀ b : RTm ε} → sz r₀ ≤ f → sz b ≤ f →
          ◇ ⊢ r₀ ∷ K≅ᵀ (dep Γ) (quoteTy t) (quoteTy V) → IsNormal r₀ →
          PayΡ ConvTₘ.J ≅ᵀF.DF (ix≅ᵀ (dep Γ) (quoteTy V) (quoteTy u)) dι b → t ≅ᵀ u

  rowᵀ₃ f {Γ} t u h (v , (b , (refl , ((dv , db) , (nv , nb))))) =
    rowᵀ₃ᶜ f t u (szʳ v b h) (unqTy {Γ = Γ} (⊢conv dv (credᵀ El-⌜Ty⌝)) nv)
      (pay-ρ (⊢conv db (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ v) done))))) done nb)

  rowᵀ₃ᶜ zero    t u () _ _
  rowᵀ₃ᶜ (suc f) {Γ} t u {v} h (V , refl) (r₀ , (b' , (refl , ((dr₀ , db') , (nr₀ , nb'))))) =
    rowᵀ₃ᵈ f t u V (szˡ r₀ b' h) (szʳ r₀ b' h)
      (⊢-cast (cong (λ z → IMu ConvTₘ.J ≅ᵀF.DF z) (midᵀ (dep Γ) (quoteTy t) v)) dr₀) nr₀
      (pay-ρ (⊢-cast (cong (λ z → El (dpay ConvTₘ.J ≅ᵀF.DF (dρ z dι))) (midᵀ' (dep Γ) (quoteTy u) v)) db') done nb')

  rowᵀ₃ᵈ zero    t u V h₀ () dr₀ nr₀ _
  rowᵀ₃ᵈ (suc f) t u V h₀ h dr₀ nr₀ (r₁ , (b , (refl , ((dr₁ , _) , (nr₁ , _))))) =
    ctrnᵀ (decConvTF (suc f) t V h₀ dr₀ nr₀) (decConvTF f V u (szˡ r₁ b h) dr₁ nr₁)

  -- the four rows
  rows≅ᵀ : (f : ℕ) {Γ : Cx} (t u : RTy Γ) {k : RTm ε} → sz k ≤ suc f →
          RowsDec ConvTₘ.J ≅ᵀF.DF (R≅ᵀ₀ (dep Γ) (conₗ (hdTy t) (pfTy t)) (quoteTy u) ∷ R≅ᵀ₁ (dep Γ) (conₗ (hdTy t) (pfTy t)) (quoteTy u)
                                 ∷ R≅ᵀ₂ (dep Γ) (conₗ (hdTy t) (pfTy t)) (quoteTy u) ∷ R≅ᵀ₃ (dep Γ) (conₗ (hdTy t) (pfTy t)) (quoteTy u) ∷ []) k →
          t ≅ᵀ u
  rows≅ᵀ f t u h (_ , (_ , (_ , (nth-z , (_ , (dq , nq)))))) = rowᵀ₀ t u (backᵀ R≅ᵀ₀ t u dq) nq
  rows≅ᵀ f t u h (_ , (_ , (_ , (nth-s nth-z , (_ , (dq , nq)))))) = rowᵀ₁ t u (backᵀ R≅ᵀ₁ t u dq) nq
  rows≅ᵀ zero t u h (_ , (_ , (q , (nth-s (nth-s nth-z) , (refl , _))))) = no0ᵀ {q = q} (szp 2 q h)
  rows≅ᵀ (suc f) t u h (_ , (_ , (q , (nth-s (nth-s nth-z) , (refl , (dq , nq)))))) =
    rowᵀ₂ f t u (szp 2 q h) (pay-ρ (backᵀ R≅ᵀ₂ t u dq) done nq)
  rows≅ᵀ zero t u h (_ , (_ , (q , (nth-s (nth-s (nth-s nth-z)) , (refl , _))))) = no0ᵀ {q = q} (szp 3 q h)
  rows≅ᵀ (suc f) t u h (_ , (_ , (q , (nth-s (nth-s (nth-s nth-z)) , (refl , (dq , nq)))))) =
    rowᵀ₃ f t u (szp 3 q h) (pay-σ (backᵀ R≅ᵀ₃ t u dq) done nq)

decConvTF zero    t u () dk nk
decConvTF (suc f) {Γ} t u {k} h dk nk =
  rows≅ᵀ f t u h
    (rows-dec {I = ConvTₘ.J} {D = ≅ᵀF.DF} {i = ix≅ᵀ (dep Γ) T c} {m = 4}
              {Cs = R≅ᵀ₀ (dep Γ) T c ∷ R≅ᵀ₁ (dep Γ) T c ∷ R≅ᵀ₂ (dep Γ) T c ∷ R≅ᵀ₃ (dep Γ) T c ∷ []}
       (≅ᵀF.fibF {s = 0} {k = hdTy t} {j = dep Γ} {p = pfTy t} {c = c} (atᵍ 0) (nhTy t))
       (subst (λ z → ◇ ⊢ k ∷ K≅ᵀ (dep Γ) z c) (quote-hdTy t) dk) nk)
  where
    T c : RTm ε
    T = conₗ (hdTy t) (pfTy t)
    c = quoteTy u

decConvT : {Γ : Cx} (t u : RTy Γ) {k : RTm ε} → ◇ ⊢ k ∷ K≅ᵀ (dep Γ) (quoteTy t) (quoteTy u) → IsNormal k → t ≅ᵀ u
decConvT t u {k} dk nk = decConvTF (sz k) t u ≤-refl dk nk
