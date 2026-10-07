-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the CONSTRUCTORS of the conversions `≅` and `≅ᵀ`
-- (`Knot/Conv`), each written ONCE for every head: the four rules have a
-- bare-variable subject, so the fibre at `conₗ k p` is the same four rows
-- for every k, and a constructor is generic in the head (its `NthSh` and
-- payload typing are arguments).  No projections: the rows read the
-- subject and the target directly.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PwCore as Core₀
module DirectedHoTT.Examples.Knot.ConvCon (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Cons; []; _∷_; tag; conₗ; nth-z; atᶜ; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( PayV; ⊢conP )
open import DirectedHoTT.Lib.SynFib 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( ⊢conRowₖ )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( toTy; hereTy; rows )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( ⌜Tm⌝; ⊢⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( w1; hereTm; toTm; wkN; wkK )
open import DirectedHoTT.Examples.Knot.RedIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Red 𝒮 wf core using ( ⌜⟶⌝; ⊢⌜⟶⌝ )
open import DirectedHoTT.Examples.Knot.RedT 𝒮 wf core using ( ⌜⟶ᵀ⌝; ⊢⌜⟶ᵀ⌝ )
open import DirectedHoTT.Examples.Knot.Conv 𝒮 wf core
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜QSig⌝ )

private
  variable
    Δ : Cx

  -- ctrn's σ-step: the middle term instantiated
  trc : (ix : RTm Δ → RTm Δ → RTm Δ → RTm Δ) (J J' T T' X X' V : RTm Δ) → J ≡ J' → T ≡ T' → X ≡ X' →
        dρ (ix J T V) (dρ (ix J V X) dι) ≡ dρ (ix J' T' V) (dρ (ix J' V X') dι)
  trc ix J J' T T' X X' V refl refl refl = refl

------------------------------------------------------------------------
-- 1. t ≅ u, at a subject `conₗ k p` of ANY term head
------------------------------------------------------------------------

module _ {Ξ : Ctx} {k : ℕ} {sh : Shape} {q j p u : RTm ⌊ Ξ ⌋} (nh : NthSh TmShs k sh) (dq : Ξ ⊢ q ∷ El ⌜QSig⌝) (dj : Ξ ⊢ j ∷ El ⌜Nat⌝)
         (dp : Ξ ⊢ p ∷ PayV sh ((tag 1) ,ₚ j) (SI 2) (SD KSig)) (du : Ξ ⊢ u ∷ K 1 j) where
  private
    t : RTm ⌊ Ξ ⌋
    t = conₗ k p
    dt : Ξ ⊢ t ∷ K 1 j
    dt = ⊢conP KOK (atᵍ 1) nh dj dp
    Cs : Cons ⌊ Ξ ⌋ 4
    Cs = dσ (⌜⟶⌝ q j t u) (lam dι) ∷ dσ (⌜Id⌝ (⌜Tm⌝ j) t u) (lam dι) ∷ dρ (ix≅ j u t) dι
         ∷ dσ (⌜Tm⌝ j) (lam (dρ (ix≅ (w1 j) (w1 t) v₀) (dρ (ix≅ (w1 j) v₀ (w1 u)) dι))) ∷ []
    fib : app (≅F.DF q) (ix≅ j t u) ⟶* rows Cs
    fib = ≅F.fibF {s = 1} {k = k} {q = q} {j = j} {p = p} {c = u} (atᵍ 1) nh

  -- ★ `cred : t ⟶ u → t ≅ u`
  cred≅ : {e : RTm ⌊ Ξ ⌋} → Ξ ⊢ e ∷ El (⌜⟶⌝ q j t u) → Ξ ⊢ conₗ 0 (e ,ₚ unit) ∷ K≅ q j t u
  cred≅ {e} de =
    ⊢conRowₖ {Ξ} {4} {0} {Convₘ.J} {(≅F.DF q)} {ix≅ j t u} {_} {pair e unit} {Cs} nth-z Convₘ.⊢J (≅F.⊢DF dq) (⊢ix≅ dj dt du) fib
      (allC≅ dq dj dt du) (⊢payσ Convₘ.⊢J (≅F.⊢DF dq) {a = e} {p = unit} (ok-σ (⊢⌜⟶⌝ dq dj dt du) ok-ι) de (⊢payι Convₘ.⊢J (≅F.⊢DF dq) ⊢unit))

  -- ★ `csym : u ≅ t → t ≅ u`
  csym≅ : {r : RTm ⌊ Ξ ⌋} → Ξ ⊢ r ∷ K≅ q j u t → Ξ ⊢ conₗ 2 (r ,ₚ unit) ∷ K≅ q j t u
  csym≅ {r} dr =
    ⊢conRowₖ {Ξ} {4} {2} {Convₘ.J} {(≅F.DF q)} {ix≅ j t u} {_} {pair r unit} {Cs} (atᶜ 2) Convₘ.⊢J (≅F.⊢DF dq) (⊢ix≅ dj dt du) fib
      (allC≅ dq dj dt du) (⊢payρ Convₘ.⊢J (≅F.⊢DF dq) {r = r} {p = unit} (ok-ρ (⊢ix≅ dj du dt) ok-ι) dr (⊢payι Convₘ.⊢J (≅F.⊢DF dq) ⊢unit))

  -- ★ `ctrn : t ≅ v → v ≅ u → t ≅ u`
  ctrn≅ : {v r₁ r₂ : RTm ⌊ Ξ ⌋} → Ξ ⊢ v ∷ K 1 j → Ξ ⊢ r₁ ∷ K≅ q j t v → Ξ ⊢ r₂ ∷ K≅ q j v u →
          Ξ ⊢ conₗ 3 (v ,ₚ r₁ ,ₚ r₂ ,ₚ unit) ∷ K≅ q j t u
  ctrn≅ {v} {r₁} {r₂} dv dr₁ dr₂ =
    ⊢conRowₖ {Ξ} {4} {3} {Convₘ.J} {(≅F.DF q)} {ix≅ j t u} {_} {pair v (r₁ ,ₚ r₂ ,ₚ unit)} {Cs} (atᶜ 3)
      Convₘ.⊢J (≅F.⊢DF dq) (⊢ix≅ dj dt du) fib (allC≅ dq dj dt du)
      (⊢payσ Convₘ.⊢J (≅F.⊢DF dq) {a = v} {p = pair r₁ (r₂ ,ₚ unit)}
         (Convₘ.okσ (⊢⌜Tm⌝ dj) (ok-ρ (⊢ix≅ (wkN dj) (wkK dt) (hereTm {m = j})) (ok-ρ (⊢ix≅ (wkN dj) (hereTm {m = j}) (wkK du)) ok-ι)))
         (toTm dv)
         (⊢-cast {Ξ} {pair r₁ (r₂ ,ₚ unit)} {El (dpay Convₘ.J (≅F.DF q) (dρ (ix≅ j t v) (dρ (ix≅ j v u) dι)))}
                 {El (dpay Convₘ.J (≅F.DF q) (subTm (single v) (dρ (ix≅ (w1 j) (w1 t) v₀) (dρ (ix≅ (w1 j) v₀ (w1 u)) dι))))}
                 (cong (λ Z → El (dpay Convₘ.J (≅F.DF q) Z)) (sym (trc ix≅ _ _ _ _ _ _ v (wk-cancel-tm v j) (wk-cancel-tm v t) (wk-cancel-tm v u))))
            (⊢payρ Convₘ.⊢J (≅F.⊢DF dq) {r = r₁} {p = pair r₂ unit} (ok-ρ (⊢ix≅ dj dt dv) (ok-ρ (⊢ix≅ dj dv du) ok-ι)) dr₁
              (⊢payρ Convₘ.⊢J (≅F.⊢DF dq) {r = r₂} {p = unit} (ok-ρ (⊢ix≅ dj dv du) ok-ι) dr₂ (⊢payι Convₘ.⊢J (≅F.⊢DF dq) ⊢unit)))))

-- ★ `crfl : t ≅ t`
crfl≅ : {Ξ : Ctx} {k : ℕ} {sh : Shape} {q j p : RTm ⌊ Ξ ⌋} (nh : NthSh TmShs k sh) → Ξ ⊢ q ∷ El ⌜QSig⌝ → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Ξ ⊢ p ∷ PayV sh ((tag 1) ,ₚ j) (SI 2) (SD KSig) →
        Ξ ⊢ conₗ 1 ((idrefl (⌜Tm⌝ j) (conₗ k p)) ,ₚ unit) ∷ K≅ q j (conₗ k p) (conₗ k p)
crfl≅ {Ξ} {k} {sh} {q} {j} {p} nh dq dj dp =
  ⊢conRowₖ {Ξ} {4} {1} {Convₘ.J} {(≅F.DF q)} {ix≅ j t t} {_} {pair (idrefl (⌜Tm⌝ j) t) unit}
           {dσ (⌜⟶⌝ q j t t) (lam dι) ∷ dσ (⌜Id⌝ (⌜Tm⌝ j) t t) (lam dι) ∷ dρ (ix≅ j t t) dι
            ∷ dσ (⌜Tm⌝ j) (lam (dρ (ix≅ (w1 j) (w1 t) v₀) (dρ (ix≅ (w1 j) v₀ (w1 t)) dι))) ∷ []}
           (atᶜ 1) Convₘ.⊢J (≅F.⊢DF dq) (⊢ix≅ dj dt dt)
    (≅F.fibF {s = 1} {k = k} {q = q} {j = j} {p = p} {c = t} (atᵍ 1) nh) (allC≅ dq dj dt dt)
    (⊢payσ Convₘ.⊢J (≅F.⊢DF dq) {a = idrefl (⌜Tm⌝ j) t} {p = unit} (ok-σ (⊢⌜Id⌝ (⊢⌜Tm⌝ dj) (toTm dt) (toTm dt)) ok-ι)
       (⊢conv (⊢idrefl (⊢⌜Tm⌝ dj) (toTm dt)) (csymᵀ (credᵀ (El-⌜Id⌝ (⌜Tm⌝ j) t t))))
       (⊢payι Convₘ.⊢J (≅F.⊢DF dq) ⊢unit))
  where
    t = conₗ k p
    dt = ⊢conP KOK (atᵍ 1) nh dj dp

------------------------------------------------------------------------
-- 2. A ≅ᵀ B, at a subject `conₗ k p` of ANY type head
------------------------------------------------------------------------

module _ {Ξ : Ctx} {k : ℕ} {sh : Shape} {q j p u : RTm ⌊ Ξ ⌋} (nh : NthSh TyShs k sh) (dq : Ξ ⊢ q ∷ El ⌜QSig⌝) (dj : Ξ ⊢ j ∷ El ⌜Nat⌝)
         (dp : Ξ ⊢ p ∷ PayV sh ((tag 0) ,ₚ j) (SI 2) (SD KSig)) (du : Ξ ⊢ u ∷ K 0 j) where
  private
    t : RTm ⌊ Ξ ⌋
    t = conₗ k p
    dt : Ξ ⊢ t ∷ K 0 j
    dt = ⊢conP KOK (atᵍ 0) nh dj dp
    Cs : Cons ⌊ Ξ ⌋ 4
    Cs = dσ (⌜⟶ᵀ⌝ q j t u) (lam dι) ∷ dσ (⌜Id⌝ (⌜Ty⌝ j) t u) (lam dι) ∷ dρ (ix≅ᵀ j u t) dι
         ∷ dσ (⌜Ty⌝ j) (lam (dρ (ix≅ᵀ (w1 j) (w1 t) v₀) (dρ (ix≅ᵀ (w1 j) v₀ (w1 u)) dι))) ∷ []
    fib : app (≅ᵀF.DF q) (ix≅ᵀ j t u) ⟶* rows Cs
    fib = ≅ᵀF.fibF {s = 0} {k = k} {q = q} {j = j} {p = p} {c = u} (atᵍ 0) nh

  -- ★ `cred : t ⟶ u → t ≅ u`
  cred≅ᵀ : {e : RTm ⌊ Ξ ⌋} → Ξ ⊢ e ∷ El (⌜⟶ᵀ⌝ q j t u) → Ξ ⊢ conₗ 0 (e ,ₚ unit) ∷ K≅ᵀ q j t u
  cred≅ᵀ {e} de =
    ⊢conRowₖ {Ξ} {4} {0} {ConvTₘ.J} {(≅ᵀF.DF q)} {ix≅ᵀ j t u} {_} {pair e unit} {Cs} nth-z ConvTₘ.⊢J (≅ᵀF.⊢DF dq) (⊢ix≅ᵀ dj dt du) fib
      (allC≅ᵀ dq dj dt du) (⊢payσ ConvTₘ.⊢J (≅ᵀF.⊢DF dq) {a = e} {p = unit} (ok-σ (⊢⌜⟶ᵀ⌝ dq dj dt du) ok-ι) de (⊢payι ConvTₘ.⊢J (≅ᵀF.⊢DF dq) ⊢unit))

  -- ★ `csym : u ≅ t → t ≅ u`
  csym≅ᵀ : {r : RTm ⌊ Ξ ⌋} → Ξ ⊢ r ∷ K≅ᵀ q j u t → Ξ ⊢ conₗ 2 (r ,ₚ unit) ∷ K≅ᵀ q j t u
  csym≅ᵀ {r} dr =
    ⊢conRowₖ {Ξ} {4} {2} {ConvTₘ.J} {(≅ᵀF.DF q)} {ix≅ᵀ j t u} {_} {pair r unit} {Cs} (atᶜ 2) ConvTₘ.⊢J (≅ᵀF.⊢DF dq) (⊢ix≅ᵀ dj dt du) fib
      (allC≅ᵀ dq dj dt du) (⊢payρ ConvTₘ.⊢J (≅ᵀF.⊢DF dq) {r = r} {p = unit} (ok-ρ (⊢ix≅ᵀ dj du dt) ok-ι) dr (⊢payι ConvTₘ.⊢J (≅ᵀF.⊢DF dq) ⊢unit))

  -- ★ `ctrn : t ≅ v → v ≅ u → t ≅ u`
  ctrn≅ᵀ : {v r₁ r₂ : RTm ⌊ Ξ ⌋} → Ξ ⊢ v ∷ K 0 j → Ξ ⊢ r₁ ∷ K≅ᵀ q j t v → Ξ ⊢ r₂ ∷ K≅ᵀ q j v u →
          Ξ ⊢ conₗ 3 (v ,ₚ r₁ ,ₚ r₂ ,ₚ unit) ∷ K≅ᵀ q j t u
  ctrn≅ᵀ {v} {r₁} {r₂} dv dr₁ dr₂ =
    ⊢conRowₖ {Ξ} {4} {3} {ConvTₘ.J} {(≅ᵀF.DF q)} {ix≅ᵀ j t u} {_} {pair v (r₁ ,ₚ r₂ ,ₚ unit)} {Cs} (atᶜ 3)
      ConvTₘ.⊢J (≅ᵀF.⊢DF dq) (⊢ix≅ᵀ dj dt du) fib (allC≅ᵀ dq dj dt du)
      (⊢payσ ConvTₘ.⊢J (≅ᵀF.⊢DF dq) {a = v} {p = pair r₁ (r₂ ,ₚ unit)}
         (ConvTₘ.okσ (⊢⌜Ty⌝ dj) (ok-ρ (⊢ix≅ᵀ (wkN dj) (wkK dt) (hereTy {m = j})) (ok-ρ (⊢ix≅ᵀ (wkN dj) (hereTy {m = j}) (wkK du)) ok-ι)))
         (toTy dv)
         (⊢-cast {Ξ} {pair r₁ (r₂ ,ₚ unit)} {El (dpay ConvTₘ.J (≅ᵀF.DF q) (dρ (ix≅ᵀ j t v) (dρ (ix≅ᵀ j v u) dι)))}
                 {El (dpay ConvTₘ.J (≅ᵀF.DF q) (subTm (single v) (dρ (ix≅ᵀ (w1 j) (w1 t) v₀) (dρ (ix≅ᵀ (w1 j) v₀ (w1 u)) dι))))}
                 (cong (λ Z → El (dpay ConvTₘ.J (≅ᵀF.DF q) Z)) (sym (trc ix≅ᵀ _ _ _ _ _ _ v (wk-cancel-tm v j) (wk-cancel-tm v t) (wk-cancel-tm v u))))
            (⊢payρ ConvTₘ.⊢J (≅ᵀF.⊢DF dq) {r = r₁} {p = pair r₂ unit} (ok-ρ (⊢ix≅ᵀ dj dt dv) (ok-ρ (⊢ix≅ᵀ dj dv du) ok-ι)) dr₁
              (⊢payρ ConvTₘ.⊢J (≅ᵀF.⊢DF dq) {r = r₂} {p = unit} (ok-ρ (⊢ix≅ᵀ dj dv du) ok-ι) dr₂ (⊢payι ConvTₘ.⊢J (≅ᵀF.⊢DF dq) ⊢unit)))))

-- ★ `crfl : t ≅ t`
crfl≅ᵀ : {Ξ : Ctx} {k : ℕ} {sh : Shape} {q j p : RTm ⌊ Ξ ⌋} (nh : NthSh TyShs k sh) → Ξ ⊢ q ∷ El ⌜QSig⌝ → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Ξ ⊢ p ∷ PayV sh ((tag 0) ,ₚ j) (SI 2) (SD KSig) →
        Ξ ⊢ conₗ 1 ((idrefl (⌜Ty⌝ j) (conₗ k p)) ,ₚ unit) ∷ K≅ᵀ q j (conₗ k p) (conₗ k p)
crfl≅ᵀ {Ξ} {k} {sh} {q} {j} {p} nh dq dj dp =
  ⊢conRowₖ {Ξ} {4} {1} {ConvTₘ.J} {(≅ᵀF.DF q)} {ix≅ᵀ j t t} {_} {pair (idrefl (⌜Ty⌝ j) t) unit}
           {dσ (⌜⟶ᵀ⌝ q j t t) (lam dι) ∷ dσ (⌜Id⌝ (⌜Ty⌝ j) t t) (lam dι) ∷ dρ (ix≅ᵀ j t t) dι
            ∷ dσ (⌜Ty⌝ j) (lam (dρ (ix≅ᵀ (w1 j) (w1 t) v₀) (dρ (ix≅ᵀ (w1 j) v₀ (w1 t)) dι))) ∷ []}
           (atᶜ 1) ConvTₘ.⊢J (≅ᵀF.⊢DF dq) (⊢ix≅ᵀ dj dt dt)
    (≅ᵀF.fibF {s = 0} {k = k} {q = q} {j = j} {p = p} {c = t} (atᵍ 0) nh) (allC≅ᵀ dq dj dt dt)
    (⊢payσ ConvTₘ.⊢J (≅ᵀF.⊢DF dq) {a = idrefl (⌜Ty⌝ j) t} {p = unit} (ok-σ (⊢⌜Id⌝ (⊢⌜Ty⌝ dj) (toTy dt) (toTy dt)) ok-ι)
       (⊢conv (⊢idrefl (⊢⌜Ty⌝ dj) (toTy dt)) (csymᵀ (credᵀ (El-⌜Id⌝ (⌜Ty⌝ j) t t))))
       (⊢payι ConvTₘ.⊢J (≅ᵀF.⊢DF dq) ⊢unit))
  where
    t = conₗ k p
    dt = ⊢conP KOK (atᵍ 0) nh dj dp
