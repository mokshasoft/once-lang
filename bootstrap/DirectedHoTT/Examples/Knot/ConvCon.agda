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
module DirectedHoTT.Examples.Knot.ConvCon where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; conₗ; nth-z; atᶜ; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢conP )
open import DirectedHoTT.Lib.SynFib using ( ⊢conRowₖ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( toTy; hereTy; rows )
open import DirectedHoTT.Examples.Knot.JudgeIx using ( ⌜Tm⌝; ⊢⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; hereTm; toTm; wkN; wkK )
open import DirectedHoTT.Examples.Knot.RedIx
open import DirectedHoTT.Examples.Knot.Red using ( ⌜⟶⌝; ⊢⌜⟶⌝ )
open import DirectedHoTT.Examples.Knot.RedT using ( ⌜⟶ᵀ⌝; ⊢⌜⟶ᵀ⌝ )
open import DirectedHoTT.Examples.Knot.Conv

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

module _ {Ξ : Ctx} {k : ℕ} {sh : Shape} {j p u : RTm ⌊ Ξ ⌋} (nh : NthSh TmShs k sh) (dj : Ξ ⊢ j ∷ El ⌜Nat⌝)
         (dp : Ξ ⊢ p ∷ PayV sh ((tag 1) ,ₚ j) (SI 2) (SD KSig)) (du : Ξ ⊢ u ∷ K 1 j) where
  private
    t : RTm ⌊ Ξ ⌋
    t = conₗ k p
    dt : Ξ ⊢ t ∷ K 1 j
    dt = ⊢conP KOK (atᵍ 1) nh dj dp
    Cs : Cons ⌊ Ξ ⌋ 4
    Cs = dσ (⌜⟶⌝ j t u) (lam dι) ∷ dσ (⌜Id⌝ (⌜Tm⌝ j) t u) (lam dι) ∷ dρ (ix≅ j u t) dι
         ∷ dσ (⌜Tm⌝ j) (lam (dρ (ix≅ (w1 j) (w1 t) v₀) (dρ (ix≅ (w1 j) v₀ (w1 u)) dι))) ∷ []
    fib : app ≅F.DF (ix≅ j t u) ⟶* rows Cs
    fib = ≅F.fibF {s = 1} {k = k} {j = j} {p = p} {c = u} (atᵍ 1) nh

  -- ★ `cred : t ⟶ u → t ≅ u`
  cred≅ : {e : RTm ⌊ Ξ ⌋} → Ξ ⊢ e ∷ El (⌜⟶⌝ j t u) → Ξ ⊢ conₗ 0 (e ,ₚ unit) ∷ K≅ j t u
  cred≅ {e} de =
    ⊢conRowₖ {Ξ} {4} {0} {Convₘ.J} {≅F.DF} {ix≅ j t u} {_} {pair e unit} {Cs} nth-z Convₘ.⊢J ≅F.⊢DF (⊢ix≅ dj dt du) fib
      (allC≅ dj dt du) (⊢payσ Convₘ.⊢J ≅F.⊢DF {a = e} {p = unit} (ok-σ (⊢⌜⟶⌝ dj dt du) ok-ι) de (⊢payι Convₘ.⊢J ≅F.⊢DF ⊢unit))

  -- ★ `csym : u ≅ t → t ≅ u`
  csym≅ : {r : RTm ⌊ Ξ ⌋} → Ξ ⊢ r ∷ K≅ j u t → Ξ ⊢ conₗ 2 (r ,ₚ unit) ∷ K≅ j t u
  csym≅ {r} dr =
    ⊢conRowₖ {Ξ} {4} {2} {Convₘ.J} {≅F.DF} {ix≅ j t u} {_} {pair r unit} {Cs} (atᶜ 2) Convₘ.⊢J ≅F.⊢DF (⊢ix≅ dj dt du) fib
      (allC≅ dj dt du) (⊢payρ Convₘ.⊢J ≅F.⊢DF {r = r} {p = unit} (ok-ρ (⊢ix≅ dj du dt) ok-ι) dr (⊢payι Convₘ.⊢J ≅F.⊢DF ⊢unit))

  -- ★ `ctrn : t ≅ v → v ≅ u → t ≅ u`
  ctrn≅ : {v r₁ r₂ : RTm ⌊ Ξ ⌋} → Ξ ⊢ v ∷ K 1 j → Ξ ⊢ r₁ ∷ K≅ j t v → Ξ ⊢ r₂ ∷ K≅ j v u →
          Ξ ⊢ conₗ 3 (v ,ₚ r₁ ,ₚ r₂ ,ₚ unit) ∷ K≅ j t u
  ctrn≅ {v} {r₁} {r₂} dv dr₁ dr₂ =
    ⊢conRowₖ {Ξ} {4} {3} {Convₘ.J} {≅F.DF} {ix≅ j t u} {_} {pair v (r₁ ,ₚ r₂ ,ₚ unit)} {Cs} (atᶜ 3)
      Convₘ.⊢J ≅F.⊢DF (⊢ix≅ dj dt du) fib (allC≅ dj dt du)
      (⊢payσ Convₘ.⊢J ≅F.⊢DF {a = v} {p = pair r₁ (r₂ ,ₚ unit)}
         (Convₘ.okσ (⊢⌜Tm⌝ dj) (ok-ρ (⊢ix≅ (wkN dj) (wkK dt) (hereTm {m = j})) (ok-ρ (⊢ix≅ (wkN dj) (hereTm {m = j}) (wkK du)) ok-ι)))
         (toTm dv)
         (⊢-cast {Ξ} {pair r₁ (r₂ ,ₚ unit)} {El (dpay Convₘ.J ≅F.DF (dρ (ix≅ j t v) (dρ (ix≅ j v u) dι)))}
                 {El (dpay Convₘ.J ≅F.DF (subTm (single v) (dρ (ix≅ (w1 j) (w1 t) v₀) (dρ (ix≅ (w1 j) v₀ (w1 u)) dι))))}
                 (cong (λ Z → El (dpay Convₘ.J ≅F.DF Z)) (sym (trc ix≅ _ _ _ _ _ _ v (wk-cancel-tm v j) (wk-cancel-tm v t) (wk-cancel-tm v u))))
            (⊢payρ Convₘ.⊢J ≅F.⊢DF {r = r₁} {p = pair r₂ unit} (ok-ρ (⊢ix≅ dj dt dv) (ok-ρ (⊢ix≅ dj dv du) ok-ι)) dr₁
              (⊢payρ Convₘ.⊢J ≅F.⊢DF {r = r₂} {p = unit} (ok-ρ (⊢ix≅ dj dv du) ok-ι) dr₂ (⊢payι Convₘ.⊢J ≅F.⊢DF ⊢unit)))))

-- ★ `crfl : t ≅ t`
crfl≅ : {Ξ : Ctx} {k : ℕ} {sh : Shape} {j p : RTm ⌊ Ξ ⌋} (nh : NthSh TmShs k sh) → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Ξ ⊢ p ∷ PayV sh ((tag 1) ,ₚ j) (SI 2) (SD KSig) →
        Ξ ⊢ conₗ 1 ((idrefl (⌜Tm⌝ j) (conₗ k p)) ,ₚ unit) ∷ K≅ j (conₗ k p) (conₗ k p)
crfl≅ {Ξ} {k} {sh} {j} {p} nh dj dp =
  ⊢conRowₖ {Ξ} {4} {1} {Convₘ.J} {≅F.DF} {ix≅ j t t} {_} {pair (idrefl (⌜Tm⌝ j) t) unit}
           {dσ (⌜⟶⌝ j t t) (lam dι) ∷ dσ (⌜Id⌝ (⌜Tm⌝ j) t t) (lam dι) ∷ dρ (ix≅ j t t) dι
            ∷ dσ (⌜Tm⌝ j) (lam (dρ (ix≅ (w1 j) (w1 t) v₀) (dρ (ix≅ (w1 j) v₀ (w1 t)) dι))) ∷ []}
           (atᶜ 1) Convₘ.⊢J ≅F.⊢DF (⊢ix≅ dj dt dt)
    (≅F.fibF {s = 1} {k = k} {j = j} {p = p} {c = t} (atᵍ 1) nh) (allC≅ dj dt dt)
    (⊢payσ Convₘ.⊢J ≅F.⊢DF {a = idrefl (⌜Tm⌝ j) t} {p = unit} (ok-σ (⊢⌜Id⌝ (⊢⌜Tm⌝ dj) (toTm dt) (toTm dt)) ok-ι)
       (⊢conv (⊢idrefl (⊢⌜Tm⌝ dj) (toTm dt)) (csymᵀ (credᵀ (El-⌜Id⌝ (⌜Tm⌝ j) t t))))
       (⊢payι Convₘ.⊢J ≅F.⊢DF ⊢unit))
  where
    t = conₗ k p
    dt = ⊢conP KOK (atᵍ 1) nh dj dp

------------------------------------------------------------------------
-- 2. A ≅ᵀ B, at a subject `conₗ k p` of ANY type head
------------------------------------------------------------------------

module _ {Ξ : Ctx} {k : ℕ} {sh : Shape} {j p u : RTm ⌊ Ξ ⌋} (nh : NthSh TyShs k sh) (dj : Ξ ⊢ j ∷ El ⌜Nat⌝)
         (dp : Ξ ⊢ p ∷ PayV sh ((tag 0) ,ₚ j) (SI 2) (SD KSig)) (du : Ξ ⊢ u ∷ K 0 j) where
  private
    t : RTm ⌊ Ξ ⌋
    t = conₗ k p
    dt : Ξ ⊢ t ∷ K 0 j
    dt = ⊢conP KOK (atᵍ 0) nh dj dp
    Cs : Cons ⌊ Ξ ⌋ 4
    Cs = dσ (⌜⟶ᵀ⌝ j t u) (lam dι) ∷ dσ (⌜Id⌝ (⌜Ty⌝ j) t u) (lam dι) ∷ dρ (ix≅ᵀ j u t) dι
         ∷ dσ (⌜Ty⌝ j) (lam (dρ (ix≅ᵀ (w1 j) (w1 t) v₀) (dρ (ix≅ᵀ (w1 j) v₀ (w1 u)) dι))) ∷ []
    fib : app ≅ᵀF.DF (ix≅ᵀ j t u) ⟶* rows Cs
    fib = ≅ᵀF.fibF {s = 0} {k = k} {j = j} {p = p} {c = u} (atᵍ 0) nh

  -- ★ `cred : t ⟶ u → t ≅ u`
  cred≅ᵀ : {e : RTm ⌊ Ξ ⌋} → Ξ ⊢ e ∷ El (⌜⟶ᵀ⌝ j t u) → Ξ ⊢ conₗ 0 (e ,ₚ unit) ∷ K≅ᵀ j t u
  cred≅ᵀ {e} de =
    ⊢conRowₖ {Ξ} {4} {0} {ConvTₘ.J} {≅ᵀF.DF} {ix≅ᵀ j t u} {_} {pair e unit} {Cs} nth-z ConvTₘ.⊢J ≅ᵀF.⊢DF (⊢ix≅ᵀ dj dt du) fib
      (allC≅ᵀ dj dt du) (⊢payσ ConvTₘ.⊢J ≅ᵀF.⊢DF {a = e} {p = unit} (ok-σ (⊢⌜⟶ᵀ⌝ dj dt du) ok-ι) de (⊢payι ConvTₘ.⊢J ≅ᵀF.⊢DF ⊢unit))

  -- ★ `csym : u ≅ t → t ≅ u`
  csym≅ᵀ : {r : RTm ⌊ Ξ ⌋} → Ξ ⊢ r ∷ K≅ᵀ j u t → Ξ ⊢ conₗ 2 (r ,ₚ unit) ∷ K≅ᵀ j t u
  csym≅ᵀ {r} dr =
    ⊢conRowₖ {Ξ} {4} {2} {ConvTₘ.J} {≅ᵀF.DF} {ix≅ᵀ j t u} {_} {pair r unit} {Cs} (atᶜ 2) ConvTₘ.⊢J ≅ᵀF.⊢DF (⊢ix≅ᵀ dj dt du) fib
      (allC≅ᵀ dj dt du) (⊢payρ ConvTₘ.⊢J ≅ᵀF.⊢DF {r = r} {p = unit} (ok-ρ (⊢ix≅ᵀ dj du dt) ok-ι) dr (⊢payι ConvTₘ.⊢J ≅ᵀF.⊢DF ⊢unit))

  -- ★ `ctrn : t ≅ v → v ≅ u → t ≅ u`
  ctrn≅ᵀ : {v r₁ r₂ : RTm ⌊ Ξ ⌋} → Ξ ⊢ v ∷ K 0 j → Ξ ⊢ r₁ ∷ K≅ᵀ j t v → Ξ ⊢ r₂ ∷ K≅ᵀ j v u →
          Ξ ⊢ conₗ 3 (v ,ₚ r₁ ,ₚ r₂ ,ₚ unit) ∷ K≅ᵀ j t u
  ctrn≅ᵀ {v} {r₁} {r₂} dv dr₁ dr₂ =
    ⊢conRowₖ {Ξ} {4} {3} {ConvTₘ.J} {≅ᵀF.DF} {ix≅ᵀ j t u} {_} {pair v (r₁ ,ₚ r₂ ,ₚ unit)} {Cs} (atᶜ 3)
      ConvTₘ.⊢J ≅ᵀF.⊢DF (⊢ix≅ᵀ dj dt du) fib (allC≅ᵀ dj dt du)
      (⊢payσ ConvTₘ.⊢J ≅ᵀF.⊢DF {a = v} {p = pair r₁ (r₂ ,ₚ unit)}
         (ConvTₘ.okσ (⊢⌜Ty⌝ dj) (ok-ρ (⊢ix≅ᵀ (wkN dj) (wkK dt) (hereTy {m = j})) (ok-ρ (⊢ix≅ᵀ (wkN dj) (hereTy {m = j}) (wkK du)) ok-ι)))
         (toTy dv)
         (⊢-cast {Ξ} {pair r₁ (r₂ ,ₚ unit)} {El (dpay ConvTₘ.J ≅ᵀF.DF (dρ (ix≅ᵀ j t v) (dρ (ix≅ᵀ j v u) dι)))}
                 {El (dpay ConvTₘ.J ≅ᵀF.DF (subTm (single v) (dρ (ix≅ᵀ (w1 j) (w1 t) v₀) (dρ (ix≅ᵀ (w1 j) v₀ (w1 u)) dι))))}
                 (cong (λ Z → El (dpay ConvTₘ.J ≅ᵀF.DF Z)) (sym (trc ix≅ᵀ _ _ _ _ _ _ v (wk-cancel-tm v j) (wk-cancel-tm v t) (wk-cancel-tm v u))))
            (⊢payρ ConvTₘ.⊢J ≅ᵀF.⊢DF {r = r₁} {p = pair r₂ unit} (ok-ρ (⊢ix≅ᵀ dj dt dv) (ok-ρ (⊢ix≅ᵀ dj dv du) ok-ι)) dr₁
              (⊢payρ ConvTₘ.⊢J ≅ᵀF.⊢DF {r = r₂} {p = unit} (ok-ρ (⊢ix≅ᵀ dj dv du) ok-ι) dr₂ (⊢payι ConvTₘ.⊢J ≅ᵀF.⊢DF ⊢unit)))))

-- ★ `crfl : t ≅ t`
crfl≅ᵀ : {Ξ : Ctx} {k : ℕ} {sh : Shape} {j p : RTm ⌊ Ξ ⌋} (nh : NthSh TyShs k sh) → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Ξ ⊢ p ∷ PayV sh ((tag 0) ,ₚ j) (SI 2) (SD KSig) →
        Ξ ⊢ conₗ 1 ((idrefl (⌜Ty⌝ j) (conₗ k p)) ,ₚ unit) ∷ K≅ᵀ j (conₗ k p) (conₗ k p)
crfl≅ᵀ {Ξ} {k} {sh} {j} {p} nh dj dp =
  ⊢conRowₖ {Ξ} {4} {1} {ConvTₘ.J} {≅ᵀF.DF} {ix≅ᵀ j t t} {_} {pair (idrefl (⌜Ty⌝ j) t) unit}
           {dσ (⌜⟶ᵀ⌝ j t t) (lam dι) ∷ dσ (⌜Id⌝ (⌜Ty⌝ j) t t) (lam dι) ∷ dρ (ix≅ᵀ j t t) dι
            ∷ dσ (⌜Ty⌝ j) (lam (dρ (ix≅ᵀ (w1 j) (w1 t) v₀) (dρ (ix≅ᵀ (w1 j) v₀ (w1 t)) dι))) ∷ []}
           (atᶜ 1) ConvTₘ.⊢J ≅ᵀF.⊢DF (⊢ix≅ᵀ dj dt dt)
    (≅ᵀF.fibF {s = 0} {k = k} {j = j} {p = p} {c = t} (atᵍ 0) nh) (allC≅ᵀ dj dt dt)
    (⊢payσ ConvTₘ.⊢J ≅ᵀF.⊢DF {a = idrefl (⌜Ty⌝ j) t} {p = unit} (ok-σ (⊢⌜Id⌝ (⊢⌜Ty⌝ dj) (toTy dt) (toTy dt)) ok-ι)
       (⊢conv (⊢idrefl (⊢⌜Ty⌝ dj) (toTy dt)) (csymᵀ (credᵀ (El-⌜Id⌝ (⌜Ty⌝ j) t t))))
       (⊢payι ConvTₘ.⊢J ≅ᵀF.⊢DF ⊢unit))
  where
    t = conₗ k p
    dt = ⊢conP KOK (atᵍ 0) nh dj dp
