-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ DEFINITIONS, the constructors of the `kref` rows at
--                      values (PLAN-REF K4).
--
--   con⟶δ    n < sizeQ q ⇒ kref n ⟶ εwkK 1 j (bodiesQ q n), the payload
--             the side condition's witness and the target's reflexivity.
--   con⊢ref  n < boundT q ⇒ Γ ⊢ kref n ∷ εwkK 0 j (typesQ (sigT q) n).
--   conv⊢ref the head's conversion row.
--
-- Each payload is built at the VALUES (the side condition, then the tail
-- after its σ-binder, `wk-cancel`ed), and the row read at the fibre's
-- SOURCES — the name out of the payload, the type out of the convoy — by
-- one `mono-by`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PwCore as Core₀
module DirectedHoTT.Examples.Knot.RefCon (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-⌜Id⌝ʳ; ⟶*-natrecᶻ; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( []; _∷_; conₗ; lt-z; lt-s; atᶜ; v₀; v₁; v₂; v₃; _,ₚ_; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynFib 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( ⊢conRowₖ )
open import DirectedHoTT.Lib.SynRed 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( prj-tup; mono-by; σₗ; _∷ʳ_; []ʳ )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctors 𝒮 wf using ( ⊢kref )
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( εwkK; ⊢εwkK )
open import DirectedHoTT.Examples.Knot.RedIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( KCtx; ⌜Ty⌝; ⊢⌜Ty⌝; cε )
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( toTy )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; ⊢JT; tmIx; ⊢tmIx; ⊢cTm; ⊢tyOf; ⌜Tm⌝; ⊢⌜Tm⌝; ⊢payK )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( toTm; w1 )
open import DirectedHoTT.Examples.Knot.Judge 𝒮 wf core using ( D⊢; ⊢D⊢; fibK )
open import DirectedHoTT.Examples.Knot.JudgeConv 𝒮 wf core using ( TCVat; ⊢payTCVat )
open import DirectedHoTT.Examples.Knot.Conv 𝒮 wf core using ( ⌜≅ᵀ⌝ )
open import DirectedHoTT.Examples.Knot.Red 𝒮 wf core using ( module ⟶F )
open import DirectedHoTT.Examples.Knot.Ref 𝒮 wf using ( nameOf; ⊢nameOf; Tδ; Tδ'; Tδ'-sub; TδT; TδT-sub; okTδ'; okTδT )
open import DirectedHoTT.Examples.Knot.RefJudge 𝒮 wf core using ( T⊢ref; T⊢ref'; T⊢ref'-sub; T⊢refT; T⊢refT-sub; okT⊢ref'; okT⊢refT; all⊢ref )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜QSig⌝; ⌜TSig⌝; sizeQ; bodiesQ; boundT; sigT; typesQ; ⊢bodiesQ; ⊢typesQ; ⊢sigT )

------------------------------------------------------------------------
-- δ
------------------------------------------------------------------------

con⟶δ : {Ξ : Ctx} {q j n h : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜QSig⌝ → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ n ∷ El ⌜Nat⌝ →
        Ξ ⊢ h ∷ El (⌜Hom⌝ ⌜Nat⌝ (nsuc n) (sizeQ q)) →
        Ξ ⊢ conₗ 0 (h ,ₚ idrefl (⌜Tm⌝ j) (εwkK 1 j (bodiesQ q n)) ,ₚ unit)
          ∷ IMu Redₘ.J (⟶F.DF q) (ix⟶ j (kref n) (εwkK 1 j (bodiesQ q n)))
con⟶δ {Ξ} {q} {j} {n} {h} dq dj dn dh =
  ⊢conRowₖ {Cs = ⌜ Tδ q j p c ⌝ᵗ ∷ []} (atᶜ 0) Redₘ.⊢J (⟶F.⊢DF dq) (⊢ix⟶ dj (⊢kref dj dn) dc)
    (⟶F.fibF {s = 1} {k = 38} {q = q} {j = j} {p = p} {c = c} (atᵍ 1) (atʰ 38))
    (⊢tel {T = Tδ q j p c} Redₘ.⊢J (okTδ' dq dj (⊢nameOf {j = j} {p = p} dp) dc) ∷ᵈ []ᵈ)
    (⊢conv dPv (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R)))))
  where
    p c e : RTm ⌊ Ξ ⌋
    p = n ,ₚ unit
    c = εwkK 1 j (bodiesQ q n)
    e = idrefl (⌜Tm⌝ j) c
    dp = ⊢payK (lt-s lt-z) ok-kref dj (a-nat dn a[])
    dc = ⊢εwkK (lt-s lt-z) dj (⊢bodiesQ dq dn)
    -- the tail at the values, after the side condition
    eq : subTm (single h) ⌜ TδT (w1 q) (w1 j) (w1 n) (w1 c) ⌝ᵗ ≡ ⌜ TδT q j n c ⌝ᵗ
    eq = trans (TδT-sub (single h) (w1 q) (w1 j) (w1 n) (w1 c))
               (cong₄ (λ a b x y → ⌜ TδT a b x y ⌝ᵗ) (wk-cancel-tm h q) (wk-cancel-tm h j) (wk-cancel-tm h n) (wk-cancel-tm h c))
    de : Ξ ⊢ e ∷ El (⌜Id⌝ (⌜Tm⌝ j) c c)
    de = ⊢conv (⊢idrefl (⊢⌜Tm⌝ dj) (toTm dc)) (csymᵀ (credᵀ (El-⌜Id⌝ (⌜Tm⌝ j) c c)))
    dPv : Ξ ⊢ pair h (pair e unit) ∷ El (dpay Redₘ.J (⟶F.DF q) ⌜ Tδ' q j n c ⌝ᵗ)
    dPv = ⊢payσ {Ξ} {Redₘ.J} {⟶F.DF q} Redₘ.⊢J (⟶F.⊢DF dq) {a = h} {p = pair e unit} (okTδ' dq dj dn dc) dh
            (⊢-cast (cong (λ Z → El (dpay Redₘ.J (⟶F.DF q) Z)) (sym eq))
              (⊢payσ {Ξ} {Redₘ.J} {⟶F.DF q} Redₘ.⊢J (⟶F.⊢DF dq) {a = e} {p = unit} (okTδT dq dj dn dc) de
                (⊢payι {Ξ} {Redₘ.J} {⟶F.DF q} Redₘ.⊢J (⟶F.⊢DF dq) {unit} ⊢unit)))
    -- … read at the sources: the name out of the payload
    R : ⌜ Tδ' q j (nameOf p) c ⌝ᵗ ⟶* ⌜ Tδ' q j n c ⌝ᵗ
    R = mono-by {Δ = ⌊ Ξ ⌋} {n = 4} {as = q ∷ j ∷ nameOf p ∷ c ∷ []} {as' = q ∷ j ∷ n ∷ c ∷ []}
          ⌜ Tδ' v₀ v₁ v₂ v₃ ⌝ᵗ
          (Tδ'-sub (σₗ (q ∷ j ∷ nameOf p ∷ c ∷ [])) v₀ v₁ v₂ v₃)
          (Tδ'-sub (σₗ (q ∷ j ∷ n ∷ c ∷ [])) v₀ v₁ v₂ v₃)
          (done ∷ʳ done ∷ʳ step (βfst n unit) done ∷ʳ done ∷ʳ []ʳ)

------------------------------------------------------------------------
-- ⊢ref
------------------------------------------------------------------------

con⊢ref : {Ξ : Ctx} {q j g n h : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜TSig⌝ → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
          Ξ ⊢ n ∷ El ⌜Nat⌝ → Ξ ⊢ h ∷ El (⌜Hom⌝ ⌜Nat⌝ (nsuc n) (boundT q)) →
          Ξ ⊢ conₗ 0 (h ,ₚ idrefl (⌜Ty⌝ j) (εwkK 0 j (typesQ (sigT q) n)) ,ₚ unit)
            ∷ IMu JT (D⊢ q) (tmIx j g (kref n) (εwkK 0 j (typesQ (sigT q) n)))
con⊢ref {Ξ} {q} {j} {g} {n} {h} dq dj dg dn dh =
  ⊢conRowₖ {Cs = ⌜ T⊢ref q j p c ⌝ᵗ ∷ ⌜ TCVat 38 q j p c ⌝ᵗ ∷ []} (atᶜ 0) ⊢JT (⊢D⊢ dq) (⊢tmIx dj dg (⊢kref dj dn) dW)
    (fibK {s = 1} {k = 38} {q = q} {j = j} {p = p} {c = c} (atᵍ 1) (atʰ 38)) (all⊢ref {q = q} {j} {p} {c} dq dj dp dc)
    (⊢conv dPv (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R)))))
  where
    W p c e : RTm ⌊ Ξ ⌋
    W = εwkK 0 j (typesQ (sigT q) n)
    p = n ,ₚ unit
    c = g ,ₚ W
    e = idrefl (⌜Ty⌝ j) W
    dW = ⊢εwkK lt-z dj (⊢typesQ (⊢sigT dq) dn)
    dp = ⊢payK (lt-s lt-z) ok-kref dj (a-nat dn a[])
    dc = ⊢cTm dj dg dW
    eq : subTm (single h) ⌜ T⊢refT (w1 q) (w1 j) (w1 n) (w1 W) ⌝ᵗ ≡ ⌜ T⊢refT q j n W ⌝ᵗ
    eq = trans (T⊢refT-sub (single h) (w1 q) (w1 j) (w1 n) (w1 W))
               (cong₄ (λ a b x y → ⌜ T⊢refT a b x y ⌝ᵗ) (wk-cancel-tm h q) (wk-cancel-tm h j) (wk-cancel-tm h n) (wk-cancel-tm h W))
    de : Ξ ⊢ e ∷ El (⌜Id⌝ (⌜Ty⌝ j) W W)
    de = ⊢conv (⊢idrefl (⊢⌜Ty⌝ dj) (toTy dW)) (csymᵀ (credᵀ (El-⌜Id⌝ (⌜Ty⌝ j) W W)))
    dPv : Ξ ⊢ pair h (pair e unit) ∷ El (dpay JT (D⊢ q) ⌜ T⊢ref' q j n W ⌝ᵗ)
    dPv = ⊢payσ {Ξ} {JT} {D⊢ q} ⊢JT (⊢D⊢ dq) {a = h} {p = pair e unit} (okT⊢ref' dq dj dn dW) dh
            (⊢-cast (cong (λ Z → El (dpay JT (D⊢ q) Z)) (sym eq))
              (⊢payσ {Ξ} {JT} {D⊢ q} ⊢JT (⊢D⊢ dq) {a = e} {p = unit} (okT⊢refT dq dj dn dW) de
                (⊢payι {Ξ} {JT} {D⊢ q} ⊢JT (⊢D⊢ dq) ⊢unit)))
    -- … read at the sources: the name out of the payload, the type out of the convoy
    R : ⌜ T⊢ref' q j (nameOf p) (snd c) ⌝ᵗ ⟶* ⌜ T⊢ref' q j n W ⌝ᵗ
    R = mono-by {Δ = ⌊ Ξ ⌋} {n = 4} {as = q ∷ j ∷ nameOf p ∷ snd c ∷ []} {as' = q ∷ j ∷ n ∷ W ∷ []}
          ⌜ T⊢ref' v₀ v₁ v₂ v₃ ⌝ᵗ
          (T⊢ref'-sub (σₗ (q ∷ j ∷ nameOf p ∷ snd c ∷ [])) v₀ v₁ v₂ v₃)
          (T⊢ref'-sub (σₗ (q ∷ j ∷ n ∷ W ∷ [])) v₀ v₁ v₂ v₃)
          (done ∷ʳ done ∷ʳ step (βfst n unit) done ∷ʳ step (βsnd g W) done ∷ʳ []ʳ)

conv⊢ref : {Ξ : Ctx} {q j g n A B r e : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜TSig⌝ → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
           Ξ ⊢ n ∷ El ⌜Nat⌝ → Ξ ⊢ A ∷ K 0 j → Ξ ⊢ B ∷ K 0 j →
           Ξ ⊢ r ∷ IMu JT (D⊢ q) (tmIx j g (kref n) A) → Ξ ⊢ e ∷ El (⌜≅ᵀ⌝ (sigT q) j A B) →
           Ξ ⊢ conₗ 1 (A ,ₚ r ,ₚ e ,ₚ unit) ∷ IMu JT (D⊢ q) (tmIx j g (kref n) B)
conv⊢ref {Ξ} {q} {j} {g} {n} {A} {B} {r} {e} dq dj dg dn dA dB dr de =
  ⊢conRowₖ {Cs = ⌜ T⊢ref q j p c ⌝ᵗ ∷ ⌜ TCVat 38 q j p c ⌝ᵗ ∷ []} (atᶜ 1) ⊢JT (⊢D⊢ dq) (⊢tmIx dj dg (⊢kref dj dn) dB)
    (fibK {s = 1} {k = 38} {q = q} {j = j} {p = p} {c = c} (atᵍ 1) (atʰ 38))
    (all⊢ref {q = q} {j} {p} {c} dq dj dp (⊢cTm dj dg dB))
    (⊢payTCVat (⊢D⊢ dq) {k = 38} dq dj dg (⊢kref dj dn) dA dB dr de)
  where
    p c : RTm ⌊ Ξ ⌋
    p = n ,ₚ unit
    c = g ,ₚ B
    dp = ⊢payK (lt-s lt-z) ok-kref dj (a-nat dn a[])
