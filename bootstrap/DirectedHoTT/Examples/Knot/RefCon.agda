-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ DEFINITIONS, the constructors of the `kref` rows at
--                      values (PLAN-BIDI §2-ter, option 3).
--
--   con⟶δ    kref n b ⟶ εwkK 1 j b, the payload the reflexivity of the
--             target: the row's Ford equation reads the body out of the
--             payload `(n , (b , unit))` by two projections.
--   con⊢ref  ◇ ⊢ b ∷ A ⇒ Γ ⊢ kref n b ∷ εwkK 0 j A — the payload built
--             at the values, the row read at the sources by one `mono-by`.
--   conv⊢ref the head's conversion row.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.RefCon (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-⌜Id⌝ʳ; ⟶*-natrecᶻ; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( []; _∷_; conₗ; lt-z; lt-s; atᶜ; v₀; v₁; v₂; v₃; _,ₚ_ )
open import DirectedHoTT.Lib.SynFib 𝒮 𝓃 ok using ( ⊢conRowₖ )
open import DirectedHoTT.Lib.SynRed 𝒮 𝓃 ok using ( prj-tup; mono-by; σₗ; _∷ʳ_; []ʳ )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctors 𝒮 wf using ( ⊢kref )
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( εwkK; ⊢εwkK )
open import DirectedHoTT.Examples.Knot.RedIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( KCtx; ⌜Ty⌝; ⊢⌜Ty⌝; cε )
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( toTy )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; ⊢JT; tmIx; ⊢tmIx; ⊢cTm; ⊢tyOf; ⌜Tm⌝; ⊢⌜Tm⌝; ⊢payK )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( toTm; w1 )
open import DirectedHoTT.Examples.Knot.Judge 𝒮 wf using ( D⊢; ⊢D⊢; fibK )
open import DirectedHoTT.Examples.Knot.JudgeConv 𝒮 wf using ( TCVat; ⊢payTCVat )
open import DirectedHoTT.Examples.Knot.Conv 𝒮 wf using ( ⌜≅ᵀ⌝ )
open import DirectedHoTT.Examples.Knot.Red 𝒮 wf using ( module ⟶F )
open import DirectedHoTT.Examples.Knot.Ref 𝒮 wf using ( bodyOf; Tδ; okTδ; allδ; ⊢bodyOf )
open import DirectedHoTT.Examples.Knot.RefJudge 𝒮 wf using ( T⊢ref; T⊢ref⁽1⁾; T⊢ref⁽1⁾-sub; okT⊢ref; okT⊢ref⁽1⁾; all⊢ref )

con⟶δ : {Ξ : Ctx} {j n b : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ n ∷ El ⌜Nat⌝ → Ξ ⊢ b ∷ K 1 nzero →
        Ξ ⊢ conₗ 0 ((idrefl (⌜Tm⌝ j) (εwkK 1 j b)) ,ₚ unit) ∷ IMu Redₘ.J ⟶F.DF (ix⟶ j (kref n b) (εwkK 1 j b))
con⟶δ {Ξ} {j} {n} {b} dj dn db =
  ⊢conRowₖ {Cs = ⌜ Tδ j p c ⌝ᵗ ∷ []} (atᶜ 0) Redₘ.⊢J ⟶F.⊢DF (⊢ix⟶ dj (⊢kref dj dn db) dc)
    (⟶F.fibF {s = 1} {k = 38} {j = j} {p = p} {c = c} (atᵍ 1) (atʰ 38)) (allδ dj dbody dc)
    (⊢payσ {Ξ} {Redₘ.J} {⟶F.DF} Redₘ.⊢J ⟶F.⊢DF (okTδ dj dbody dc) da
      (⊢payι {Ξ} {Redₘ.J} {⟶F.DF} Redₘ.⊢J ⟶F.⊢DF {unit} ⊢unit))
  where
    p c : RTm ⌊ Ξ ⌋
    p = n ,ₚ b ,ₚ unit
    c = εwkK 1 j b
    dc = ⊢εwkK (lt-s lt-z) dj db
    dbody = ⊢bodyOf {j = j} {p = p} (⊢payK (lt-s lt-z) ok-kref dj (a-nat dn (a-cls db a[])))
    da : Ξ ⊢ idrefl (⌜Tm⌝ j) c ∷ El (⌜Id⌝ (⌜Tm⌝ j) c (εwkK 1 j (fst (snd p))))
    da = ⊢conv (⊢idrefl (⊢⌜Tm⌝ dj) (toTm dc))
           (ctrnᵀ (csymᵀ (credᵀ (El-⌜Id⌝ (⌜Tm⌝ j) c c)))
                  (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-⌜Id⌝ʳ (⟶*-natrecᶻ (prj-tup {ws = n ∷ b ∷ []} unit (atᶜ 1))))))))

con⊢ref : {Ξ : Ctx} {j g n b A r : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ n ∷ El ⌜Nat⌝ →
          Ξ ⊢ b ∷ K 1 nzero → Ξ ⊢ A ∷ K 0 nzero → Ξ ⊢ r ∷ IMu JT D⊢ (tmIx nzero cε b A) →
          Ξ ⊢ conₗ 0 (A ,ₚ r ,ₚ idrefl (⌜Ty⌝ j) (εwkK 0 j A) ,ₚ unit) ∷ IMu JT D⊢ (tmIx j g (kref n b) (εwkK 0 j A))
con⊢ref {Ξ} {j} {g} {n} {b} {A} {r} dj dg dn db dA dr =
  ⊢conRowₖ {Cs = ⌜ T⊢ref j p c ⌝ᵗ ∷ ⌜ TCVat 38 j p c ⌝ᵗ ∷ []} (atᶜ 0) ⊢JT ⊢D⊢ (⊢tmIx dj dg (⊢kref dj dn db) dW)
    (fibK {s = 1} {k = 38} {j = j} {p = p} {c = c} (atᵍ 1) (atʰ 38)) (all⊢ref {j = j} {p} {c} dj dp dc)
    (⊢payσ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {a = A} (okT⊢ref dj dbody (⊢tyOf dc)) (toTy dA) dTail)
  where
    W p c : RTm ⌊ Ξ ⌋
    W = εwkK 0 j A
    p = n ,ₚ b ,ₚ unit
    c = g ,ₚ W
    dW = ⊢εwkK lt-z dj dA
    dp = ⊢payK (lt-s lt-z) ok-kref dj (a-nat dn (a-cls db a[]))
    dc = ⊢cTm dj dg dW
    dbody = ⊢bodyOf {j = j} {p = p} dp
    okRest : {J' : RTm ⌊ Ξ ⌋} {T : Tel ⌊ Ξ ⌋} → TelOK Ξ JT (tρ J' T) → TelOK Ξ JT T
    okRest (ok-ρ _ o) = o
    okB : TelOK Ξ JT (T⊢ref⁽1⁾ j b W A)
    okB = okT⊢ref⁽1⁾ dj db dW dA
    -- the tail at the values …
    dVal : Ξ ⊢ (r ,ₚ idrefl (⌜Ty⌝ j) W ,ₚ unit) ∷ El (dpay JT D⊢ ⌜ T⊢ref⁽1⁾ j b W A ⌝ᵗ)
    dVal = ⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ okB dr
             (⊢payσ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ (okRest okB)
               (⊢conv (⊢idrefl (⊢⌜Ty⌝ dj) (toTy dW)) (csymᵀ (credᵀ (El-⌜Id⌝ (⌜Ty⌝ j) W W))))
               (⊢payι {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ ⊢unit))
    -- … read at the sources: the body out of the payload, the type out of the convoy
    R : ⌜ T⊢ref⁽1⁾ j (bodyOf p) (snd c) A ⌝ᵗ ⟶* ⌜ T⊢ref⁽1⁾ j b W A ⌝ᵗ
    R = mono-by {Δ = ⌊ Ξ ⌋} {n = 4} {as = j ∷ bodyOf p ∷ snd c ∷ A ∷ []} {as' = j ∷ b ∷ W ∷ A ∷ []}
          ⌜ T⊢ref⁽1⁾ v₀ v₁ v₂ v₃ ⌝ᵗ
          (T⊢ref⁽1⁾-sub (σₗ (j ∷ bodyOf p ∷ snd c ∷ A ∷ [])) v₀ v₁ v₂ v₃)
          (T⊢ref⁽1⁾-sub (σₗ (j ∷ b ∷ W ∷ A ∷ [])) v₀ v₁ v₂ v₃)
          (done ∷ʳ prj-tup {ws = n ∷ b ∷ []} unit (atᶜ 1) ∷ʳ step (βsnd g W) done ∷ʳ done ∷ʳ []ʳ)
    -- … and A substituted for the row's bound variable
    inst : subTm (single A) ⌜ T⊢ref⁽1⁾ (w1 j) (w1 (bodyOf p)) (w1 (snd c)) v₀ ⌝ᵗ ≡ ⌜ T⊢ref⁽1⁾ j (bodyOf p) (snd c) A ⌝ᵗ
    inst = trans (T⊢ref⁽1⁾-sub (single A) (w1 j) (w1 (bodyOf p)) (w1 (snd c)) v₀)
                 (cong₃' (λ J B C → ⌜ T⊢ref⁽1⁾ J B C A ⌝ᵗ) (wk-cancel-tm A j) (wk-cancel-tm A (bodyOf p)) (wk-cancel-tm A (snd c)))
      where
        cong₃' : {X Y Z V : Set} (f : X → Y → Z → V) {x x' : X} {y y' : Y} {z z' : Z} →
                 x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
        cong₃' f refl refl refl = refl
    dTail : Ξ ⊢ (r ,ₚ idrefl (⌜Ty⌝ j) W ,ₚ unit) ∷ El (dpay JT D⊢ (subTm (single A) ⌜ T⊢ref⁽1⁾ (w1 j) (w1 (bodyOf p)) (w1 (snd c)) v₀ ⌝ᵗ))
    dTail = ⊢-cast (cong (λ Z → El (dpay JT D⊢ Z)) (sym inst))
                   (⊢conv dVal (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R)))))

conv⊢ref : {Ξ : Ctx} {j g n b A B r e : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ n ∷ El ⌜Nat⌝ →
           Ξ ⊢ b ∷ K 1 nzero → Ξ ⊢ A ∷ K 0 j → Ξ ⊢ B ∷ K 0 j →
           Ξ ⊢ r ∷ IMu JT D⊢ (tmIx j g (kref n b) A) → Ξ ⊢ e ∷ El (⌜≅ᵀ⌝ j A B) →
           Ξ ⊢ conₗ 1 (A ,ₚ r ,ₚ e ,ₚ unit) ∷ IMu JT D⊢ (tmIx j g (kref n b) B)
conv⊢ref {Ξ} {j} {g} {n} {b} {A} {B} {r} {e} dj dg dn db dA dB dr de =
  ⊢conRowₖ {Cs = ⌜ T⊢ref j p c ⌝ᵗ ∷ ⌜ TCVat 38 j p c ⌝ᵗ ∷ []} (atᶜ 1) ⊢JT ⊢D⊢ (⊢tmIx dj dg (⊢kref dj dn db) dB)
    (fibK {s = 1} {k = 38} {j = j} {p = p} {c = c} (atᵍ 1) (atʰ 38)) (all⊢ref {j = j} {p} {c} dj dp (⊢cTm dj dg dB))
    (⊢payTCVat ⊢D⊢ {k = 38} dj dg (⊢kref dj dn db) dA dB dr de)
  where
    p c : RTm ⌊ Ξ ⌋
    p = n ,ₚ b ,ₚ unit
    c = g ,ₚ B
    dp = ⊢payK (lt-s lt-z) ok-kref dj (a-nat dn (a-cls db a[]))
