-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — `⊢conv : Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B`, the `⊢`
-- rule with a bare-variable subject: one row in EVERY term fibre (D077),
-- parametric in the subject, typed once.  `A` is a σ-field, `A ≅ᵀ B` a
-- σ-field of the lower stratum's code (`Knot/Conv`), at the signature of
-- the typing parameter (`sigT q`; PLAN-REF).  And the `∋` premise of
-- `⊢var` as an opaque code.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PwCore as Core₀
module DirectedHoTT.Examples.Knot.JudgeConv (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) as ᴵSugar
open ᴵSugar using ( tag; conₗ; tag-sub; v₀; v₁; v₂; v₃; v₄; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( PayV; ⊢conP )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( hereTy; toTy; I∋; ⊢I∋; I∋-sub; D∋; ⊢D∋; ix∋; ⊢ix∋; K∋ )
open import DirectedHoTT.Examples.Knot.LookupCon 𝒮 wf using ( D∋-sub )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( w1; w1-sub; okσJ; wkN; wkK; wkG )
open import DirectedHoTT.Examples.Knot.Conv 𝒮 wf core using ( ⌜≅ᵀ⌝; ⊢⌜≅ᵀ⌝; ⌜≅ᵀ⌝-sub )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜TSig⌝; sigT; ⊢sigT; wkT )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Lib.SynRed 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( mono-by; σₗ; _∷ʳ_; []ʳ )
open ᴵSugar using ( Cons; []; _∷_ )

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- ⊢conv
------------------------------------------------------------------------

TCV : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
TCV Q J G T X = tσ (⌜Ty⌝ J) (tρ (tmIx (w1 J) (w1 G) (w1 T) v₀) (tσ (⌜≅ᵀ⌝ (sigT (w1 Q)) (w1 J) v₀ (w1 X)) tι))

private
  cv-cong : (a a' : RTm Δ) (J J' G G' T T' X X' : RTm (Δ ∙)) → a ≡ a' → J ≡ J' → G ≡ G' → T ≡ T' → X ≡ X' →
            (b b' : RTm (Δ ∙)) → b ≡ b' →
            dσ a (lam (dρ (tmIx J G T v₀) (dσ b (lam dι)))) ≡ dσ a' (lam (dρ (tmIx J' G' T' v₀) (dσ b' (lam dι))))
  cv-cong a a' J J' G G' T T' X X' refl refl refl refl refl b b' refl = refl

TCV-sub : (σ : Sub Δ Θ) (Q J G T X : RTm Δ) → subTm σ ⌜ TCV Q J G T X ⌝ᵗ ≡ ⌜ TCV (subTm σ Q) (subTm σ J) (subTm σ G) (subTm σ T) (subTm σ X) ⌝ᵗ
TCV-sub σ Q J G T X =
  cv-cong _ _ _ _ _ _ _ _ _ _ (⌜Ty⌝-sub σ J) (w1-sub σ J) (w1-sub σ G) (w1-sub σ T) (w1-sub σ X) _ _
          (trans (⌜≅ᵀ⌝-sub (extS σ) (sigT (w1 Q)) (w1 J) v₀ (w1 X))
                 (cong₃ (λ q a b → ⌜≅ᵀ⌝ (sigT q) a v₀ b) (w1-sub σ Q) (w1-sub σ J) (w1-sub σ X)))

okTCV : {Ξ : Ctx} {Q J G T X : RTm ⌊ Ξ ⌋} → Ξ ⊢ Q ∷ El ⌜TSig⌝ → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ G ∷ KCtx J → Ξ ⊢ T ∷ K 1 J →
        Ξ ⊢ X ∷ K 0 J → TelOK Ξ JT (TCV Q J G T X)
okTCV {J = J} dQ dJ dG dT dX =
  okσJ (⊢⌜Ty⌝ dJ)
    (ok-ρ (⊢tmIx (wkN dJ) (wkG dG) (wkK dT) (hereTy {m = J}))
          (okσJ (⊢⌜≅ᵀ⌝ (⊢sigT (wkT dQ)) (wkN dJ) (hereTy {m = J}) (wkK dX)) ok-ι))

-- at head `k`: the subject is `conₗ k p`, the convoy `(Γ , B)`
TCVat : ℕ → RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
TCVat k q j p c = TCV q j (fst c) (conₗ k p) (snd c)

TCVat-law : (k : ℕ) → TelLaw (TCVat k)
TCVat-law k σ q j p c =
  trans (TCV-sub σ q j (fst c) (conₗ k p) (snd c))
        (cong (λ z → ⌜ TCV (subTm σ q) (subTm σ j) (fst (subTm σ c)) z (snd (subTm σ c)) ⌝ᵗ)
              {x = subTm σ (conₗ k p)} {y = conₗ k (subTm σ p)}
              (cong (λ t → con (t ,ₚ (subTm σ p))) (tag-sub σ k)))

okTCVat : {c₀ k : ℕ} {shs : Shapes c₀} {sh : Shape} → NthG KSig 1 shs → NthSh shs k sh →
          {Ξ : Ctx} {q j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜TSig⌝ → Ξ ⊢ j ∷ El ⌜Nat⌝ →
          Ξ ⊢ p ∷ PayV sh ((tag 1) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CTat ((tag 1) ,ₚ j)) →
          TelOK Ξ JT (TCVat k q j p c)
okTCVat ng nh dq dj dp dc = okTCV dq dj (⊢ctxOf dc) (⊢conP KOK ng nh dj dp) (⊢tyOf dc)

-- ★ its CONSTRUCTOR's payload `(A , r , e)`, typed ONCE for every head and
--   any description over `JT`: built at the values, read at the sources
private
  cv2-cong : (J J' G G' T T' A : RTm Δ) (C C' : RTm Δ) → J ≡ J' → G ≡ G' → T ≡ T' → C ≡ C' →
             dρ (tmIx J G T A) (dσ C (lam dι)) ≡ dρ (tmIx J' G' T' A) (dσ C' (lam dι))
  cv2-cong J J' G G' T T' A C C' refl refl refl refl = refl

module _ {Ξ : Ctx} {D : RTm ⌊ Ξ ⌋} (dD : Ξ ⊢ D ∷ DescF JT) where
  ⊢payTCV : {q j g T A B r e : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜TSig⌝ → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ T ∷ K 1 j →
            Ξ ⊢ A ∷ K 0 j → Ξ ⊢ B ∷ K 0 j → Ξ ⊢ r ∷ IMu JT D (tmIx j g T A) → Ξ ⊢ e ∷ El (⌜≅ᵀ⌝ (sigT q) j A B) →
            Ξ ⊢ pair A (r ,ₚ e ,ₚ unit) ∷ El (dpay JT D ⌜ TCV q j g T B ⌝ᵗ)
  ⊢payTCV {q} {j} {g} {T} {A} {B} {r} {e} dq dj dg dT dA dB dr de =
    ⊢payσ ⊢JT dD {a = A} {p = pair r (e ,ₚ unit)} (okTCV dq dj dg dT dB) (toTy dA)
      (⊢-cast {Ξ} {pair r (e ,ₚ unit)} {El (dpay JT D ⌜ tρ (tmIx j g T A) (tσ (⌜≅ᵀ⌝ (sigT q) j A B) tι) ⌝ᵗ)}
              {El (dpay JT D (subTm (single A) ⌜ tρ (tmIx (w1 j) (w1 g) (w1 T) v₀) (tσ (⌜≅ᵀ⌝ (sigT (w1 q)) (w1 j) v₀ (w1 B)) tι) ⌝ᵗ))}
              (cong (λ Z → El (dpay JT D Z)) (sym eq))
        (⊢payρ ⊢JT dD {r = r} {p = pair e unit} (ok-ρ (⊢tmIx dj dg dT dA) okC) dr
          (⊢payσ ⊢JT dD {a = e} {p = unit} okC de (⊢payι ⊢JT dD ⊢unit))))
    where
      okC : TelOK Ξ JT (tσ (⌜≅ᵀ⌝ (sigT q) j A B) tι)
      okC = okσJ (⊢⌜≅ᵀ⌝ (⊢sigT dq) dj dA dB) ok-ι
      eq : subTm (single A) ⌜ tρ (tmIx (w1 j) (w1 g) (w1 T) v₀) (tσ (⌜≅ᵀ⌝ (sigT (w1 q)) (w1 j) v₀ (w1 B)) tι) ⌝ᵗ
           ≡ ⌜ tρ (tmIx j g T A) (tσ (⌜≅ᵀ⌝ (sigT q) j A B) tι) ⌝ᵗ
      eq = cv2-cong _ _ _ _ _ _ A _ _ (wk-cancel-tm A j) (wk-cancel-tm A g) (wk-cancel-tm A T)
             (trans (⌜≅ᵀ⌝-sub (single A) (sigT (w1 q)) (w1 j) v₀ (w1 B))
                    (cong₃ (λ x a b → ⌜≅ᵀ⌝ (sigT x) a A b) (wk-cancel-tm A q) (wk-cancel-tm A j) (wk-cancel-tm A B)))

  -- …at the fibre's sources `(j , conₗ k p , (g , B))`
  ⊢payTCVat : {k : ℕ} {q j g p A B r e : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜TSig⌝ → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
              Ξ ⊢ conₗ k p ∷ K 1 j → Ξ ⊢ A ∷ K 0 j → Ξ ⊢ B ∷ K 0 j → Ξ ⊢ r ∷ IMu JT D (tmIx j g (conₗ k p) A) →
              Ξ ⊢ e ∷ El (⌜≅ᵀ⌝ (sigT q) j A B) →
              Ξ ⊢ pair A (r ,ₚ e ,ₚ unit) ∷ El (dpay JT D ⌜ TCVat k q j p (g ,ₚ B) ⌝ᵗ)
  ⊢payTCVat {k} {q} {j} {g} {p} {A} {B} dq dj dg dT dA dB dr de =
    ⊢conv (⊢payTCV dq dj dg dT dA dB dr de) (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R))))
    where
      c = pair g B
      R : ⌜ TCV q j (fst c) (conₗ k p) (snd c) ⌝ᵗ ⟶* ⌜ TCV q j g (conₗ k p) B ⌝ᵗ
      R = mono-by {Δ = ⌊ Ξ ⌋} {n = 5} {as = q ∷ j ∷ fst c ∷ conₗ k p ∷ snd c ∷ []} {as' = q ∷ j ∷ g ∷ conₗ k p ∷ B ∷ []}
            ⌜ TCV v₀ v₁ v₂ v₃ v₄ ⌝ᵗ
            (TCV-sub (σₗ (q ∷ j ∷ fst c ∷ conₗ k p ∷ snd c ∷ [])) v₀ v₁ v₂ v₃ v₄)
            (TCV-sub (σₗ (q ∷ j ∷ g ∷ conₗ k p ∷ B ∷ [])) v₀ v₁ v₂ v₃ v₄)
            (done ∷ʳ done ∷ʳ step (βfst g B) done ∷ʳ done ∷ʳ step (βsnd g B) done ∷ʳ []ʳ)

------------------------------------------------------------------------
-- the `∋` premise, as a CODE (opaque)
------------------------------------------------------------------------

opaque
  ⌜∋⌝ : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
  ⌜∋⌝ d g x a = ⌜IMu⌝ I∋ D∋ (ix∋ d g x a)

  ⊢⌜∋⌝ : {Ξ : Ctx} {d g x a : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx d → Ξ ⊢ x ∷ Fin d → Ξ ⊢ a ∷ K 0 d →
         Ξ ⊢ ⌜∋⌝ d g x a ∷ U
  ⊢⌜∋⌝ dd dg dx da = ⊢⌜IMu⌝ ⊢I∋ ⊢D∋ (⊢ix∋ dd dg dx da)

  ⌜∋⌝-sub : (σ : Sub Δ Θ) (d g x a : RTm Δ) → subTm σ (⌜∋⌝ d g x a) ≡ ⌜∋⌝ (subTm σ d) (subTm σ g) (subTm σ x) (subTm σ a)
  ⌜∋⌝-sub σ d g x a = cong₂ (λ I D → ⌜IMu⌝ I D (ix∋ (subTm σ d) (subTm σ g) (subTm σ x) (subTm σ a))) (I∋-sub σ) (D∋-sub σ)

  El-⌜∋⌝ : {d g x a : RTm Δ} → El (⌜∋⌝ d g x a) ⟶ᵀ K∋ (ix∋ d g x a)
  El-⌜∋⌝ = El-⌜IMu⌝
