-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★ `Γ ⊢ty A` / `Γ ⊢ t ∷ A`: THE TYPING JUDGEMENT,
-- ONE FAMILY OVER BOTH SORTS, FIBRED BY ITS SUBJECT (D077, `Lib/SynFib`).
--
-- The index is `(i , t , c)`: a Knot index `i = (sort , depth)`, the
-- subject `t : K sort depth`, and the CONVOY `c`:
--
--     sort Ty:   c = (Γ , tt)       Γ ⊢ty t
--     sort Tm:   c = (Γ , A)        Γ ⊢ t ∷ A
--
-- The fibre over `(i , t , c)` is a case on `t`'s head: exactly the rules
-- whose conclusion has that head.  Nothing about the subject Fords; a
-- computed OUTPUT (a conclusion type such as `B[u]`) Fords explicitly.
--
-- ⬜ This module is built in stages: the `⊢ty` rows first.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PwCore as Core₀
module DirectedHoTT.Examples.Knot.Judge (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where




open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
import DirectedHoTT.Lib.NatCode 𝒮 (Defs.size 𝒮) as ᴵNatCode
open ᴵNatCode using ( fromI )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic 𝒮 using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; doneᵀ; ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimⁱ; ⟶*-ielimᵗ; ⟶*-fst; ⟶*-snd; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; ⟶ᵀ*-IMu )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Cons; []; _∷_; conₗ; tag; Lt; lt-z; lt-s; subC; selF-sub; []ᵈ; _∷ᵈ_; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( PayV; payV-red; ⊢recFst; ⊢recSnd; ⊢atDepthSK )
open ᴵNatCode using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( wk; wk-sub; ⊢wkS )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Sorted 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( ⊢sortOf )
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.SynFib 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Row; module Fib; ⊢conRow )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( ⌜Ctx⌝; rows; ⊢rows )

import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf as ᴵJudgeIx
open ᴵJudgeIx
open import DirectedHoTT.Examples.Knot.JudgeFib 𝒮 wf
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜TSig⌝; ⌜TSig⌝-sub; ⊢⌜TSig⌝; wkT )
open import DirectedHoTT.Examples.Knot.JudgeRowsGen 𝒮 wf core using ( rows⊢ty; rows⊢ )

private
  variable
    Δ Θ : Cx

-- ★ THE JUDGEMENT, as its table: the `⊢ty` rows (sort 0) and the `⊢` rows
--   (sort 1), each constructor's row with its typing (`JudgeRowsGen`)
rowsT : RowsOKG zero KSig
rowsT = rows⊢ty ∷ᴳ rows⊢ ∷ᴳ []ᴳ

rowT : ℕ → ℕ → Row
rowT = rowIn rowsT


------------------------------------------------------------------------
-- 5. ★ THE FAMILY: the fibre method at the Knot's signature, typed from
--   every row's typing.
------------------------------------------------------------------------

open Fib KOK ⌜TSig⌝ ⌜TSig⌝-sub ⊢⌜TSig⌝ JT JT-sub ⊢JT CT CT-sub ⊢CT rowT public hiding ( RowOK; Cat; C-inst; ⊢Cat; FM; FM-sub; ⊢FM
                                                       ; RowsOK; RowsOKG; pastRow; rowInSh; rowIn; okInSh; okIn; okOf )

-- ★ every row typed, by its position in the signature
rowOK : {s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG KSig s shs → NthSh shs k sh → RowOK s sh (rowT s k)
rowOK = okOf rowsT

⊢FIBMT : {Γ : Ctx} {q : RTm ⌊ Γ ⌋} → Γ ⊢ q ∷ El ⌜TSig⌝ → Γ ⊢ FIBM q ∷ MethTy (SI 2) (SD KSig) FM
⊢FIBMT dq = ⊢FIBM dq rowOK

-- ★ the fibre method behind an ABSTRACTION BOUNDARY: it carries every row,
--   and a transparent one is compared by normalisation wherever two
--   syntactic forms of one context meet (measured: `⊢D⊢` 50 s)
opaque
  FIBMₒ : RTm Δ → RTm Δ
  FIBMₒ q = FIBM q

  ⊢FIBMₒ : {Γ : Ctx} {q : RTm ⌊ Γ ⌋} → Γ ⊢ q ∷ El ⌜TSig⌝ → Γ ⊢ FIBMₒ q ∷ MethTy (SI 2) (SD KSig) FM
  ⊢FIBMₒ dq = ⊢FIBMT dq

  FIBMₒ-sub : (σ : Sub Δ Θ) (q : RTm Δ) → subTm σ (FIBMₒ {Δ} q) ≡ FIBMₒ (subTm σ q)
  FIBMₒ-sub σ q = FIBM-sub σ q

  fib-βₒ : {s c₀ k : ℕ} {shs : Shapes c₀} {sh : Shape} {D q j p c : RTm Δ} → NthG KSig s shs → NthSh shs k sh →
           app (ielim D ((tag s) ,ₚ j) (FIBMₒ q) (conₗ k p)) c ⟶* Row.R (rowT s k) q j p c
  fib-βₒ {D = D} {q = q} {j = j} {p = p} {c = c} ng nh = fib-β {D = D} {q = q} {j = j} {p = p} {c₀ = c} ng nh

------------------------------------------------------------------------
-- 6. ★ THE FIBRE FUNCTION and the family, at the typing parameter `q`
--   (the signature and the bound; PLAN-REF).
------------------------------------------------------------------------

D⊢ : RTm Δ → RTm Δ
D⊢ q = lam (app (ielim KD (fst v₀) (FIBMₒ (renTm vs q)) (fst (snd v₀))) (snd (snd v₀)))

K⊢ : RTm Δ → RTm Δ → RTy Δ
K⊢ q x = IMu JT (D⊢ q) x


-- an index's three components (the inverse of `⊢ixJ`)
module UnJ {Ξ : Ctx} {x : RTm ⌊ Ξ ⌋} (dx : Ξ ⊢ x ∷ El JT) where
  i0 t0 c0 : RTm ⌊ Ξ ⌋
  i0 = fst x
  t0 = fst (snd x)
  c0 = snd (snd x)
  private
    B1 : RTm (⌊ Ξ ⌋ ∙)
    B1 = ⌜Σ⌝ (⌜IMu⌝ (SI 2) KD v₀) (renTm vs CT)
    B2 : RTm (⌊ Ξ ⌋ ∙)
    B2 = renTm vs (CTat i0)
    e1 : subTy (single i0) (El B1) ≡ El (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i0) B2)
    e1 = cong El (cong₂ ⌜Σ⌝ {x = subTm (single i0) (⌜IMu⌝ (SI 2) KD v₀)} {x' = ⌜IMu⌝ (SI 2) KD i0}
                            {y = subTm (extS (single i0)) (renTm vs CT)} {y' = B2}
                    (cong (λ D → ⌜IMu⌝ (SI 2) D i0) (SD-sub (single i0) KSig))
                    (wkS (single i0) CT))
    dx' : Ξ ⊢ x ∷ Σ' (El (SI 2)) (El B1)
    dx' = ⊢conv dx (credᵀ (El-⌜Σ⌝ (SI 2) B1))
    d2 : Ξ ⊢ snd x ∷ Σ' (El (⌜IMu⌝ (SI 2) KD i0)) (El B2)
    d2 = ⊢conv (⊢-cast {Ξ} {snd x} {subTy (single i0) (El B1)} {El (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i0) B2)} e1 (⊢snd dx'))
               (credᵀ (El-⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i0) B2))
  di0 : Ξ ⊢ i0 ∷ El (SI 2)
  di0 = ⊢fst dx'
  dt0 : Ξ ⊢ t0 ∷ IMu (SI 2) KD i0
  dt0 = ⊢conv (⊢fst d2) (credᵀ El-⌜IMu⌝)
  dc0 : Ξ ⊢ c0 ∷ El (CTat i0)
  dc0 = ⊢-cast {Ξ} {c0} {subTy (single t0) (El B2)} {El (CTat i0)} (cong El (wk-cancel-tm t0 (CTat i0))) (⊢snd d2)

module _ {Γ : Ctx} {q : RTm ⌊ Γ ⌋} (dq : Γ ⊢ q ∷ El ⌜TSig⌝) where
  private
    Ξ : Ctx
    Ξ = Γ ▹ El JT
    dv : Ξ ⊢ v₀ ∷ El JT
    dv = ⊢-cast {Ξ} {v₀} {renTy vs (El JT)} {El JT} (cong El (JT-ren vs)) (⊢var here)
    open UnJ dv
    M = FIBMₒ (renTm vs q)
    dI : Ξ ⊢ ielim KD i0 M t0 ∷ iinst i0 t0 FM
    dI = ⊢ielim {Ξ} {SI 2} {KD} {FM} {M} {i0} {t0} ⊢SI ⊢KD ⊢FM (⊢FIBMₒ (wkT dq)) di0 dt0
    eI : iinst i0 t0 FM ≡ Π (El (CTat i0)) (Desc JT)
    eI = trans {x = iinst i0 t0 FM} {y = subTy (single t0 ∘ₛ extS (single i0)) FM} {z = Π (El (CTat i0)) (Desc JT)}
               (subTy-subTy {τ = single t0} {σ = extS (single i0)} FM)
               (trans (FM-sub (single t0 ∘ₛ extS (single i0)))
                      (cong (λ z → Π (El (CTat z)) (Desc JT)) {x = subTm (single t0) (renTm vs i0)} {y = i0}
                            (wk-cancel-tm t0 i0)))
    bodyD : Ξ ⊢ app (ielim KD i0 M t0) c0 ∷ Desc (renTm vs JT)
    bodyD = ⊢-cast {Ξ} {app (ielim KD i0 M t0) c0} {subTy (single c0) (Desc JT)} {Desc (renTm vs JT)}
                   (trans (cong Desc (JT-sub (single c0))) (cong Desc (sym (JT-ren vs))))
                   (⊢app {Ξ} {El (CTat i0)} {Desc JT} {ielim KD i0 M t0} {c0}
                         (⊢-cast {Ξ} {ielim KD i0 M t0} {iinst i0 t0 FM} {Π (El (CTat i0)) (Desc JT)} eI dI) dc0)

  -- ★ THE TYPING JUDGEMENT IS A WELL-FORMED FAMILY, at a well-typed parameter
  ⊢D⊢ : Γ ⊢ D⊢ q ∷ DescF JT
  ⊢D⊢ = ⊢lam (ty-El ⊢JT) bodyD

  ty-K⊢ : {x : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ El JT → Γ ⊢ty K⊢ q x
  ty-K⊢ dx = ty-IMu ⊢JT ⊢D⊢ dx

------------------------------------------------------------------------
-- 7. ★ THE FIBRE COMPUTES, and the constructors.
------------------------------------------------------------------------

-- the fibre function at an index is the case on its subject
D⊢-β : (q i t c : RTm Δ) → app (D⊢ q) (ixJ i t c) ⟶* app (ielim KD i (FIBMₒ q) t) c
D⊢-β {Δ} q i t c =
  step (β B x)
    (subst (λ z → z ⟶* app (ielim KD i (FIBMₒ q) t) c) (sym e)
      (⟶*-trans {t = app (ielim KD (fst x) (FIBMₒ q) (fst (snd x))) (snd (snd x))}
                {u = app (ielim KD i (FIBMₒ q) t) (snd (snd x))} {v = app (ielim KD i (FIBMₒ q) t) c}
        (⟶*-appˡ (⟶*-trans {t = ielim KD (fst x) (FIBMₒ q) (fst (snd x))} {u = ielim KD i (FIBMₒ q) (fst (snd x))}
                            {v = ielim KD i (FIBMₒ q) t}
                    (⟶*-ielimⁱ (step (βfst i (t ,ₚ c)) done))
                    (⟶*-ielimᵗ (⟶*-trans {t = fst (snd x)} {u = fst (t ,ₚ c)} {v = t}
                                  (⟶*-fst (step (βsnd i (t ,ₚ c)) done)) (step (βfst t c) done)))))
        (⟶*-appʳ (⟶*-trans {t = snd (snd x)} {u = snd (t ,ₚ c)} {v = c}
                   (⟶*-snd (step (βsnd i (t ,ₚ c)) done)) (step (βsnd t c) done)))))
  where
    x = ixJ i t c
    B : RTm (Δ ∙)
    B = app (ielim KD (fst v₀) (FIBMₒ (renTm vs q)) (fst (snd v₀))) (snd (snd v₀))
    e : subTm (single x) B ≡ app (ielim KD (fst x) (FIBMₒ q) (fst (snd x))) (snd (snd x))
    e = cong₂ (λ D M → app (ielim D (fst x) M (fst (snd x))) (snd (snd x)))
              {x = subTm (single x) (KD {Δ ∙})} {x' = KD} {y = subTm (single x) (FIBMₒ {Δ ∙} (renTm vs q))} {y' = FIBMₒ q}
              (SD-sub (single x) KSig) (trans (FIBMₒ-sub (single x) (renTm vs q)) (cong FIBMₒ (wk-cancel-tm x q)))

-- ★ at a canonical subject, the fibre IS the row
fibK : {s c₀ k : ℕ} {shs : Shapes c₀} {sh : Shape} {q j p c : RTm Δ} → NthG KSig s shs → NthSh shs k sh →
       app (D⊢ q) (ixJ ((tag s) ,ₚ j) (conₗ k p) c) ⟶* Row.R (rowT s k) q j p c
fibK {s = s} {k = k} {q = q} {j = j} {p} {c} ng nh =
  ⟶*-trans (D⊢-β q ((tag s) ,ₚ j) (conₗ k p) c) (fib-βₒ {D = KD} {q = q} {j = j} {p = p} {c = c} ng nh)

