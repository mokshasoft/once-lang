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
module DirectedHoTT.Examples.Knot.Judge where


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; doneᵀ; ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimⁱ; ⟶*-ielimᵗ; ⟶*-fst; ⟶*-snd; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; ⟶ᵀ*-IMu )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; Lt; lt-z; lt-s; subC; selF-sub; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; payV-red; ⊢recFst; ⊢recSnd; ⊢atDepthSK )
open import DirectedHoTT.Lib.FinFam using ( FinI; ffz; ⊢ffz; ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Ren using ( wk; wk-sub; ⊢wkS )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Sorted using ( ⊢sortOf )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row; module Fib; ⊢conRow )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( ⌜Ctx⌝; rows; ⊢rows )

open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeFib
open import DirectedHoTT.Examples.Knot.JudgeRowsGen using ( rowTmGen; okTmGen; rowTyGen; okTyGen )

private
  variable
    Δ Θ : Cx

-- ★ the rows, by (sort, constructor)
rowT : ℕ → ℕ → Row
rowT 1 k  = rowTmGen k   -- the `⊢` rows (`JudgeRowsGen`)
rowT 0 k  = rowTyGen k   -- the `⊢ty` rows (`JudgeRowsGen`)
rowT _ _  = rNone


------------------------------------------------------------------------
-- 5. ★ THE FAMILY: the fibre method at the Knot's signature, typed from
--   every row's typing.
------------------------------------------------------------------------

open Fib KOK JT JT-sub ⊢JT CT CT-sub ⊢CT rowT public hiding ( RowOK; Cat; C-inst; ⊢Cat; FM; FM-sub; ⊢FM )

-- ★ every row typed, by its position in the signature
rowOK : {s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG KSig s shs → NthSh shs k sh → RowOK s sh (rowT s k)
rowOK nthᵍ-z nh = okTyGen nh
rowOK (nthᵍ-s nthᵍ-z) nh = okTmGen nh

⊢FIBMT : {Γ : Ctx} → Γ ⊢ FIBM ∷ MethTy (SI 2) (SD KSig) FM
⊢FIBMT = ⊢FIBM rowOK

-- ★ the fibre method behind an ABSTRACTION BOUNDARY: it carries every row,
--   and a transparent one is compared by normalisation wherever two
--   syntactic forms of one context meet (measured: `⊢D⊢` 50 s)
opaque
  FIBMₒ : RTm Δ
  FIBMₒ = FIBM

  ⊢FIBMₒ : {Γ : Ctx} → Γ ⊢ FIBMₒ ∷ MethTy (SI 2) (SD KSig) FM
  ⊢FIBMₒ = ⊢FIBMT

  FIBMₒ-sub : (σ : Sub Δ Θ) → subTm σ (FIBMₒ {Δ}) ≡ FIBMₒ
  FIBMₒ-sub σ = FIBM-sub σ

  fib-βₒ : {s c₀ k : ℕ} {shs : Shapes c₀} {sh : Shape} {D j p c : RTm Δ} → NthG KSig s shs → NthSh shs k sh →
           app (ielim D (pair (tag s) j) FIBMₒ (conₗ k p)) c ⟶* Row.R (rowT s k) j p c
  fib-βₒ {D = D} {j = j} {p = p} {c = c} ng nh = fib-β {D = D} {j = j} {p = p} {c₀ = c} ng nh

------------------------------------------------------------------------
-- 6. ★ THE FIBRE FUNCTION and the family.
------------------------------------------------------------------------

D⊢ : RTm Δ
D⊢ = lam (app (ielim KD (fst (var vz)) FIBMₒ (fst (snd (var vz)))) (snd (snd (var vz))))

K⊢ : RTm Δ → RTy Δ
K⊢ x = IMu JT D⊢ x


-- an index's three components (the inverse of `⊢ixJ`)
module UnJ {Ξ : Ctx} {x : RTm ⌊ Ξ ⌋} (dx : Ξ ⊢ x ∷ El JT) where
  i0 t0 c0 : RTm ⌊ Ξ ⌋
  i0 = fst x
  t0 = fst (snd x)
  c0 = snd (snd x)
  private
    B1 : RTm (⌊ Ξ ⌋ ∙)
    B1 = ⌜Σ⌝ (⌜IMu⌝ (SI 2) KD (var vz)) (renTm vs CT)
    B2 : RTm (⌊ Ξ ⌋ ∙)
    B2 = renTm vs (CTat i0)
    e1 : subTy (single i0) (El B1) ≡ El (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD i0) B2)
    e1 = cong El (cong₂ ⌜Σ⌝ {x = subTm (single i0) (⌜IMu⌝ (SI 2) KD (var vz))} {x' = ⌜IMu⌝ (SI 2) KD i0}
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

module _ {Γ : Ctx} where
  private
    Ξ : Ctx
    Ξ = Γ ▹ El JT
    dv : Ξ ⊢ var vz ∷ El JT
    dv = ⊢-cast {Ξ} {var vz} {renTy vs (El JT)} {El JT} (cong El (JT-ren vs)) (⊢var here)
    open UnJ dv
    dI : Ξ ⊢ ielim KD i0 FIBMₒ t0 ∷ iinst i0 t0 FM
    dI = ⊢ielim {Ξ} {SI 2} {KD} {FM} {FIBMₒ} {i0} {t0} ⊢SI ⊢KD ⊢FM ⊢FIBMₒ di0 dt0
    eI : iinst i0 t0 FM ≡ Π (El (CTat i0)) (Desc JT)
    eI = trans {x = iinst i0 t0 FM} {y = subTy (single t0 ∘ₛ extS (single i0)) FM} {z = Π (El (CTat i0)) (Desc JT)}
               (subTy-subTy {τ = single t0} {σ = extS (single i0)} FM)
               (trans (FM-sub (single t0 ∘ₛ extS (single i0)))
                      (cong (λ z → Π (El (CTat z)) (Desc JT)) {x = subTm (single t0) (renTm vs i0)} {y = i0}
                            (wk-cancel-tm t0 i0)))
    bodyD : Ξ ⊢ app (ielim KD i0 FIBMₒ t0) c0 ∷ Desc (renTm vs JT)
    bodyD = ⊢-cast {Ξ} {app (ielim KD i0 FIBMₒ t0) c0} {subTy (single c0) (Desc JT)} {Desc (renTm vs JT)}
                   (trans (cong Desc (JT-sub (single c0))) (cong Desc (sym (JT-ren vs))))
                   (⊢app {Ξ} {El (CTat i0)} {Desc JT} {ielim KD i0 FIBMₒ t0} {c0}
                         (⊢-cast {Ξ} {ielim KD i0 FIBMₒ t0} {iinst i0 t0 FM} {Π (El (CTat i0)) (Desc JT)} eI dI) dc0)

  -- ★ THE TYPING JUDGEMENT IS A WELL-FORMED FAMILY
  ⊢D⊢ : Γ ⊢ D⊢ ∷ DescF JT
  ⊢D⊢ = ⊢lam (ty-El ⊢JT) bodyD

  ty-K⊢ : {x : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ El JT → Γ ⊢ty K⊢ x
  ty-K⊢ dx = ty-IMu ⊢JT ⊢D⊢ dx

------------------------------------------------------------------------
-- 7. ★ THE FIBRE COMPUTES, and the constructors.
------------------------------------------------------------------------

-- the fibre function at an index is the case on its subject
D⊢-β : (i t c : RTm Δ) → app D⊢ (ixJ i t c) ⟶* app (ielim KD i FIBMₒ t) c
D⊢-β {Δ} i t c =
  step (β B x)
    (subst (λ z → z ⟶* app (ielim KD i FIBMₒ t) c) (sym e)
      (⟶*-trans {t = app (ielim KD (fst x) FIBMₒ (fst (snd x))) (snd (snd x))}
                {u = app (ielim KD i FIBMₒ t) (snd (snd x))} {v = app (ielim KD i FIBMₒ t) c}
        (⟶*-appˡ (⟶*-trans {t = ielim KD (fst x) FIBMₒ (fst (snd x))} {u = ielim KD i FIBMₒ (fst (snd x))}
                            {v = ielim KD i FIBMₒ t}
                    (⟶*-ielimⁱ (step (βfst i (pair t c)) done))
                    (⟶*-ielimᵗ (⟶*-trans {t = fst (snd x)} {u = fst (pair t c)} {v = t}
                                  (⟶*-fst (step (βsnd i (pair t c)) done)) (step (βfst t c) done)))))
        (⟶*-appʳ (⟶*-trans {t = snd (snd x)} {u = snd (pair t c)} {v = c}
                   (⟶*-snd (step (βsnd i (pair t c)) done)) (step (βsnd t c) done)))))
  where
    x = ixJ i t c
    B : RTm (Δ ∙)
    B = app (ielim KD (fst (var vz)) FIBMₒ (fst (snd (var vz)))) (snd (snd (var vz)))
    e : subTm (single x) B ≡ app (ielim KD (fst x) FIBMₒ (fst (snd x))) (snd (snd x))
    e = cong₂ (λ D M → app (ielim D (fst x) M (fst (snd x))) (snd (snd x)))
              {x = subTm (single x) (KD {Δ ∙})} {x' = KD} {y = subTm (single x) (FIBMₒ {Δ ∙})} {y' = FIBMₒ}
              (SD-sub (single x) KSig) (FIBMₒ-sub (single x))

-- ★ at a canonical subject, the fibre IS the row
fibK : {s c₀ k : ℕ} {shs : Shapes c₀} {sh : Shape} {j p c : RTm Δ} → NthG KSig s shs → NthSh shs k sh →
       app D⊢ (ixJ (pair (tag s) j) (conₗ k p) c) ⟶* Row.R (rowT s k) j p c
fibK {s = s} {k = k} {j = j} {p} {c} ng nh =
  ⟶*-trans (D⊢-β (pair (tag s) j) (conₗ k p) c) (fib-βₒ {D = KD} {j = j} {p = p} {c = c} ng nh)

