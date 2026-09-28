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
open import DirectedHoTT.Lib.SynView using ( PayV; payV-red; ⊢recFst; ⊢recSnd; ⊢atDepth )
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
open import DirectedHoTT.Examples.Knot.JudgeRowsTy

private
  variable
    Δ Θ : Cx

-- ★ the rows, by (sort, constructor); the `⊢` rows are the next stage
rowT : ℕ → ℕ → Row
rowT 0 0  = defRow T0 (λ σ j p c → refl)      -- base
rowT 0 1  = defRow T0 (λ σ j p c → refl)      -- U
rowT 0 2  = defRow TPi (λ σ j p c → refl)     -- Π
rowT 0 3  = defRow TPi (λ σ j p c → refl)     -- Σ
rowT 0 4  = defRow TEl (λ σ j p c → refl)     -- El
rowT 0 5  = defRow THom (λ σ j p c → refl)    -- Hom
rowT 0 6  = defRow T0 (λ σ j p c → refl)      -- Unit
rowT 0 7  = defRow T0 (λ σ j p c → refl)      -- Nat
rowT 0 8  = defRow THom (λ σ j p c → refl)    -- Id
rowT 0 9  = rIMu           -- IMu
rowT 0 10 = defRow TDesc (λ σ j p c → refl)   -- Desc
rowT 0 11 = defRow TDIh TDIh-law   -- DIh
rowT 0 12 = defRow T0 (λ σ j p c → refl)      -- Fin
rowT _ _  = rNone


------------------------------------------------------------------------
-- 5. ★ THE FAMILY: the fibre method at the Knot's signature, typed from
--   every row's typing.
------------------------------------------------------------------------

open Fib KOK JT JT-sub ⊢JT CT CT-sub ⊢CT rowT public hiding ( RowOK; Cat; C-inst; ⊢Cat; FM; FM-sub; ⊢FM )

-- ★ every row typed, by its position in the signature
rowOK : {s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG KSig s shs → NthSh shs k sh → RowOK s sh (rowT s k)
rowOK nthᵍ-z nthʰ-z = ok0 {sh-kbase}
rowOK nthᵍ-z (nthʰ-s nthʰ-z) = ok0 {sh-kU}
rowOK nthᵍ-z (nthʰ-s (nthʰ-s nthʰ-z)) = okPi
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z))) = okPi
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z)))) = okEl
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z))))) = okHom
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z)))))) = ok0 {sh-kUnit}
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z))))))) = ok0 {sh-kNat}
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z)))))))) = okHom
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z))))))))) = okIMu
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z)))))))))) = okDesc
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z))))))))))) = okDIh
rowOK nthᵍ-z (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s (nthʰ-s nthʰ-z)))))))))))) = ok0 {sh-kFin}
rowOK {sh = sh} (nthᵍ-s nthᵍ-z) nh = okNone {1} {sh}

⊢FIBMT : {Γ : Ctx} → Γ ⊢ FIBM ∷ MethTy (SI 2) (SD KSig) FM
⊢FIBMT = ⊢FIBM rowOK

------------------------------------------------------------------------
-- 6. ★ THE FIBRE FUNCTION and the family.
------------------------------------------------------------------------

D⊢ : RTm Δ
D⊢ = lam (app (ielim KD (fst (var vz)) FIBM (fst (snd (var vz)))) (snd (snd (var vz))))

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
    dI : Ξ ⊢ ielim KD i0 FIBM t0 ∷ iinst i0 t0 FM
    dI = ⊢ielim {Ξ} {SI 2} {KD} {FM} {FIBM} {i0} {t0} ⊢SI ⊢KD ⊢FM ⊢FIBMT di0 dt0
    eI : iinst i0 t0 FM ≡ Π (El (CTat i0)) (Desc JT)
    eI = trans {x = iinst i0 t0 FM} {y = subTy (single t0 ∘ₛ extS (single i0)) FM} {z = Π (El (CTat i0)) (Desc JT)}
               (subTy-subTy {τ = single t0} {σ = extS (single i0)} FM)
               (trans (FM-sub (single t0 ∘ₛ extS (single i0)))
                      (cong (λ z → Π (El (CTat z)) (Desc JT)) {x = subTm (single t0) (renTm vs i0)} {y = i0}
                            (wk-cancel-tm t0 i0)))
    bodyD : Ξ ⊢ app (ielim KD i0 FIBM t0) c0 ∷ Desc (renTm vs JT)
    bodyD = ⊢-cast {Ξ} {app (ielim KD i0 FIBM t0) c0} {subTy (single c0) (Desc JT)} {Desc (renTm vs JT)}
                   (trans (cong Desc (JT-sub (single c0))) (cong Desc (sym (JT-ren vs))))
                   (⊢app {Ξ} {El (CTat i0)} {Desc JT} {ielim KD i0 FIBM t0} {c0}
                         (⊢-cast {Ξ} {ielim KD i0 FIBM t0} {iinst i0 t0 FM} {Π (El (CTat i0)) (Desc JT)} eI dI) dc0)

  -- ★ THE TYPING JUDGEMENT IS A WELL-FORMED FAMILY
  ⊢D⊢ : Γ ⊢ D⊢ ∷ DescF JT
  ⊢D⊢ = ⊢lam (ty-El ⊢JT) bodyD

  ty-K⊢ : {x : RTm ⌊ Γ ⌋} → Γ ⊢ x ∷ El JT → Γ ⊢ty K⊢ x
  ty-K⊢ dx = ty-IMu ⊢JT ⊢D⊢ dx

------------------------------------------------------------------------
-- 7. ★ THE FIBRE COMPUTES, and the constructors.
------------------------------------------------------------------------

-- the fibre function at an index is the case on its subject
D⊢-β : (i t c : RTm Δ) → app D⊢ (ixJ i t c) ⟶* app (ielim KD i FIBM t) c
D⊢-β {Δ} i t c =
  step (β B x)
    (subst (λ z → z ⟶* app (ielim KD i FIBM t) c) (sym e)
      (⟶*-trans {t = app (ielim KD (fst x) FIBM (fst (snd x))) (snd (snd x))}
                {u = app (ielim KD i FIBM t) (snd (snd x))} {v = app (ielim KD i FIBM t) c}
        (⟶*-appˡ (⟶*-trans {t = ielim KD (fst x) FIBM (fst (snd x))} {u = ielim KD i FIBM (fst (snd x))}
                            {v = ielim KD i FIBM t}
                    (⟶*-ielimⁱ (step (βfst i (pair t c)) done))
                    (⟶*-ielimᵗ (⟶*-trans {t = fst (snd x)} {u = fst (pair t c)} {v = t}
                                  (⟶*-fst (step (βsnd i (pair t c)) done)) (step (βfst t c) done)))))
        (⟶*-appʳ (⟶*-trans {t = snd (snd x)} {u = snd (pair t c)} {v = c}
                   (⟶*-snd (step (βsnd i (pair t c)) done)) (step (βsnd t c) done)))))
  where
    x = ixJ i t c
    B : RTm (Δ ∙)
    B = app (ielim KD (fst (var vz)) FIBM (fst (snd (var vz)))) (snd (snd (var vz)))
    e : subTm (single x) B ≡ app (ielim KD (fst x) FIBM (fst (snd x))) (snd (snd x))
    e = cong₂ (λ D M → app (ielim D (fst x) M (fst (snd x))) (snd (snd x)))
              {x = subTm (single x) (KD {Δ ∙})} {x' = KD} {y = subTm (single x) (FIBM {Δ ∙})} {y' = FIBM}
              (SD-sub (single x) KSig) (FIBM-sub (single x))

-- ★ at a canonical subject, the fibre IS the row
fibK : {s c₀ k : ℕ} {shs : Shapes c₀} {sh : Shape} {j p c : RTm Δ} → NthG KSig s shs → NthSh shs k sh →
       app D⊢ (ixJ (pair (tag s) j) (conₗ k p) c) ⟶* Row.R (rowT s k) j p c
fibK {s = s} {k = k} {j = j} {p} {c} ng nh =
  ⟶*-trans (D⊢-β (pair (tag s) j) (conₗ k p) c) (fib-β {D = KD} {j = j} {p = p} {c₀ = c} ng nh)

-- a payload of the Knot, at its normal form
⊢payK : {Ξ : Ctx} {s : ℕ} {j p : RTm ⌊ Ξ ⌋} {sh : Shape} → Lt s 2 → ShOK 2 sh → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Args Ξ 2 KD j sh p → Ξ ⊢ p ∷ PayV sh (pair (tag s) j) (SI 2) (SD KSig)
⊢payK {s = s} {j = j} {sh = sh} lt ok dj as =
  ⊢conv (⊢payArgs ⊢KD ok (⊢ix lt dj) (step (βsnd (tag s) j) done) as) (red→≅ᵀ (payV-red sh (pair (tag s) j) (SI 2) (SD KSig)))

