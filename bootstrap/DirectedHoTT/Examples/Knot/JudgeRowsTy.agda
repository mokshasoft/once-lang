------------------------------------------------------------------------
-- OCP-0009 · KNOT — the `⊢ty` ROWS of the typing judgement (D077): one per type former, its premises at computed indices; each row's substitution law and its typing at any payload.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeRowsTy where


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

open import DirectedHoTT.Lib.SynFib using ( module Fib₀ )
open import DirectedHoTT.Examples.Knot.JudgeIx

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- The `⊢ty` rows: telescopes, laws, and typings.
------------------------------------------------------------------------

-- the telescopes (index `j`, payload `p`, convoy `c`; the context is `fst c`)
T0 TPi TEl THom TIMu TDesc : RTm Δ → RTm Δ → RTm Δ → Tel Δ
T0 j p c = tι
TPi j p c = tρ (tyIx j (fst c) (fst p)) (tρ (tyIx (nsuc j) (cext (fst c) (fst p)) (fst (snd p))) tι)
TEl j p c = tρ (tmIx j (fst c) (fst p) kU) tι
THom j p c = tρ (tyIx j (fst c) (fst p))
               (tρ (tmIx j (fst c) (fst (snd p)) (fst p)) (tρ (tmIx j (fst c) (fst (snd (snd p))) (fst p)) tι))
TIMu j p c = tρ (tmIx j (fst c) (fst p) kU)
               (tρ (tmIx j (fst c) (fst (snd p)) (DF j (fst p))) (tρ (tmIx j (fst c) (fst (snd (snd p))) (kEl (fst p))) tι))
TDesc j p c = tρ (tmIx j (fst c) (fst p) kU) tι


rIMu : Row
rIMu = record
  { R = λ j p c → row1 (TIMu j p c)
  ; R-sub = λ σ j p c →
      trans (rows-sub' σ (⌜ TIMu j p c ⌝ᵗ ∷ []))
            (cong (λ X → rows (dρ (tmIx (subTm σ j) (fst (subTm σ c)) (fst (subTm σ p)) kU)
                                  (dρ (tmIx (subTm σ j) (fst (subTm σ c)) (fst (snd (subTm σ p))) X)
                                      (dρ (tmIx (subTm σ j) (fst (subTm σ c)) (fst (snd (snd (subTm σ p)))) (kEl (fst (subTm σ p)))) dι))
                               ∷ []))
                  {x = subTm σ (DF j (fst p))} {y = DF (subTm σ j) (fst (subTm σ p))}
                  (DF-sub σ j (fst p)))
  }


-- the premises under the σ-field, every position a parameter
TDIhI : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
TDIhI J G V D M C Q =
  tρ (tmIx J G V kU)
    (tρ (tmIx J G D (DF J V))
      (tρ (tyIx (nsuc (nsuc J)) (mc J G V D) M)
        (tρ (tmIx J G C (kDesc V))
          (tρ (tmIx J G Q (kEl (kdpay V D C))) tι))))

TDIhI-sub : (σ : Sub Δ Θ) (J G V D M C Q : RTm Δ) →
            subTm σ ⌜ TDIhI J G V D M C Q ⌝ᵗ
            ≡ ⌜ TDIhI (subTm σ J) (subTm σ G) (subTm σ V) (subTm σ D) (subTm σ M) (subTm σ C) (subTm σ Q) ⌝ᵗ
TDIhI-sub σ J G V D M C Q =
  cong₂ (λ X Y → dρ (tmIx J' G' V' kU)
                   (dρ (tmIx J' G' D' X)
                     (dρ (tyIx (nsuc (nsuc J')) Y M')
                       (dρ (tmIx J' G' C' (kDesc V')) (dρ (tmIx J' G' Q' (kEl (kdpay V' D' C'))) dι)))))
        {x = subTm σ (DF J V)} {x' = DF J' V'} {y = subTm σ (mc J G V D)} {y' = mc J' G' V' D'}
        (DF-sub σ J V) (mc-sub σ J G V D)
  where J' = subTm σ J ; G' = subTm σ G ; V' = subTm σ V ; D' = subTm σ D ; M' = subTm σ M ; C' = subTm σ C ; Q' = subTm σ Q

TDIh : RTm Δ → RTm Δ → RTm Δ → Tel Δ
TDIh j p c = tσ (⌜Tm⌝ j) (TDIhI (renTm vs j) (renTm vs (fst c)) (var vz) (renTm vs (fst p)) (renTm vs (fst (snd p)))
                                (renTm vs (fst (snd (snd p)))) (renTm vs (fst (snd (snd (snd p))))))

TDIh-law : TelLaw TDIh
TDIh-law σ j p c =
  cong₂ (λ S X → dσ S (lam X))
        {x = subTm σ (⌜Tm⌝ j)} {x' = ⌜Tm⌝ (subTm σ j)}
        {y = subTm (extS σ) ⌜ TDIhI (w j) (w (fst c)) (var vz) (w (fst p)) (w (fst (snd p))) (w (fst (snd (snd p))))
                                    (w (fst (snd (snd (snd p))))) ⌝ᵗ}
        {y' = ⌜ TDIhI (w j') (w (fst c')) (var vz) (w (fst p')) (w (fst (snd p'))) (w (fst (snd (snd p'))))
                      (w (fst (snd (snd (snd p'))))) ⌝ᵗ}
        (⌜Tm⌝-sub σ j)
        (trans (TDIhI-sub (extS σ) (w j) (w (fst c)) (var vz) (w (fst p)) (w (fst (snd p))) (w (fst (snd (snd p))))
                          (w (fst (snd (snd (snd p))))))
               (cong₆' (wkS σ j) (wkS σ (fst c)) (wkS σ (fst p)) (wkS σ (fst (snd p))) (wkS σ (fst (snd (snd p))))
                       (wkS σ (fst (snd (snd (snd p)))))))
  where
    w : {Ξ : Cx} → RTm Ξ → RTm (Ξ ∙)
    w t = renTm vs t
    j' = subTm σ j ; p' = subTm σ p ; c' = subTm σ c
    cong₆' : {a a' b b' d d' e e' f f' h h' : RTm _} → a ≡ a' → b ≡ b' → d ≡ d' → e ≡ e' → f ≡ f' → h ≡ h' →
             ⌜ TDIhI a b (var vz) d e f h ⌝ᵗ ≡ ⌜ TDIhI a' b' (var vz) d' e' f' h' ⌝ᵗ
    cong₆' refl refl refl refl refl refl = refl


open Fib₀ KOK JT JT-sub ⊢JT CT CT-sub ⊢CT public

module TyOK where
  module RowTyping {Ξ : Ctx} {j c : RTm ⌊ Ξ ⌋} (dj : Ξ ⊢ j ∷ El ⌜Nat⌝) (dc : Ξ ⊢ c ∷ El (CTat (pair (tag 0) j))) where
    dg : Ξ ⊢ fst c ∷ KCtx j
    dg = ⊢ctxOf dc
    done1 : (T : Tel ⌊ Ξ ⌋) → TelOK Ξ JT T → Ξ ⊢ rows (⌜ T ⌝ᵗ ∷ []) ∷ Desc JT
    done1 T ok = ⊢rows ⊢JT (⊢tel {Ξ} {JT} {T} ⊢JT ok ∷ᵈ []ᵈ)

  -- a payload's fields at sort 0, the shape EXPLICIT (`PayV` computes on it)
  f0 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
       Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) (pair (tag 0) j) (SI 2) (SD KSig) → Ξ ⊢ fst p ∷ K s (nsucs k j)
  f0 {j = j} s k sh dp = ⊢atDepth {a = tag 0} {j = j} {s = s} {k = k} (⊢recFst {s = s} {k = k} {sh = sh} dp)

  r1 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
       Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) (pair (tag 0) j) (SI 2) (SD KSig) → Ξ ⊢ snd p ∷ PayV sh (pair (tag 0) j) (SI 2) (SD KSig)
  r1 s k sh dp = ⊢recSnd {s = s} {k = k} {sh = sh} dp

  ok0 : {sh : Shape} → RowOK 0 sh (defRow T0 (λ σ j p c → refl))
  ok0 {j = j} {p} {c} dj dp dc = RowTyping.done1 dj dc (T0 j p c) ok-ι

  okPi : RowOK 0 sh-kPi (defRow TPi (λ σ j p c → refl))
  okPi {j = j} {p} {c} dj dp dc =
    done1 (TPi j p c) (ok-ρ (⊢tyIx dj dg dA) (ok-ρ (⊢tyIx (⊢isuc dj) (⊢cext dj dg dA) dB) ok-ι))
    where open RowTyping dj dc
          dA = f0 0 0 (rec 0 1 ∷ʰ []ʰ) dp
          dB = f0 0 1 []ʰ (r1 0 0 (rec 0 1 ∷ʰ []ʰ) dp)

  okEl : RowOK 0 sh-kEl (defRow TEl (λ σ j p c → refl))
  okEl {j = j} {p} {c} dj dp dc = done1 (TEl j p c) (ok-ρ (⊢tmIx dj dg (f0 1 0 []ʰ dp) (⊢kU dj)) ok-ι)
    where open RowTyping dj dc

  okHom : RowOK 0 sh-kHom (defRow THom (λ σ j p c → refl))
  okHom {j = j} {p} {c} dj dp dc =
    done1 (THom j p c) (ok-ρ (⊢tyIx dj dg dA) (ok-ρ (⊢tmIx dj dg dt dA) (ok-ρ (⊢tmIx dj dg du dA) ok-ι)))
    where open RowTyping dj dc
          p1 = r1 0 0 (rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) dp
          dA = f0 0 0 (rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) dp
          dt = f0 1 0 (rec 1 0 ∷ʰ []ʰ) p1
          du = f0 1 0 []ʰ (r1 1 0 (rec 1 0 ∷ʰ []ʰ) p1)

  okIMu : RowOK 0 sh-kIMu rIMu
  okIMu {j = j} {p} {c} dj dp dc =
    done1 (TIMu j p c) (ok-ρ (⊢tmIx dj dg dI (⊢kU dj)) (ok-ρ (⊢tmIx dj dg dD (⊢DF dj dI)) (ok-ρ (⊢tmIx dj dg di (⊢kEl dj dI)) ok-ι)))
    where open RowTyping dj dc
          p1 = r1 1 0 (rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) dp
          dI = f0 1 0 (rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) dp
          dD = f0 1 0 (rec 1 0 ∷ʰ []ʰ) p1
          di = f0 1 0 []ʰ (r1 1 0 (rec 1 0 ∷ʰ []ʰ) p1)

  okDesc : RowOK 0 sh-kDesc (defRow TDesc (λ σ j p c → refl))
  okDesc {j = j} {p} {c} dj dp dc = done1 (TDesc j p c) (ok-ρ (⊢tmIx dj dg (f0 1 0 []ʰ dp) (⊢kU dj)) ok-ι)
    where open RowTyping dj dc

  okDIh : RowOK 0 sh-kDIh (defRow TDIh TDIh-law)
  okDIh {Ξ} {j} {p} {c} dj dp dc =
    done1 (TDIh j p c) (ok-σ (⊢⌜Tm⌝ dj) (subst (λ X → TelOK Ξ₁ X T₁) (sym (JT-ren vs)) okI))
    where
      open RowTyping dj dc
      p1 = r1 1 0 (rec 0 2 ∷ʰ rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) dp
      p2 = r1 0 2 (rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) p1
      p3 = r1 1 0 (rec 1 0 ∷ʰ []ʰ) p2
      dD = f0 1 0 (rec 0 2 ∷ʰ rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) dp
      dM = f0 0 2 (rec 1 0 ∷ʰ rec 1 0 ∷ʰ []ʰ) p1
      dC = f0 1 0 (rec 1 0 ∷ʰ []ʰ) p2
      dq = f0 1 0 []ʰ p3
      Ξ₁ : Ctx
      Ξ₁ = Ξ ▹ El (⌜Tm⌝ j)
      j₁ = renTm vs j
      T₁ = TDIhI j₁ (renTm vs (fst c)) (var vz) (renTm vs (fst p)) (renTm vs (fst (snd p)))
                 (renTm vs (fst (snd (snd p)))) (renTm vs (fst (snd (snd (snd p)))))
      dj₁ : Ξ₁ ⊢ j₁ ∷ El ⌜Nat⌝
      dj₁ = ⊢wk {Ξ} {El (⌜Tm⌝ j)} {j} {El ⌜Nat⌝} dj
      dg₁ = ⊢wkCtx {Ξ} {El (⌜Tm⌝ j)} {j} {fst c} dg
      wkK : {s : ℕ} {d t : RTm ⌊ Ξ ⌋} → Ξ ⊢ t ∷ K s d → Ξ₁ ⊢ renTm vs t ∷ K s (renTm vs d)
      wkK {s} {d} {t} dt = ⊢wkSK {Γ = Ξ} {B = El (⌜Tm⌝ j)} {sg = KSig} {s = s} {d = d} {t = t} dt
      dv : Ξ₁ ⊢ var vz ∷ K 1 j₁
      dv = ⊢conv (⊢-cast {Ξ₁} {var vz} {renTy vs (El (⌜Tm⌝ j))} {El (⌜Tm⌝ j₁)} (cong El (⌜Tm⌝-ren vs j)) (⊢var here))
                 (credᵀ El-⌜Tm⌝)
      dD₁ = wkK dD
      dmc : Ξ₁ ⊢ mc j₁ (renTm vs (fst c)) (var vz) (renTm vs (fst p)) ∷ KCtx (nsuc (nsuc j₁))
      dmc = ⊢cext (⊢isuc dj₁) (⊢cext dj₁ dg₁ (⊢kEl dj₁ dv))
                  (⊢kIMu (⊢isuc dj₁) (⊢wkS (lt-s lt-z) dj₁ dv) (⊢wkS (lt-s lt-z) dj₁ dD₁) (⊢kvar (⊢isuc dj₁) (⊢ffz dj₁)))
      okI : TelOK Ξ₁ JT T₁
      okI = ok-ρ (⊢tmIx dj₁ dg₁ dv (⊢kU dj₁))
              (ok-ρ (⊢tmIx dj₁ dg₁ dD₁ (⊢DF dj₁ dv))
                (ok-ρ (⊢tyIx (⊢isuc (⊢isuc dj₁)) dmc (wkK dM))
                  (ok-ρ (⊢tmIx dj₁ dg₁ (wkK dC) (⊢kDesc dj₁ dv))
                    (ok-ρ (⊢tmIx dj₁ dg₁ (wkK dq) (⊢kEl dj₁ (⊢kdpay dj₁ dv dD₁ (wkK dC)))) ok-ι))))

  okNone : {s : ℕ} {sh : Shape} → RowOK s sh rNone
  okNone dj dp dc = ⊢rows {I = JT} {Cs = []} ⊢JT []ᵈ


open TyOK public

-- the Π/Σ row's telescope, typed (what a constructor needs)
okPiT : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Ξ ⊢ p ∷ PayV sh-kPi (pair (tag 0) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CTat (pair (tag 0) j)) → TelOK Ξ JT (TPi j p c)
okPiT dj dp dc = ok-ρ (⊢tyIx dj dg dA) (ok-ρ (⊢tyIx (⊢isuc dj) (⊢cext dj dg dA) dB) ok-ι)
  where dg = ⊢ctxOf dc
        dA = f0 0 0 (rec 0 1 ∷ʰ []ʰ) dp
        dB = f0 0 1 []ʰ (r1 0 0 (rec 0 1 ∷ʰ []ʰ) dp)

