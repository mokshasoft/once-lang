-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the hand-written typing rows, decoded
-- (PLAN-FAITHFUL F6): `⊢ref` (`Knot/RefJudge`), `⊢fzero`/`⊢fsuc`
-- (`Knot/JudgeConFin`).  Same discipline as the generated rows
-- (`JudgeDecodeTm`): each row along its own constructor's reduction.
--
--   ⊢ref    the definition's type unquoted, its typing decoded at `◇`,
--           the Ford closed against `εwk-agree-ty`;
--   ⊢fzero  the case on the type reads `Fin m`; at `m = 0` the row's
--   ⊢fsuc   `natrec` leaves NO rule (absurd), at `suc m` the rule.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeDecodeHand where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ; ⟶*-trans; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-natrecⁿ; ⟶*-dρʲ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal )
open import DirectedHoTT.Metatheory.Canonicity using ( sz )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; atᶜ; v₀; _,ₚ_; nth-z; nth-s )
open import DirectedHoTT.Lib.SynRed using ( prj-tup )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Decode
open import DirectedHoTT.Lib.PatDecode
open import DirectedHoTT.Lib.Size using ( _<_; <ˡ; <ʳ )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Ctx using ( quoteCtx; cε; El-⌜Ty⌝ )
open import DirectedHoTT.Examples.Knot.Unquote
open import DirectedHoTT.Examples.Knot.Lookup using ( rows )
open import DirectedHoTT.Examples.Knot.JudgeIx using ( JT; tmIx )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w2 )
open import DirectedHoTT.Examples.Knot.Judge using ( D⊢ )
open import DirectedHoTT.Examples.Knot.JudgeRowsTm using ( module PFz; module PFs; TFs )
open import DirectedHoTT.Examples.Knot.RefJudge using ( T⊢ref; T⊢ref⁽1⁾; T⊢ref⁽1⁾-sub )
open import DirectedHoTT.Examples.Knot.Ref using ( bodyOf )
open import DirectedHoTT.Examples.Knot.Ren using ( εwkK )
open import DirectedHoTT.Examples.Knot.OpAgree using ( εwk-agree-ty )
open import DirectedHoTT.Examples.Knot.JudgeDecodeBase

------------------------------------------------------------------------
-- ⊢ref : ◇ ⊢ b ∷ A₀ → Γ ⊢ ref d b ∷ εwkTy A₀
------------------------------------------------------------------------

private
  cong₃' : {A B C D : Set} (f : A → B → C → D) {a a' : A} {b b' : B} {x x' : C} →
           a ≡ a' → b ≡ b' → x ≡ x' → f a b x ≡ f a' b' x'
  cong₃' f refl refl refl = refl

jdref : {N : ℕ} → IHTy N → IHTm N → (Γ : Ctx) (d : ℕ) (b : RTm ε) (A : RTy ⌊ Γ ⌋) {w : RTm ε} → sz w < N →
        ◇ ⊢ w ∷ El (dpay JT D⊢ ⌜ T⊢ref (dep ⌊ Γ ⌋) (pair (quoteℕ d) (pair (quoteTm b) unit)) (pair (quoteCtx Γ) (quoteTy A)) ⌝ᵗ) →
        IsNormal w → Γ ⊢ ref d b ∷ A
jdref ihTy ihTm Γ d b A {w} hq dq nq =
  pay-σ dq done nq
  ▷ λ { (a , (b₁ , (eq₀ , ((da , db₁) , (na , nb₁))))) →
  unqTy {Γ = ε} (⊢conv da (credᵀ El-⌜Ty⌝)) na
  ▷ λ { (A₀ , eqA) →
  pay-ρ (⊢-cast (cong (λ Z → El (dpay JT D⊢ Z)) (EQ a)) (⊢conv db₁ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ a) done)))))) done nb₁
  ▷ λ { (r , (b₂ , (eq₁ , ((dr , db₂) , (nr , nb₂))))) →
  pay-σ db₂ done nb₂
  ▷ λ { (_ , (_ , (_ , ((dF , _) , (nF , _))))) →
  ihTm ◇ b A₀ (<ˡ eq₁ (<ʳ eq₀ hq))
       (subst (λ z → ◇ ⊢ r ∷ IMu JT D⊢ (tmIx nzero cε (quoteTm b) z)) eqA
         (⊢conv dr (tmIx≅ done (prj-tup {ws = quoteℕ d ∷ quoteTm b ∷ []} unit (atᶜ 1)) done))) nr
  ▷ λ D →
  quoteTy-inj A (εwkTy A₀)
    (nf-≅ (quoteTy-normal {Γ = ⌊ Γ ⌋} A) (quoteTy-normal {Γ = ⌊ Γ ⌋} (εwkTy A₀))
      (ctrn (csym (cred (βsnd g X)))
        (ctrn (subst (λ z → snd c ≅ εwkK 0 j z) eqA (idrefl-decᶜ dF nF)) (⟶*→≅ (εwk-agree-ty ⌊ Γ ⌋ A₀)))))
  ▷ λ eqT → subst (λ z → Γ ⊢ ref d b ∷ z) (sym eqT) (⊢ref D) } } } }
  where
    j g X p c : RTm ε
    j = dep ⌊ Γ ⌋
    g = quoteCtx Γ
    X = quoteTy A
    p = pair (quoteℕ d) (pair (quoteTm b) unit)
    c = pair g X
    EQ : (a : RTm ε) → subTm (single a) ⌜ T⊢ref⁽1⁾ (w1 j) (w1 (bodyOf p)) (w1 (snd c)) v₀ ⌝ᵗ ≡ ⌜ T⊢ref⁽1⁾ j (bodyOf p) (snd c) a ⌝ᵗ
    EQ a = trans (T⊢ref⁽1⁾-sub (single a) (w1 j) (w1 (bodyOf p)) (w1 (snd c)) v₀)
                 (cong₃' (λ J B C → ⌜ T⊢ref⁽1⁾ J B C a ⌝ᵗ) (wk-cancel-tm a j) (wk-cancel-tm a (bodyOf p)) (wk-cancel-tm a (snd c)))

------------------------------------------------------------------------
-- ⊢fzero / ⊢fsuc: a case on the type (it is `Fin m`), then `m`.
------------------------------------------------------------------------

private
  e1-cong : {Γ : Cx} (J J' G G' T T' A A' : RTm Γ) → J ≡ J' → G ≡ G' → T ≡ T' → A ≡ A' →
            dρ (tmIx J G T (kFin A)) dι ≡ dρ (tmIx J' G' T' (kFin A')) dι
  e1-cong J J' G G' T T' A A' refl refl refl refl = refl

  w2c : {Γ : Cx} (N m x : RTm Γ) → subTm (single N) (subTm (extS (single m)) (w2 x)) ≡ x
  w2c N m x = trans (cong (subTm (single N)) (trans (wkS (single m) (w1 x)) (cong w1 (wk-cancel-tm m x)))) (wk-cancel-tm N x)

  -- the row at `Fin m`
  fzᴸ : (Γ : Ctx) (m : ℕ) {w : RTm ε} →
        ◇ ⊢ w ∷ El (dpay JT D⊢ (PFz.CX (dep ⌊ Γ ⌋) unit (pair (quoteCtx Γ) (quoteTy (RTy.Fin {⌊ Γ ⌋} m))))) → IsNormal w →
        Γ ⊢ fzero ∷ RTy.Fin m
  fzᴸ Γ zero {w} dq nq = ⊥-elim (pay-none dq R nq)
    where
      j g X c q c' : RTm ε
      j = dep ⌊ Γ ⌋
      g = quoteCtx Γ
      X = kFin nzero
      c = pair g X
      q = pair nzero unit
      c' = pair g unit
      R : PFz.CX j unit c ⟶* rows []
      R = ⟶*-trans {t = PFz.CX j unit c} {u = PFz.CASE j X ((fst c) ,ₚ unit)} {v = rows []} (PFz.CASE-⟶ᵃ (step (βsnd g X) done))
            (⟶*-trans {t = PFz.CASE j X ((fst c) ,ₚ unit)} {u = PFz.CASE j X c'} {v = rows []} (PFz.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g X) done)))
            (⟶*-trans {t = PFz.CASE j X c'} {u = natrec (rows []) dι (fst q)} {v = rows []} (PFz.case-β {j = j} {q = q} {c = c'} (atᵍ 0) (atʰ 12))
            (⟶*-trans {t = natrec (rows []) dι (fst q)} {u = natrec (rows []) dι nzero} {v = rows []}
                      (⟶*-natrecⁿ (step (βfst nzero unit) done)) (step (natrec-zero (rows []) dι) done))))
  fzᴸ Γ (suc m) dq nq = ⊢fzero

  fsᴸ : {N : ℕ} → IHTm N → (Γ : Ctx) (a0 : RTm ⌊ Γ ⌋) (m : ℕ) {w : RTm ε} → sz w < N →
        ◇ ⊢ w ∷ El (dpay JT D⊢ (PFs.CX (dep ⌊ Γ ⌋) (pair (quoteTm a0) unit) (pair (quoteCtx Γ) (quoteTy (RTy.Fin {⌊ Γ ⌋} m))))) → IsNormal w →
        Γ ⊢ fsuc a0 ∷ RTy.Fin m
  fsᴸ ih Γ a0 zero {w} hq dq nq = ⊥-elim (pay-none dq R nq)
    where
      j g X p c q c' : RTm ε
      j = dep ⌊ Γ ⌋
      g = quoteCtx Γ
      X = kFin nzero
      p = pair (quoteTm a0) unit
      c = pair g X
      q = pair nzero unit
      c' = pair g p
      R : PFs.CX j p c ⟶* rows []
      R = ⟶*-trans {t = PFs.CX j p c} {u = PFs.CASE j X ((fst c) ,ₚ p)} {v = rows []} (PFs.CASE-⟶ᵃ (step (βsnd g X) done))
            (⟶*-trans {t = PFs.CASE j X ((fst c) ,ₚ p)} {u = PFs.CASE j X c'} {v = rows []} (PFs.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g X) done)))
            (⟶*-trans {t = PFs.CASE j X c'} {u = natrec (rows []) (TFs j c') (fst q)} {v = rows []} (PFs.case-β {j = j} {q = q} {c = c'} (atᵍ 0) (atʰ 12))
            (⟶*-trans {t = natrec (rows []) (TFs j c') (fst q)} {u = natrec (rows []) (TFs j c') nzero} {v = rows []}
                      (⟶*-natrecⁿ (step (βfst nzero unit) done)) (step (natrec-zero (rows []) (TFs j c')) done))))
  fsᴸ ih Γ a0 (suc m) {w} hq dq nq =
    pay-ρ (⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R)))) done nq
    ▷ λ { (r , (b , (eq , ((dr , _) , (nr , _))))) → ⊢fsuc (ih Γ a0 (RTy.Fin m) (<ˡ eq hq) dr nr) }
    where
      j g X p c q c' n N : RTm ε
      j = dep ⌊ Γ ⌋
      g = quoteCtx Γ
      n = quoteℕ m
      X = kFin (nsuc n)
      p = pair (quoteTm a0) unit
      c = pair g X
      q = pair (nsuc n) unit
      c' = pair g p
      N = natrec (rows []) (TFs j c') n
      t = quoteTm a0
      Y : RTm ε
      Y = dρ (tmIx j (fst c') (fst (snd c')) (kFin n)) dι
      eY : subTm (single N) (subTm (extS (single n)) (TFs j c')) ≡ Y
      eY = e1-cong _ _ _ _ _ _ _ _ (w2c N n j) (w2c N n (fst c')) (w2c N n (fst (snd c'))) (wk-cancel-tm N n)
      tgt = dρ (tmIx j g t (kFin n)) dι
      rix : Y ⟶* tgt
      rix = ⟶*-dρʲ (⟶*-pairʳ (⟶*-trans {t = pair (fst (snd c')) ((fst c') ,ₚ (kFin n))} {u = pair t ((fst c') ,ₚ (kFin n))}
                                         {v = pair t (g ,ₚ (kFin n))}
                      (⟶*-pairˡ (prj-tup {ws = g ∷ t ∷ []} unit (nth-s nth-z)))
                      (⟶*-pairʳ (⟶*-pairˡ (prj-tup {ws = g ∷ t ∷ []} unit nth-z)))))
      R : PFs.CX j p c ⟶* tgt
      R = ⟶*-trans {t = PFs.CX j p c} {u = PFs.CASE j X ((fst c) ,ₚ p)} {v = tgt} (PFs.CASE-⟶ᵃ (step (βsnd g X) done))
            (⟶*-trans {t = PFs.CASE j X ((fst c) ,ₚ p)} {u = PFs.CASE j X c'} {v = tgt} (PFs.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g X) done)))
            (⟶*-trans {t = PFs.CASE j X c'} {u = natrec (rows []) (TFs j c') (fst q)} {v = tgt} (PFs.case-β {j = j} {q = q} {c = c'} (atᵍ 0) (atʰ 12))
            (⟶*-trans {t = natrec (rows []) (TFs j c') (fst q)} {u = natrec (rows []) (TFs j c') (nsuc n)} {v = tgt}
                      (⟶*-natrecⁿ (step (βfst (nsuc n) unit) done))
                      (step (natrec-suc (rows []) (TFs j c') n) (subst (λ Z → Z ⟶* tgt) (sym eY) rix)))))

-- the case on the type: it is `Fin m`
jdfzero : {N : ℕ} → IHTy N → IHTm N → (Γ : Ctx) (A : RTy ⌊ Γ ⌋) {w : RTm ε} → sz w < N →
          ◇ ⊢ w ∷ El (dpay JT D⊢ (PFz.CX (dep ⌊ Γ ⌋) unit (pair (quoteCtx Γ) (quoteTy A)))) → IsNormal w →
          Γ ⊢ fzero ∷ A
jdfzero ihTy ihTm Γ A {w} hq dq nq =
  pat-hit 0 12 (hdTy A) dq₃ nq
  ▷ λ e → isFin A e
  ▷ λ { (m , eqv) → subst (λ z → Γ ⊢ fzero ∷ z) (sym eqv)
          (fzᴸ Γ m (subst (λ z → ◇ ⊢ w ∷ El (dpay JT D⊢ (PFz.CX (dep ⌊ Γ ⌋) unit (pair (quoteCtx Γ) (quoteTy z))))) eqv dq) nq) }
  where
    j g X0 p c c' : RTm ε
    j = dep ⌊ Γ ⌋
    g = quoteCtx Γ
    X0 = quoteTy A
    p = unit
    c = pair g X0
    c' = pair g p
    dq₁ = ⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (⟶*-trans {t = PFz.CX j p c} {u = PFz.CASE j X0 ((fst c) ,ₚ p)} {v = PFz.CASE j X0 c'}
            (PFz.CASE-⟶ᵃ (step (βsnd g X0) done)) (PFz.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g X0) done)))))))
    dq₂ = subst (λ z → ◇ ⊢ w ∷ El (dpay JT D⊢ (PFz.CASE j z c'))) (quote-hdTy A) dq₁
    dq₃ = ⊢conv dq₂ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (PFz.case-any {j = j} {q = pfTy A} {c = c'} (atᵍ 0) (nhTy A)))))

jdfsuc : {N : ℕ} → IHTy N → IHTm N → (Γ : Ctx) (a0 : RTm ⌊ Γ ⌋) (A : RTy ⌊ Γ ⌋) {w : RTm ε} → sz w < N →
         ◇ ⊢ w ∷ El (dpay JT D⊢ (PFs.CX (dep ⌊ Γ ⌋) (pair (quoteTm a0) unit) (pair (quoteCtx Γ) (quoteTy A)))) → IsNormal w →
         Γ ⊢ fsuc a0 ∷ A
jdfsuc ihTy ihTm Γ a0 A {w} hq dq nq =
  pat-hit 0 12 (hdTy A) dq₃ nq
  ▷ λ e → isFin A e
  ▷ λ { (m , eqv) → subst (λ z → Γ ⊢ fsuc a0 ∷ z) (sym eqv)
          (fsᴸ ihTm Γ a0 m hq (subst (λ z → ◇ ⊢ w ∷ El (dpay JT D⊢ (PFs.CX (dep ⌊ Γ ⌋) (pair (quoteTm a0) unit) (pair (quoteCtx Γ) (quoteTy z))))) eqv dq) nq) }
  where
    j g X0 p c c' : RTm ε
    j = dep ⌊ Γ ⌋
    g = quoteCtx Γ
    X0 = quoteTy A
    p = pair (quoteTm a0) unit
    c = pair g X0
    c' = pair g p
    dq₁ = ⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (⟶*-trans {t = PFs.CX j p c} {u = PFs.CASE j X0 ((fst c) ,ₚ p)} {v = PFs.CASE j X0 c'}
            (PFs.CASE-⟶ᵃ (step (βsnd g X0) done)) (PFs.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g X0) done)))))))
    dq₂ = subst (λ z → ◇ ⊢ w ∷ El (dpay JT D⊢ (PFs.CASE j z c'))) (quote-hdTy A) dq₁
    dq₃ = ⊢conv dq₂ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (PFs.case-any {j = j} {q = pfTy A} {c = c'} (atᵍ 0) (nhTy A)))))
