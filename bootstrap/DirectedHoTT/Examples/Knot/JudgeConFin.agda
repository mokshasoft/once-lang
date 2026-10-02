-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the constructors of the two HAND-WRITTEN `⊢` rows,
-- fzero and fsuc (`JudgeRowsTm`: a case on the type at `Fin N`, then a
-- `Desc`-valued `natrec` on the numeral).  Every other row's constructor
-- is generated (`JudgeConGen`); these add one `natrec-suc` step.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeConFin where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ; ⟶*-trans; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-natrecⁿ; ⟶*-dρʲ )
open import DirectedHoTT.Metatheory.TySub using ( wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; conₗ; lt-z; lt-s; nth-z; nth-s )
open import DirectedHoTT.Lib.SynFib using ( ⊢conRowₖ )
open import DirectedHoTT.Lib.SynRed using ( prj-tup )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( rows )
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w2 )
open import DirectedHoTT.Examples.Knot.JudgeConv using ( TCVat )
open import DirectedHoTT.Examples.Knot.JudgeRowsTm using ( module PFz; module PFs; TFs )
open import DirectedHoTT.Examples.Knot.JudgeRowsGen using ( allr⊢fzero; allr⊢fsuc )
open import DirectedHoTT.Examples.Knot.Judge using ( D⊢; ⊢D⊢; fibK )
open import DirectedHoTT.Examples.Knot.JudgeIx using ( ⊢payK )

private
  nh12 : NthSh TyShs 12 sh-kFin
  nh12 = atʰ 12

-- ★ `⊢fzero : Γ ⊢ fzero ∷ Fin (suc n)`
con⊢fzero : {Ξ : Ctx} {j g n : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ n ∷ El ⌜Nat⌝ →
            Ξ ⊢ conₗ 0 unit ∷ IMu JT D⊢ (tmIx j g kfzero (kFin (nsuc n)))
con⊢fzero {Ξ} {j} {g} {n} dj dg dn =
  ⊢conRowₖ {Ξ} {2} {0} {JT} {D⊢} {tmIx j g kfzero X} {PFz.CX j p c} {unit} {PFz.CX j p c ∷ ⌜ TCVat 29 j p c ⌝ᵗ ∷ []}
           nth-z ⊢JT ⊢D⊢ (⊢tmIx dj dg (⊢kfzero dj) dX)
    (fibK {s = 1} {k = 29} {j = j} {p = p} {c = c} (atᵍ 1) nh29) (allr⊢fzero dj dp dc)
    (⊢conv (⊢payι ⊢JT ⊢D⊢ ⊢unit) (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R)))))
  where
    nh29 : NthSh TmShs 29 sh-kfzero
    nh29 = atʰ 29
    X p c q c' : RTm ⌊ Ξ ⌋
    X = kFin (nsuc n)
    p = unit
    c = pair g X
    q = pair (nsuc n) unit
    c' = pair g p
    dX = ⊢kFin dj (⊢isuc dn)
    dp = ⊢payK (lt-s lt-z) ok-kfzero dj a[]
    dc = ⊢cTm dj dg dX
    R : PFz.CX j p c ⟶* dι
    R = ⟶*-trans {t = PFz.CX j p c} {u = PFz.CASE j X (pair (fst c) p)} {v = dι} (PFz.CASE-⟶ᵃ (step (βsnd g X) done))
          (⟶*-trans {t = PFz.CASE j X (pair (fst c) p)} {u = PFz.CASE j X c'} {v = dι} (PFz.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g X) done)))
          (⟶*-trans {t = PFz.CASE j X c'} {u = natrec (rows []) dι (fst q)} {v = dι} (PFz.case-β {j = j} {q = q} {c = c'} (atᵍ 0) nh12)
          (⟶*-trans {t = natrec (rows []) dι (fst q)} {u = natrec (rows []) dι (nsuc n)} {v = dι}
                    (⟶*-natrecⁿ (step (βfst (nsuc n) unit) done)) (step (natrec-suc (rows []) dι n) done))))

-- ★ `⊢fsuc : Γ ⊢ t ∷ Fin n → Γ ⊢ fsuc t ∷ Fin (suc n)`
private
  e1-cong : {Γ : Cx} (J J' G G' T T' A A' : RTm Γ) → J ≡ J' → G ≡ G' → T ≡ T' → A ≡ A' →
            dρ (tmIx J G T (kFin A)) dι ≡ dρ (tmIx J' G' T' (kFin A')) dι
  e1-cong J J' G G' T T' A A' refl refl refl refl = refl

  -- natrec's two binders, cancelled by its successor step's substitution
  w2c : {Γ : Cx} (N m x : RTm Γ) → subTm (single N) (subTm (extS (single m)) (w2 x)) ≡ x
  w2c N m x = trans (cong (subTm (single N)) (trans (wkS (single m) (w1 x)) (cong w1 (wk-cancel-tm m x)))) (wk-cancel-tm N x)

con⊢fsuc : {Ξ : Ctx} {j g n t r : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ n ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ K 1 j →
           Ξ ⊢ r ∷ IMu JT D⊢ (tmIx j g t (kFin n)) →
           Ξ ⊢ conₗ 0 (pair r unit) ∷ IMu JT D⊢ (tmIx j g (kfsuc t) (kFin (nsuc n)))
con⊢fsuc {Ξ} {j} {g} {n} {t} {r} dj dg dn dt dr =
  ⊢conRowₖ {Ξ} {2} {0} {JT} {D⊢} {tmIx j g (kfsuc t) X} {PFs.CX j p c} {pair r unit} {PFs.CX j p c ∷ ⌜ TCVat 30 j p c ⌝ᵗ ∷ []}
           nth-z ⊢JT ⊢D⊢ (⊢tmIx dj dg (⊢kfsuc dj dt) dX)
    (fibK {s = 1} {k = 30} {j = j} {p = p} {c = c} (atᵍ 1) nh30) (allr⊢fsuc dj dp dc)
    (⊢conv (⊢payρ ⊢JT ⊢D⊢ {r = r} {p = unit} (ok-ρ (⊢tmIx dj dg dt (⊢kFin dj dn)) ok-ι) dr (⊢payι ⊢JT ⊢D⊢ ⊢unit))
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R)))))
  where
    nh30 : NthSh TmShs 30 sh-kfsuc
    nh30 = atʰ 30
    X p c q c' N : RTm ⌊ Ξ ⌋
    X = kFin (nsuc n)
    p = pair t unit
    c = pair g X
    q = pair (nsuc n) unit
    c' = pair g p
    N = natrec (rows []) (TFs j c') n
    dX = ⊢kFin dj (⊢isuc dn)
    dp = ⊢payK (lt-s lt-z) ok-kfsuc dj (a-rec dt a[])
    dc = ⊢cTm dj dg dX
    Y : RTm ⌊ Ξ ⌋
    Y = dρ (tmIx j (fst c') (fst (snd c')) (kFin n)) dι
    eY : subTm (single N) (subTm (extS (single n)) (TFs j c')) ≡ Y
    eY = e1-cong _ _ _ _ _ _ _ _ (w2c N n j) (w2c N n (fst c')) (w2c N n (fst (snd c'))) (wk-cancel-tm N n)
    rix : Y ⟶* dρ (tmIx j g t (kFin n)) dι
    rix = ⟶*-dρʲ (⟶*-pairʳ (⟶*-trans {t = pair (fst (snd c')) (pair (fst c') (kFin n))} {u = pair t (pair (fst c') (kFin n))}
                                       {v = pair t (pair g (kFin n))}
                    (⟶*-pairˡ (prj-tup {ws = g ∷ t ∷ []} unit (nth-s nth-z)))
                    (⟶*-pairʳ (⟶*-pairˡ (prj-tup {ws = g ∷ t ∷ []} unit nth-z)))))
    tgt = dρ (tmIx j g t (kFin n)) dι
    R : PFs.CX j p c ⟶* tgt
    R = ⟶*-trans {t = PFs.CX j p c} {u = PFs.CASE j X (pair (fst c) p)} {v = tgt} (PFs.CASE-⟶ᵃ (step (βsnd g X) done))
          (⟶*-trans {t = PFs.CASE j X (pair (fst c) p)} {u = PFs.CASE j X c'} {v = tgt} (PFs.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g X) done)))
          (⟶*-trans {t = PFs.CASE j X c'} {u = natrec (rows []) (TFs j c') (fst q)} {v = tgt} (PFs.case-β {j = j} {q = q} {c = c'} (atᵍ 0) nh12)
          (⟶*-trans {t = natrec (rows []) (TFs j c') (fst q)} {u = natrec (rows []) (TFs j c') (nsuc n)} {v = tgt}
                    (⟶*-natrecⁿ (step (βfst (nsuc n) unit) done))
                    (step (natrec-suc (rows []) (TFs j c') n) (subst (λ Z → Z ⟶* tgt) (sym eY) rix)))))
