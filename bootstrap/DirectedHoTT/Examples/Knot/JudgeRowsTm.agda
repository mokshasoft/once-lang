-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the hand-written `⊢` pieces the generated rows (`JudgeRowsGen`) use: the fzero/fsuc rows (a case on `Fin N`, then a Desc-valued natrec), the payload-field views.
--
-- A rule whose conclusion TYPE is a constructor pattern is a NESTED CASE
-- on the convoy's type (`Lib/SynPat`): the pattern's variables are the
-- type's payload, the case's convoy is `(Γ , term payload)`
-- (`JudgeTmIx`).  A computed conclusion type Fords (`⌜Id⌝` field).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeRowsTm where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; Lt; lt-z; lt-s; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢recFst; ⊢recSnd; ⊢atDepthSK; ⊢natFst )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row )
open import DirectedHoTT.Examples.Knot.JudgeCase
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( rows; ⊢rows )
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeTmIx
open import DirectedHoTT.Examples.Knot.JudgeFib using ( RowOK; f0; r1 )
open import DirectedHoTT.Examples.Knot.Lookup using ( toTy; hereTy; I∋; ⊢I∋; I∋-sub; ix∋; ⊢ix∋; D∋; ⊢D∋ )
open import DirectedHoTT.Examples.Knot.LookupCon using ( D∋-sub )
open import DirectedHoTT.Lib.FinFam using ( FinI; FinD; toI; fromI )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-⌜IMu⌝ⁱ )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0; ⊢sub0; sub0-sub )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )

private
  variable
    Δ Θ : Cx

-- a TERM payload's field (index `(1 , j)`), its depth read off
g0 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
     Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) (pair (tag 1) j) (SI 2) (SD KSig) → Ξ ⊢ fst p ∷ K s (nsucs k j)
g0 {j = j} s k sh dp = ⊢atDepthSK {sg = KSig} {a = tag 1} {j = j} {s = s} {k = k} (⊢recFst {s = s} {k = k} {sh = sh} dp)

-- a variable payload's field, at the depth
⊢varOf : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} → Ξ ⊢ p ∷ PayV sh-kvar (pair (tag 1) j) (SI 2) (SD KSig) → Ξ ⊢ fst p ∷ FinI j
⊢varOf {j = j} dp = ⊢conv (⊢fst dp) (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-⌜IMu⌝ⁱ (step (βsnd (tag 1) j) done)))) (credᵀ El-⌜IMu⌝))

------------------------------------------------------------------------
-- ⊢fzero : Γ ⊢ fzero ∷ Fin (suc n)      ⊢fsuc : Γ ⊢ t ∷ Fin n → Γ ⊢ fsuc t ∷ Fin (suc n)
--   the conclusion is a pattern with a fresh variable, one level deep: case
--   on the type at `Fin N`, then on the numeral `N` — a `Desc`-valued
--   `natrec`: no row at `0`, the rule at `suc n` (`n` bound by the case)
------------------------------------------------------------------------

⊢natD : {Ξ : Ctx} {z N : RTm ⌊ Ξ ⌋} {s : RTm ((⌊ Ξ ⌋ ∙) ∙)} → Ξ ⊢ z ∷ Desc JT →
        ((Ξ ▹ Nat) ▹ Desc JT) ⊢ s ∷ Desc JT → Ξ ⊢ N ∷ El ⌜Nat⌝ → Ξ ⊢ natrec z s N ∷ Desc JT
⊢natD {Ξ} {z} {N} {s} dz ds dN =
  ⊢-cast {Ξ} {natrec z s N} {subTy (single N) (Desc JT)} {Desc JT} (cong Desc (JT-sub (single N)))
    (⊢natrec {Ξ} {Desc JT} {z} {s} {N} (ty-Desc ⊢JT)
             (⊢-cast {Ξ} {z} {Desc JT} {subTy (single nzero) (Desc JT)} (cong Desc (sym (JT-sub (single nzero)))) dz)
             (⊢-cast {(Ξ ▹ Nat) ▹ Desc JT} {s} {Desc JT} {subTy nrs (Desc JT)} (cong Desc (sym (JT-sub nrs))) ds)
             (fromI dN))

-- fzero: no premises
rFzI : Row
rFzI = record { R = λ j q c → natrec (rows []) dι (fst q) ; R-sub = λ σ j q c → refl }

module PFz = CaseRow sh-kfzero ok-kfzero 12 rFzI

okFzI : PFz.RowOK 0 sh-kFin rFzI
okFzI {Ξ} {j} {q} {c} dj dq dc =
  ⊢natD {Ξ} {rows []} {fst q} {dι} (⊢rows {Ξ} {JT} {0} {[]} ⊢JT []ᵈ) (⊢dι ⊢JT) (⊢natFst {Ξ} {pair (tag 0) j} {SI 2} {SD KSig} {q} {sh = []ʰ} dq)

rFz : Row
rFz = PFz.rX

okFz : RowOK 1 sh-kfzero rFz
okFz = PFz.okX okFzI

-- fsuc t: `t ∷ Fin n`, `n` the case's predecessor (`var 1` under natrec's two binders)
TFs : RTm Δ → RTm Δ → RTm ((Δ ∙) ∙)
TFs j c = ⌜ tρ (tmIx (w2 j) (w2 (fst c)) (w2 (fst (snd c))) (kFin (var (vs vz)))) tι ⌝ᵗ

TFs-cong : {Γ : Cx} (J J' G G' T T' : RTm ((Γ ∙) ∙)) → J ≡ J' → G ≡ G' → T ≡ T' →
           dρ (tmIx J G T (kFin (var (vs vz)))) dι ≡ dρ (tmIx J' G' T' (kFin (var (vs vz)))) dι
TFs-cong J J' G G' T T' refl refl refl = refl

rFsI : Row
rFsI = record
  { R = λ j q c → natrec (rows []) (TFs j c) (fst q)
  ; R-sub = λ σ j q c →
      cong (λ S → natrec (rows []) S (fst (subTm σ q)))
           (TFs-cong _ _ _ _ _ _ (w2-sub σ j) (w2-sub σ (fst c)) (w2-sub σ (fst (snd c)))) }

module PFs = CaseRow sh-kfsuc ok-kfsuc 12 rFsI

okFsI : PFs.RowOK 0 sh-kFin rFsI
okFsI {Ξ} {j} {q} {c} dj dq dc = ⊢natD {Ξ} {rows []} {fst q} {TFs j c} (⊢rows {Ξ} {JT} {0} {[]} ⊢JT []ᵈ) dS (⊢natFst {Ξ} {pair (tag 0) j} {SI 2} {SD KSig} {q} {sh = []ʰ} dq)
  where
    dt : Ξ ⊢ fst (snd c) ∷ K 1 j
    dt = g0 1 0 []ʰ (⊢pI sh-kfsuc dc)
    dS : ((Ξ ▹ Nat) ▹ Desc JT) ⊢ TFs j c ∷ Desc JT
    dS = ⊢tel ⊢JT
           (ok-ρ (⊢tmIx dj₂ (⊢wkCtx {Ξ ▹ Nat} {Desc JT} {w1 j} {w1 (fst c)} (⊢wkCtx {Ξ} {Nat} {j} {fst c} (⊢gI sh-kfsuc dc)))
                     (⊢wkSK {Γ = Ξ ▹ Nat} {B = Desc JT} {sg = KSig} {s = 1} {d = w1 j} {t = w1 (fst (snd c))}
                            (⊢wkSK {Γ = Ξ} {B = Nat} {sg = KSig} {s = 1} {d = j} {t = fst (snd c)} dt))
                     (⊢kFin dj₂ (toI (⊢var (there here)))))
                 ok-ι)
      where
        dj₂ : ((Ξ ▹ Nat) ▹ Desc JT) ⊢ w2 j ∷ El ⌜Nat⌝
        dj₂ = ⊢wk {Ξ ▹ Nat} {Desc JT} {w1 j} {El ⌜Nat⌝} (⊢wk {Ξ} {Nat} {j} {El ⌜Nat⌝} dj)

rFs : Row
rFs = PFs.rX

okFs : RowOK 1 sh-kfsuc rFs
okFs = PFs.okX okFsI
