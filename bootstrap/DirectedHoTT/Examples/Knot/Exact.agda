-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★ THE KNOT IS EXACT (PLAN-FAITHFUL F6, closing F6.6).
--
-- F5 (`*Agree`): every Spec derivation has a Knot inhabitant at the
-- quoted judgement.  F6: every CLOSED Knot inhabitant at a quoted
-- judgement IS a Spec derivation — normal or not: the kernel normalises
-- it (`wnorm`), subject reduction keeps its type (`sr*`), and the normal
-- decoders (`*Decode`) read the normal form back.  Together: the Knot's
-- families say exactly what the Agda kernel's judgements say — no more
-- (F6), no less (F5).
--
--   exactTy/exactTm      Γ ⊢ty A,  Γ ⊢ t ∷ A        (JudgeDecode)
--   exactRed/exactRedT   t ⟶ u,    A ⟶ᵀ B           (RedDecode, RedTDecode)
--   exactConv/exactConvT t ≅ u,    A ≅ᵀ B           (ConvDecode)
--   exactLk              Γ ∋ x ∷ A                  (LookupDecode)
--   exactPw, exactNNC, exactStkA, exactStkC, exactFlat   the side conditions
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.Exact (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; Σ; _,_; _×_ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( NoNatC; pw?; pwBody; stkA?; stkC?; flat?; 𝔹; true )
open import DirectedHoTT.Metatheory.LogicalRelation 𝒮 using ( IsNormal; WN )
open import DirectedHoTT.Metatheory.Fundamental 𝒮 𝓃 ok refs using ( wnorm )
open import DirectedHoTT.Metatheory.SubjectReduction 𝒮 𝓃 ok using ( sr* )
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( quoteCtx )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; tyIx; tmIx )
open import DirectedHoTT.Examples.Knot.Judge 𝒮 wf using ( D⊢ )
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( K∋; ix∋ )
open import DirectedHoTT.Examples.Knot.Red 𝒮 wf using ( K⟶ )
open import DirectedHoTT.Examples.Knot.RedT 𝒮 wf using ( K⟶ᵀ )
open import DirectedHoTT.Examples.Knot.Conv 𝒮 wf using ( K≅; K≅ᵀ )
open import DirectedHoTT.Examples.Knot.Pw 𝒮 wf using ( KPw )
open import DirectedHoTT.Examples.Knot.Preds 𝒮 wf using ( KNNC; KStkA; KStkC; KFlat )
open import DirectedHoTT.Examples.Knot.JudgeDecode 𝒮 wf using ( decTy; decTm )
open import DirectedHoTT.Examples.Knot.RedDecode 𝒮 wf using ( decRed )
open import DirectedHoTT.Examples.Knot.RedTDecode 𝒮 wf using ( decRedT )
open import DirectedHoTT.Examples.Knot.ConvDecode 𝒮 wf using ( decConv; decConvT )
open import DirectedHoTT.Examples.Knot.LookupDecode 𝒮 wf using ( decLk )
open import DirectedHoTT.Examples.Knot.PwDecode 𝒮 wf using ( decPw )
open import DirectedHoTT.Examples.Knot.PredsDecode 𝒮 wf using ( decNNC; decStkA; decStkC; decFlat )

-- a closed typed term has a closed normal form at the same type
private
  nf : {T : RTy ε} {k : RTm ε} → ◇ ⊢ k ∷ T → Σ (RTm ε) (λ k' → (◇ ⊢ k' ∷ T) × IsNormal k')
  nf d = WN.nfm w , (sr* d (WN.rd w) , WN.nrm w)
    where w = wnorm c-◇ d

  -- …so a normal decoder decodes every inhabitant
  via : {T : RTy ε} {P : Set} → ((k' : RTm ε) → ◇ ⊢ k' ∷ T → IsNormal k' → P) → {k : RTm ε} → ◇ ⊢ k ∷ T → P
  via dec d with nf d
  ... | k' , (d' , n') = dec k' d' n'

exactTy : (Γ : Ctx) (A : RTy ⌊ Γ ⌋) {k : RTm ε} →
          ◇ ⊢ k ∷ IMu JT D⊢ (tyIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTy A)) → Γ ⊢ty A
exactTy Γ A = via (λ _ d n → decTy Γ A d n)

exactTm : (Γ : Ctx) (t : RTm ⌊ Γ ⌋) (A : RTy ⌊ Γ ⌋) {k : RTm ε} →
          ◇ ⊢ k ∷ IMu JT D⊢ (tmIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTm t) (quoteTy A)) → Γ ⊢ t ∷ A
exactTm Γ t A = via (λ _ d n → decTm Γ t A d n)

exactRed : {Γ : Cx} (t u : RTm Γ) {k : RTm ε} → ◇ ⊢ k ∷ K⟶ (dep Γ) (quoteTm t) (quoteTm u) → t ⟶ u
exactRed t u = via (λ _ d n → decRed t {u} d n)

exactRedT : {Γ : Cx} (A B : RTy Γ) {k : RTm ε} → ◇ ⊢ k ∷ K⟶ᵀ (dep Γ) (quoteTy A) (quoteTy B) → A ⟶ᵀ B
exactRedT A B = via (λ _ d n → decRedT A {B} d n)

exactConv : {Γ : Cx} (t u : RTm Γ) {k : RTm ε} → ◇ ⊢ k ∷ K≅ (dep Γ) (quoteTm t) (quoteTm u) → t ≅ u
exactConv t u = via (λ _ d n → decConv t u d n)

exactConvT : {Γ : Cx} (A B : RTy Γ) {k : RTm ε} → ◇ ⊢ k ∷ K≅ᵀ (dep Γ) (quoteTy A) (quoteTy B) → A ≅ᵀ B
exactConvT A B = via (λ _ d n → decConvT A B d n)

exactLk : {Γ : Ctx} (x : Var ⌊ Γ ⌋) (A : RTy ⌊ Γ ⌋) {k : RTm ε} →
          ◇ ⊢ k ∷ K∋ (ix∋ (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteVar x) (quoteTy A)) → Γ ∋ x ∷ A
exactLk x A = via (λ _ d n → decLk x {A} d n)

exactPw : {Γ : Cx} (c : RTm Γ) (b : RTm (Γ ∙)) {k : RTm ε} →
          ◇ ⊢ k ∷ KPw (dep Γ) (quoteTm c) (quoteTm b) → (pw? c ≡ true) × (b ≡ pwBody c)
exactPw c b = via (λ _ d n → decPw c {b} d n)

exactNNC : {Γ : Cx} (c : RTm Γ) {k : RTm ε} → ◇ ⊢ k ∷ KNNC (dep Γ) (quoteTm c) → NoNatC c
exactNNC c = via (λ _ d n → decNNC c d n)

exactStkA : {Γ : Cx} (c : RTm Γ) {k : RTm ε} → ◇ ⊢ k ∷ KStkA (dep Γ) (quoteTm c) → stkA? c ≡ true
exactStkA c = via (λ _ d n → decStkA c d n)

exactStkC : {Γ : Cx} (c : RTm Γ) {k : RTm ε} → ◇ ⊢ k ∷ KStkC (dep Γ) (quoteTm c) → stkC? c ≡ true
exactStkC c = via (λ _ d n → decStkC c d n)

exactFlat : {Γ : Cx} (c : RTm Γ) {k : RTm ε} → ◇ ⊢ k ∷ KFlat (dep Γ) (quoteTm c) → flat? c ≡ true
exactFlat c = via (λ _ d n → decFlat c d n)
