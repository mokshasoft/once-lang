-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalTrView — plan 0.146 B1.4b (D417): A TRAMPOLINE'S CELL PART'S POINT, by its
-- instruction. A trampoline point at `open1`/`nopen`/`fopen`/`openω` is its trampoline's depth 0;
-- the split that rules out every other point lives here, in a module with a small context (in a
-- step's module it unifies each point's code with the instruction's, at tens of seconds).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr; StoredValue)

module Once.LinCore.GlobalTrView
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (_∣_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.ImagePt fmt ans bw using (Pt)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.TrampAt fmt ans bw using (under)
open import Once.LinCore.Global fmt ans bw using (module Relate)

module TrV {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf using (TrPt; tp0; to0; tf0; tw0)
  open Program ds f using (U)

  data Is-tp0 : ∀ {σ sh V} {κ : Key σ} {c : Codeᴵ sh V} {p : under κ ∈ allK U} {pt : Pt (blockᴵ κ) c} → TrPt p pt → Set where
    it-tp0 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p : under (ktr1 ds′ b γ) ∈ allK U) → Is-tp0 (tp0 p)

  data Is-to0 : ∀ {σ sh V} {κ : Key σ} {c : Codeᴵ sh V} {p : under κ ∈ allK U} {pt : Pt (blockᴵ κ) c} → TrPt p pt → Set where
    it-to0 : ∀ {Γ′} {ds′ : Defs Γ′} {F S} (p : under (ktro ds′ F S) ∈ allK U) → Is-to0 (to0 p)

  data Is-tf0 : ∀ {σ sh V} {κ : Key σ} {c : Codeᴵ sh V} {p : under κ ∈ allK U} {pt : Pt (blockᴵ κ) c} → TrPt p pt → Set where
    it-tf0 : ∀ {X C} (p : under (ktrf X C) ∈ allK U) → Is-tf0 (tf0 {X = X} {C} p)

  data Is-tw0 : ∀ {σ sh V} {κ : Key σ} {c : Codeᴵ sh V} {p : under κ ∈ allK U} {pt : Pt (blockᴵ κ) c} → TrPt p pt → Set where
    it-tw0 : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} (p : under (ktrω ds′ b γ) ∈ allK U) → Is-tw0 (tw0 p)

  open1-v : ∀ {σ} {κ : Key σ} {Es g X A B S V} {k : Codeᴵ (Es ∣ (X ⊗t A) ∷ S) V} {p : under κ ∈ allK U}
              {pt : Pt (blockᴵ κ) (open1 {Es = Es} {g = g} {X = X} {A = A} {B = B} {S = S} ⨾ k)} (tp : TrPt p pt) → Is-tp0 tp
  open1-v (tp0 p) = it-tp0 p

  nopen-v : ∀ {σ} {κ : Key σ} {Es F S S′ V} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) V} {p : under κ ∈ allK U}
              {pt : Pt (blockᴵ κ) (nopen {Es = Es} {F = F} {S = S} {S′ = S′} ⨾ k)} (tp : TrPt p pt) → Is-to0 tp
  nopen-v (to0 p) = it-to0 p

  fopen-v : ∀ {σ} {κ : Key σ} {X C Es S V} {k : Codeᴵ (Es ∣ X ∷ S) V} {p : under κ ∈ allK U}
              {pt : Pt (blockᴵ κ) (fopen {X = X} {C = C} {Es = Es} {S = S} ⨾ k)} (tp : TrPt p pt) → Is-tf0 tp
  fopen-v (tf0 p) = it-tf0 p

  openω-v : ∀ {σ} {κ : Key σ} {Es g X A B S V} {k : Codeᴵ (X ∷ Fn many g A B ∷ Es ∣ S) V} {p : under κ ∈ allK U}
              {pt : Pt (blockᴵ κ) (openω {Es = Es} {g = g} {X = X} {A = A} {B = B} {S = S} ⨾ k)} (tp : TrPt p pt) → Is-tw0 tp
  openω-v (tw0 p) = it-tw0 p
