-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.StepIos — plan 0.146 B1.5 (D427): A STEP OTHER THAN AN OP
-- SHOWS THE WORLD NOTHING. A local step's trace has no call and no halt
-- (`ios t ≡ []`): its events are a cell's birth, death or read, or a
-- temporary's; a primitive of the image is atomic (`PrimIn`, read off the
-- point's lowering), and none but an op calls the world. The split on a
-- step lives here, in a module of its own.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.StepIos
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Cfg; _∣_)
open import Once.LinCore.Image fmt ans bw using (Codeᴵ; _⨾_; prim)
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.Keys fmt ans bw using (Univ; module In; module Program)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.PointAt fmt ans bw using (module Ctl)
open import Once.LinCore.StepKinds fmt ans bw using (NotOp; StraightC)
open import Once.LinCore.Global fmt ans bw using (module Relate)

-- ★ an atomic primitive other than an op: its run calls nothing
module _ (U : Univ) where
  open In U using (PrimIn)

  prim-ios : ∀ {Γ} {ds : Defs Γ} {A B} {g : LTm Γ A B} {v : MV A} {w : MV B} {n n′ t}
           → PrimIn ds g → NotOp g → Run ds g mone v n (gives w n′) t → ios t ≡ []
  prim-ios p q (r-tmp r wv _) = trans (ios-weave wv) (prim-ios p q r)
  prim-ios _ _ r-ρ = refl
  prim-ios _ _ r-ρ⁻ = refl
  prim-ios _ _ r-λ = refl
  prim-ios _ _ r-λ⁻ = refl
  prim-ios _ _ r-α = refl
  prim-ios _ _ r-α⁻ = refl
  prim-ios _ _ r-swap = refl
  prim-ios _ _ (r-drop {v = v}) = ios-freeAll v
  prim-ios _ _ r-inl = refl
  prim-ios _ _ r-inr = refl
  prim-ios _ _ r-In = refl
  prim-ios _ _ r-Outμ = refl
  prim-ios _ _ r-clo = refl
  prim-ios _ _ r-lam = refl
  prim-ios _ _ r-lamω = refl
  prim-ios _ _ r-unf = refl
  prim-ios _ _ r-const = refl
  prim-ios _ () (r-op _)
  prim-ios () _ r-id
  prim-ios () _ (r-∘ _ _)
  prim-ios () _ (r-⊗ _ _)
  prim-ios () _ r-dup
  prim-ios () _ (r-case₁ _)
  prim-ios () _ (r-case₂ _)
  prim-ios () _ (r-app _ _)
  prim-ios () _ (r-cata _ _)
  prim-ios () _ (r-cata-reuse _ _)
  prim-ios () _ (r-lend _)
  prim-ios () _ (r-lift _)
  prim-ios () _ r-copy
  prim-ios () _ (r-ev _)
  prim-ios () _ (r-nout _)
  prim-ios () _ (r-iter _ _)

-- ★ at a related point
module IosG {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
            (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
            (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
            (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf using (Related; HereP; module Related)
  open Ctl {FS} ds f ldConst ld-nl using (Pnt; p-start; p-block; p-tramp; L₀ˢ; L₀ᵇ; module S; module B)
  open Program ds f using (U)
  open In U using (PrimIn)
  open FlatMachine {FS} using (FlatState)
  open import Once.LinCore.ImagePt fmt ans bw using (at)

  -- a primitive at a point is one the lowering took
  here-prim : ∀ {Γ′} {ds′ : Defs Γ′} {A B Es S V} {g : LTm Γ′ A B} {k : Codeᴵ (Es ∣ B ∷ S) V} {m fs}
              (P : Pnt (prim ds′ g ⨾ k)) → HereP P m fs → PrimIn ds′ g
  here-prim (p-start (at s)) H = proj₁ (S.lcin (S.L (S.sub-low L₀ˢ s)))
  here-prim (p-block {κ = κ} p (at s)) H = proj₁ (B.lcin (B.L (B.sub-low κ p (L₀ᵇ κ p) s)))
  here-prim (p-tramp p pt) (() , H)

  -- ★ a straight step's trace shows the world nothing
  straight-ios : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ fs}
               → (st : StepI c r m n t c′ r′ m′ n′) → StraightC c → Related c r m n fs → ios t ≡ []
  straight-ios (i-prim run) l G = prim-ios U (here-prim (Related.g-pt G) (Related.g-here G)) l run
  straight-ios (i-opend _) () G
  straight-ios i-unpair _ _ = refl
  straight-ios i-pair _ _ = refl
  straight-ios i-swap _ _ = refl
  straight-ios i-unit _ _ = refl
  straight-ios i-untag _ _ = refl
  straight-ios i-untag₁ _ _ = refl
  straight-ios i-tag₁ _ _ = refl
  straight-ios i-case₁ _ _ = refl
  straight-ios i-case₂ _ _ = refl
  straight-ios i-elend _ _ = refl
  straight-ios i-eunlend _ _ = refl
  straight-ios i-elift _ _ = refl
  straight-ios i-epop _ _ = refl
  straight-ios i-call _ _ = refl
  straight-ios i-ret _ _ = refl
  straight-ios i-reti _ _ = refl
  straight-ios i-loop _ _ = refl
  straight-ios i-icall _ _ = refl
  straight-ios i-iobs _ _ = refl
  straight-ios i-cfree _ _ = refl
  straight-ios i-nfree _ _ = refl
  straight-ios i-open1 _ _ = refl
  straight-ios i-nopen _ _ = refl
  straight-ios i-fopen _ _ = refl
  straight-ios i-fopenν _ _ = refl
  straight-ios (i-efst _) _ _ = refl
  straight-ios (i-esnd _) _ _ = refl
  straight-ios (i-eout _) _ _ = refl
  straight-ios (i-eoutq _) _ _ = refl
  straight-ios (i-ecase₁ _) _ _ = refl
  straight-ios (i-ecase₂ _) _ _ = refl
  straight-ios (i-eapp _) _ _ = refl
  straight-ios (i-eword _) _ _ = refl
  straight-ios (i-icallω _) _ _ = refl
  straight-ios (i-ccopy _) _ _ = refl
  straight-ios (i-ncopy _) _ _ = refl
  straight-ios (i-openω _) _ _ = refl
  straight-ios (i-copen _) _ _ = refl
  straight-ios (i-copenν _) _ _ = refl
  straight-ios (i-reclose _) _ _ = refl
  straight-ios (i-recloseν _) _ _ = refl
