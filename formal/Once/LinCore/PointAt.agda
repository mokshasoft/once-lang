-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.PointAt — plan 0.146 B1.4b (D417, step 3): the word layer's
-- CONTROL half — a point of the image's run, with the membership its
-- lowering was made with, and the flat code there.
--
-- `Pnt c`: `c` is at a point of the start code, of a universe key's block
-- (`p : (σ , κ) ∈ allK U`, the evidence the caller's `call` was lowered
-- with, so its target is `nameOf (idx p)`), or of a trampoline (`p : under κ
-- ∈ allK U`, the cell's code word's), or the run has stopped. `ptCode` is
-- the flat code at the point (`LowAt`'s, `dispC` at a loop's dispatch,
-- `TrampAt`'s), `ptFin` what its `end` lowers to (the block's way out, the
-- start's `leave`, or a loop body's jump to its dispatch), and the code lies
-- inside the image (`ptIn`), so the flat run finds it at its prefix's length
-- (`in-seg`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.PointAt
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.ImagePt fmt ans bw using (Sub; Pt; at; disp)
open import Once.LinCore.LowAt fmt ans bw using (Inside; in-trans; in-l; in-r; in-∷; module At)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.EntriesI fmt ans bw using (module ImgE)
open import Once.LinCore.TrampAt fmt ans bw using (under; ptDepth; in-[]; in-drop4; module Tr; module TrImg)

------------------------------------------------------------------------
-- 1. A CODE INSIDE THE PROGRAM IS AT ITS PREFIX'S LENGTH.
------------------------------------------------------------------------

module Fetch {FS : FrameSemantics} where
  open FlatMachine {FS} using (fetch; fetch-++-right)
  open import Once.LinCore.Moves {FS} using (Seg)

  seg-from : ∀ prog pc ys post → (∀ k → fetch prog (pc + k) ≡ fetch (ys ++ post) k) → Seg prog pc ys
  seg-from prog pc []       post h = tt
  seg-from prog pc (y ∷ ys) post h =
    trans (cong (fetch prog) (sym (+-identityʳ pc))) (h 0) ,
    seg-from prog (suc pc) ys post (λ k → trans (cong (fetch prog) (sym (+-suc pc k))) (h (suc k)))

  in-seg : ∀ {prog xs} (ins : Inside prog xs) → Seg prog (length (proj₁ ins)) xs
  in-seg {xs = xs} (pre , post , refl) = seg-from _ (length pre) xs post (fetch-++-right pre (xs ++ post))

------------------------------------------------------------------------
-- 2. ★ POINTS WITH THEIR MEMBERSHIPS, AND THE FLAT CODE THERE.
------------------------------------------------------------------------

module Ctl {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing) where
  open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
  open Program ds f using (U; blocks-in; start-in)
  open ProgramRun ds f using (ncty)
  open In U
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst
  open ImgE {FS} ds f ldConst ld-nl using (image-at)
  open TrImg {FS} ds f ldConst ld-nl using (image-tr)
  open Tr U ncty ldConst using (trAt)

  -- the start code, and a block's way out (`lowBlock`'s `fin`)
  main : Codeᴵ (One ∷ [] ∣ One ∷ []) (One ∷ [] ∣ One ∷ [])
  main = compᴵ ds f {[]} {[]} end

  blockFin : ∀ {σ} → Key σ → AbstractTrace
  blockFin {bsig t A B} κ =
    let φ = frameOf (blockᴵ κ) ; M = wsz A ⊔ wsz B
    in restore-input (sv₁ φ) ∷ mvSP (Tp φ (B ∷ [])) (M ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret (fbudget φ)) ∷ []

  module S = At U ncty ldConst (frameOf main) j₀
  module B {σ} (κ : Key σ) (p : (σ , κ) ∈ allK U) = At U ncty ldConst (frameOf (blockᴵ κ)) (idx p)

  -- the roots: the start with `leave`, a block with its way out
  L₀ˢ : S.Low main
  L₀ˢ = S.low 0 (instr-ctrl c-leave ∷ []) (start-in {[]} {[]} tt)

  L₀ᵇ : ∀ {σ} (κ : Key σ) (p : (σ , κ) ∈ allK U) → B.Low κ p (blockᴵ κ)
  L₀ᵇ κ p = B.low 0 (blockFin κ) (blocks-in p)

  -- ★ a point, with the membership its lowering was made with
  data Pnt : ∀ {sh U′} → Codeᴵ sh U′ → Set where
    p-start : ∀ {sh U′} {c : Codeᴵ sh U′} → Pt main c → Pnt c
    p-block : ∀ {σ sh U′} {κ : Key σ} {c : Codeᴵ sh U′} (p : (σ , κ) ∈ allK U) → Pt (blockᴵ κ) c → Pnt c
    p-tramp : ∀ {σ sh U′} {κ : Key σ} {c : Codeᴵ sh U′} (p : under κ ∈ allK U) → Pt (blockᴵ κ) c → Pnt c
    p-halt  : ∀ {sh U′} → Pnt (halted {sh} {U′})

  -- a trampoline's way out (the code at its `end`)
  trFin : ∀ {σ} (j : ℕ) → Key σ → AbstractTrace
  trFin j κ@(ktr1 _ _ _) = trAt j κ 2
  trFin j κ@(ktrω _ _ _) = trAt j κ 3
  trFin j κ@(ktro _ _ _) = trAt j κ 2
  trFin j κ@(ktrc _ _)   = trAt j κ 4
  trFin j κ@(ktrf _ _)   = trAt j κ 2
  trFin j (kbody1 _ _ _) = []
  trFin j (kbodyω _ _ _) = []
  trFin j (kfold _ _ _)  = []
  trFin j (kobs _ _ _)   = []
  trFin j (kcopy _)      = []
  trFin j (kfree _)      = []

  -- ★ the flat code at a point, and its way out
  ptCode : ∀ {sh U′} {c : Codeᴵ sh U′} → Pnt c → AbstractTrace
  ptCode (p-start (at s))         = S.code (S.L (S.sub-low L₀ˢ s))
  ptCode (p-start (disp s))       = S.dispC (S.L (S.sub-low L₀ˢ s))
  ptCode (p-block {κ = κ} p (at s))   = B.code κ p (B.L (B.sub-low κ p (L₀ᵇ κ p) s))
  ptCode (p-block {κ = κ} p (disp s)) = B.dispC κ p (B.L (B.sub-low κ p (L₀ᵇ κ p) s))
  ptCode (p-tramp {κ = κ} p pt)   = trAt (idx p) κ (ptDepth pt)
  ptCode p-halt                   = []

  ptFin : ∀ {sh U′} {c : Codeᴵ sh U′} → Pnt c → AbstractTrace
  ptFin (p-start (at s))         = S.lfin (S.L (S.sub-low L₀ˢ s))
  ptFin (p-start (disp s))       = S.lfin (S.L (S.sub-low L₀ˢ s))
  ptFin (p-block {κ = κ} p (at s))   = B.lfin (B.L (B.sub-low κ p (L₀ᵇ κ p) s))
  ptFin (p-block {κ = κ} p (disp s)) = B.lfin (B.L (B.sub-low κ p (L₀ᵇ κ p) s))
  ptFin (p-tramp {κ = κ} p pt)   = trFin (idx p) κ
  ptFin p-halt                   = []

  ----------------------------------------------------------------------
  -- 3. ★ THE CODE AT A POINT LIES INSIDE THE IMAGE.
  ----------------------------------------------------------------------

  -- the start's code: after `c-start`, before the blocks
  start-root : Inside image (S.code L₀ˢ)
  start-root = in-trans in-∷ (in-l (S.code L₀ˢ) _)

  -- a block's code: after its entry, saves and copies in
  block-root : ∀ {σ} j (κ : Key σ) ev → Inside (lowBlock j κ ev) (proj₁ (lowC (frameOf (blockᴵ κ)) j 0 (blockFin κ) (blockᴵ κ) ev))
  block-root {bsig t A B} j κ ev =
    let φ = frameOf (blockᴵ κ) ; M = wsz A ⊔ wsz B
    in in-trans in-drop4 (in-trans (in-r (mvPS (M ∸ wsz A) (Tp φ (A ∷ [])) (wsz A)) _) (in-r (view-in t φ) _))

  ptIn : ∀ {sh U′} {c : Codeᴵ sh U′} (P : Pnt c) → Inside image (ptCode P)
  ptIn (p-start (at s))   = in-trans start-root (S.ins (S.sub-low L₀ˢ s))
  ptIn (p-start (disp s)) = in-trans (in-trans start-root (S.ins (S.sub-low L₀ˢ s))) (S.disp-in (S.L (S.sub-low L₀ˢ s)))
  ptIn (p-block {κ = κ} p (at s)) =
    in-trans (in-trans (in-trans (image-at p) (in-l _ _)) (block-root (idx p) κ (blocks-in p)))
             (B.ins (B.sub-low κ p (L₀ᵇ κ p) s))
  ptIn (p-block {κ = κ} p (disp s)) =
    in-trans (in-trans (in-trans (in-trans (image-at p) (in-l _ _)) (block-root (idx p) κ (blocks-in p)))
                       (B.ins (B.sub-low κ p (L₀ᵇ κ p) s)))
             (B.disp-in κ p (B.L (B.sub-low κ p (L₀ᵇ κ p) s)))
  ptIn (p-tramp {κ = κ} p pt) = image-tr κ p (ptDepth pt)
  ptIn p-halt                 = in-[] image
