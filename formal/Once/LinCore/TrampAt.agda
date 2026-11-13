-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.TrampAt — plan 0.146 B1.4b (D417, step 3): the flat code AT
-- a trampoline's points.
--
-- A trampoline key (`ktr1`, `ktrω`, `ktro`, `ktrc`, `ktrf`) is not lowered:
-- its flat code is `tramp j κ` of its UNDERLYING key `κ` (`under`), at that
-- key's index `j`. Its image block is straight-line (the cell's part, the
-- call, the tail), so a point is its depth. As for a block, the entry and
-- its saves are the way in (`call-in`'s); the code at depth `d` is
-- `trAt j κ d`, written out (what the step lemmas read), and it lies inside
-- the trampoline's (`tr-in`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.Machine.SMCore
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Data.Maybe using (nothing)

module Once.LinCore.TrampAt
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.ImagePt fmt ans bw using (Sub; Pt; at; disp; whole; next; left; right; eleft; eright; body)
open import Once.LinCore.LowAt fmt ans bw using (Inside; in-trans; in-r; in-∷)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.EntriesI fmt ans bw using (module ImgE)

------------------------------------------------------------------------
-- 1. A TRAMPOLINE'S UNDERLYING KEY, AND A POINT'S DEPTH.
------------------------------------------------------------------------

under : ∀ {σ} → Key σ → AKey
under (ktr1 ds b γ)          = _ , kbody1 ds b γ
under (ktrω ds b γ)          = _ , kbodyω ds b γ
under (ktro ds F S)          = _ , kobs ds F S
under (ktrc X C)             = _ , kcopy X
under (ktrf X C)             = _ , kfree X
under κ@(kbody1 _ _ _)       = _ , κ
under κ@(kbodyω _ _ _)       = _ , κ
under κ@(kfold _ _ _)        = _ , κ
under κ@(kobs _ _ _)         = _ , κ
under κ@(kcopy _)            = _ , κ
under κ@(kfree _)            = _ , κ

depth : ∀ {sh U sh′ U′} {root : Codeᴵ sh U} {c : Codeᴵ sh′ U′} → Sub root c → ℕ
depth whole      = 0
depth (next p)   = suc (depth p)
depth (left p)   = suc (depth p)
depth (right p)  = suc (depth p)
depth (eleft p)  = suc (depth p)
depth (eright p) = suc (depth p)
depth (body p)   = suc (depth p)

ptDepth : ∀ {sh U sh′ U′} {root : Codeᴵ sh U} {c : Codeᴵ sh′ U′} → Pt root c → ℕ
ptDepth (at p)   = depth p
ptDepth (disp p) = depth p

------------------------------------------------------------------------
-- 2. ★ THE CODE AT DEPTH `d`, AND IT LIES INSIDE THE TRAMPOLINE.
------------------------------------------------------------------------

-- the code of one of (at most) five points
pick : ℕ → (c₀ c₁ c₂ c₃ c₄ : AbstractTrace) → AbstractTrace
pick 0 c₀ _ _ _ _ = c₀
pick 1 _ c₁ _ _ _ = c₁
pick 2 _ _ c₂ _ _ = c₂
pick 3 _ _ _ c₃ _ = c₃
pick 4 _ _ _ _ c₄ = c₄
pick (suc (suc (suc (suc (suc _))))) _ _ _ _ _ = []

in-[] : ∀ xs → Inside xs []
in-[] xs = xs , [] , sym (++-identityʳ xs)

pick-in : ∀ {T c₀ c₁ c₂ c₃ c₄} d → Inside T c₀ → Inside T c₁ → Inside T c₂ → Inside T c₃ → Inside T c₄
        → Inside T (pick d c₀ c₁ c₂ c₃ c₄)
pick-in 0 i₀ _ _ _ _ = i₀
pick-in 1 _ i₁ _ _ _ = i₁
pick-in 2 _ _ i₂ _ _ = i₂
pick-in 3 _ _ _ i₃ _ = i₃
pick-in 4 _ _ _ _ i₄ = i₄
pick-in {T} (suc (suc (suc (suc (suc _))))) _ _ _ _ _ = in-[] T

-- past `n` instructions
in-drop4 : ∀ {a b c d xs} → Inside (a ∷ b ∷ c ∷ d ∷ xs) xs
in-drop4 = in-trans in-∷ (in-trans in-∷ (in-trans in-∷ in-∷))

in-drop3 : ∀ {a b c xs} → Inside (a ∷ b ∷ c ∷ xs) xs
in-drop3 = in-trans in-∷ (in-trans in-∷ in-∷)

in-drop2 : ∀ {a b xs} → Inside (a ∷ b ∷ xs) xs
in-drop2 = in-trans in-∷ in-∷

module Tr (U : Univ)
          (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
          (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr) where
  open Lowering U ncty ldConst

  trAt : ∀ {σ} (j : ℕ) → Key σ → ℕ → AbstractTrace
  -- one-shot body: `open1` the environment and argument in, the cell freed;
  -- the call; `end` the result back
  trAt j (ktr1 {X = X} {A = A} {B = B} ds b γ) d =
    let wX = wsz X ; wA = wsz A ; wB = wsz B ; M = (wX + wA) ⊔ wB ; Mc = suc wA ⊔ wB ; a = M ∸ (wX + wA)
        E = restore-input (suc M) ∷ mvSP (M ∸ wB) (Mc ∸ wB) wB ++ instr-ctrl (c-ret (suc (suc M))) ∷ []
        K = lea-slot 0 ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf j)) ∷ E
    in pick d (mvPS hdr a wX ++ restore-input (suc M) ∷ mvPS (Mc ∸ wA) (a + wX) wA ++ restore-input M ∷ instr-free-heap (hdr + wX) ∷ K)
              K E [] []
  -- many-use body: `openω` the view the cell's contents; the call; `epop`
  -- nothing; `end` the return
  trAt j (ktrω {X = X} ds b γ) d =
    let E = instr-ctrl (c-ret 1) ∷ []
        K = restore-input 0 ∷ instr-ctrl (c-call-fn (nameOf j)) ∷ E
    in pick d (contentsAddr (wsz X) ∷ K) K E E []
  -- observation: `nopen` the coalgebra and seed in, the cell freed; the
  -- call; `end` the layer back
  trAt j (ktro ds F S) d =
    let wP = wsz (cty (F , S)) ; wL = wsz (LF∙ F (Nu F)) ; M = wP ⊔ wL ; Mc = 1 ⊔ wL
        E = restore-input (suc M) ∷ mvSP (M ∸ wL) (Mc ∸ wL) wL ++ instr-ctrl (c-ret (suc (suc M))) ∷ []
        K = lea-slot 0 ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf j)) ∷ E
    in pick d (mvPS hdr (M ∸ wP) wP ++ restore-input M ∷ instr-free-heap (hdr + wP) ∷ K) K E [] []
  -- a copy: `copen` the contents' address; the call (the contents' copy);
  -- `epop` nothing; `reclose` a fresh cell, the code words, the contents;
  -- `end` its address back
  trAt j (ktrc X C) d =
    let w = wsz X ; s₁ = w ; s₂ = suc w ; s₃ = suc (suc w) ; b = suc s₃
        E = restore-input s₁ ∷ load-from-slot s₃ ∷ store-at 0 ∷ instr-ctrl (c-ret b) ∷ []
        R = instr-alloc-heap (hdr + w) ∷ store-at-slot s₃
            ∷ restore-input s₂ ∷ load-at 1 ∷ restore-input s₃ ∷ store-at 1
            ∷ restore-input s₂ ∷ load-at 2 ∷ restore-input s₃ ∷ store-at 2
            ∷ restore-input s₂ ∷ load-at 3 ∷ restore-input s₃ ∷ store-at 3
            ∷ mov-to-output ∷ store-at 0 ∷ mvSP 0 hdr w ++ E
        K = lea-slot 0 ∷ mov-to-input ∷ load-from-slot s₃ ∷ instr-ctrl (c-call-fn (nameOf j)) ∷ R
    in pick d (restore-input s₂ ∷ contentsAddr w ∷ store-at-slot s₃ ∷ K) K R R E
  -- a free: `fopen` the contents out, the cell freed; the call; `end` the return
  trAt j (ktrf X C) d =
    let w = wsz X
        E = instr-ctrl (c-ret (suc w)) ∷ []
        K = lea-slot 0 ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf j)) ∷ E
    in pick d (restore-input w ∷ mvPS hdr 0 w ++ instr-free-heap (hdr + w) ∷ K) K E [] []
  trAt j (kbody1 _ _ _) d = []
  trAt j (kbodyω _ _ _) d = []
  trAt j (kfold _ _ _)  d = []
  trAt j (kobs _ _ _)   d = []
  trAt j (kcopy _)      d = []
  trAt j (kfree _)      d = []

  -- ★ the code at a point lies inside the underlying key's trampoline
  tr-in : ∀ {σ} j (κ : Key σ) d → Inside (tramp j (proj₂ (under κ))) (trAt j κ d)
  tr-in j (ktr1 {X = X} {A = A} {B = B} ds b γ) d =
    let wX = wsz X ; wA = wsz A ; M = (wX + wA) ⊔ wsz B ; Mc = suc wA ⊔ wsz B ; a = M ∸ (wX + wA)
        i₀ = in-drop4
        i₁ = in-trans i₀ (in-trans (in-r (mvPS hdr a wX) _) (in-trans in-∷ (in-trans (in-r (mvPS (Mc ∸ wA) (a + wX) wA) _) in-drop2)))
        i₂ = in-trans i₁ in-drop3
    in pick-in d i₀ i₁ i₂ (in-[] _) (in-[] _)
  tr-in j (ktrω {X = X} ds b γ) d =
    let i₀ = in-drop2 ; i₁ = in-trans i₀ in-∷ ; i₂ = in-trans i₁ in-drop2
    in pick-in d i₀ i₁ i₂ i₂ (in-[] _)
  tr-in j (ktro ds F S) d =
    let wP = wsz (cty (F , S)) ; M = wP ⊔ wsz (LF∙ F (Nu F))
        i₀ = in-drop4
        i₁ = in-trans i₀ (in-trans (in-r (mvPS hdr (M ∸ wP) wP) _) in-drop2)
        i₂ = in-trans i₁ in-drop3
    in pick-in d i₀ i₁ i₂ (in-[] _) (in-[] _)
  tr-in j (ktrc X C) d =
    let w = wsz X
        i₀ = in-drop4
        i₁ = in-trans i₀ in-drop3
        i₂ = in-trans i₁ in-drop4
        i₄ = in-trans i₂ (in-trans in-drop4 (in-trans in-drop4 (in-trans in-drop4 (in-trans in-drop4 (in-r (mvSP 0 hdr w) _)))))
    in pick-in d i₀ i₁ i₂ i₂ i₄
  tr-in j (ktrf X C) d =
    let w = wsz X
        i₀ = in-drop2
        i₁ = in-trans i₀ (in-trans in-∷ (in-trans (in-r (mvPS hdr 0 w) _) in-∷))
        i₂ = in-trans i₁ in-drop3
    in pick-in d i₀ i₁ i₂ (in-[] _) (in-[] _)
  tr-in j (kbody1 _ _ _) d = in-[] _
  tr-in j (kbodyω _ _ _) d = in-[] _
  tr-in j (kfold _ _ _)  d = in-[] _
  tr-in j (kobs _ _ _)   d = in-[] _
  tr-in j (kcopy _)      d = in-[] _
  tr-in j (kfree _)      d = in-[] _

------------------------------------------------------------------------
-- 3. ★ …HENCE INSIDE THE IMAGE, at the underlying key's index.
------------------------------------------------------------------------

module TrImg {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
             (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
             (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing) where
  open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
  open Program ds f using (U; blocks-in)
  open ProgramRun ds f using (ncty)
  open Program′ ds f ldConst using (image)
  open Lowering U ncty ldConst using (lowBlock; tramp)
  open ImgE {FS} ds f ldConst ld-nl using (image-at)
  open Tr U ncty ldConst

  image-tr : ∀ {σ} (κ : Key σ) (p : under κ ∈ allK U) d → Inside image (trAt (idx p) κ d)
  image-tr κ p d =
    in-trans (in-trans (image-at p) (in-r (lowBlock (idx p) (proj₂ (under κ)) (blocks-in p)) _)) (tr-in (idx p) κ d)
