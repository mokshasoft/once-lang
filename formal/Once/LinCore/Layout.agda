-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Layout — plan 0.146 B1.4b, part 2: the image's words (D416).
--
-- * A value is words: a flat value its `Spec.ABI` words (`wsz`: `Unit` none,
--   a scalar one, a pair its two in order, a sum its tag and its payload
--   padded to the larger side); a tagged closure its environment's; a μ
--   node, a closure, a ν one word, the address of its cell.
-- * A block's frame (D415: one per call, at the block's closed shape) has two
--   regions at fixed offsets. The ENVIRONMENT's: each slot a buffer holding
--   the words of what it sees (a view's are a copy: it reads, never owns; a
--   lend's are the lent pair's), stacked upward from slot 0. The OPERAND
--   STACK's, above it, growing DOWNWARD from the frame's top, so the top
--   element is at the lowest offset and a pair on the stack is its two
--   components in place.
-- * Each region is sized by the most its block's code reaches (`peak`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.Layout
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_)
open import Once.LinCore.Image fmt ans bw

------------------------------------------------------------------------
-- 1. WORDS.
------------------------------------------------------------------------

-- a value's words (D416; `Spec.ABI.words` on the flat types)
wsz : LTy → ℕ
wsz One          = 0
wsz Zero         = 0
wsz (A ⊗t B)     = wsz A + wsz B
wsz (A ⊕t B)     = suc (wsz A ⊔ wsz B)
wsz (Bt b)       = 1
wsz (μt F)       = 1
wsz (Fn k g A B) = 1
wsz (Nu F)       = 1
wsz (Ct l X)     = wsz X

-- a stack's words
ws : List LTy → ℕ
ws []       = 0
ws (A ∷ As) = wsz A + ws As

-- a shape's: its environment's, its operand stack's
envW : Sh → ℕ
envW (Es ∣ S) = ws Es

opW : Sh → ℕ
opW (Es ∣ S) = ws S

------------------------------------------------------------------------
-- 2. THE MOST A CODE REACHES: each region's size.
------------------------------------------------------------------------

infixr 6 _⊔²_
_⊔²_ : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
(a , b) ⊔² (c , d) = a ⊔ c , b ⊔ d

at : Sh → ℕ × ℕ
at sh = envW sh , opW sh

peakI : ∀ {sh sh′} → Insᴵ sh sh′ → ℕ × ℕ
peakC : ∀ {sh T} → Codeᴵ sh T → ℕ × ℕ

peakI (loop c) = peakC c
-- a swap keeps its top element below the stack while it moves the next
peakI (swap {A = A} {B} {S}) = 0 , wsz A + ws (A ∷ B ∷ S)
peakI (prim ds {S = S} (lswap {A = A} {B = B})) = 0 , wsz A + ws ((A ⊗t B) ∷ S)
{-# CATCHALL #-}
peakI _        = 0 , 0

peakC {sh} end           = at sh
peakC {sh} (i ⨾ c)       = at sh ⊔² peakI i ⊔² peakC c
peakC {sh} (case c₁ c₂)  = at sh ⊔² peakC c₁ ⊔² peakC c₂
peakC {sh} (ecase c₁ c₂) = at sh ⊔² peakC c₁ ⊔² peakC c₂
peakC {sh} halted        = at sh

------------------------------------------------------------------------
-- 3. OFFSETS in a frame whose environment region holds `EP` words and whose
-- operand region `OP`.
------------------------------------------------------------------------

record Frame : Set where
  constructor frame
  field
    EP OP : ℕ
open Frame public

-- the frame's slots: both regions
budget : Frame → ℕ
budget φ = EP φ + OP φ

-- a block's frame: the most its code reaches
frameOf : ∀ {sh T} → Codeᴵ sh T → Frame
frameOf c = frame (proj₁ (peakC c)) (proj₂ (peakC c))

-- the top environment slot's first word: the words of the slots below it
envAt : List LTy → ℕ
envAt Es = ws Es

-- the top operand's first word: the region's top, less the stack's words
opAt : Frame → List LTy → ℕ
opAt φ S = budget φ ∸ ws S
