-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Image — plan 0.146 B1.4a: the stack machine with FINITE code.
--
-- A16's `Machine` expands a fold, a loop, an observation and a closure's
-- body when it reaches them; an image is finite. Here a program is a table
-- of BLOCKS over a fixed list of signatures `Σ`:
--
--   * a signature is what a block expects: the top of the environment stack
--     (or none) and the operand it takes and gives. A block's code is
--     polymorphic in the rest of both stacks: compiled once, called from
--     anywhere, in a frame of its own (`call`, A16's `enter … leave`);
--   * the table may refer to itself (a fold's block calls itself on each
--     child): this is code, run by a step relation;
--   * a closure's and a ν's cell hold a LABEL (the run's hold the body's
--     term): the code word D404 says applying, copying and dropping the
--     value run (`Vt`, three entries, since the environment's type is hidden
--     in the cell);
--   * a server's loop is a structured instruction over a finite round
--     (`loop`), its back edge a jump in the flat image (B1.4b).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.Image
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans

------------------------------------------------------------------------
-- 1. SIGNATURES AND LABELS.
------------------------------------------------------------------------

-- a block's signature: the environment's top it reads (if any), its operand
-- and its result
record BSig : Set where
  constructor bsig
  field
    top : Maybe LTy
    dom : LTy
    cod : LTy
open BSig public

-- the environment stack a block sees: its top, over the caller's
_⊳_ : Maybe LTy → List LTy → List LTy
nothing ⊳ Es = Es
just E  ⊳ Es = E ∷ Es

-- a label: a position in the signatures
data _∈ᴮ_ : BSig → List BSig → Set where
  bhere  : ∀ {σ Σ} → σ ∈ᴮ (σ ∷ Σ)
  bthere : ∀ {σ τ Σ} → σ ∈ᴮ Σ → σ ∈ᴮ (τ ∷ Σ)

------------------------------------------------------------------------
-- 2. VALUES: a cell's code word is a table of labels.
------------------------------------------------------------------------

-- applying a closure: a one-shot body owns its environment beside the
-- argument; a many-use body reads it lent
runSig : Kd → LTy → LTy → LTy → BSig
runSig once X A B = bsig nothing (X ⊗t A) B
runSig many X A B = bsig (just X) A B

module _ (Σ : List BSig) where

  -- ★ a closure's code word (D404): apply it, copy its environment, free it
  record Vt (k : Kd) (X A B : LTy) : Set where
    constructor vt
    field
      run : runSig k X A B ∈ᴮ Σ
      cpy : bsig nothing X (X ⊗t X) ∈ᴮ Σ
      del : bsig nothing X One ∈ᴮ Σ

  -- ★ a ν's code word: observe it, copy and free what its cell holds
  record NVt (F : LF) (S : LTy) : Set where
    constructor nvt
    field
      obs : bsig nothing (Coalg F S ⊗t S) (LF∙ F (Nu F)) ∈ᴮ Σ
      cpy : bsig nothing (Coalg F S ⊗t S) ((Coalg F S ⊗t S) ⊗t (Coalg F S ⊗t S)) ∈ᴮ Σ
      del : bsig nothing (Coalg F S ⊗t S) One ∈ᴮ Σ

  -- the image's values: the run's (`Events.MV`), with labels for code words
  data MVᴵ : LTy → Set where
    mone  : MVᴵ One
    mpair : ∀ {A B} → MVᴵ A → MVᴵ B → MVᴵ (A ⊗t B)
    minl  : ∀ {A B} → MVᴵ A → MVᴵ (A ⊕t B)
    minr  : ∀ {A B} → MVᴵ B → MVᴵ (A ⊕t B)
    mbase : ∀ {b} → ⟦ b ⟧b → MVᴵ (Bt b)
    mmu   : ∀ {F} → ℕ × ℕ → MVᴵ (LF∙ F (μt F)) → MVᴵ (μt F)
    mct   : ∀ {l X} → MVᴵ X → MVᴵ (Ct l X)
    mfn   : ∀ {k g X A B} → ℕ × ℕ → Vt k X A B → MVᴵ X → MVᴵ (Fn k g A B)
    mnu   : ∀ {F S} → ℕ × ℕ → NVt F S → MVᴵ (Coalg F S ⊗t S) → MVᴵ (Nu F)
