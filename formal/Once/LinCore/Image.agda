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

  ------------------------------------------------------------------------
  -- 3. THE MACHINE: A16's, with calls in place of expansion.
  ------------------------------------------------------------------------

  infixr 5 _∷ᴵ_
  data Stkᴵ : List LTy → Set where
    []ᴵ  : Stkᴵ []
    _∷ᴵ_ : ∀ {A S} → MVᴵ A → Stkᴵ S → Stkᴵ (A ∷ S)

  -- the environment's slots: a view, or a lend's slot (A16's `Slots`)
  data Slotsᴵ : List LTy → Set where
    []ᵉ : Slotsᴵ []
    vw  : ∀ {E Es} → MVᴵ E → Slotsᴵ Es → Slotsᴵ (E ∷ Es)
    ln  : ∀ {E X Es} → MVᴵ E → MVᴵ X → Slotsᴵ (E ∷ Es) → Slotsᴵ ((E ⊗t X) ∷ E ∷ Es)

  infix 4 _∥_
  record Cfgᴵ (env ops : List LTy) : Set where
    constructor _∥_
    field envs : Slotsᴵ env
          opds : Stkᴵ ops

  -- the shapes: the environment's types and the operands'
  infix 4 _∣_
  record Shᴵ : Set where
    constructor _∣_
    field env ops : List LTy

  data Codeᴵ : Shᴵ → Shᴵ → Set
  data Insᴵ : Shᴵ → Shᴵ → Set where
    unpair  : ∀ {Es A B S} → Insᴵ (Es ∣ (A ⊗t B) ∷ S) (Es ∣ A ∷ B ∷ S)
    pair    : ∀ {Es A B S} → Insᴵ (Es ∣ A ∷ B ∷ S) (Es ∣ (A ⊗t B) ∷ S)
    swap    : ∀ {Es A B S} → Insᴵ (Es ∣ A ∷ B ∷ S) (Es ∣ B ∷ A ∷ S)
    -- a generator that moves no cell's contents but its own (no call, no
    -- view): one step
    prim    : ∀ {Γ} (ds : Defs Γ) {Es A B S} → LTm Γ A B → Insᴵ (Es ∣ A ∷ S) (Es ∣ B ∷ S)
    untag   : ∀ {Es l X A S} → Insᴵ (Es ∣ (Ct l X ⊗t A) ∷ S) (Es ∣ (X ⊗t A) ∷ S)
    -- the views (A16's)
    elend   : ∀ {E Es X A S} → Insᴵ (E ∷ Es ∣ (X ⊗t A) ∷ S) ((E ⊗t X) ∷ E ∷ Es ∣ A ∷ S)
    eunlend : ∀ {E Es X B S} → Insᴵ ((E ⊗t X) ∷ E ∷ Es ∣ B ∷ S) (E ∷ Es ∣ (X ⊗t B) ∷ S)
    elift   : ∀ {Es S} → Insᴵ (Es ∣ S) (One ∷ Es ∣ S)
    efst    : ∀ {E₁ E₂ Es S} → Insᴵ ((E₁ ⊗t E₂) ∷ Es ∣ S) (E₁ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S)
    esnd    : ∀ {E₁ E₂ Es S} → Insᴵ ((E₁ ⊗t E₂) ∷ Es ∣ S) (E₂ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S)
    eout    : ∀ {F Es S} → Insᴵ (μt F ∷ Es ∣ S) (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S)
    eapp    : ∀ {l X Es S} → Insᴵ (Ct l X ∷ Es ∣ S) (X ∷ Ct l X ∷ Es ∣ S)
    epop    : ∀ {E Es S} → Insᴵ (E ∷ Es ∣ S) (Es ∣ S)
    -- ★ a cell built with its code word: a closure (A16's `llam`/`llamω`)
    -- and a ν (`lunf`)
    mkfn    : ∀ {Es k g X A B S} → Vt k X A B → Insᴵ (Es ∣ X ∷ S) (Es ∣ Fn k g A B ∷ S)
    mknu    : ∀ {Es F S′ S} → NVt F S′ → Insᴵ (Es ∣ (Coalg F S′ ⊗t S′) ∷ S) (Es ∣ Nu F ∷ S)
    -- ★ a CALL: a block, in a frame of its own, on the caller's environment
    call    : ∀ {σ Es S} → σ ∈ᴮ Σ → Insᴵ (top σ ⊳ Es ∣ dom σ ∷ S) (top σ ⊳ Es ∣ cod σ ∷ S)
    -- ★ through a cell's code word: apply a one-shot closure (its cell
    -- freed), a lent many-use one (read), observe a ν (freed); copy and free
    -- a closure's or a ν's cell with what it holds
    icall   : ∀ {Es g A B S} → Insᴵ (Es ∣ (Fn once g A B ⊗t A) ∷ S) (Es ∣ B ∷ S)
    icallω  : ∀ {Es g A B S} → Insᴵ (Fn many g A B ∷ Es ∣ A ∷ S) (Fn many g A B ∷ Es ∣ B ∷ S)
    iobs    : ∀ {Es F S} → Insᴵ (Es ∣ Nu F ∷ S) (Es ∣ LF∙ F (Nu F) ∷ S)
    icopy   : ∀ {Es k g A B S} → Insᴵ (Es ∣ Fn k g A B ∷ S) (Es ∣ (Fn k g A B ⊗t Fn k g A B) ∷ S)
    ifree   : ∀ {Es k g A B S} → Insᴵ (Es ∣ Fn k g A B ∷ S) (Es ∣ One ∷ S)
    ncopy   : ∀ {Es F S} → Insᴵ (Es ∣ Nu F ∷ S) (Es ∣ (Nu F ⊗t Nu F) ∷ S)
    nfree   : ∀ {Es F S} → Insᴵ (Es ∣ Nu F ∷ S) (Es ∣ One ∷ S)
    -- a μ node's cell: copied, freed (its layer by the code that follows)
    mcopy   : ∀ {Es F S} → Insᴵ (Es ∣ μt F ∷ S) (Es ∣ LF∙ F (μt F) ∷ S)
    -- ★ the loop (D317): a finite round, run again while it says so
    loop    : ∀ {E Es A B S} → Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S) → Insᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ B ∷ S)
    stuck   : ∀ {sh sh′} → Insᴵ sh sh′

  infixr 5 _⨾_
  data Codeᴵ where
    end    : ∀ {sh} → Codeᴵ sh sh
    _⨾_    : ∀ {sh sh′ T} → Insᴵ sh sh′ → Codeᴵ sh′ T → Codeᴵ sh T
    case   : ∀ {Es A B S T} → Codeᴵ (Es ∣ A ∷ S) T → Codeᴵ (Es ∣ B ∷ S) T → Codeᴵ (Es ∣ (A ⊕t B) ∷ S) T
    ecase  : ∀ {E₁ E₂ Es S T} → Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) T → Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) T
           → Codeᴵ ((E₁ ⊕t E₂) ∷ Es ∣ S) T
    halted : ∀ {sh T} → Codeᴵ sh T

  -- ★ a block: its signature's code, polymorphic in the rest of both stacks
  Block : BSig → Set
  Block σ = ∀ {Es S} → Codeᴵ (top σ ⊳ Es ∣ dom σ ∷ S) (top σ ⊳ Es ∣ cod σ ∷ S)

  -- ★ AN IMAGE: a block for every signature
  data Blocks : List BSig → Set where
    []ᵇ  : Blocks []
    _∷ᵇ_ : ∀ {σ Σ′} → Block σ → Blocks Σ′ → Blocks (σ ∷ Σ′)
