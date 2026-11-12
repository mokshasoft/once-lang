-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Image — plan 0.146 B1.4a: the stack machine with FINITE code.
--
-- A16's `Machine` expands a fold, a loop, an observation, a closure's body
-- and a deep copy or free when it reaches them; an image's code is finite.
-- Here code CALLS BLOCKS, each named by what it runs (`Key`):
--
--   * a closure's body (the `Lam` the run's closure value holds is its code
--     word), a fold of an algebra, an observation of a ν, and the copy and
--     the free of a type;
--   * a block's code is a FUNCTION of its key, polymorphic in the rest of
--     both stacks: compiled once, called from anywhere, in a frame of its
--     own (A16's `enter … leave`); a fold's block calls itself on each child;
--   * the values are the run's (`Events.MV`): a cell's code word is its
--     `Lam`, so copying or freeing a closure or a ν dispatches on what its
--     cell holds;
--   * the loop is a structured instruction over its round's finite code.
--
-- Finiteness — a program reaches finitely many keys (its subterms and their
-- types) — is B1.4b's, where the keys are numbered into labels.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; Σ; _,_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.Image
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_)

------------------------------------------------------------------------
-- 1. BLOCKS, NAMED BY WHAT THEY RUN.
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

data Key : BSig → Set where
  -- a closure's body: one-shot (it owns its environment beside the
  -- argument), many-use (it reads it lent)
  kbody1 : ∀ {Γ g X A B} → Defs Γ → (b : Tm Γ One (X ⊗t A) B) → Gd g b → Key (bsig nothing (X ⊗t A) B)
  kbodyω : ∀ {Γ g X A B} → Defs Γ → (b : Tm Γ X A B) → Gd g b → Key (bsig (just X) A B)
  -- a fold of an algebra: the node's cell freed, each child folded (the
  -- block calling itself), the algebra on the layer
  kfold  : ∀ {Γ} → Defs Γ → ∀ F {E A} → Tm Γ E (LF∙ F A) A → Key (bsig (just E) (μt F) A)
  -- a ν's observation: `obsT` on its coalgebra and seed
  kobs   : ∀ F S → Key (bsig nothing (Coalg F S ⊗t S) (LF∙ F (Nu F)))
  -- a COPY of the value the top view sees (`dup`'s, D403: deep), and the
  -- FREE of every cell of the operand (`drop`'s)
  kcopy  : ∀ A → Key (bsig (just A) One A)
  kfree  : ∀ A → Key (bsig nothing A One)

-- the block a closure's code word names
key-of : ∀ {k g X A B} → Lam k g X A B → Σ BSig Key
key-of (c1 ds b γ) = _ , kbody1 ds b γ
key-of (cω ds b γ) = _ , kbodyω ds b γ

------------------------------------------------------------------------
-- 2. THE INSTRUCTIONS: A16's, with calls in place of expansion.
------------------------------------------------------------------------

data Codeᴵ : Sh → Sh → Set
data Insᴵ : Sh → Sh → Set where
  unpair  : ∀ {Es A B S} → Insᴵ (Es ∣ (A ⊗t B) ∷ S) (Es ∣ A ∷ B ∷ S)
  pair    : ∀ {Es A B S} → Insᴵ (Es ∣ A ∷ B ∷ S) (Es ∣ (A ⊗t B) ∷ S)
  swap    : ∀ {Es A B S} → Insᴵ (Es ∣ A ∷ B ∷ S) (Es ∣ B ∷ A ∷ S)
  unit    : ∀ {Es S} → Insᴵ (Es ∣ S) (Es ∣ One ∷ S)
  -- a generator that touches at most one cell and calls nothing: one step
  prim    : ∀ {Γ} (ds : Defs Γ) {Es A B S} → LTm Γ A B → Insᴵ (Es ∣ A ∷ S) (Es ∣ B ∷ S)
  untag   : ∀ {Es l X A S} → Insᴵ (Es ∣ (Ct l X ⊗t A) ∷ S) (Es ∣ (X ⊗t A) ∷ S)
  untag₁  : ∀ {Es l X S} → Insᴵ (Es ∣ Ct l X ∷ S) (Es ∣ X ∷ S)
  tag₁    : ∀ {Es l X S} → Insᴵ (Es ∣ X ∷ S) (Es ∣ Ct l X ∷ S)
  -- the views (A16's); an owned operand lent and taken back (to copy it)
  elend   : ∀ {E Es X A S} → Insᴵ (E ∷ Es ∣ (X ⊗t A) ∷ S) ((E ⊗t X) ∷ E ∷ Es ∣ A ∷ S)
  eunlend : ∀ {E Es X B S} → Insᴵ ((E ⊗t X) ∷ E ∷ Es ∣ B ∷ S) (E ∷ Es ∣ (X ⊗t B) ∷ S)
  elift   : ∀ {Es S} → Insᴵ (Es ∣ S) (One ∷ Es ∣ S)
  efst    : ∀ {E₁ E₂ Es S} → Insᴵ ((E₁ ⊗t E₂) ∷ Es ∣ S) (E₁ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S)
  esnd    : ∀ {E₁ E₂ Es S} → Insᴵ ((E₁ ⊗t E₂) ∷ Es ∣ S) (E₂ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S)
  eout    : ∀ {F Es S} → Insᴵ (μt F ∷ Es ∣ S) (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S)
  eoutq   : ∀ {F Es S} → Insᴵ (μt F ∷ Es ∣ S) (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S)   -- no event: a copy's read
  eapp    : ∀ {l X Es S} → Insᴵ (Ct l X ∷ Es ∣ S) (X ∷ Ct l X ∷ Es ∣ S)
  epop    : ∀ {E Es S} → Insᴵ (E ∷ Es ∣ S) (Es ∣ S)
  epush   : ∀ {Es A S} → Insᴵ (Es ∣ A ∷ S) (A ∷ Es ∣ S)
  epull   : ∀ {Es A S} → Insᴵ (A ∷ Es ∣ S) (Es ∣ A ∷ S)
  eword   : ∀ {b Es S} → Insᴵ (Bt b ∷ Es ∣ One ∷ S) (Bt b ∷ Es ∣ Bt b ∷ S)
  -- ★ a CALL: a block, in a frame of its own, on the caller's environment
  call    : ∀ {σ Es S} → Key σ → Insᴵ (top σ ⊳ Es ∣ dom σ ∷ S) (top σ ⊳ Es ∣ cod σ ∷ S)
  -- ★ THROUGH A CELL'S CODE WORD: apply a one-shot closure (its cell freed),
  -- a lent many-use one (read), observe a ν (freed); copy a viewed closure
  -- or ν (what it holds, then a cell with the same code word); free one
  icall   : ∀ {Es g A B S} → Insᴵ (Es ∣ (Fn once g A B ⊗t A) ∷ S) (Es ∣ B ∷ S)
  icallω  : ∀ {Es g A B S} → Insᴵ (Fn many g A B ∷ Es ∣ A ∷ S) (Fn many g A B ∷ Es ∣ B ∷ S)
  iobs    : ∀ {Es F S} → Insᴵ (Es ∣ Nu F ∷ S) (Es ∣ LF∙ F (Nu F) ∷ S)
  ccopy   : ∀ {Es k g A B S} → Insᴵ (Fn k g A B ∷ Es ∣ One ∷ S) (Fn k g A B ∷ Es ∣ Fn k g A B ∷ S)
  ncopy   : ∀ {Es F S} → Insᴵ (Nu F ∷ Es ∣ One ∷ S) (Nu F ∷ Es ∣ Nu F ∷ S)
  cfree   : ∀ {Es k g A B S} → Insᴵ (Es ∣ Fn k g A B ∷ S) (Es ∣ One ∷ S)
  nfree   : ∀ {Es F S} → Insᴵ (Es ∣ Nu F ∷ S) (Es ∣ One ∷ S)
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
