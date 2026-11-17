-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Code — plan 0.146 A16 (D410): the model machine's SHAPES,
-- CONFIGURATIONS and CODE, and the lowering of a term to it (`comp`). D440:
-- at the target's numerics alone; how the machine steps and the simulation
-- are `Machine`'s.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}


open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (n∸n≡0)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Relation.Nullary using (yes; no)
open import Once.Spec.Numerics using (TargetNum)
open import Data.Sum using (inj₁; inj₂)
open import Once.LinCore.Flat using (Base; FTy)
open import Once.LinCore.Free

module Once.LinCore.Code
  (fmt : TargetNum)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Values fmt bw

------------------------------------------------------------------------
-- 1. THE MACHINE.
------------------------------------------------------------------------

-- a frame: one word (where to return), in a heap block of its own
fsz : ℕ
fsz = 1

-- the machine's shape: the environment's types and the operands'
infix 4 _∣_
record Sh : Set where
  constructor _∣_
  field env ops : List LTy

infixr 5 _∷ˢ_
data Stk : List LTy → Set where
  []ˢ  : Stk []
  _∷ˢ_ : ∀ {A S} → MV A → Stk S → Stk (A ∷ S)

-- the environment's slots (D410 amended): a VIEW, or a LEND's slot, whose
-- view is the pair of what was lent and the value `x` lent beside it, which
-- the slot owns until `eunlend` hands it back. Which slots are lends is the
-- lowering's (each `elend` is matched by an `eunlend` in the code); the tag is
-- kept here for the proof, and the machine reads only `see`
data Slots : List LTy → Set where
  []ᵉ : Slots []
  vw  : ∀ {E Es} → MV E → Slots Es → Slots (E ∷ Es)
  ln  : ∀ {E X Es} → MV E → MV X → Slots (E ∷ Es) → Slots ((E ⊗t X) ∷ E ∷ Es)

see : ∀ {E Es} → Slots (E ∷ Es) → MV E
see (vw e _)   = e
see (ln e x _) = mpair e x

infix 4 _∥_
record Cfg (sh : Sh) : Set where
  constructor _∥_
  field envs : Slots (Sh.env sh)
        opds : Stk (Sh.ops sh)

data Ins : Sh → Sh → Set where
  unpair  : ∀ {Es A B S} → Ins (Es ∣ (A ⊗t B) ∷ S) (Es ∣ A ∷ B ∷ S)
  pair    : ∀ {Es A B S} → Ins (Es ∣ A ∷ B ∷ S) (Es ∣ (A ⊗t B) ∷ S)
  swap    : ∀ {Es A B S} → Ins (Es ∣ A ∷ B ∷ S) (Es ∣ B ∷ A ∷ S)
  -- a generator with no control and no view of its own, as one step
  prim    : ∀ {Γ} (ds : Defs Γ) {Es A B S} → LTm Γ A B → Ins (Es ∣ A ∷ S) (Es ∣ B ∷ S)
  untag   : ∀ {Es l X A S} → Ins (Es ∣ (Ct l X ⊗t A) ∷ S) (Es ∣ (X ⊗t A) ∷ S)
  enter   : ∀ {sh} → Ins sh sh
  leave   : ∀ {sh} → Ins sh sh
  -- the views: lend (the lent view and the owned value beside it), nothing
  -- lent, a part, a node looked into (a read), a closure's environment; and
  -- a view's end
  elend   : ∀ {E Es X A S} → Ins (E ∷ Es ∣ (X ⊗t A) ∷ S) ((E ⊗t X) ∷ E ∷ Es ∣ A ∷ S)
  eunlend : ∀ {E Es X B S} → Ins ((E ⊗t X) ∷ E ∷ Es ∣ B ∷ S) (E ∷ Es ∣ (X ⊗t B) ∷ S)
  elift   : ∀ {Es S} → Ins (Es ∣ S) (One ∷ Es ∣ S)
  efst    : ∀ {E₁ E₂ Es S} → Ins ((E₁ ⊗t E₂) ∷ Es ∣ S) (E₁ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S)
  esnd    : ∀ {E₁ E₂ Es S} → Ins ((E₁ ⊗t E₂) ∷ Es ∣ S) (E₂ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S)
  eout    : ∀ {F Es S} → Ins (μt F ∷ Es ∣ S) (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S)
  eapp    : ∀ {l X Es S} → Ins (Ct l X ∷ Es ∣ S) (X ∷ Ct l X ∷ Es ∣ S)
  epop    : ∀ {E Es S} → Ins (E ∷ Es ∣ S) (Es ∣ S)
  ecopy   : ∀ {E Es S} → Ins (E ∷ Es ∣ One ∷ S) (E ∷ Es ∣ E ∷ S)
  -- ★ D409 part 3, AN INDIRECT CALL: apply the closure on the operands (one
  -- shot: free its cell), or the one the top view sees (many-use: read its
  -- cell); its code word says which body runs, decided by the data
  apply   : ∀ {Es g A B S} → Ins (Es ∣ (Fn once g A B ⊗t A) ∷ S) (Es ∣ B ∷ S)
  eapply  : ∀ {Es g A B S} → Ins (Fn many g A B ∷ Es ∣ A ∷ S) (Fn many g A B ∷ Es ∣ B ∷ S)
  -- ★ observe a ν: free its cell, run `obsT` on its coalgebra and seed
  -- (expanded when reached: the seed's type is the cell's)
  nopen   : ∀ {Γ} (ds : Defs Γ) {F Es S} → Ins (Es ∣ Nu F ∷ S) (Es ∣ LF∙ F (Nu F) ∷ S)
  -- a fold's node, a loop's round: expanded when reached
  fold    : ∀ {Γ} (ds : Defs Γ) F {E A Es S} → Tm Γ E (LF∙ F A) A → Ins (E ∷ Es ∣ μt F ∷ S) (E ∷ Es ∣ A ∷ S)
  loop    : ∀ {Γ} (ds : Defs Γ) {E A B Es S} → Tm Γ E A (B ⊕t A) → Ins (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ B ∷ S)
  stuck   : ∀ {sh sh′} → Ins sh sh′

infixr 5 _⨾_
data Code : Sh → Sh → Set where
  end    : ∀ {sh} → Code sh sh
  _⨾_    : ∀ {sh sh′ T} → Ins sh sh′ → Code sh′ T → Code sh T
  case   : ∀ {Es A B S T} → Code (Es ∣ A ∷ S) T → Code (Es ∣ B ∷ S) T → Code (Es ∣ (A ⊕t B) ∷ S) T
  ecase  : ∀ {E₁ E₂ Es S T} → Code (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) T → Code (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) T
         → Code ((E₁ ⊕t E₂) ∷ Es ∣ S) T
  halted : ∀ {sh T} → Code sh T

------------------------------------------------------------------------
-- 2. THE LOWERING, in front of the code that follows.
------------------------------------------------------------------------

mutual
  comp : ∀ {Γ} (ds : Defs Γ) {E A B} → Tm Γ E A B → ∀ {Es S T} → Code (E ∷ Es ∣ B ∷ S) T → Code (E ∷ Es ∣ A ∷ S) T
  comp ds lid k            = k
  comp ds (f ∘l g) k       = comp ds g (comp ds f k)
  comp ds (f ⊗l g) k       = unpair ⨾ comp ds f (swap ⨾ comp ds g (swap ⨾ pair ⨾ k))
  comp ds (lcase f g) k    = case (comp ds f k) (comp ds g k)
  comp ds (lcata F alg) k  = fold ds F alg ⨾ k
  comp ds (liter f φ) k      = loop ds f ⨾ k
  comp ds (lapp p) k       = untag ⨾ enter ⨾ elift ⨾ body ds p (epop ⨾ leave ⨾ k)
  comp ds (lend b) k       = elend ⨾ comp ds b (eunlend ⨾ k)
  comp ds (blift f) k      = elift ⨾ comp ds f (epop ⨾ k)
  comp ds (bfst f) k       = efst ⨾ comp ds f (epop ⨾ k)
  comp ds (bsnd f) k       = esnd ⨾ comp ds f (epop ⨾ k)
  comp ds (bcaseE f g) k   = ecase (comp ds f (epop ⨾ k)) (comp ds g (epop ⨾ k))
  comp ds (bout f) k       = eout ⨾ comp ds f (epop ⨾ k)
  comp ds bcopy k          = ecopy ⨾ k
  comp ds (bapp p) k       = eapp ⨾ enter ⨾ bodyω ds p (leave ⨾ epop ⨾ k)
  comp ds ρl k             = prim ds ρl ⨾ k
  comp ds ρl⁻ k            = prim ds ρl⁻ ⨾ k
  comp ds lul k            = prim ds lul ⨾ k
  comp ds lul⁻ k           = prim ds lul⁻ ⨾ k
  comp ds lassoc k         = prim ds lassoc ⨾ k
  comp ds lassoc⁻ k        = prim ds lassoc⁻ ⨾ k
  comp ds lswap k          = prim ds lswap ⨾ k
  comp ds dup k            = prim ds dup ⨾ k
  comp ds drop k           = prim ds drop ⨾ k
  comp ds linl k           = prim ds linl ⨾ k
  comp ds linr k           = prim ds linr ⨾ k
  comp ds lIn k            = prim ds lIn ⨾ k
  comp ds lOutμ k          = prim ds lOutμ ⨾ k
  comp ds (lclo F p) k     = prim ds (lclo F p) ⨾ k
  comp ds (lconst v) k     = prim ds (lconst v) ⨾ k
  comp ds (lop s) k        = prim ds (lop s) ⨾ k
  comp ds lzero k          = stuck ⨾ k
  comp ds (llam b γ) k     = prim ds (llam b γ) ⨾ k
  comp ds (llamω b γ) k    = prim ds (llamω b γ) ⨾ k
  comp ds lev k            = apply ⨾ k
  comp ds bev k            = eapply ⨾ k
  comp ds lunf k           = prim ds lunf ⨾ k
  comp ds lout k           = nopen ds ⨾ k

  -- a one-shot label's body (nothing lent), compiled in place over its prefix
  body : ∀ {Γ l g X A B} (ds : Defs Γ) → Γ ∋[ l ] sg once g X A B → ∀ {Es S T}
       → Code (One ∷ Es ∣ B ∷ S) T → Code (One ∷ Es ∣ (X ⊗t A) ∷ S) T
  body (ds ▸ _)    (there p) k = body ds p k
  body (ds ▸ b1 b _) here      k = comp ds b k

  -- a many-use label's body (its environment lent)
  bodyω : ∀ {Γ l g X A B} (ds : Defs Γ) → Γ ∋[ l ] sg many g X A B → ∀ {Es S T}
        → Code (X ∷ Es ∣ B ∷ S) T → Code (X ∷ Es ∣ A ∷ S) T
  bodyω (ds ▸ _)    (there p) k = bodyω ds p k
  bodyω (ds ▸ bω b _) here      k = comp ds b k

-- a fold's node: its children folded in order, the layer rebuilt
trav : ∀ {Γ} (ds : Defs Γ) F {E A} (alg : Tm Γ E (LF∙ F A) A) G → ∀ {Es S T}
     → Code (E ∷ Es ∣ LF∙ G A ∷ S) T → Code (E ∷ Es ∣ LF∙ G (μt F) ∷ S) T
trav ds F alg Idf      k = fold ds F alg ⨾ k
trav ds F alg Kone     k = k
trav ds F alg Kzero    k = k
trav ds F alg (Kb _)   k = k
trav ds F alg (Kμ _)   k = k
trav ds F alg (G ⊕f H) k = case (trav ds F alg G (prim ε linl ⨾ k)) (trav ds F alg H (prim ε linr ⨾ k))
trav ds F alg (G ⊗f H) k = unpair ⨾ trav ds F alg G (swap ⨾ trav ds F alg H (swap ⨾ pair ⨾ k))
