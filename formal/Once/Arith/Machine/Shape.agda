-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Machine.Shape
--
-- The WIDTH-AGNOSTIC core of the arith-block machine: the input-shape
-- tree, its ℤ-spec interpretation `⟦_⟧S`, and positional `InputPath`s.
--
-- Split out of `Once.Arith.Machine.AbsState` (clean-semantics L1 step a)
-- so the width-bearing abstract state can be parameterised by `bits`
-- (D054 `Word` width) WITHOUT dragging the width into `MArithIR` /
-- `ArithBlock` — which `Once.Compile` / `Once.Target` consume
-- width-agnostically. Nothing here mentions `Word`.
------------------------------------------------------------------------

module Once.Arith.Machine.Shape where

open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)

------------------------------------------------------------------------
-- InputShape: tree-shape of an arith block's input
--
-- Plan 0.20 Phase G: shape-unit added so closed arith expressions
-- (`exit (3 + 5*2)`) — whose CCC type is `IR Unit Int` — can be
-- lifted into a block. With shape-int / shape-pair only, recognition
-- could never produce a SigOpInfo whose A matched Unit.
------------------------------------------------------------------------

data InputShape : Set where
  shape-unit  : InputShape
  shape-int   : InputShape
  -- PLAN 0.75 F4: a FLOAT leaf. Its spec value is the target's BIT PATTERN,
  -- not an exact number — D113 removed the exact value level from `Float`
  -- exactly as D054 removed it from `Int`, so there is nothing else it could
  -- be. That is why this leaf is `ℕ` where the `Int` leaf is `ℤ`: the `Int`
  -- leaf still carries a spec-level integer that `fromℤ` narrows to a `Word`,
  -- and a float has no such intermediate.
  shape-float : InputShape
  shape-pair  : InputShape → InputShape → InputShape

⟦_⟧S : InputShape → Set
⟦ shape-unit      ⟧S = ⊤
⟦ shape-int       ⟧S = ℤ
⟦ shape-float     ⟧S = ℕ
⟦ shape-pair l r  ⟧S = ⟦ l ⟧S × ⟦ r ⟧S

------------------------------------------------------------------------
-- InputPath
------------------------------------------------------------------------

data Side : Set where
  Fst : Side
  Snd : Side

InputPath : Set
InputPath = List Side

-- | Project an `Int` leaf. A path that lands anywhere else — including on a
-- FLOAT leaf — is `nothing`, and the caller defaults. Recognition only ever
-- builds paths that land correctly; the validity theorem restates that, so the
-- default never fires in practice.
project : ∀ (sh : InputShape) → InputPath → ⟦ sh ⟧S → Maybe ℤ
project shape-unit       _        _       = nothing
project shape-int        []       z       = just z
project shape-int        (_ ∷ _)  _       = nothing
project shape-float      _        _       = nothing
project (shape-pair _ _) []       _       = nothing
project (shape-pair l _) (Fst ∷ p) (x , _) = project l p x
project (shape-pair _ r) (Snd ∷ p) (_ , y) = project r p y

-- | …and its FLOAT twin (plan 0.75 F4). Two projections rather than one
-- returning a sum: the leaf types are different Agda types, and a caller
-- always knows which it wants — the `MArithIR` node it is evaluating is
-- indexed by the `NumType`.
projectF : ∀ (sh : InputShape) → InputPath → ⟦ sh ⟧S → Maybe ℕ
projectF shape-unit       _        _       = nothing
projectF shape-int        _        _       = nothing
projectF shape-float      []       w       = just w
projectF shape-float      (_ ∷ _)  _       = nothing
projectF (shape-pair _ _) []       _       = nothing
projectF (shape-pair l _) (Fst ∷ p) (x , _) = projectF l p x
projectF (shape-pair _ r) (Snd ∷ p) (_ , y) = projectF r p y
