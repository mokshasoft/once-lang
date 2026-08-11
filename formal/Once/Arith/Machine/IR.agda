-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Machine.IR
--
-- Plan 0.20 — D-arith-3 / D-arith-1: the *positional* arith IR
-- carried by `ArithBlock`. Variable references are `InputPath`s into
-- the block's input tree, not source-level names. This is what
-- compile-abs (Phase C) consumes and what `eval-arith-block` (the
-- denotational ground truth) is defined over.
--
-- Distinct from `Once.Arith.IR` (`ArithIR Γ τ`), which is the
-- typed-context version OCP-0001 ships. The two coexist for now;
-- a cleanup plan removes one once recognition + codegen stabilise.
------------------------------------------------------------------------

module Once.Arith.Machine.IR where

open import Data.Integer using (ℤ; +_; ∣_∣; sign; _◃_)
import Data.Integer as ℤ
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as ℕ
import Data.Sign as Sign

open import Once.Type using (Type; Unit; Int)
import Once.Type as T
open import Once.Arith.Machine.Shape
  using (InputShape; shape-unit; shape-int; shape-pair; ⟦_⟧S; InputPath;
         Side; Fst; Snd; project)

------------------------------------------------------------------------
-- MArithIR: machine-level arith expression tree
------------------------------------------------------------------------

-- | A pure arith expression at the result type `Int`, indexed by
-- the block's input shape so projections can be evaluated.
--
-- Plan 0.20 — mono-Int. Comparison ops / Bool returns and other
-- widths are out of scope per the plan's Scope section.
data MArithIR (sh : InputShape) : Set where
  alit       : ℤ → MArithIR sh
  ainput     : InputPath → MArithIR sh
  aadd       : MArithIR sh → MArithIR sh → MArithIR sh
  asub       : MArithIR sh → MArithIR sh → MArithIR sh
  amul       : MArithIR sh → MArithIR sh → MArithIR sh
  adiv       : MArithIR sh → MArithIR sh → MArithIR sh
  amod       : MArithIR sh → MArithIR sh → MArithIR sh
  aneg       : MArithIR sh → MArithIR sh

------------------------------------------------------------------------
-- Denotational semantics
------------------------------------------------------------------------

-- | Evaluate an MArithIR against an input value.
--
-- An `ainput` whose path doesn't land on an Int leaf evaluates to 0
-- as a default. Recognition (Phase B) only produces well-formed
-- paths; the validity theorem (Phase C) restates this so the default
-- never fires in practice.
-- Spec-level (ℤ) truncated-toward-zero signed div/rem. This ℤ evaluator
-- is a legacy artifact (the machine-faithful meaning is `eval-arith-W`
-- over `Word`, with the D055 total sentinels); here we keep it TOTAL by
-- the same policy: a zero divisor gives `0` (div) / the dividend (rem).
private
  divℤ modℤ : ℤ → ℤ → ℤ
  divℤ a (+ zero)     = + 0
  divℤ a (+ suc d)    = (sign a Sign.* Sign.+) ◃ (∣ a ∣ ℕ./ suc d)
  divℤ a (ℤ.-[1+ d ]) = (sign a Sign.* Sign.-) ◃ (∣ a ∣ ℕ./ suc d)
  modℤ a (+ zero)     = a
  modℤ a (+ suc d)    = sign a ◃ (∣ a ∣ ℕ.% suc d)
  modℤ a (ℤ.-[1+ d ]) = sign a ◃ (∣ a ∣ ℕ.% suc d)

eval-arith : ∀ {sh} → MArithIR sh → ⟦ sh ⟧S → ℤ
eval-arith {sh} (alit z)     _   = z
eval-arith {sh} (ainput p)   inp with project sh p inp
... | just z   = z
... | nothing  = + 0
eval-arith (aadd a b) inp = eval-arith a inp ℤ.+ eval-arith b inp
eval-arith (asub a b) inp = eval-arith a inp ℤ.- eval-arith b inp
eval-arith (amul a b) inp = eval-arith a inp ℤ.* eval-arith b inp
eval-arith (adiv a b) inp = divℤ (eval-arith a inp) (eval-arith b inp)
eval-arith (amod a b) inp = modℤ (eval-arith a inp) (eval-arith b inp)
eval-arith (aneg a)   inp = ℤ.- eval-arith a inp

-- (The machine-level modular-`Word` evaluator `eval-arith-W` is now in
-- the width-parameterised `Once.Arith.Machine.WordSem`, so this module
-- and `ArithBlock` stay width-agnostic — D054 width is the arch's choice.)

------------------------------------------------------------------------
-- Shape ↔ CCC Type bridge
------------------------------------------------------------------------

-- | Mapping from `InputShape` to the corresponding CCC `Type`.
-- Used at the boundary so a `MArithIR sh` corresponds to a CCC
-- morphism `IR (shape-as-type sh) Int`.
shape-as-type : InputShape → Type
shape-as-type shape-unit       = Unit
shape-as-type shape-int        = Int
shape-as-type (shape-pair l r) = shape-as-type l T.* shape-as-type r

------------------------------------------------------------------------
-- ArithBlock: the package recognition produces
------------------------------------------------------------------------

-- | An arith block extracted from a larger CCC IR.
--
-- Carries the block's input shape and the recognised body. The
-- block's CCC-level type is `IR (shape-as-type block-shape) Int`;
-- the boundary (Phase E) wraps this as a `SigOp arith.block.<digest>`.
record ArithBlock : Set where
  constructor mk-block
  field
    block-shape : InputShape
    block-body  : MArithIR block-shape

------------------------------------------------------------------------
-- Counts (for register allocation, Phase F)
------------------------------------------------------------------------

-- | Number of leaves (literals + input projections). Sethi–Ullman's
-- starting estimate for the register budget.
leaf-count : ∀ {sh} → MArithIR sh → ℕ
leaf-count (alit _)     = 1
leaf-count (ainput _)   = 1
leaf-count (aadd a b)   = leaf-count a ℕ.+ leaf-count b
leaf-count (asub a b)   = leaf-count a ℕ.+ leaf-count b
leaf-count (amul a b)   = leaf-count a ℕ.+ leaf-count b
leaf-count (adiv a b)   = leaf-count a ℕ.+ leaf-count b
leaf-count (amod a b)   = leaf-count a ℕ.+ leaf-count b
leaf-count (aneg a)     = leaf-count a
