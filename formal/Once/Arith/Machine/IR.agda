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
open import Once.Arith.CmpOp using (CmpOp; c-lt; c-le; c-gt; c-ge; c-eq; c-ne)
open import Data.Bool using (Bool; not; _∧_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as ℕ
import Data.Sign as Sign

open import Once.Spec.Type using (Type; Unit; Int)
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Spec.Float.Decimal using (Decimal)
import Once.Type.Core as T
import Once.Spec.Type as T
import Once.Type as T
open import Once.Arith.Machine.Shape
  using (InputShape; shape-unit; shape-int; shape-float; shape-pair; ⟦_⟧S; Path; readLeaf)

------------------------------------------------------------------------
-- MArithIR: machine-level arith expression tree
------------------------------------------------------------------------

-- | A pure arith expression at the result type `Int`, indexed by
-- the block's input shape so projections can be evaluated.
--
-- Plan 0.20 — mono-Int. Comparison ops / Bool returns and other
-- widths are out of scope per the plan's Scope section.
data MArithIR (sh : InputShape) : NumType → Set where
  alit       : ℤ → MArithIR sh NInt
  -- PLAN 0.75 F4: a FLOAT literal's payload is the `Decimal` the programmer
  -- wrote (D117), not a pattern — the ONE rounding happens at the backend, at
  -- the target's format, and putting a pattern here would move it earlier and
  -- cap precision at whatever format this node chose.
  aflit      : Decimal → MArithIR sh NFloat
  -- The path is TYPED (`Path sh n`): it lands on an `n` leaf by construction.
  -- Untyped, this node could read a float leaf as an `Int`, and the abstract
  -- machine had to invent `0` for that — a value for a case that should not
  -- exist, and the reason the float-argument correspondence was a postulate.
  -- The evidence travels with the path instead, so `readLeaf` is total.
  ainput     : ∀ {n} → Path sh n → MArithIR sh n
  -- `+`, `−` and `×` are POLYMORPHIC in the number kind — one constructor
  -- each, dispatched by the index. That is the whole reason `NumType` exists
  -- (`NInt | NFloat`, width-free): the emitter reads the index to choose
  -- `addq` or `addsd`, and every proof that recurses structurally keeps
  -- working with `n` implicit.
  aadd       : ∀ {n} → MArithIR sh n → MArithIR sh n → MArithIR sh n
  asub       : ∀ {n} → MArithIR sh n → MArithIR sh n → MArithIR sh n
  amul       : ∀ {n} → MArithIR sh n → MArithIR sh n → MArithIR sh n
  -- `/` joins them: `Once.Spec.Float.Arith.fdiv` is the correctly-rounded quotient
  -- (the sticky bit through the division), pinned against the machine on both
  -- formats, so a float `adiv` now has a meaning to denote.
  adiv       : ∀ {n} → MArithIR sh n → MArithIR sh n → MArithIR sh n
  -- `%` stays `Int`-ONLY, and that IS still principled: IEEE's `fmod` is a
  -- different function from integer remainder, and D055's identity
  -- `a = (a/b)*b + (a%b)` does not survive rounding. It needs its own decision
  -- before it can have a node. `isFloatArithmeticOp` refuses it at the source,
  -- so no well-typed program reaches a float `amod`.
  amod       : MArithIR sh NInt → MArithIR sh NInt → MArithIR sh NInt
  aneg       : ∀ {n} → MArithIR sh n → MArithIR sh n
  -- D125's widening, as a node: `1 + 1.5` puts one of these on the `Int` side.
  ai2f       : MArithIR sh NInt → MArithIR sh NFloat
  -- plan 0.108: a COMPARISON, as a 0/1 word — the tag of the `Bool` the
  -- comparison SigOp means (true = inr = 1, D263). Int operands only.
  acmp       : CmpOp → MArithIR sh NInt → MArithIR sh NInt → MArithIR sh NInt

------------------------------------------------------------------------
-- Denotational semantics
------------------------------------------------------------------------

-- (D391: the legacy ℤ evaluator `eval-arith` is gone — `Int` is a word (D054),
-- the block's input leaves are words, and the meaning is `eval-arith-W`.)

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
shape-as-type shape-float      = T.Float
shape-as-type (shape-pair l r) = shape-as-type l T.* shape-as-type r

-- | …and the RESULT kind's `Type` (plan 0.75 F4). A block used to be
-- `IR (shape-as-type sh) Int` with the codomain fixed; now the codomain is
-- whichever number kind the body computes.
numtype-as-type : NumType → Type
numtype-as-type NInt   = Int
numtype-as-type NFloat = T.Float

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
    -- PLAN 0.75 F4: which number kind the block RETURNS. The body is indexed
    -- by it, so a block is self-describing about whether the backend should
    -- emit integer or float instructions — the emitter never has to re-derive
    -- it from the CCC type.
    block-kind  : NumType
    block-body  : MArithIR block-shape block-kind

------------------------------------------------------------------------
-- Counts (for register allocation, Phase F)
------------------------------------------------------------------------

-- | Number of leaves (literals + input projections). Sethi–Ullman's
-- starting estimate for the register budget.
-- Kind-POLYMORPHIC: register pressure is about the tree's shape, not about
-- which register file the values live in. `ai2f` is a leaf-preserving unary
-- node like `aneg`.
leaf-count : ∀ {sh n} → MArithIR sh n → ℕ
leaf-count (alit _)     = 1
leaf-count (aflit _)    = 1
leaf-count (ainput _)   = 1
leaf-count (aadd a b)   = leaf-count a ℕ.+ leaf-count b
leaf-count (asub a b)   = leaf-count a ℕ.+ leaf-count b
leaf-count (amul a b)   = leaf-count a ℕ.+ leaf-count b
leaf-count (adiv a b)   = leaf-count a ℕ.+ leaf-count b
leaf-count (amod a b)   = leaf-count a ℕ.+ leaf-count b
leaf-count (aneg a)     = leaf-count a
leaf-count (ai2f a)     = leaf-count a
leaf-count (acmp _ a b) = leaf-count a ℕ.+ leaf-count b
