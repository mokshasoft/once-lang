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
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Float.Decimal using (Decimal)
import Once.Type as T
open import Once.Arith.Machine.Shape
  using (InputShape; shape-unit; shape-int; shape-float; shape-pair; ⟦_⟧S; InputPath;
         Side; Fst; Snd; project; projectF)

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
  ainput     : ∀ {n} → InputPath → MArithIR sh n
  -- `+`, `−` and `×` are POLYMORPHIC in the number kind — one constructor
  -- each, dispatched by the index. That is the whole reason `NumType` exists
  -- (`NInt | NFloat`, width-free): the emitter reads the index to choose
  -- `addq` or `addsd`, and every proof that recurses structurally keeps
  -- working with `n` implicit.
  aadd       : ∀ {n} → MArithIR sh n → MArithIR sh n → MArithIR sh n
  asub       : ∀ {n} → MArithIR sh n → MArithIR sh n → MArithIR sh n
  amul       : ∀ {n} → MArithIR sh n → MArithIR sh n → MArithIR sh n
  -- …but `/` and `%` are `Int`-ONLY, and that is not an oversight: float
  -- division needs a correctly-rounded quotient (a sticky bit through the
  -- division) and IEEE's `fmod` is a different function from integer
  -- remainder. `isFloatArithmeticOp` refuses both at the source, so no
  -- well-typed program can reach a float node here.
  adiv       : MArithIR sh NInt → MArithIR sh NInt → MArithIR sh NInt
  amod       : MArithIR sh NInt → MArithIR sh NInt → MArithIR sh NInt
  aneg       : ∀ {n} → MArithIR sh n → MArithIR sh n
  -- D125's widening, as a node: `1 + 1.5` puts one of these on the `Int` side.
  ai2f       : MArithIR sh NInt → MArithIR sh NFloat

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

-- PLAN 0.75 F4: STATED AT `NInt`, and that is the honest restriction rather
-- than a gap. This is the legacy ℤ evaluator, and there is no ℤ spec for a
-- float to have — D113 removed the exact value level from `Float` exactly as
-- D054 removed it from `Int`, so a float's meaning needs a FORMAT and lives in
-- `WordSem` with the rest of the target-relative semantics. Every clause below
-- is unchanged: an `NInt` tree cannot contain `aflit` or `ai2f`, so the index
-- does the restricting and no case analysis is added.
eval-arith : ∀ {sh} → MArithIR sh NInt → ⟦ sh ⟧S → ℤ
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
