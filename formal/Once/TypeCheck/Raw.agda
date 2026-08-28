-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Raw
--
-- Raw (untyped) syntax for Once programs.
-- Mirrors compiler/src/Once/Syntax.hs with named variables.
--
-- Part of OCP-0003: Verified Type Checker
------------------------------------------------------------------------

module Once.TypeCheck.Raw where

open import Data.String using (String)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Once.Type using (Type; Functor)
open import Once.CanonicalName using (CanonicalName)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Binary Operators (OCP-0002)
------------------------------------------------------------------------

-- | Binary operators for infix syntax
-- Mirrors Once.Syntax.BinOp from Haskell
data BinOp : Set where
  -- Arithmetic operators
  OpAdd : BinOp    -- a + b
  OpSub : BinOp    -- a - b
  OpMul : BinOp    -- a * b
  OpDiv : BinOp    -- a / b
  OpMod : BinOp    -- a % b
  -- Comparison operators
  OpLt  : BinOp    -- a < b
  OpLe  : BinOp    -- a <= b
  OpGt  : BinOp    -- a > b
  OpGe  : BinOp    -- a >= b
  OpEq  : BinOp    -- a == b
  OpNe  : BinOp    -- a != b

------------------------------------------------------------------------
-- Unary Operators
------------------------------------------------------------------------

-- | Unary operators
-- Mirrors Once.Syntax.UnaryOp from Haskell
data UnaryOp : Set where
  OpNeg : UnaryOp  -- -x

------------------------------------------------------------------------
-- Raw Expressions
------------------------------------------------------------------------

-- | Raw expressions with named variables
-- Mirrors Once.Syntax.Expr from Haskell
--
-- These are the expressions produced by the parser, before
-- type checking converts them to well-typed intrinsic terms.
data RawExpr : Set where
  -- Variable reference
  RVar      : String → RawExpr

  -- Qualified variable reference: name@alias (e.g., exit0@S)
  -- First String is the name, second is the module alias
  RQualified : String → String → RawExpr

  -- Plan 0.50: a qualified ref RESOLVED to its canonical identity. The parser
  -- emits `RQualified name alias`; `canon` (resolveImports) resolves alias→path
  -- and rewrites it to `RResolved (canonical (path ++ [name]))`, so by typecheck
  -- time the reference carries its clash-free canonical name directly.
  RResolved : CanonicalName → RawExpr

  -- Function application
  RApp      : RawExpr → RawExpr → RawExpr

  -- Lambda abstraction: λx. body
  RLam      : String → RawExpr → RawExpr

  -- Let binding: let x = e1 in e2
  RLet      : String → RawExpr → RawExpr → RawExpr

  -- Pair introduction: (e1, e2)
  RPair     : RawExpr → RawExpr → RawExpr

  -- Sum elimination: destruct e | x -> e1 | y -> e2
  -- First branch handles inl (Left), second handles inr (Right)
  RDestruct : RawExpr → String → RawExpr → String → RawExpr → RawExpr

  -- Unit value: ()
  RUnit     : RawExpr

  -- Integer literal
  RInt      : ℤ → RawExpr

  -- Plan 0.71: float literal, carried as the DECIMAL the lexer read — integer
  -- part, fraction digits, fraction length — exactly as `Token.TFloat` does.
  -- Not a dyadic value and not an `AgdaFloat`: this is RAW syntax, and the
  -- conversion is a CHECKING-time judgement (F4/F5), because a literal that is
  -- not exactly representable at every target width must produce a type ERROR
  -- rather than a rounded value. Deciding that here would put the check on the
  -- parse path, where there is no way to report it.
  -- PLAN 0.74 (positions): int part, fraction digits, fraction length, and
  -- the literal's SOURCE OFFSET. The offset is diagnostic metadata — the
  -- elaborator drops it, so it never reaches `Surface.Expr`, the IR, the
  -- machine or any correspondence proof. `Once.Warnings` is its only consumer.
  RFloat    : ℕ → ℕ → ℕ → ℕ → RawExpr

  -- String literal
  RStringLit : String → RawExpr

  -- Type annotation: (e : T)
  RAnnot    : RawExpr → Type → RawExpr

  -- Binary operator application (OCP-0002)
  RBinOp    : BinOp → RawExpr → RawExpr → RawExpr

  -- Unary operator application (OCP-0002)
  RUnaryOp  : UnaryOp → RawExpr → RawExpr

  -- Anamorphism (the corecursive unfold) carrying its functor `F`. Unlike `cata`
  -- (whose μ-value self-marks recursion with `Vin`, so the untyped fold finds the
  -- recursive positions), `ana`'s coalgebra output `F(A)` has UNMARKED seeds — so
  -- the untyped operational unfold needs `F` to know where to recurse. The
  -- elaboration erases `ana wfF coalg` to `RAna F (erase coalg)`. (Internal: not
  -- yet surface-parseable; the parser never produces it.)
  RAna      : Functor → RawExpr → RawExpr

------------------------------------------------------------------------
-- Raw Types (with type variable names)
------------------------------------------------------------------------

-- | Raw surface types
-- Mirrors Once.Syntax.SType from Haskell
-- Used for type annotations before resolution
data RawType : Set where
  RTVar     : String → RawType              -- Type variable: A
  RTUnit    : RawType                       -- Unit
  RTVoid    : RawType                       -- Void
  RTInt     : RawType                       -- Int
  RTFloat   : RawType                       -- Float
  RTBuffer  : RawType                       -- Buffer
  RTStr     : RawType                       -- String
  RTProduct : RawType → RawType → RawType   -- A * B
  RTSum     : RawType → RawType → RawType   -- A + B
  RTArrow   : RawType → RawType → RawType   -- A -> B
  RTEff     : RawType → RawType → RawType   -- Eff A B
  RTFix     : RawType → RawType             -- Fix F

------------------------------------------------------------------------
-- Utility: Operator result type classification
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false)

-- | Is this a comparison operator?
-- Comparison operators return Bool (encoded as Unit + Unit)
isComparisonOp : BinOp → Bool
isComparisonOp OpLt  = true
isComparisonOp OpLe  = true
isComparisonOp OpGt  = true
isComparisonOp OpGe  = true
isComparisonOp OpEq  = true
isComparisonOp OpNe  = true
isComparisonOp OpAdd = false
isComparisonOp OpSub = false
isComparisonOp OpMul = false
isComparisonOp OpDiv = false
isComparisonOp OpMod = false

-- | Is this an arithmetic operator?
-- | The FLOAT arithmetic operators (plan 0.75 F4).
--
-- NOT `isArithmeticOp`. `/` and `%` are missing on purpose and for different
-- reasons, both recorded in `Once.Float.Arith`:
--
--   * `/` — a quotient is not a binary rational, so one rounding at the end is
--     not correct rounding; doing it right needs a sticky bit through the
--     division and doing it wrong means silently differing from the hardware.
--     `Int`'s own `div-semM` is still a postulate, so a float `/` built the
--     easy way would be WORSE than its integer twin, not equal to it.
--   * `%` — IEEE's `fmod` is a different function from integer remainder, and
--     inventing one silently is not something this compiler does.
--
-- Both stay TYPE ERRORS, which is the honest state: a rule with no lowering is
-- a promise the backend has to break (D124).
isFloatArithmeticOp : BinOp → Bool
isFloatArithmeticOp OpAdd = true
isFloatArithmeticOp OpSub = true
isFloatArithmeticOp OpMul = true
isFloatArithmeticOp OpDiv = false
isFloatArithmeticOp OpMod = false
isFloatArithmeticOp OpLt  = false
isFloatArithmeticOp OpLe  = false
isFloatArithmeticOp OpGt  = false
isFloatArithmeticOp OpGe  = false
isFloatArithmeticOp OpEq  = false
isFloatArithmeticOp OpNe  = false

isArithmeticOp : BinOp → Bool
isArithmeticOp OpAdd = true
isArithmeticOp OpSub = true
isArithmeticOp OpMul = true
isArithmeticOp OpDiv = true
isArithmeticOp OpMod = true
isArithmeticOp OpLt  = false
isArithmeticOp OpLe  = false
isArithmeticOp OpGt  = false
isArithmeticOp OpGe  = false
isArithmeticOp OpEq  = false
isArithmeticOp OpNe  = false
------------------------------------------------------------------------
-- D126: the closed-expression lift's side condition
------------------------------------------------------------------------

-- | The shapes with NO check-mode rule of their own — the ones whose
-- check-mode elaboration falls through to infer-then-embed.
--
-- This is the classic bidirectional side condition ("the subsumption rule
-- applies only to non-introduction forms"), written out. Without it D126
-- would be derivable for `λx. body` too, and then two DIFFERENT check-mode
-- derivations — `t-lam` and the lift — would give the same expression two
-- different meanings at the same type. The elaborator resolves that in favour
-- of `t-lam`, so the judgment must not claim the other.
--
-- The check-DIRECTED shapes left out, and where each is already served:
--   * `RLam`            — `t-lam` (and it has no infer rule at all).
--   * `RInt` / `RFloat` / `- <literal>`
--                       — the older value-lift (D018/D041/D124), which gives
--                         these the same constant morphism by another route.
--   * `RPair`           — `checkPairLit`, and closed pairs by `g-pair`.
--   * `RApp`            — head-directed (`In`/`inl`/`inr`/`apply`/the morphism
--                         combinators). A lift for ordinary applications would
--                         need the head view as a further premise; not done.
data ClosedLiftShape : RawExpr → Set where
  cls-var    : ∀ {x}         → ClosedLiftShape (RVar x)
  cls-qual   : ∀ {n a}       → ClosedLiftShape (RQualified n a)
  cls-res    : ∀ {cn}        → ClosedLiftShape (RResolved cn)
  cls-let    : ∀ {x e₁ e₂}   → ClosedLiftShape (RLet x e₁ e₂)
  cls-destr  : ∀ {s x eL y eR} → ClosedLiftShape (RDestruct s x eL y eR)
  cls-unit   :                 ClosedLiftShape RUnit
  cls-str    : ∀ {s}         → ClosedLiftShape (RStringLit s)
  cls-annot  : ∀ {e T}       → ClosedLiftShape (RAnnot e T)
  cls-binop  : ∀ {op a b}    → ClosedLiftShape (RBinOp op a b)

-- | Decides it. The elaborator calls this on the expression it is checking, so
-- the rule's side condition is discharged by the elaborator itself.
closedLiftShape? : ∀ (e : RawExpr) → Maybe (ClosedLiftShape e)
closedLiftShape? (RVar _)              = just cls-var
closedLiftShape? (RQualified _ _)      = just cls-qual
closedLiftShape? (RResolved _)         = just cls-res
closedLiftShape? (RLet _ _ _)          = just cls-let
closedLiftShape? (RDestruct _ _ _ _ _) = just cls-destr
closedLiftShape? RUnit                 = just cls-unit
closedLiftShape? (RStringLit _)        = just cls-str
closedLiftShape? (RAnnot _ _)          = just cls-annot
closedLiftShape? (RBinOp _ _ _)        = just cls-binop
closedLiftShape? (RApp _ _)            = nothing
closedLiftShape? (RLam _ _)            = nothing
closedLiftShape? (RPair _ _)           = nothing
closedLiftShape? (RInt _)              = nothing
closedLiftShape? (RFloat _ _ _ _)      = nothing
closedLiftShape? (RUnaryOp _ _)        = nothing
closedLiftShape? (RAna _ _)            = nothing

-- | …and agrees with the witness, which is what makes the elaborator's
-- dispatch reduce in the completeness proof.
closedLiftShape?-just : ∀ {e : RawExpr} (c : ClosedLiftShape e)
                      → closedLiftShape? e ≡ just c
closedLiftShape?-just cls-var   = refl
closedLiftShape?-just cls-qual  = refl
closedLiftShape?-just cls-res   = refl
closedLiftShape?-just cls-let   = refl
closedLiftShape?-just cls-destr = refl
closedLiftShape?-just cls-unit  = refl
closedLiftShape?-just cls-str   = refl
closedLiftShape?-just cls-annot = refl
closedLiftShape?-just cls-binop = refl
