------------------------------------------------------------------------
-- Once.Arith.IR
--
-- The Arithmetic Intermediate Representation.
-- This is an expression language for efficient register-based computation,
-- orthogonal to the categorical generators.
--
-- Key design: Linearity is enforced via context splitting (Γ ⊕ Δ).
-- A variable can only appear in one subexpression unless marked ω.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.IR where

open import Once.Arith.Type

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Variable context
------------------------------------------------------------------------

-- | Variable binding: name with its numeric type
record Binding : Set where
  constructor _∶_
  field
    name : String
    type : NumType

-- | Context: list of variable bindings
--
-- We use a simple list representation. For linearity:
-- - Context splitting (Γ ⊕ Δ) partitions bindings between subexpressions
-- - A variable can appear in only one partition (linear)
-- - Context contraction (Γ ⊕ Γ → Γ) is not allowed for linear variables
--
Ctx : Set
Ctx = List Binding

-- | Empty context
∅ : Ctx
∅ = []

-- | Singleton context
singleton : String → NumType → Ctx
singleton x τ = (x ∶ τ) ∷ []

-- | Context merge (for binary operations)
-- This is the disjoint union; the caller must ensure no duplicates.
_⊕_ : Ctx → Ctx → Ctx
Γ ⊕ Δ = Γ ++ Δ

infixr 5 _⊕_

------------------------------------------------------------------------
-- Variable membership
------------------------------------------------------------------------

-- | Evidence that a variable is in the context
data _∈_ : Binding → Ctx → Set where
  here  : ∀ {b Γ} → b ∈ (b ∷ Γ)
  there : ∀ {b b' Γ} → b ∈ Γ → b ∈ (b' ∷ Γ)

-- | Look up a variable's type by name
lookup-type : ∀ {b Γ} → b ∈ Γ → NumType
lookup-type {b} _ = Binding.type b

------------------------------------------------------------------------
-- Arithmetic IR
------------------------------------------------------------------------

-- | ArithIR: Arithmetic expressions with linear context tracking
--
-- The context Γ tracks which variables are used in the expression.
-- Binary operations split the context: Add uses Γ for left, Δ for right.
-- This enforces linearity: each variable is used in exactly one place.
--
-- Note: For ω (unrestricted) variables, we'd need context contraction.
-- For now, we model only linear usage. Extension to QTT quantities
-- is future work.
--
data ArithIR : Ctx → NumType → Set where

  -- | Literal: constant value, uses no variables
  Lit : ∀ {τ} → ⟦ τ ⟧N → ArithIR ∅ τ

  -- | Variable: uses exactly this variable
  Var : ∀ {x τ Γ} → (x ∶ τ) ∈ Γ → ArithIR Γ τ

  -- | Addition: splits context between operands
  Add : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → ArithIR (Γ ⊕ Δ) τ

  -- | Subtraction: splits context between operands
  Sub : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → ArithIR (Γ ⊕ Δ) τ

  -- | Multiplication: splits context between operands
  Mul : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → ArithIR (Γ ⊕ Δ) τ

  -- | Division: splits context between operands
  -- Note: Division by zero is undefined. Proof of non-zero divisor is future work.
  Div : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → ArithIR (Γ ⊕ Δ) τ

  -- | Modulo: splits context between operands (integers only)
  Mod : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → ArithIR (Γ ⊕ Δ) τ

  -- | Negation: uses same context (unary operation)
  Neg : ∀ {Γ τ} → ArithIR Γ τ → ArithIR Γ τ

------------------------------------------------------------------------
-- Comparison operations (return Bool)
------------------------------------------------------------------------

-- | Bool type for comparisons
-- In the full system, Bool = Unit + Unit. Here we use a simple encoding.
data BoolType : Set where
  BoolT : BoolType

-- | Comparison IR: produces a boolean from numeric inputs
--
-- These operations return to control flow via the boundary.
-- The result feeds into generator IR (case analysis).
--
data CmpIR : Ctx → Set where
  -- | Less than
  Lt : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → CmpIR (Γ ⊕ Δ)

  -- | Equal
  Eq : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → CmpIR (Γ ⊕ Δ)

  -- | Less than or equal
  Le : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → CmpIR (Γ ⊕ Δ)

  -- | Greater than
  Gt : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → CmpIR (Γ ⊕ Δ)

  -- | Greater than or equal
  Ge : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → CmpIR (Γ ⊕ Δ)

  -- | Not equal
  Ne : ∀ {Γ Δ τ} → ArithIR Γ τ → ArithIR Δ τ → CmpIR (Γ ⊕ Δ)

------------------------------------------------------------------------
-- Expression size (for complexity analysis)
------------------------------------------------------------------------

-- | Size of an arithmetic expression (number of nodes)
size : ∀ {Γ τ} → ArithIR Γ τ → ℕ
size (Lit _)     = 1
size (Var _)     = 1
size (Add e₁ e₂) = 1 + size e₁ + size e₂
size (Sub e₁ e₂) = 1 + size e₁ + size e₂
size (Mul e₁ e₂) = 1 + size e₁ + size e₂
size (Div e₁ e₂) = 1 + size e₁ + size e₂
size (Mod e₁ e₂) = 1 + size e₁ + size e₂
size (Neg e)     = 1 + size e

-- | Size of a comparison expression
size-cmp : ∀ {Γ} → CmpIR Γ → ℕ
size-cmp (Lt e₁ e₂) = 1 + size e₁ + size e₂
size-cmp (Eq e₁ e₂) = 1 + size e₁ + size e₂
size-cmp (Le e₁ e₂) = 1 + size e₁ + size e₂
size-cmp (Gt e₁ e₂) = 1 + size e₁ + size e₂
size-cmp (Ge e₁ e₂) = 1 + size e₁ + size e₂
size-cmp (Ne e₁ e₂) = 1 + size e₁ + size e₂

------------------------------------------------------------------------
-- Variable count (for register allocation)
------------------------------------------------------------------------

-- | Number of variables in an expression
varCount : ∀ {Γ τ} → ArithIR Γ τ → ℕ
varCount (Lit _)     = 0
varCount (Var _)     = 1
varCount (Add e₁ e₂) = varCount e₁ + varCount e₂
varCount (Sub e₁ e₂) = varCount e₁ + varCount e₂
varCount (Mul e₁ e₂) = varCount e₁ + varCount e₂
varCount (Div e₁ e₂) = varCount e₁ + varCount e₂
varCount (Mod e₁ e₂) = varCount e₁ + varCount e₂
varCount (Neg e)     = varCount e
