-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Semantics
--
-- Denotational semantics for the arithmetic IR.
-- Expressions are evaluated to their mathematical values.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Semantics where

open import Once.Arith.Type
open import Once.Arith.IR

open import Data.Bool using (Bool; true; false)
open import Data.Integer as ℤ using (ℤ; +_; -_; ∣_∣; _<?_)
open import Data.Integer.Properties as ℤP using ()
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Relation.Nullary using (does)
open import Data.Float as F using (Float)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

------------------------------------------------------------------------
-- Environment
------------------------------------------------------------------------

-- | Environment: maps variable bindings to their values
--
-- The environment structure mirrors the context structure.
-- For context Γ = [(x ∶ τ₁), (y ∶ τ₂), ...],
-- the environment is a nested tuple of values.
--
data Env : Ctx → Set where
  ε    : Env ∅
  _∷ᵉ_ : ∀ {b Γ} → ⟦ Binding.type b ⟧N → Env Γ → Env (b ∷ Γ)

infixr 5 _∷ᵉ_

-- | Look up a variable in the environment
lookupEnv : ∀ {b Γ} → b ∈ Γ → Env Γ → ⟦ Binding.type b ⟧N
lookupEnv here      (v ∷ᵉ _)   = v
lookupEnv (there p) (_ ∷ᵉ env) = lookupEnv p env

-- | Split environment according to context split
--
-- When Γ = Γ₁ ⊕ Γ₂, we can split the environment into two parts.
-- This is needed for evaluating binary operations.
--
splitEnv : ∀ {Γ Δ} → Env (Γ ⊕ Δ) → Env Γ × Env Δ
splitEnv {[]}     env         = ε , env
splitEnv {_ ∷ Γ} (v ∷ᵉ env) with splitEnv {Γ} env
... | env₁ , env₂ = (v ∷ᵉ env₁) , env₂

------------------------------------------------------------------------
-- Arithmetic operations (type-indexed)
------------------------------------------------------------------------

-- | Addition for each numeric type
add : ∀ τ → ⟦ τ ⟧N → ⟦ τ ⟧N → ⟦ τ ⟧N
add I8  = ℤ._+_
add I16 = ℤ._+_
add I32 = ℤ._+_
add I64 = ℤ._+_
add F32 = F._+_
add F64 = F._+_

-- | Subtraction for each numeric type
sub : ∀ τ → ⟦ τ ⟧N → ⟦ τ ⟧N → ⟦ τ ⟧N
sub I8  = ℤ._-_
sub I16 = ℤ._-_
sub I32 = ℤ._-_
sub I64 = ℤ._-_
sub F32 = F._-_
sub F64 = F._-_

-- | Multiplication for each numeric type
mul : ∀ τ → ⟦ τ ⟧N → ⟦ τ ⟧N → ⟦ τ ⟧N
mul I8  = ℤ._*_
mul I16 = ℤ._*_
mul I32 = ℤ._*_
mul I64 = ℤ._*_
mul F32 = F._*_
mul F64 = F._*_

-- | Division for each numeric type
-- Note: Integer division requires NonZero proof in stdlib.
-- For now, we postulate a total division function.
-- The proof of non-zero divisor is deferred to the boundary proof.
postulate
  ℤ-div : ℤ → ℤ → ℤ  -- Assumed total; undefined for zero divisor

div : ∀ τ → ⟦ τ ⟧N → ⟦ τ ⟧N → ⟦ τ ⟧N
div I8  = ℤ-div
div I16 = ℤ-div
div I32 = ℤ-div
div I64 = ℤ-div
div F32 = F._÷_
div F64 = F._÷_

-- | Modulo for each numeric type
-- Same issue as division: requires NonZero proof.
postulate
  ℤ-mod : ℤ → ℤ → ℤ  -- Assumed total; undefined for zero divisor

mod : ∀ τ → ⟦ τ ⟧N → ⟦ τ ⟧N → ⟦ τ ⟧N
mod I8  = ℤ-mod
mod I16 = ℤ-mod
mod I32 = ℤ-mod
mod I64 = ℤ-mod
mod F32 = λ x _ → x  -- Float mod not in stdlib, placeholder (returns first arg)
mod F64 = λ x _ → x  -- Float mod not in stdlib, placeholder (returns first arg)

-- | Negation for each numeric type
neg : ∀ τ → ⟦ τ ⟧N → ⟦ τ ⟧N
neg I8  = ℤ.-_
neg I16 = ℤ.-_
neg I32 = ℤ.-_
neg I64 = ℤ.-_
neg F32 = F.-_
neg F64 = F.-_

-- | Less than comparison for each numeric type
-- Use 'does' to extract Bool from Dec
lt : ∀ τ → ⟦ τ ⟧N → ⟦ τ ⟧N → Bool
lt I8  = λ x y → does (x ℤ.<? y)
lt I16 = λ x y → does (x ℤ.<? y)
lt I32 = λ x y → does (x ℤ.<? y)
lt I64 = λ x y → does (x ℤ.<? y)
lt F32 = F._<ᵇ_
lt F64 = F._<ᵇ_

-- | Equality comparison for each numeric type
-- Uses absolute difference = 0 for integers
eq : ∀ τ → ⟦ τ ⟧N → ⟦ τ ⟧N → Bool
eq I8  = λ x y → ℕ._≡ᵇ_ (∣ x ℤ.- y ∣) 0
eq I16 = λ x y → ℕ._≡ᵇ_ (∣ x ℤ.- y ∣) 0
eq I32 = λ x y → ℕ._≡ᵇ_ (∣ x ℤ.- y ∣) 0
eq I64 = λ x y → ℕ._≡ᵇ_ (∣ x ℤ.- y ∣) 0
eq F32 = F._≡ᵇ_
eq F64 = F._≡ᵇ_

-- | Convert Bool to numeric type (0 for false, 1 for true)
-- This is how comparisons are encoded in machine registers.
boolToNum : ∀ τ → Bool → ⟦ τ ⟧N
boolToNum I8  false = + 0
boolToNum I8  true  = + 1
boolToNum I16 false = + 0
boolToNum I16 true  = + 1
boolToNum I32 false = + 0
boolToNum I32 true  = + 1
boolToNum I64 false = + 0
boolToNum I64 true  = + 1
boolToNum F32 false = 0.0
boolToNum F32 true  = 1.0
boolToNum F64 false = 0.0
boolToNum F64 true  = 1.0

-- | Apply comparison operator
cmpApply : CmpOp → ∀ τ → ⟦ τ ⟧N → ⟦ τ ⟧N → Bool
cmpApply CmpLt τ x y = lt τ x y
cmpApply CmpLe τ x y = lt τ x y Data.Bool.∨ eq τ x y
cmpApply CmpGt τ x y = lt τ y x
cmpApply CmpGe τ x y = lt τ y x Data.Bool.∨ eq τ x y
cmpApply CmpEq τ x y = eq τ x y
cmpApply CmpNe τ x y = Data.Bool.not (eq τ x y)

------------------------------------------------------------------------
-- Type conversion (OCP-0002)
------------------------------------------------------------------------

-- | Convert a value from one numeric type to another
-- For integers: this is identity (ℤ → ℤ)
-- For floats: this is identity (Float → Float)
-- Cross-domain conversion (int ↔ float) is a type error at the source level
convert : ∀ (τ₁ τ₂ : NumType) → ⟦ τ₁ ⟧N → ⟦ τ₂ ⟧N
-- Integer to integer: identity (all are ℤ)
convert I8  I8  n = n
convert I8  I16 n = n
convert I8  I32 n = n
convert I8  I64 n = n
convert I16 I8  n = n
convert I16 I16 n = n
convert I16 I32 n = n
convert I16 I64 n = n
convert I32 I8  n = n
convert I32 I16 n = n
convert I32 I32 n = n
convert I32 I64 n = n
convert I64 I8  n = n
convert I64 I16 n = n
convert I64 I32 n = n
convert I64 I64 n = n
-- Float to float: identity (all are Float)
convert F32 F32 n = n
convert F32 F64 n = n
convert F64 F32 n = n
convert F64 F64 n = n
-- Cross-domain: not allowed at source level, but we need totality
-- Return 0 for int→float, 0.0 for float→int
convert I8  F32 _ = 0.0
convert I8  F64 _ = 0.0
convert I16 F32 _ = 0.0
convert I16 F64 _ = 0.0
convert I32 F32 _ = 0.0
convert I32 F64 _ = 0.0
convert I64 F32 _ = 0.0
convert I64 F64 _ = 0.0
convert F32 I8  _ = + 0
convert F32 I16 _ = + 0
convert F32 I32 _ = + 0
convert F32 I64 _ = + 0
convert F64 I8  _ = + 0
convert F64 I16 _ = + 0
convert F64 I32 _ = + 0
convert F64 I64 _ = + 0

------------------------------------------------------------------------
-- Expression evaluation
------------------------------------------------------------------------

-- | Evaluate an arithmetic expression
--
-- eval-arith : ArithIR Γ τ → Env Γ → ⟦ τ ⟧N
--
-- The expression uses variables from context Γ.
-- The environment provides values for those variables.
-- The result is a value of the expression's type τ.
--
eval-arith : ∀ {Γ τ} → ArithIR Γ τ → Env Γ → ⟦ τ ⟧N

-- Literal: ignore environment, return the constant
eval-arith (Lit n) _ = n

-- Variable: look up in environment
eval-arith (Var p) env = lookupEnv p env

-- Binary operations: split environment, evaluate both sides, combine
eval-arith (Add {Γ} {Δ} {τ} e₁ e₂) env =
  let (env₁ , env₂) = splitEnv {Γ} {Δ} env
  in add τ (eval-arith e₁ env₁) (eval-arith e₂ env₂)

eval-arith (Sub {Γ} {Δ} {τ} e₁ e₂) env =
  let (env₁ , env₂) = splitEnv {Γ} {Δ} env
  in sub τ (eval-arith e₁ env₁) (eval-arith e₂ env₂)

eval-arith (Mul {Γ} {Δ} {τ} e₁ e₂) env =
  let (env₁ , env₂) = splitEnv {Γ} {Δ} env
  in mul τ (eval-arith e₁ env₁) (eval-arith e₂ env₂)

eval-arith (Div {Γ} {Δ} {τ} e₁ e₂) env =
  let (env₁ , env₂) = splitEnv {Γ} {Δ} env
  in div τ (eval-arith e₁ env₁) (eval-arith e₂ env₂)

eval-arith (Mod {Γ} {Δ} {τ} e₁ e₂) env =
  let (env₁ , env₂) = splitEnv {Γ} {Δ} env
  in mod τ (eval-arith e₁ env₁) (eval-arith e₂ env₂)

-- Negation: use same environment
eval-arith (Neg {_} {τ} e) env = neg τ (eval-arith e env)

-- Comparison: evaluate both operands, compare, return 0/1
eval-arith (Cmp {Γ} {Δ} {τ} op e₁ e₂) env =
  let (env₁ , env₂) = splitEnv {Γ} {Δ} env
      v₁ = eval-arith e₁ env₁
      v₂ = eval-arith e₂ env₂
  in boolToNum τ (cmpApply op τ v₁ v₂)

-- Type conversion: evaluate operand and convert to target type
eval-arith (Conv {_} {τ₁} τ₂ e) env = convert τ₁ τ₂ (eval-arith e env)

------------------------------------------------------------------------
-- Semantic properties (for proofs)
------------------------------------------------------------------------

-- | Evaluation is deterministic
--
-- For any expression e and environment env, eval-arith e env
-- produces a unique result.
--
eval-deterministic : ∀ {Γ τ} (e : ArithIR Γ τ) (env : Env Γ) →
                     eval-arith e env ≡ eval-arith e env
eval-deterministic _ _ = refl