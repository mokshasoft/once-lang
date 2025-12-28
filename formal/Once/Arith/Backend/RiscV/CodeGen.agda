------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV.CodeGen
--
-- RISC-V code generation for arithmetic expressions.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV.CodeGen where

open import Once.Arith.Type
open import Once.Arith.IR
open import Once.Arith.Backend.RiscV.Syntax

open import Data.Bool using (Bool; true; false)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Type Conversion
------------------------------------------------------------------------

toℤ : ∀ {τ} → isInteger τ ≡ true → ⟦ τ ⟧N → ℤ
toℤ {I8}  refl n = n
toℤ {I16} refl n = n
toℤ {I32} refl n = n
toℤ {I64} refl n = n

------------------------------------------------------------------------
-- Code Generation (simplified for proofs)
------------------------------------------------------------------------

-- | First temporary register (t0 = x5)
temp-reg : GPReg
temp-reg = x5

-- | Result register (a0 = x10)
result-reg : GPReg
result-reg = x10

-- | Compile an ArithIR to RISC-V instructions
compile-arith : ∀ {Γ τ} → ArithIR Γ τ → ArithProgram

compile-arith (Lit {I8}  n) = intI (li x5 n) ∷ intI (mv x10 x5) ∷ []
compile-arith (Lit {I16} n) = intI (li x5 n) ∷ intI (mv x10 x5) ∷ []
compile-arith (Lit {I32} n) = intI (li x5 n) ∷ intI (mv x10 x5) ∷ []
compile-arith (Lit {I64} n) = intI (li x5 n) ∷ intI (mv x10 x5) ∷ []
compile-arith (Lit {F32} n) = []  -- Float literals require different handling
compile-arith (Lit {F64} n) = []  -- Float literals require different handling

compile-arith (Var x) = []  -- Variables loaded from environment

compile-arith (Add e1 e2) =
  let prog1 = compile-arith e1
      prog2 = compile-arith e2
  in prog1 ++ prog2 ++ intI (add x5 x5 x6) ∷ intI (mv x10 x5) ∷ []

compile-arith (Sub e1 e2) =
  let prog1 = compile-arith e1
      prog2 = compile-arith e2
  in prog1 ++ prog2 ++ intI (sub x5 x5 x6) ∷ intI (mv x10 x5) ∷ []

compile-arith (Mul e1 e2) =
  let prog1 = compile-arith e1
      prog2 = compile-arith e2
  in prog1 ++ prog2 ++ intI (mul x5 x5 x6) ∷ intI (mv x10 x5) ∷ []

compile-arith (Div e1 e2) =
  let prog1 = compile-arith e1
      prog2 = compile-arith e2
  in prog1 ++ prog2 ++ intI (div x5 x5 x6) ∷ intI (mv x10 x5) ∷ []

compile-arith (Mod e1 e2) =
  let prog1 = compile-arith e1
      prog2 = compile-arith e2
  in prog1 ++ prog2 ++ intI (rem x5 x5 x6) ∷ intI (mv x10 x5) ∷ []

compile-arith (Neg e) =
  let prog = compile-arith e
  in prog ++ intI (neg x5 x5) ∷ intI (mv x10 x5) ∷ []

------------------------------------------------------------------------
-- Characterization Lemmas
------------------------------------------------------------------------

-- | Characterization of integer literal compilation
compile-lit-int-char : ∀ {τ} (n : ⟦ τ ⟧N) (p : isInteger τ ≡ true) →
  compile-arith (Lit n) ≡ intI (li x5 (toℤ p n)) ∷ intI (mv x10 x5) ∷ []
compile-lit-int-char {I8}  n refl = refl
compile-lit-int-char {I16} n refl = refl
compile-lit-int-char {I32} n refl = refl
compile-lit-int-char {I64} n refl = refl
