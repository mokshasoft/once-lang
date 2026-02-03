------------------------------------------------------------------------
-- Once.Arith.Backend.X86.Bridge
--
-- State bridge between Arith's model and CCC's model.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- This module provides:
--   1. Conversion from ArithState to CCC State
--   2. Register correspondence lemma
--   3. Tools to transfer Arith proofs to PrimEffect specifications
--
-- Key insight: We don't simulate execution step-by-step.
-- We just show that Arith's final state, when converted, satisfies
-- the PrimEffect specification.
------------------------------------------------------------------------

module Once.Arith.Backend.X86.Bridge where

-- Arith model
open import Once.Arith.Backend.X86.Syntax as Arith
  using (GPReg; ArithInstr; ArithProgram)
open import Once.Arith.Backend.X86.Correct as ArithCorrect
  using (ArithState; GPRFile; readGPR; gpr-file; apc;
         get-rax; get-rbx; get-rcx; get-rdx; get-rsi; get-rdi;
         get-r8; get-r9; get-r10; get-r11)

-- CCC model
open import Once.Backend.X86.Semantics as CCC
  using (State; RegFile; readReg; emptyMemory; initFlags)
open CCC.State using (regs; memory; flags; pc; halted)
open import Once.Backend.X86.Syntax as CCC using (Reg)

-- Standard library
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Register Mapping: Arith GPReg → CCC Reg
------------------------------------------------------------------------

-- | Map Arith's GPReg to CCC's Reg
-- Arith uses a subset of x86-64 GPRs
gpr-to-reg : Arith.GPReg → CCC.Reg
gpr-to-reg Arith.rax = CCC.rax
gpr-to-reg Arith.rbx = CCC.rbx
gpr-to-reg Arith.rcx = CCC.rcx
gpr-to-reg Arith.rdx = CCC.rdx
gpr-to-reg Arith.rsi = CCC.rsi
gpr-to-reg Arith.rdi = CCC.rdi
gpr-to-reg Arith.r8  = CCC.r8
gpr-to-reg Arith.r9  = CCC.r9
gpr-to-reg Arith.r10 = CCC.r10
gpr-to-reg Arith.r11 = CCC.r11

------------------------------------------------------------------------
-- Register File Conversion: GPRFile → RegFile
------------------------------------------------------------------------

-- | Convert Arith's GPRFile to CCC's RegFile
-- Uses absolute value to convert ℤ → ℕ
-- Registers not in Arith's model are set to 0
arith-regs-to-ccc : GPRFile → RegFile
arith-regs-to-ccc gf = CCC.mkregfile
  (∣ get-rax gf ∣)   -- rax
  (∣ get-rbx gf ∣)   -- rbx
  (∣ get-rcx gf ∣)   -- rcx
  (∣ get-rdx gf ∣)   -- rdx
  (∣ get-rsi gf ∣)   -- rsi
  (∣ get-rdi gf ∣)   -- rdi
  0                  -- rbp (not in Arith)
  0                  -- rsp (would need stack depth)
  (∣ get-r8 gf ∣)    -- r8
  (∣ get-r9 gf ∣)    -- r9
  (∣ get-r10 gf ∣)   -- r10
  (∣ get-r11 gf ∣)   -- r11
  0                  -- r12 (not in Arith)
  0                  -- r13 (not in Arith)
  0                  -- r14 (not in Arith)
  0                  -- r15 (not in Arith)

------------------------------------------------------------------------
-- State Conversion: ArithState → State
------------------------------------------------------------------------

-- | Convert Arith's ArithState to CCC's State
-- Memory is empty (Arith uses stack differently)
-- Flags are initial (Arith doesn't track flags in our model)
arith-to-ccc : ArithState → State
arith-to-ccc as = CCC.mkstate
  (arith-regs-to-ccc (gpr-file as))
  emptyMemory
  initFlags
  (apc as)
  false

------------------------------------------------------------------------
-- Register Correspondence Lemma
------------------------------------------------------------------------

-- | Reading a register in the converted state equals
-- the absolute value of the original register.
--
-- This is the KEY LEMMA for transferring Arith proofs to PrimEffect.
--
reg-correspondence : ∀ (gf : GPRFile) (r : Arith.GPReg) →
  readReg (arith-regs-to-ccc gf) (gpr-to-reg r) ≡ ∣ readGPR gf r ∣
reg-correspondence gf Arith.rax = refl
reg-correspondence gf Arith.rbx = refl
reg-correspondence gf Arith.rcx = refl
reg-correspondence gf Arith.rdx = refl
reg-correspondence gf Arith.rsi = refl
reg-correspondence gf Arith.rdi = refl
reg-correspondence gf Arith.r8  = refl
reg-correspondence gf Arith.r9  = refl
reg-correspondence gf Arith.r10 = refl
reg-correspondence gf Arith.r11 = refl

------------------------------------------------------------------------
-- Absolute Value Properties
------------------------------------------------------------------------

-- | For non-negative integers, absolute value is identity
abs-nonneg : ∀ (n : ℕ) → ∣ + n ∣ ≡ n
abs-nonneg n = refl

-- | Absolute value of sum (when both non-negative)
abs-sum-nonneg : ∀ (a b : ℕ) → ∣ (+ a) ℤ.+ (+ b) ∣ ≡ a Data.Nat.+ b
abs-sum-nonneg zero b = refl
abs-sum-nonneg (suc a) b = cong suc (abs-sum-nonneg a b)

------------------------------------------------------------------------
-- Transfer Lemma: Arith result → PrimEffect result
------------------------------------------------------------------------

-- | If Arith proves the result is in rax, we can derive PrimEffect's result condition.
--
-- Given:
--   arith-result : readGPR (gpr-file as') rax ≡ result
-- Derive:
--   readReg (regs (arith-to-ccc as')) rax ≡ ∣ result ∣
--
transfer-result : ∀ (as : ArithState) (result : ℤ) →
  readGPR (gpr-file as) Arith.rax ≡ result →
  readReg (regs (arith-to-ccc as)) CCC.rax ≡ ∣ result ∣
transfer-result as result arith-eq =
  let
    -- Step 1: reg-correspondence gives us the structure
    step1 : readReg (arith-regs-to-ccc (gpr-file as)) CCC.rax ≡ ∣ readGPR (gpr-file as) Arith.rax ∣
    step1 = reg-correspondence (gpr-file as) Arith.rax

    -- Step 2: Substitute arith-eq
    step2 : ∣ readGPR (gpr-file as) Arith.rax ∣ ≡ ∣ result ∣
    step2 = cong ∣_∣ arith-eq

    -- Step 3: arith-to-ccc as extracts regs
    step3 : regs (arith-to-ccc as) ≡ arith-regs-to-ccc (gpr-file as)
    step3 = refl
  in
    Relation.Binary.PropositionalEquality.trans step1 step2

------------------------------------------------------------------------
-- Usage Notes
------------------------------------------------------------------------

-- To eliminate the postulate in Contract.agda:
--
-- 1. Use Arith's proven lemmas (e.g., mov-reg-correct, add-reg-correct)
--    to show: readGPR (gpr-file (execArithProg prog as)) rax ≡ expected-result
--
-- 2. Apply transfer-result to get:
--    readReg (regs (arith-to-ccc final-as)) rax ≡ ∣ expected-result ∣
--
-- 3. Since encode-int n = ∣ n ∣, this matches PrimEffect's effect-result.
--
-- 4. For register preservation (r14, r15, rbp, rsp):
--    These registers are NOT in Arith's model, so they're always 0
--    in arith-to-ccc. Need to handle specially at boundary.
--
-- The key insight: PrimEffect talks about CCC's State, but we construct
-- that state from Arith's proven result, not from CCC's execution.
------------------------------------------------------------------------
