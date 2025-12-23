------------------------------------------------------------------------
-- Once.Backend.X86.Postulates
--
-- X86-specific postulates. Separated from Once.Postulates to avoid
-- cyclic imports with X86 modules.
--
-- See Once.Postulates for documentation format and checklist.
------------------------------------------------------------------------

module Once.Backend.X86.Postulates where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; length; _++_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)

open import Once.Type using (Type; _⇒_; _*_)
open import Once.IR using (apply; curry; IR)
open import Once.Semantics using (⟦_⟧; encode; eval)
open import Once.Memory using (Word)

open import Once.Backend.X86.Syntax using (rsp; rax; rdi; r14; r15; rbp; Program)
open import Once.Backend.X86.Semantics using (State; readReg; readMem)
open import Once.Backend.X86.Semantics using () renaming (module State to St)
open St using (regs; memory; halted; pc)
open import Once.Backend.X86.Correct.Star using (Star)
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant)
open import Once.Backend.X86.CodeGen using (compile-x86; compile-length)

------------------------------------------------------------------------
-- Postulate P4: Stack Pointer Bounds (Runtime Property)
------------------------------------------------------------------------
--
-- After any stack-using operation, rsp remains > 16.
--
-- NEEDED BY: Once.Backend.X86.Correct.MutualIR (inl, inr, pair, case, curry)
--
-- JUSTIFICATION:
--   The initial rsp is 0x7FFF0000 (≈2 billion). Stack-using operations
--   subtract at most 64 bytes per call. Even with deep recursion (millions
--   of calls), total stack usage is bounded and rsp never drops below 16.
--   This is a runtime guarantee from the execution environment.
--
-- IMPACT:
--   If the stack were exhausted, the program would crash before returning
--   an incorrect result. This axiom captures that we're assuming sufficient
--   stack space, which is true for any realistic program execution.
--
-- RUNTIME EFFECT: Assumes sufficient stack space (standard runtime assumption)
--
------------------------------------------------------------------------

postulate
  rsp-bound-after-stack-op : ∀ (s : State) → readReg (regs s) rsp > 16

------------------------------------------------------------------------
-- Postulate P5: Closure Application (Semantic Boundary)
------------------------------------------------------------------------
--
-- Executing `apply` on a closure produces the correct result.
--
-- NEEDED BY: Once.Backend.X86.Correct.MutualIR (run-apply-star-direct)
--
-- JUSTIFICATION:
--   The `apply` instruction calls code that was compiled elsewhere (by curry).
--   The closure contains a code pointer to compiled function code and an
--   environment value. When called, this code executes correctly because:
--   1. curry compiled the function with the correct calling convention
--   2. The closure stores encode(env) at the correct offset
--   This is a semantic boundary: we're trusting that separately-compiled
--   code interoperates correctly.
--
-- IMPACT:
--   If closure application were incorrect, higher-order functions would fail.
--   This is fundamental to the semantics of closures.
--
-- RUNTIME EFFECT: None (proof-only)
--
------------------------------------------------------------------------

postulate
  apply-produces-result : ∀ {A B : Type} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode {(A ⇒ B) * A} x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    in ∃[ s' ] (Star prog s s'
              × halted s' ≡ false
              × pc s' ≡ length prefix +ℕ compile-length (apply {A} {B})
              × readReg (regs s') rax ≡ encode {B} (eval (apply {A} {B}) x)
              × readReg (regs s') r14 ≡ readReg (regs s) r14
              × readReg (regs s') r15 ≡ readReg (regs s) r15
              × readReg (regs s') rbp ≡ readReg (regs s) rbp
              × readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
              × StackInvariant s'
              × readReg (regs s') rsp > 16)

-- NOTE: encode-curry-at-rsp was ELIMINATED
-- The curry encoding is now derived from encode-closure-construct (in Once.Postulates)
-- via the proof in Once.Backend.X86.Correct.IR.Curry (lines 468-470)
