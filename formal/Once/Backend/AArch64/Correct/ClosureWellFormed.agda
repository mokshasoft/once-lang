{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.ClosureWellFormed
--
-- Well-formedness predicate for closures: tracks that a closure's
-- code-ptr points to valid thunk code within the program.
--
-- This is the key to eliminating the apply-produces-result postulate.
-- In whole-program proofs:
-- 1. Curry produces a ClosureWellFormed proof along with the closure
-- 2. Apply requires a ClosureWellFormed proof as a precondition
-- 3. This allows tracing execution through blr → thunk → ret
--
-- Key difference from x86:
-- - x86 uses call instruction which pushes return address to stack
-- - AArch64 uses blr which stores return address in x30 (link register)
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.ClosureWellFormed where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Star
  using (Star; refl*; step*; star-trans)
open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant)

open import Once.Backend.AArch64.Correct.Foundation using (encode)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_; _<_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

------------------------------------------------------------------------
-- ThunkResult: Result type for thunk execution
------------------------------------------------------------------------

-- | When a thunk executes, it produces this result
-- This captures what happens when apply calls a closure via blr
--
-- AArch64 register mapping:
-- - x0  = result register (like x86 rax)
-- - x19 = env register in thunk (like x86 r12)
-- - x20, x21 = callee-saved context (like x86 r14, r15)
-- - x29 = frame pointer (like x86 rbp)
-- - x30 = link register (return address, no x86 equivalent)
record ThunkResult {A B : Type} (prog : Program) (s s' : State)
                   (f : ⟦ A ⟧ → ⟦ B ⟧) (a : ⟦ A ⟧) : Set where
  field
    thunk-star      : Star prog s s'
    thunk-halted    : halted s' ≡ false
    thunk-x0        : readReg (regs s') x0 ≡ encode (f a)
    thunk-x20       : readReg (regs s') x20 ≡ readReg (regs s) x20
    thunk-x21       : readReg (regs s') x21 ≡ readReg (regs s) x21
    thunk-x29       : readReg (regs s') x29 ≡ readReg (regs s) x29
    thunk-stack-inv : StackInvariant s'
    thunk-sp-bound  : readSP (regs s') > 16

open ThunkResult public

------------------------------------------------------------------------
-- ClosureWellFormed: Well-formedness predicate for closures
------------------------------------------------------------------------

-- | A closure is well-formed in a program if:
-- 1. Its code-ptr points to a location in the program
-- 2. Executing from code-ptr produces the correct result
--
-- Key insight: This is established by curry and consumed by apply.
-- In whole-program proofs, curry and apply are in the same program,
-- so the well-formedness proof can be threaded through.
--
-- The thunk ends with `ret`, which returns to address in x30.
-- The caller (apply) sets x30 via `blr`, and thunk-correct
-- guarantees execution returns there.
--
-- NOTE: We use explicit runtime values (code-ptr, env-addr) rather than
-- the semantic Closure record because:
-- 1. Closure.code-ptr in semantics is 0 (placeholder)
-- 2. The actual code-ptr comes from compilation (offset + 6)
-- 3. Apply reads these from memory, not from the semantic record
record ClosureWellFormed {A B : Type} (prog : Program)
                         (code-ptr : ℕ) (env-addr : ℕ)
                         (semantics : ⟦ A ⟧ → ⟦ B ⟧) : Set where
  field
    -- The code-ptr is within the program bounds
    code-ptr-valid : code-ptr < length prog

    -- Executing from code-ptr produces correct result for any input
    -- ret-addr: the return address (set in x30 by blr, used by ret)
    --
    -- AArch64 thunk setup by apply:
    -- - x0  = argument (encoded)
    -- - x19 = env-addr (loaded from closure by apply)
    -- - x30 = return address (set by blr instruction)
    thunk-correct : ∀ (a : ⟦ A ⟧) (s : State) (ret-addr : ℕ) →
      halted s ≡ false →
      pc s ≡ code-ptr →
      readReg (regs s) x0 ≡ encode a →
      readReg (regs s) x19 ≡ env-addr →
      readReg (regs s) x30 ≡ ret-addr →  -- Return address in link register
      StackInvariant s →
      readSP (regs s) > 16 →
      ∃[ s' ] (ThunkResult prog s s' semantics a
              × pc s' ≡ ret-addr)

open ClosureWellFormed public

------------------------------------------------------------------------
-- CurryResult: Extended result for curry that includes well-formedness
------------------------------------------------------------------------

-- | When curry executes, it produces:
-- 1. A closure value (in x0)
-- 2. A proof that this closure is well-formed
--
-- This allows apply to use the well-formedness proof
--
-- The closure's runtime values are:
-- - x0 = closure address (new-sp after sub-sp 16)
-- - [closure]   = env-addr = encode x
-- - [closure+8] = code-ptr = offset + 6
record CurryResult {i} {A B C : Type} (f : IR i (A * B) C)
                   (prog : Program) (s s' : State) (x : ⟦ A ⟧)
                   (offset : ℕ) : Set where
  field
    -- Standard execution properties
    curry-star      : Star prog s s'
    curry-halted    : halted s' ≡ false
    curry-pc        : pc s' ≡ offset +ℕ compile-length (curry f)
    curry-x0        : readReg (regs s') x0 ≡ encode {B ⇒ C} (eval (curry f) x)
    curry-x20       : readReg (regs s') x20 ≡ readReg (regs s) x20
    curry-x21       : readReg (regs s') x21 ≡ readReg (regs s) x21
    curry-x29       : readReg (regs s') x29 ≡ readReg (regs s) x29
    curry-x30       : readReg (regs s') x30 ≡ readReg (regs s) x30
    curry-mem-x21   : readMem (memory s') (readReg (regs s) x21) ≡
                      readMem (memory s) (readReg (regs s) x21)
    curry-mem-x29   : readMem (memory s') (readReg (regs s) x29) ≡
                      readMem (memory s) (readReg (regs s) x29)
    curry-mem-x29+8 : readMem (memory s') (readReg (regs s) x29 +ℕ 8) ≡
                      readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    curry-stack-inv : StackInvariant s'
    curry-sp-bound  : readSP (regs s') > 16

    -- The closure produced is well-formed!
    -- This is the key property that apply needs
    -- Note: curry f : IR A (B ⇒ C), so eval (curry f) x : Closure B C
    --       semantics = Closure.semantics (eval (curry f) x) = λ b → eval f (x , b)
    --       code-ptr = offset + 6 (thunk entry in program)
    --       env-addr = encode x (captured value)
    closure-wf : ClosureWellFormed {B} {C} prog
                   (offset +ℕ 6)           -- code-ptr: thunk at offset+6
                   (encode x)              -- env-addr: encoded captured value
                   (λ b → eval f (x , b))  -- semantics: partial application

open CurryResult public

------------------------------------------------------------------------
-- ApplyWithWF: Apply execution that uses well-formedness
------------------------------------------------------------------------

-- | Apply a closure, given a well-formedness proof
-- This eliminates the need for apply-produces-result postulate!
--
-- Sketch of proof for AArch64:
-- 1. ldr x9 [x0]       -- Load closure from pair.fst
-- 2. ldr x10 [x0+8]    -- Load argument from pair.snd
-- 3. ldr x19 [x9]      -- Load env from closure.fst
-- 4. ldr x9 [x9+8]     -- Load code-ptr from closure.snd
-- 5. mov x0 x10        -- Argument → x0
-- 6. blr x9            -- Call thunk (sets x30 = pc+1, jumps to code-ptr)
-- 7. By ClosureWellFormed.thunk-correct, execution produces correct result
-- 8. Return lands at ret addr (instruction after blr)
-- 9. Result is in x0
record ApplyWithWFResult {A B : Type} (prog : Program) (s s' : State)
                         (cl : Closure A B) (a : ⟦ A ⟧)
                         (offset : ℕ) : Set where
  field
    apply-star      : Star prog s s'
    apply-halted    : halted s' ≡ false
    apply-pc        : pc s' ≡ offset +ℕ compile-length (apply {_} {A} {B})
    apply-x0        : readReg (regs s') x0 ≡ encode (Closure.semantics cl a)
    apply-x20       : readReg (regs s') x20 ≡ readReg (regs s) x20
    apply-x21       : readReg (regs s') x21 ≡ readReg (regs s) x21
    apply-x29       : readReg (regs s') x29 ≡ readReg (regs s) x29
    apply-mem-x21   : readMem (memory s') (readReg (regs s) x21) ≡
                      readMem (memory s) (readReg (regs s) x21)
    apply-mem-x29   : readMem (memory s') (readReg (regs s) x29) ≡
                      readMem (memory s) (readReg (regs s) x29)
    apply-mem-x29+8 : readMem (memory s') (readReg (regs s) x29 +ℕ 8) ≡
                      readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    apply-stack-inv : StackInvariant s'
    apply-sp-bound  : readSP (regs s') > 16

open ApplyWithWFResult public

------------------------------------------------------------------------
-- run-apply-with-wf postulate
------------------------------------------------------------------------

-- | Execute apply with a well-formedness proof
-- This is the key function that could eliminate the postulate
--
-- TODO: Implement this by:
-- 1. Trace the 5 apply instructions up to the blr
-- 2. Use ClosureWellFormed.thunk-correct to trace through the thunk
-- 3. Thunk ends with ret, which returns to x30
-- 4. Compose all Star proofs
--
-- For now, postulated due to complexity of tracing blr/ret interaction
postulate
  run-apply-with-wf : ∀ {A B} (prefix suffix : Program)
                      (cl : Closure A B) (a : ⟦ A ⟧) (s : State)
                      (code-ptr env-addr : ℕ) →
    ClosureWellFormed {A} {B}
      (prefix ++ compile-aarch64 (apply {_} {A} {B}) ++ suffix)
      code-ptr env-addr (Closure.semantics cl) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode {(A ⇒ B) * A} (cl , a) →
    StackInvariant s →
    readSP (regs s) > 16 →
    ∃[ s' ] ApplyWithWFResult
              (prefix ++ compile-aarch64 (apply {_} {A} {B}) ++ suffix)
              s s' cl a (length prefix)
