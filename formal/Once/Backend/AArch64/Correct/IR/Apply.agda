{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.IR.Apply
--
-- Helper records and functions for apply proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
--
-- IMPORTANT: Apply is fundamentally postulated due to model limitation.
-- The blr instruction performs an indirect call to code at an arbitrary
-- location (the thunk created by curry). This requires whole-program
-- reasoning that the local execution model cannot provide.
--
-- HOWEVER: With ClosureWellFormed threading from curry to apply,
-- we can eliminate the postulate in whole-program proofs. See
-- ClosureWellFormed.agda for the Star-based alternative that uses
-- the well-formedness proof provided by curry.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.IR.Apply where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.Semantics using (Word)
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation using (encode; encodedMemory)

-- | Re-export Star-based types from ClosureWellFormed
-- These are the preferred types for whole-program proofs
open import Once.Backend.AArch64.Correct.ClosureWellFormed public
  using ( ThunkResult
        ; ClosureWellFormed
        ; ApplyWithWFResult
        ; run-apply-with-wf
        )

open import Data.Bool using (false; true)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Apply Code Structure
------------------------------------------------------------------------
--
-- compile-aarch64 apply =
--   ldr x9 (base x0)          -- 0: load closure from pair.fst
--   ldr x10 (base+imm x0 8)   -- 1: load argument from pair.snd
--   ldr x19 (base x9)         -- 2: load env from closure.fst
--   ldr x9 (base+imm x9 8)    -- 3: load code_ptr from closure.snd
--   mov x0 (reg x10)          -- 4: argument → x0
--   blr x9                    -- 5: call thunk (pc → code_ptr)
--
-- compile-length apply = 6
--
-- WHY FUNDAMENTALLY POSTULATED (Model Limitation):
-- Apply involves INDIRECT CALL semantics via blr:
--   1. blr x9 jumps to code_ptr (stored in closure by curry)
--   2. The thunk code executes at an arbitrary location
--   3. ret in the thunk returns to instruction after blr
--
-- The thunk code (from curry) is embedded in a DIFFERENT part of
-- the program. Proving apply would require:
--   1. Global program reasoning (not just local prefix/suffix)
--   2. Knowing what code exists at closure.code_ptr
--   3. Proving the thunk correctly executes f on (env, arg)
--   4. Proving ret returns to the right location
--
-- This is a genuine model limitation - the local execution model
-- can't reason about jumps to code in other program regions.
-- The postulate is INTENTIONAL and mathematically justified.

------------------------------------------------------------------------
-- Apply Context: computed values for apply proof
------------------------------------------------------------------------

record ApplyContext {A B : Type}
                    (prefix suffix : Program) : Set where
  field
    -- Computed program
    prog : Program

    -- Apply instruction sequence
    apply-code : Program

open ApplyContext public

-- | Construct ApplyContext from prefix/suffix
mkApplyContext : ∀ {A B : Type}
                 (prefix suffix : Program) → ApplyContext {A} {B} prefix suffix
mkApplyContext {A} {B} prefix suffix = record
  { prog = the-prog
  ; apply-code = the-apply-code
  }
  where
    the-apply-code = compile-aarch64 (apply {A} {B})
    the-prog = prefix ++ the-apply-code ++ suffix

------------------------------------------------------------------------
-- Closure Field Accessors
------------------------------------------------------------------------
--
-- A closure created by curry has this memory layout:
--   [closure-ptr]     = env-addr (captured environment address)
--   [closure-ptr + 8] = code-ptr (address of thunk entry)
--
-- The Closure record (from Once.Semantics) has these fields directly:
--   - Closure.env-addr : Word
--   - Closure.code-ptr : Word
--
-- The encoding axioms (encode-closure-env, encode-closure-code-ptr)
-- are now in Once.Postulates alongside other encoding axioms.

------------------------------------------------------------------------
-- Apply Setup Result
------------------------------------------------------------------------
--
-- Result after executing apply's 6 setup instructions.
-- After execution:
--   pc = Closure.code-ptr (thunk entry)
--   x19 = Closure.env-addr (environment for thunk)
--   x0 = arg (argument for thunk)
--   x30 = return address (after blr)
--   halted = false (blr doesn't halt)

record ApplySetupResult {A B : Type}
                        (ctx : ApplyContext {A} {B} [] [])
                        (closure : ⟦ A ⇒ B ⟧) (arg : ⟦ A ⟧)
                        (s s-after : State) : Set where
  field
    -- Execution reached s-after
    setup-exec : exec 6 (prog ctx) s ≡ just s-after

    -- Not halted (blr doesn't halt)
    setup-halted : halted s-after ≡ false

    -- PC jumped to thunk entry
    setup-pc : pc s-after ≡ Closure.code-ptr closure

    -- x19 holds environment
    setup-x19 : readReg (regs s-after) x19 ≡ Closure.env-addr closure

    -- x0 holds argument
    setup-x0 : readReg (regs s-after) x0 ≡ encode arg

    -- x30 holds return address (pc + 6)
    setup-x30 : readReg (regs s-after) x30 ≡ 6

    -- Callee-saved register preserved
    setup-x20 : readReg (regs s-after) x20 ≡ readReg (regs s) x20

open ApplySetupResult public

------------------------------------------------------------------------
-- Apply Full Result (with prefix/suffix)
------------------------------------------------------------------------
--
-- Result for apply with arbitrary prefix/suffix.
-- This is the type used by the main IR proof.

record ApplyResult {A B : Type}
                   (prefix suffix : Program)
                   (ctx : ApplyContext {A} {B} prefix suffix)
                   (s s-final : State)
                   (x : ⟦ (A ⇒ B) * A ⟧) : Set where
  field
    -- Execution reached s-final
    apply-exec : exec 6 (prog ctx) s ≡ just s-final

    -- Not halted after apply code
    apply-halted : halted s-final ≡ false

    -- PC at end of apply code
    apply-pc : pc s-final ≡ length prefix +ℕ 6

    -- x0 contains result of applying closure to argument
    apply-x0 : readReg (regs s-final) x0 ≡ encode {B} (eval (apply {A} {B}) x)

    -- Callee-saved registers preserved
    apply-x20 : readReg (regs s-final) x20 ≡ readReg (regs s) x20
    apply-x21 : readReg (regs s-final) x21 ≡ readReg (regs s) x21

open ApplyResult public

------------------------------------------------------------------------
-- Thunk Execution (Legacy/Exec-based)
------------------------------------------------------------------------
--
-- NOTE: This is the legacy exec-based ThunkResult. For Star-based
-- proofs, use the ThunkResult from ClosureWellFormed (re-exported above).
--
-- After blr jumps to the thunk, the thunk code executes:
--   sub-sp 16           ; allocate pair on stack
--   stp x19 x0 [sp]     ; store (env, arg) pair
--   mov-from-sp x0      ; x0 = pair pointer
--   <f code>            ; execute f on pair
--   ret                 ; return to caller
--
-- The thunk receives:
--   x19 = encoded env (from closure)
--   x0 = encoded arg (from caller)
--
-- The thunk produces:
--   x0 = encode (eval f (env, arg))
--   Then ret returns to x30 (instruction after blr)

record ThunkResultExec {A B C : Type} (f : IR (A * B) C)
                       (env : ⟦ A ⟧) (arg : ⟦ B ⟧)
                       (s s-after : State) : Set where
  field
    -- Execution completed
    thunk-exec : ∃[ n ] (exec n (compile-aarch64 f) s ≡ just s-after)

    -- Halted after ret
    thunk-halted : halted s-after ≡ true

    -- x0 contains result
    thunk-x0 : readReg (regs s-after) x0 ≡ encode (eval f (env , arg))

open ThunkResultExec public

------------------------------------------------------------------------
-- Phase 3: Eliminated run-thunk-at-offset postulate
------------------------------------------------------------------------
--
-- This postulate was imported but never used in Apply.agda.
-- The actual thunk execution proof is provided by curry-thunk-correct-impl
-- in MutualIR.agda, which is used via ThunkProof.agda.
--
-- Eliminated in Phase 3 of postulate cleanup.

------------------------------------------------------------------------
-- Main Apply Postulate
------------------------------------------------------------------------
--
-- NOTE: The main apply postulate (apply-produces-result) is now in
-- Once.Backend.AArch64.Postulates. It provides a Star-based proof
-- with complete register and memory preservation guarantees.
--
-- For apply proofs, import from Postulates:
--   open import Once.Backend.AArch64.Postulates using (apply-produces-result)
--
-- For whole-program proofs with closure well-formedness, use:
--   run-apply-with-wf (from ClosureWellFormed, re-exported above)
--
-- The apply postulate is mathematically justified: we're asserting that
-- the AArch64 semantics correctly implement function application
-- when closures are properly formed by curry.

------------------------------------------------------------------------
-- Arithmetic Lemma
------------------------------------------------------------------------

-- | compile-length apply = 6
compile-length-apply : ∀ {A B : Type} → compile-length (apply {A} {B}) ≡ 6
compile-length-apply = refl

