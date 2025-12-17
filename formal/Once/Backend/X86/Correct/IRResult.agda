------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IRResult
--
-- Result record type for IR execution proofs.
-- Replaces the 9-tuple with named fields for cleaner access.
--
-- Level 2 - depends on StackInvariant, ExecLemmas
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IRResult where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant)
open import Once.Backend.X86.Correct.ExecLemmas using (runFuel)

open import Once.Postulates using (encode)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Maybe using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- IRResult Record
------------------------------------------------------------------------

-- | Result of executing IR at an offset in a program
-- Captures all 9 properties about the final state s'
record IRResult {A B : Type} (ir : IR A B)
                (prefix suffix : Program) (x : ⟦ A ⟧)
                (s s' : State) : Set where
  field
    -- Execution reaches s' via exec-until-pc
    exec-eq   : exec-until-pc (length prefix +ℕ compile-length ir) runFuel
                  (prefix ++ compile-x86 ir ++ suffix) s ≡ just s'
    -- Still executing (not halted)
    halted-eq : halted s' ≡ false
    -- PC at exact end of compiled code
    pc-eq     : pc s' ≡ length prefix +ℕ compile-length ir
    -- RAX contains encoded result
    rax-eq    : readReg (regs s') rax ≡ encode (eval ir x)
    -- Callee-saved r14 preserved
    r14-pres  : readReg (regs s') r14 ≡ readReg (regs s) r14
    -- Callee-saved r15 preserved
    r15-pres  : readReg (regs s') r15 ≡ readReg (regs s) r15
    -- Memory at frame base [r15] preserved
    mem-pres  : readMem (memory s') (readReg (regs s) r15) ≡
                  readMem (memory s) (readReg (regs s) r15)
    -- Stack invariant maintained
    stack-inv : StackInvariant s'
    -- RSP still valid for stack operations
    rsp-valid : readReg (regs s') rsp > 16

open IRResult public

------------------------------------------------------------------------
-- Helper: Convert 9-tuple to IRResult
------------------------------------------------------------------------

-- | Convert the old 9-tuple format to IRResult record
-- Useful for transitioning existing proofs
mkIRResult : ∀ {A B : Type} {ir : IR A B} {prefix suffix : Program} {x : ⟦ A ⟧} {s s' : State} →
  exec-until-pc (length prefix +ℕ compile-length ir) runFuel
    (prefix ++ compile-x86 ir ++ suffix) s ≡ just s' →
  halted s' ≡ false →
  pc s' ≡ length prefix +ℕ compile-length ir →
  readReg (regs s') rax ≡ encode (eval ir x) →
  readReg (regs s') r14 ≡ readReg (regs s) r14 →
  readReg (regs s') r15 ≡ readReg (regs s) r15 →
  readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15) →
  StackInvariant s' →
  readReg (regs s') rsp > 16 →
  IRResult ir prefix suffix x s s'
mkIRResult e h p rax-p r14-p r15-p m si rsp-p = record
  { exec-eq   = e
  ; halted-eq = h
  ; pc-eq     = p
  ; rax-eq    = rax-p
  ; r14-pres  = r14-p
  ; r15-pres  = r15-p
  ; mem-pres  = m
  ; stack-inv = si
  ; rsp-valid = rsp-p
  }
