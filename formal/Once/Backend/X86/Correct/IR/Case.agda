------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Case
--
-- Case setup and cleanup helpers for the case (sum elimination) proof.
-- Non-recursive parts that don't need the mutual recursion dispatcher.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Case where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Backend.X86.Correct.Star using (Star; refl*; step*; star-trans; star-step2; star-step6)
open import Once.Backend.X86.Correct.FetchStep using (step-exec)
open import Once.Backend.X86.Correct.ExecLemmas using (fetch-at-prefix-end)
open import Once.Backend.X86.Correct.InstrExec
  using (execPush-reg; execMov-reg-reg; execMov-reg-mem-base; execMov-reg-mem-disp;
         execCmp-zero; execCmp-one; execJne-not-taken; execJne-taken; execJmp; execPop)
open import Once.Backend.X86.Correct.StarBase using (IRStarResultV)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation
  using (slots; slot-size; StackCapacity; ir-stack-requirement; capacity-after-push)
-- RegisterLemmas not needed yet - will add when filling in step proofs
open import Once.Backend.Common.MemoryRegions using (InStack; InHeap; InCode; StackPointer)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _>_; _≤_; _<_; _∸_; suc; zero) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-trans; <-trans; ≤-<-trans; <⇒≤; m∸n≤m)
open import Data.List using (List; _++_; length; _∷_; [])
open import Data.List.Properties using (++-assoc)
open import Once.Backend.X86.Correct.CompileLength using (length-++)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst; subst₂)

------------------------------------------------------------------------
-- Case Inl Setup Result
--
-- Result of executing the 6-instruction setup sequence for inl branch:
--   0: push rbp
--   1: mov rbp, rsp
--   2: mov r11, [rdi]     ; load tag (should be 0)
--   3: cmp r11, 0         ; sets ZF=true
--   4: jne right-offset   ; NOT taken (ZF=true)
--   5: mov rdi, [rdi+8]   ; load value pointer
------------------------------------------------------------------------

record CaseInlSetupResult {A B C : Type} (a : ⟦ A ⟧)
    (prefix suffix : Program) (f : IR A C) (g : IR B C)
    (s s-setup : State) (val-addr : ℕ) : Set where
  field
    -- Execution star
    star-setup : Star (prefix ++ compile-x86 [ f , g ] ++ suffix) s s-setup
    -- State properties
    h-setup    : halted s-setup ≡ false
    pc-setup   : pc s-setup ≡ length prefix +ℕ 6
    -- Register values
    rdi-setup  : readReg (regs s-setup) rdi ≡ val-addr
    rbp-setup  : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ slot-size
    rsp-setup  : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slot-size
    r14-setup  : readReg (regs s-setup) r14 ≡ readReg (regs s) r14
    r15-setup  : readReg (regs s-setup) r15 ≡ readReg (regs s) r15
    -- Memory preservation
    mem-heap-setup : ∀ addr → InHeap addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    -- Invariants
    stack-inv-setup : StackInvariant s-setup
    rbp-inv-setup   : RbpInvariant s-setup

------------------------------------------------------------------------
-- Case Inl Setup Proof
--
-- This is the core setup proof: execute 6 instructions step by step.
-- Uses postulates for now - will be filled in with actual step proofs.
------------------------------------------------------------------------

-- | Execute the 6-instruction inl setup sequence
-- Takes: ValidAt (inj₁ a) rdi mem (so tag=0 and value ptr exists)
-- Returns: CaseInlSetupResult with all invariants
postulate
  case-inl-setup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
    (prefix suffix : Program) (a : ⟦ A ⟧) (s : State) (val-addr : ℕ) →
    halted s ≡ false →
    pc s ≡ length prefix →
    -- Tag is 0 (from ValidAt inl)
    readMem (memory s) (readReg (regs s) rdi) ≡ just 0 →
    -- Value pointer is at rdi+8
    readMem (memory s) (readReg (regs s) rdi +ℕ slot-size) ≡ just val-addr →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement [ f , g ]) →
    RbpInvariant s →
    ∃[ s-setup ] CaseInlSetupResult {A} {B} {C} a prefix suffix f g s s-setup val-addr

------------------------------------------------------------------------
-- Case Cleanup Result
--
-- Result of executing the 3-instruction cleanup sequence:
--   jmp cleanup-offset  ; skip right branch (for inl)
--   mov rsp, rbp        ; restore stack pointer
--   pop rbp             ; restore frame pointer
------------------------------------------------------------------------

record CaseCleanupResult {A B C : Type} (prefix suffix : Program) (f : IR A C) (g : IR B C)
    (s s-final : State) : Set where
  field
    -- Execution star
    star-cleanup : Star (prefix ++ compile-x86 [ f , g ] ++ suffix) s s-final
    -- State properties
    h-final : halted s-final ≡ false
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    -- Register restoration
    rsp-final : readReg (regs s-final) rsp ≡ readReg (regs s) rsp  -- restored via rbp
    rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s) rbp  -- popped from stack

------------------------------------------------------------------------
-- Case Cleanup Proof (for inl branch)
------------------------------------------------------------------------

postulate
  case-inl-cleanup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
    (prefix suffix : Program) (s : State) →
    halted s ≡ false →
    -- PC is at jmp instruction (after f completes)
    pc s ≡ length prefix +ℕ 6 +ℕ compile-length f →
    -- rbp points to saved old rbp
    -- rsp is somewhere in the stack
    StackInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s-final ] CaseCleanupResult {A} {B} {C} prefix suffix f g s s-final

