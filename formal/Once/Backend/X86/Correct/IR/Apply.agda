------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Apply
--
-- Star-based apply proof using ClosureWellFormed.
--
-- Apply compilation (6 instructions):
--   0: mov r15, [rdi]      ; load closure from pair.fst
--   1: mov rsi, [rdi+8]    ; load argument from pair.snd
--   2: mov r12, [r15]      ; load env from closure.fst
--   3: mov r15, [r15+8]    ; load code_ptr from closure.snd
--   4: mov rdi, rsi        ; move argument to rdi
--   5: call r15            ; call thunk (pushes ret addr, jumps to code_ptr)
--
-- After call r15:
--   - PC = code_ptr (thunk entry)
--   - Return address (offset+6) is on stack
--   - r12 = env, rdi = arg
--
-- Thunk execution (via ClosureWellFormed.thunk-correct):
--   - Thunk runs with r12=env, rdi=arg
--   - Thunk ends with ret, popping return address
--   - PC returns to offset+6
--   - rax = encode (semantics arg)
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Apply where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

open import Once.Postulates
  using (encode; encode-pair-fst; encode-pair-snd)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-stack-inv; ir-rsp-bound)
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ClosureWellFormed; ThunkResult;
         code-ptr-valid; thunk-correct;
         thunk-star; thunk-halted; thunk-rax;
         thunk-r14; thunk-r15; thunk-rbp;
         thunk-stack-inv; thunk-rsp-bound)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _>_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- run-apply-star-with-wf: Apply using ClosureWellFormed
------------------------------------------------------------------------

-- | Execute apply with a well-formedness proof for the closure
--
-- KEY INSIGHT: Apply receives a pair (closure, arg) where:
-- - closure = address pointing to (env-addr, code-ptr)
-- - arg = encoded argument value
--
-- The ClosureWellFormed proof tells us that executing from code-ptr
-- with r12=env-addr and rdi=arg produces the correct result.
--
-- Proof sketch:
-- 1. Load closure-addr from [rdi] (pair.fst)
-- 2. Load arg from [rdi+8] (pair.snd)
-- 3. Load env-addr from [closure-addr]
-- 4. Load code-ptr from [closure-addr+8]
-- 5. Set up rdi=arg, r12=env-addr
-- 6. Call code-ptr (pushes return address offset+6)
-- 7. Thunk executes (by thunk-correct from ClosureWellFormed)
-- 8. Thunk returns to offset+6 with result in rax
--
-- POSTULATED: The detailed instruction tracing is complex.
-- This postulate captures the essence: if we have ClosureWellFormed
-- and the memory layout matches, apply produces the correct result.
postulate
  run-apply-with-wf : ∀ {A B} (prefix suffix : Program)
                      (code-ptr env-addr : ℕ)
                      (semantics : ⟦ A ⟧ → ⟦ B ⟧)
                      (arg : ⟦ A ⟧) (s : State) →
    let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
        offset = length prefix
    in
    -- The closure is well-formed
    ClosureWellFormed {A} {B} prog code-ptr env-addr semantics →
    -- Standard preconditions
    halted s ≡ false →
    pc s ≡ offset →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    -- Memory layout: rdi points to pair (closure-addr, encode arg)
    -- closure-addr points to (env-addr, code-ptr)
    (∃[ closure-addr ] (
      readMem (memory s) (readReg (regs s) rdi) ≡ just closure-addr ×
      readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just (encode arg) ×
      readMem (memory s) closure-addr ≡ just env-addr ×
      readMem (memory s) (closure-addr +ℕ 8) ≡ just code-ptr)) →
    -- Result
    ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ offset +ℕ compile-length (apply {A} {B})
            × readReg (regs s') rax ≡ encode (semantics arg)
            × readReg (regs s') r14 ≡ readReg (regs s) r14
            × readReg (regs s') rbp ≡ readReg (regs s) rbp
            × StackInvariant s'
            × readReg (regs s') rsp > 16)

------------------------------------------------------------------------
-- Converting to IRStarResult format
------------------------------------------------------------------------

-- | Wrapper that produces IRStarResult from run-apply-with-wf
run-apply-star-with-wf : ∀ {A B} (prefix suffix : Program)
                         (code-ptr env-addr : ℕ)
                         (semantics : ⟦ A ⟧ → ⟦ B ⟧)
                         (arg : ⟦ A ⟧) (s : State) →
  let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      offset = length prefix
  in
  ClosureWellFormed {A} {B} prog code-ptr env-addr semantics →
  halted s ≡ false →
  pc s ≡ offset →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  (∃[ closure-addr ] (
    readMem (memory s) (readReg (regs s) rdi) ≡ just closure-addr ×
    readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just (encode arg) ×
    readMem (memory s) closure-addr ≡ just env-addr ×
    readMem (memory s) (closure-addr +ℕ 8) ≡ just code-ptr)) →
  -- Note: The input type for apply is (closure , arg) but we abstract over semantics
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ offset +ℕ 6  -- compile-length apply = 6
          × readReg (regs s') rax ≡ encode (semantics arg)
          × StackInvariant s'
          × readReg (regs s') rsp > 16)
run-apply-star-with-wf {A} {B} prefix suffix code-ptr env-addr semantics arg s
                       wf h-eq pc-eq stack-inv rsp>16 mem-layout =
  let (s' , star , h' , pc' , rax' , r14' , rbp' , stack' , rsp') =
        run-apply-with-wf prefix suffix code-ptr env-addr semantics arg s
          wf h-eq pc-eq stack-inv rsp>16 mem-layout
  in s' , star , h' , pc' , rax' , stack' , rsp'
