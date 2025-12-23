------------------------------------------------------------------------
-- Once.Backend.X86.Correct.ThunkProof
--
-- Infrastructure for proving thunk correctness in curry.
-- The thunk is the closure body that executes when apply calls it.
--
-- ARCHITECTURE:
--   curry f compiles to:
--     [0-5]: Closure creation (stores env and code-ptr, returns closure addr)
--     [6]: label (thunk entry point)
--     [7-10]: Thunk setup (creates pair from r12 and rdi)
--     [11 to 10+len(f)]: compile-x86 f
--     [11+len(f)]: ret
--     [12+len(f)]: label (end)
--
--   When apply calls the closure:
--     1. apply loads env into r12, arg into rdi
--     2. apply calls code-ptr (jumps to offset 6)
--     3. thunk creates pair (env, arg), calls f, returns result in rax
--     4. ret jumps back to after the call in apply
--
-- PROVING THUNK CORRECTNESS:
--   Given: state at thunk entry (pc = code-ptr)
--          r12 = encoded env, rdi = encoded arg
--          return address on stack
--   Prove: executing thunk produces correct result and returns
--
--   Steps:
--     1. Trace 5 instructions (label, sub, mov, mov, mov)
--     2. At pc = offset+11, rdi = address of pair (env, arg)
--     3. Call IH on f: run-ir-star-at-offset f prefix' suffix'
--        where prefix' = prefix ++ [first 11 curry instructions]
--              suffix' = [ret, label] ++ suffix
--     4. Trace ret instruction
--     5. Compose Star proofs
------------------------------------------------------------------------

module Once.Backend.X86.Correct.ThunkProof where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant)
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ThunkResult; ClosureWellFormed; CurryResult;
         thunk-star; thunk-halted; thunk-rax;
         thunk-r14; thunk-r15; thunk-rbp; thunk-stack-inv; thunk-rsp-bound;
         code-ptr-valid; thunk-correct;
         curry-star; curry-halted; curry-pc; curry-rax;
         curry-r14; curry-r15; curry-rbp; curry-mem;
         curry-stack-inv; curry-rsp-bound; closure-wf)

open import Once.Postulates using (encode)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_; _<_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

------------------------------------------------------------------------
-- Postulate: thunk correctness
--
-- This captures that the thunk executes correctly.
-- TO PROVE: Use run-ir-star-at-offset on f from within the mutual block.
--
-- JUSTIFICATION:
--   The thunk is compiled by curry and contains compile-x86 f.
--   In a whole-program context, the thunk is part of the same program
--   that the IH (run-ir-star-at-offset) applies to.
--   The proof would:
--   1. Trace 5 setup instructions (Star steps)
--   2. Call run-ir-star-at-offset on f
--   3. Trace ret instruction
--   4. Compose via star-trans
--
-- This postulate is more targeted than apply-produces-result because:
--   - It's about the thunk only, not all of apply
--   - It can be proven once curry's structure is understood
--   - It doesn't cross compilation boundaries (thunk is in curry's output)
--
-- KEY INSIGHT:
--   The thunk code is:
--     label :: sub rsp 16 :: mov [rsp] r12 :: mov [rsp+8] rdi :: mov rdi rsp
--     :: compile-x86 f :: ret :: label end
--   The IH on f gives us that compile-x86 f is correct.
--   We just need to trace the setup and ret around it.
------------------------------------------------------------------------

postulate
  curry-thunk-correct : ∀ {A B C} (f : IR (A * B) C)
                        (prefix suffix : Program) (env : ⟦ A ⟧)
                        (arg : ⟦ B ⟧) (s : State) (ret-addr : ℕ) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 6  -- code-ptr label is at offset 6
    in
    halted s ≡ false →
    pc s ≡ thunk-offset →
    readReg (regs s) rdi ≡ encode arg →
    readReg (regs s) r12 ≡ encode env →
    readMem (memory s) (readReg (regs s) rsp) ≡ just ret-addr →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    ∃[ s' ] (ThunkResult prog s s' (λ b → eval f (env , b)) arg
            × pc s' ≡ ret-addr)

------------------------------------------------------------------------
-- construct-closure-wf: Build ClosureWellFormed from curry context
--
-- After curry executes, we know:
--   - The closure is at rax (= new-rsp)
--   - [closure] = encode env
--   - [closure+8] = code-ptr = offset + 6
--
-- The thunk at code-ptr is correct by curry-thunk-correct.
------------------------------------------------------------------------

construct-closure-wf : ∀ {A B C} (f : IR (A * B) C)
                       (prefix suffix : Program) (env : ⟦ A ⟧) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
  in
  -- Precondition: thunk-offset is within program bounds
  thunk-offset < length prog →
  ClosureWellFormed {B} {C} prog
    thunk-offset          -- code-ptr
    (encode env)          -- env-addr
    (λ b → eval f (env , b))  -- semantics
construct-closure-wf {A} {B} {C} f prefix suffix env thunk-in-bounds =
  record
    { code-ptr-valid = thunk-in-bounds
    ; thunk-correct = λ arg s ret-addr h-eq pc-eq rdi-eq r12-eq mem-ret stack-inv rsp>16 →
        curry-thunk-correct f prefix suffix env arg s ret-addr
          h-eq
          pc-eq
          rdi-eq
          r12-eq
          mem-ret
          stack-inv
          rsp>16
    }
