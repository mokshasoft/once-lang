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
-- run-apply-with-wf: Apply using ClosureWellFormed
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
-- Proof structure:
-- 1. Trace 5 setup instructions (load closure, env, code-ptr, arg)
-- 2. Trace call instruction (pushes return address, jumps to code-ptr)
-- 3. Use thunk-correct from ClosureWellFormed
-- 4. Thunk returns to offset+6 with result in rax
-- 5. Compose via star-trans

-- Postulate for tracing the 5 apply setup instructions
-- These load: closure-addr, arg, env-addr, code-ptr, then set up registers
postulate
  apply-setup-star : ∀ {A B} (prefix suffix : Program)
                     (code-ptr env-addr closure-addr : ℕ)
                     (arg : ⟦ A ⟧) (s : State) →
    let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
        offset = length prefix
    in
    halted s ≡ false →
    pc s ≡ offset →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    -- Memory layout
    readMem (memory s) (readReg (regs s) rdi) ≡ just closure-addr →
    readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just (encode arg) →
    readMem (memory s) closure-addr ≡ just env-addr →
    readMem (memory s) (closure-addr +ℕ 8) ≡ just code-ptr →
    -- Result after 5 instructions: r12=env, rdi=arg, r15=code-ptr, pc=offset+5
    ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ offset +ℕ 5
            × readReg (regs s') rdi ≡ encode arg
            × readReg (regs s') r12 ≡ env-addr
            × readReg (regs s') r15 ≡ code-ptr
            × readReg (regs s') r14 ≡ readReg (regs s) r14
            × readReg (regs s') rbp ≡ readReg (regs s) rbp
            × StackInvariant s'
            × readReg (regs s') rsp > 16)

-- Postulate for tracing the call instruction
-- call r15 pushes return address and jumps to code-ptr
postulate
  apply-call-star : ∀ {A B} (prefix suffix : Program)
                    (code-ptr : ℕ) (s : State) →
    let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
        offset = length prefix
        ret-addr = offset +ℕ 6
    in
    halted s ≡ false →
    pc s ≡ offset +ℕ 5 →
    readReg (regs s) r15 ≡ code-ptr →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    -- Result after call: pc=code-ptr, ret-addr on stack
    ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ code-ptr
            × readMem (memory s') (readReg (regs s') rsp) ≡ just ret-addr
            × readReg (regs s') rdi ≡ readReg (regs s) rdi
            × readReg (regs s') r12 ≡ readReg (regs s) r12
            × readReg (regs s') r14 ≡ readReg (regs s) r14
            × readReg (regs s') rbp ≡ readReg (regs s) rbp
            × StackInvariant s'
            × readReg (regs s') rsp > 16)

-- | run-apply-with-wf-impl: Implementation using targeted postulates
run-apply-with-wf : ∀ {A B} (prefix suffix : Program)
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
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ offset +ℕ compile-length (apply {A} {B})
          × readReg (regs s') rax ≡ encode (semantics arg)
          × readReg (regs s') r14 ≡ readReg (regs s) r14
          × readReg (regs s') rbp ≡ readReg (regs s) rbp
          × StackInvariant s'
          × readReg (regs s') rsp > 16)
run-apply-with-wf {A} {B} prefix suffix code-ptr env-addr semantics arg s
                  wf h-eq pc-eq stack-inv rsp>16 (closure-addr , mem-cl , mem-arg , mem-env , mem-cp) =
  s-final , star-all , h-final , pc-final , rax-final , r14-final , rbp-final , stack-inv-final , rsp>16-final
  where
    prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    offset = length prefix
    ret-addr = offset +ℕ 6

    -- Step 1: Trace 5 setup instructions
    setup-result = apply-setup-star {A} {B} prefix suffix code-ptr env-addr closure-addr arg s
                     h-eq pc-eq stack-inv rsp>16 mem-cl mem-arg mem-env mem-cp
    s-setup = proj₁ setup-result
    star-setup = proj₁ (proj₂ setup-result)
    h-setup = proj₁ (proj₂ (proj₂ setup-result))
    pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
    rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
    r12-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
    r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
    r14-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
    rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
    stack-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))
    rsp>16-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))

    -- Step 2: Trace call instruction
    call-result = apply-call-star {A} {B} prefix suffix code-ptr s-setup
                    h-setup pc-setup r15-setup stack-inv-setup rsp>16-setup
    s-call = proj₁ call-result
    star-call = proj₁ (proj₂ call-result)
    h-call = proj₁ (proj₂ (proj₂ call-result))
    pc-call = proj₁ (proj₂ (proj₂ (proj₂ call-result)))
    mem-ret = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ call-result))))
    rdi-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result)))))
    r12-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result))))))
    r14-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result)))))))
    rbp-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result))))))))
    stack-inv-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result)))))))))
    rsp>16-call = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result)))))))))

    -- Step 3: Use thunk-correct from ClosureWellFormed
    -- The thunk executes and returns to ret-addr with result in rax
    rdi-for-thunk : readReg (regs s-call) rdi ≡ encode arg
    rdi-for-thunk = trans rdi-call rdi-setup

    r12-for-thunk : readReg (regs s-call) r12 ≡ env-addr
    r12-for-thunk = trans r12-call r12-setup

    thunk-result = thunk-correct wf arg s-call ret-addr
                     h-call pc-call rdi-for-thunk r12-for-thunk mem-ret
                     stack-inv-call rsp>16-call
    s-thunk = proj₁ thunk-result
    thunk-res = proj₁ (proj₂ thunk-result)
    pc-thunk = proj₂ (proj₂ thunk-result)

    -- Final state is after thunk
    s-final = s-thunk
    star-thunk = thunk-star thunk-res

    -- Compose all Star proofs
    star-all : Star prog s s-final
    star-all = star-trans star-setup (star-trans star-call star-thunk)

    -- Extract final properties
    h-final = thunk-halted thunk-res
    pc-final = pc-thunk  -- pc = ret-addr = offset + 6
    rax-final = thunk-rax thunk-res
    r14-final = trans (thunk-r14 thunk-res) (trans r14-call r14-setup)
    rbp-final = trans (thunk-rbp thunk-res) (trans rbp-call rbp-setup)
    stack-inv-final = thunk-stack-inv thunk-res
    rsp>16-final = thunk-rsp-bound thunk-res

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
