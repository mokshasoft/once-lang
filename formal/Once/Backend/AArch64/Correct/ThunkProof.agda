{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.ThunkProof
--
-- Infrastructure for proving thunk correctness in curry.
-- The thunk is the closure body that executes when apply calls it.
--
-- ARCHITECTURE:
--   curry f compiles to:
--     [0]: sub-sp 16           ; allocate closure
--     [1]: str x0 [sp]         ; store env (input x)
--     [2]: adr x9 4            ; compute code-ptr = pc + 4
--     [3]: str x9 [sp+8]       ; store code pointer
--     [4]: mov-from-sp x0      ; return closure pointer
--     [5]: b end-label         ; jump over thunk (11 + |f|)
--     [6]: label 6             ; thunk entry point
--     [7]: sub-sp 16           ; thunk: allocate pair
--     [8]: stp x19 x0 [sp]     ; thunk: store (env, arg)
--     [9]: mov-from-sp x0      ; thunk: x0 = pair pointer
--     [10 to 9+|f|]: code-f    ; thunk: execute f
--     [10+|f|]: ret            ; thunk: return to x30
--     [11+|f|]: label end      ; end of curry
--
--   compile-length (curry f) = 12 + |f|
--
--   When apply calls the closure via blr:
--     1. apply loads env into x19, arg into x0
--     2. blr x9 jumps to code-ptr, sets x30 = return address
--     3. thunk creates pair (x19, x0), calls f, returns result in x0
--     4. ret reads x30 and jumps back to after blr in apply
--
-- PROVING THUNK CORRECTNESS:
--   Given: state at thunk entry (pc = code-ptr)
--          x19 = encoded env, x0 = encoded arg
--          x30 = return address (set by blr)
--   Prove: executing thunk produces correct result and returns
--
--   Steps:
--     1. Trace 4 instructions (label, sub-sp, stp, mov-from-sp)
--     2. At pc = offset+10, x0 = address of pair (env, arg)
--     3. Call IH on f: run-ir-star-at-offset f prefix' suffix'
--        where prefix' = prefix ++ [first 10 curry instructions]
--              suffix' = [ret, label] ++ suffix
--     4. Trace ret instruction
--     5. Compose Star proofs
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.ThunkProof where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open Once.Backend.AArch64.Semantics.State
open import Once.Backend.AArch64.CodeGen
  using (compile-aarch64; compile-length; thunk-entry-offset)

open import Once.Backend.AArch64.Correct.Star
  using (Star; refl*; step*; star-trans)
open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant)
open import Once.Backend.AArch64.Correct.ClosureWellFormed
  using (ThunkResult; ClosureWellFormed; CurryResult;
         thunk-star; thunk-halted; thunk-x0;
         thunk-x20; thunk-x21; thunk-x29; thunk-stack-inv; thunk-sp-bound;
         code-ptr-valid; thunk-correct;
         curry-star; curry-halted; curry-pc; curry-x0;
         curry-x20; curry-x21; curry-x29; curry-x30;
         curry-mem-x21; curry-mem-x29; curry-mem-x29+8;
         curry-stack-inv; curry-sp-bound; closure-wf)

open import Once.Backend.AArch64.Correct.Foundation using (encode)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_; _<_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

-- Import curry-thunk-correct-impl from MutualIR (proven in mutual block)
-- Phase 3: Eliminated curry-thunk-correct postulate by using the implementation
open import Once.Backend.AArch64.Correct.MutualIR using (curry-thunk-correct-impl)

------------------------------------------------------------------------
-- construct-closure-wf: Build ClosureWellFormed from curry context
--
-- After curry executes, we know:
--   - The closure is at x0 (= new-sp)
--   - [closure] = encode env
--   - [closure+8] = code-ptr = offset + 6
--
-- The thunk at code-ptr is correct by curry-thunk-correct-impl.
-- The implementation returns exactly the type expected by thunk-correct:
--   ∃[ s' ] (ThunkResult prog s s' semantics arg × pc s' ≡ ret-addr)
------------------------------------------------------------------------

construct-closure-wf : ∀ {i} {A B C} (f : IR (A * B) C)
                       (prefix suffix : Program) (env : ⟦ A ⟧) →
  let prog = prefix ++ compile-aarch64 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ thunk-entry-offset
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
    ; thunk-correct = λ arg s ret-addr h-eq pc-eq x0-eq x19-eq x30-eq stack-inv sp>16 →
        curry-thunk-correct-impl f prefix suffix env arg s ret-addr
                                  h-eq pc-eq x0-eq x19-eq x30-eq stack-inv sp>16
    }
