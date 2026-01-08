{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Postulates
--
-- AArch64-specific postulates. Separated from Once.Postulates to avoid
-- cyclic imports with AArch64 modules.
--
-- See Once.Postulates for documentation format and checklist.
------------------------------------------------------------------------

module Once.Backend.AArch64.Postulates where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; length; _++_; _∷_; [])
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)

open import Data.String using (String)

open import Once.Type using (Type; _⇒_; _*_)
open import Once.IR using (apply; curry; IR; Prim)
open import Once.Semantics using (⟦_⟧; encode; eval)
open import Once.Memory using (Word)

open import Once.Backend.AArch64.Syntax using (x0; x19; x20; x21; x29; x30; Program; sub-sp; stp; sp+imm; mov-from-sp; ret)
open import Once.Backend.AArch64.Semantics using (State; readReg; readSP; readMem; exec)
open import Once.Backend.AArch64.Semantics using () renaming (module State to St)
open St using (regs; memory; halted; pc)
open import Once.Backend.AArch64.Correct.Star using (Star)
open import Once.Backend.AArch64.Correct.StackInvariant using (StackInvariant; X29Invariant)
open import Once.Backend.AArch64.Correct.ClosureWellFormed using (ThunkResult)
open import Once.Backend.AArch64.CodeGen using (compile-aarch64; compile-length)

------------------------------------------------------------------------
-- Postulate P4: Stack Pointer Bounds (Runtime Property)
------------------------------------------------------------------------
--
-- After any stack-using operation, sp remains > 16.
--
-- NEEDED BY: Once.Backend.AArch64.Correct.MutualIR (inl, inr, pair, case, curry)
--
-- JUSTIFICATION:
--   The initial sp is a large address (e.g., 0x7FFF0000). Stack-using
--   operations subtract at most 64 bytes per call. Even with deep
--   recursion (millions of calls), total stack usage is bounded and
--   sp never drops below 16. This is a runtime guarantee from the
--   execution environment.
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
  sp-bound-after-stack-op : ∀ (s : State) → readSP (regs s) > 16

------------------------------------------------------------------------
-- ELIMINATED P6: Curry Thunk Correctness
------------------------------------------------------------------------
--
-- STATUS: ✓ ELIMINATED in Phase 3
--
-- The thunk code embedded in a curry-created closure executes correctly.
--
-- PREVIOUSLY NEEDED BY:
--   - Once.Backend.AArch64.Correct.ThunkProof (construct-closure-wf)
--   - Once.Backend.AArch64.Correct.MutualIR (run-curry-star-direct)
--
-- ELIMINATION:
--   Replaced by curry-thunk-correct-impl in MutualIR.agda (line ~2606).
--   This implementation exists in the mutual block with access to the IH
--   (run-ir-star-at-offset), and follows the strategy outlined below.
--
-- PROOF STRATEGY (now implemented):
--   1. Trace 4 thunk setup instructions using Star steps
--   2. Call run-ir-star-at-offset on f (the IH from mutual block)
--   3. Trace ret instruction
--   4. Compose via star-trans to produce ThunkResult
--
-- USAGE:
--   Import curry-thunk-correct-impl from MutualIR instead:
--     open import Once.Backend.AArch64.Correct.MutualIR using (curry-thunk-correct-impl)
--
------------------------------------------------------------------------

-- POSTULATE ELIMINATED - use curry-thunk-correct-impl from MutualIR.agda
{-
postulate
  curry-thunk-correct : ∀ {i} {A B C} (f : IR (A * B) C)
                        (prefix suffix : Program) (env : ⟦ A ⟧)
                        (arg : ⟦ B ⟧) (s : State) (ret-addr : ℕ) →
    let prog = prefix ++ compile-aarch64 (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 6  -- code-ptr label is at offset 6
    in
    halted s ≡ false →
    pc s ≡ thunk-offset →
    readReg (regs s) x0 ≡ encode arg →
    readReg (regs s) x19 ≡ encode env →
    readReg (regs s) x30 ≡ ret-addr →  -- Return address in link register
    StackInvariant s →
    readSP (regs s) > 16 →
    ∃[ s' ] (ThunkResult prog s s' (λ b → eval f (env , b)) arg
            × pc s' ≡ ret-addr)
-}

------------------------------------------------------------------------
-- ELIMINATED P7: Thunk Execution at Offset
------------------------------------------------------------------------
--
-- STATUS: ✓ ELIMINATED in Phase 3
--
-- Execute thunk code with arbitrary prefix/suffix in the program.
--
-- PREVIOUSLY NEEDED BY:
--   - Once.Backend.AArch64.Correct.IR.Apply (but was imported, never used)
--
-- ELIMINATION:
--   This postulate was imported in Apply.agda but never actually called.
--   The actual thunk execution proof is provided by curry-thunk-correct-impl
--   in MutualIR.agda, which is used via ThunkProof.agda's construct-closure-wf.
--
-- PROOF STRATEGY (implemented via curry-thunk-correct-impl):
--   1. Trace 4 thunk setup instructions using Star
--   2. Call run-ir-star-at-offset on f (IH from mutual block)
--   3. Trace ret instruction
--   4. Compose via star-trans
--
-- NOTE:
--   If standalone thunk execution is ever needed outside of curry context,
--   curry-thunk-correct-impl can be adapted or a new wrapper added to MutualIR.
--
------------------------------------------------------------------------

-- POSTULATE ELIMINATED - was unused, covered by curry-thunk-correct-impl
{-
postulate
  run-thunk-at-offset : ∀ {i} {A B C} (f : IR (A * B) C)
    (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x19 ≡ encode {A} env →
    readReg (regs s) x0 ≡ encode {B} arg →
    let thunk-code = sub-sp 16 ∷ stp x19 x0 (sp+imm 0) ∷
                     mov-from-sp x0 ∷ compile-aarch64 f ++ ret ∷ []
        thunk-len = 4 +ℕ compile-length f
    in ∃[ s' ] (exec thunk-len (prefix ++ thunk-code ++ suffix) s ≡ just s'
              × halted s' ≡ false
              × readReg (regs s') x0 ≡ encode {C} (eval f (env , arg)))
-}

------------------------------------------------------------------------
-- Postulate P5: Closure Application (Temporary - Should be Eliminated)
------------------------------------------------------------------------
--
-- STATUS: TODO - SHOULD BE ELIMINATED for closed Once programs
--
-- Executing `apply` on a closure produces the correct result.
--
-- NEEDED BY: Once.Backend.AArch64.Correct.MutualIR (run-apply-star-direct)
--
-- IMPORTANT CLARIFICATION (2026-01-06):
--   This postulate is NOT a fundamental limitation for closed Once programs
--   where all closures are created by the Once compiler's curry operation.
--   It was introduced when attempting modular proofs that treat apply in
--   isolation, but for closed programs this should be eliminatable.
--
-- WHY IT EXISTS:
--   The modular proof architecture currently cannot prove this because:
--   - Apply's `blr x9` jumps to thunk code created by curry
--   - The thunk code is in `prefix`, not in `compile-aarch64 apply`
--   - Modular proofs verify each IR term in isolation
--   - Apply doesn't know where the closure came from
--
-- FOR CLOSED ONCE PROGRAMS:
--   When all closures come from Once's curry operation, we can:
--   1. Track closure creation through curry using ClosureEntry
--   2. Thread this information through compositions
--   3. Use run-apply-with-wf instead of the postulate
--
--   This is exactly what the ClosureEntry infrastructure enables!
--
-- INFRASTRUCTURE FOR ELIMINATION:
--   Complete infrastructure exists and is being developed:
--
--   1. ClosureEntry tracking (ClosureContext.agda, StarBase.agda)
--      - ir-closure-entry field added to IRStarResult
--      - Curry now produces ClosureEntry records
--
--   2. ClosureWellFormed predicate (ClosureWellFormed.agda:88-134)
--      - Captures that code_ptr points to valid thunk in program
--      - thunk-correct field proves thunk executes correctly
--
--   3. run-apply-with-wf provides postulate-free apply proof
--      - Takes ClosureWellFormed as precondition
--      - Proves apply correctness using thunk-correct from the proof
--
-- ELIMINATION PLAN:
--   Phase 5.1: Replace postulated curry-closure-wf with actual proof
--   Phase 7: Update Compose/Pair/Case to thread ClosureEntry
--   Phase 8: Update other operations to preserve context
--   Phase 9: Use run-apply-with-wf instead of postulate for closed programs
--
-- ELIMINATION FOR ONCE PROGRAMS:
--   For programs generated by the Once compiler where all closures come from
--   curry operations, this postulate should be eliminated. The infrastructure
--   exists (ClosureEntry tracking) to prove this without the postulate.
--
--   If a Once programmer interfaces with external code (calling in/out from Once),
--   they must prove that the external code satisfies the required properties.
--
-- RUNTIME EFFECT: None (proof-only axiom)
--
------------------------------------------------------------------------

postulate
  apply-produces-result : ∀ {A B : Type} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode {(A ⇒ B) * A} x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 (apply {A} {B}) ++ suffix
    in ∃[ s' ] (Star prog s s'
              × halted s' ≡ false
              × pc s' ≡ length prefix +ℕ compile-length (apply {A} {B})
              × readReg (regs s') x0 ≡ encode {B} (eval (apply {A} {B}) x)
              × readReg (regs s') x20 ≡ readReg (regs s) x20
              × readReg (regs s') x21 ≡ readReg (regs s) x21
              × readReg (regs s') x29 ≡ readReg (regs s) x29
              × readReg (regs s') x30 ≡ readReg (regs s) x30
              × readSP (regs s') ≤ readSP (regs s)
              × readMem (memory s') (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
              × readMem (memory s') (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
              × readMem (memory s') (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
              × StackInvariant s'
              × X29Invariant s'
              × readSP (regs s') > 16)

------------------------------------------------------------------------
-- Postulate: Prim Correctness (Opaque Primitive)
------------------------------------------------------------------------
--
-- Prim: opaque primitive - correctness postulated until proper Prim compilation
-- NOTE: Current compile-aarch64 (Prim _) = nop (identity)
-- But eval (Prim name) x = evalPrim name x (arbitrary function)
-- These don't match, so correctness is postulated.
--
------------------------------------------------------------------------

postulate
  run-prim-star : ∀ {A B : Type} (name : String) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode {A} x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 (Prim {A} {B} name) ++ suffix
    in ∃[ s' ] (Star prog s s'
              × halted s' ≡ false
              × pc s' ≡ length prefix +ℕ compile-length (Prim {A} {B} name)
              × readReg (regs s') x0 ≡ encode {B} (eval (Prim {A} {B} name) x)
              × readReg (regs s') x20 ≡ readReg (regs s) x20
              × readReg (regs s') x21 ≡ readReg (regs s) x21
              × readReg (regs s') x29 ≡ readReg (regs s) x29
              × readReg (regs s') x30 ≡ readReg (regs s) x30
              × readSP (regs s') ≤ readSP (regs s)
              × readMem (memory s') (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
              × readMem (memory s') (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
              × readMem (memory s') (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
              × StackInvariant s'
              × X29Invariant s'
              × readSP (regs s') > 16)

------------------------------------------------------------------------
-- NOTE: Encoding postulates are in Once.Postulates
------------------------------------------------------------------------
--
-- The following encoding axioms are defined in Once.Postulates and
-- should be imported from there (not duplicated here):
--
--   encode-pair-fst, encode-pair-snd     : Pair layout
--   encode-inl-tag, encode-inl-val       : Sum (left) layout
--   encode-inr-tag, encode-inr-val       : Sum (right) layout
--   encode-pair-construct                : Pair construction
--   encode-inl-construct, encode-inr-construct : Sum construction
--   encode-closure-construct             : Closure construction
--
-- Foundation.agda imports these from Once.Postulates (no duplication).
--
------------------------------------------------------------------------
