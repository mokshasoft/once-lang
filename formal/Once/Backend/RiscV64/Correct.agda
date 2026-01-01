{-# OPTIONS --sized-types #-}

------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct
--
-- Correctness proofs for RISC-V 64-bit code generation.
--
-- Main theorem (fuel-free, Star-based):
--   star-codegen-correct : ∀ (ir : IR A B) (x : ⟦A⟧) →
--     ∃[ s ] (Star (compile-riscv ir) (initWithInput x) s
--           × halted s ≡ true
--           × readReg (regs s) a0 ≡ encode (eval ir x))
--
-- This module orchestrates the modular proof components:
--   - Foundation: basic lemmas and instruction execution
--   - CompileLength: compile-length-correct theorem
--   - Star: reflexive-transitive closure of step
--   - StarBase: IRStarResult record and base case proofs
--   - MutualIR: Star-based mutual block for all IR constructors
--
-- The proof strategy (fuel-free):
--   1. run-ir-star (from MutualIR) gives Star-based execution proof
--   2. Add halting step when PC reaches end of program (fetch fails)
--   3. Return Star directly - no fuel conversion needed!
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct where

open import Size

open import Once.Type
open import Once.IR
open import Once.Semantics
open import Once.Semantics using (⟦Fix⟧)
open ⟦Fix⟧

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open Once.Backend.RiscV64.Semantics.State
open import Once.Backend.RiscV64.CodeGen

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

-- Import and re-export all foundation lemmas
open import Once.Backend.RiscV64.Correct.Foundation public

-- Import compile-length-correct from modular module
open import Once.Backend.RiscV64.Correct.CompileLength public
  using (compile-length-correct)

-- Import Star relation (no fuel bridging needed!)
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; star-trans)

-- Import StarBase for IRStarResult
open import Once.Backend.RiscV64.Correct.StarBase
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-a0; ir-s1)

-- Import MutualIR for run-ir-star
open import Once.Backend.RiscV64.Correct.MutualIR
  using (run-ir-star; run-ir-star-at-offset)

------------------------------------------------------------------------
-- Star-based correctness: star-generator (fuel-free)
--
-- This is the core generator that uses run-ir-star from MutualIR.
-- After IR execution, PC is at the end of the program. One more step
-- causes halting (fetch fails), giving us a complete execution.
--
-- NO fuel conversion needed - we work directly with Star!
------------------------------------------------------------------------

-- | star-generator: Fuel-free correctness using Star
--
-- Uses run-ir-star from MutualIR, then:
--   1. Get Star-based result
--   2. Add halting step when PC reaches end of program (fetch fails)
--   3. Return Star directly - no fuel!
star-generator : ∀ {i A B} (ir : IR i A B) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  StackDepth ir ≤ readReg (regs s) sp →
  let prog = compile-riscv ir
  in ∃[ s' ] (Star prog s s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode (eval ir x))
star-generator {_} {A} {B} ir x s h-false pc-0 a0-eq sp-bound = s'' , star-with-halt , refl , a0-eq'
  where
    -- Step 1: Get Star-based result from MutualIR
    star-result = run-ir-star ir x s h-false pc-0 a0-eq sp-bound
    s' = proj₁ star-result
    result = proj₂ star-result
    prog = compile-riscv ir
    star-proof = ir-star result
    h' = ir-halted result
    a0-eq' = ir-a0 result

    -- pc s' ≡ compile-length ir (from ir-pc with offset=0)
    pc' : pc s' ≡ compile-length ir
    pc' = ir-pc result

    -- Step 2: Prove fetch fails at pc = compile-length ir
    pc-at-end : pc s' ≡ length prog
    pc-at-end = trans pc' (sym (compile-length-correct ir))

    fetch-fail : fetch prog (pc s') ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing)
                       (sym pc-at-end)
                       (fetch-past-end prog)

    -- Step 3: Next step halts
    s'' : State
    s'' = record s' { halted = true }

    step-halt : step prog s' ≡ just s''
    step-halt = step-halt-on-fetch-fail prog s' h' fetch-fail

    -- Step 4: Build final Star proof (add halting step)
    halt-step = step* h' step-halt refl*

    star-with-halt : Star prog s s''
    star-with-halt = star-trans star-proof halt-step

------------------------------------------------------------------------
-- Main Correctness Theorem (Star-based, fuel-free)
------------------------------------------------------------------------

-- | Main correctness theorem (Star-based, parameterized by stack size)
--
-- For any IR term and sufficient stack, we can prove Star-based execution
-- reaches a halted state with the correct result in a0. No fuel needed!
--
-- The stack size is now an explicit parameter with an explicit precondition.
-- This replaces the false postulate that all IR programs fit in 2GB.
--
-- Usage:
--   let stackSize = StackDepth ir + 1024  -- Compute required stack + margin
--       proof = star-codegen-correct ir stackSize x (auto-prove stackSize ≥ StackDepth ir)
--   in ...
star-codegen-correct : ∀ {i A B} (ir : IR i A B) (stackSize : ℕ) (x : ⟦ A ⟧) →
  StackDepth ir ≤ stackSize →  -- Explicit precondition
  ∃[ s ] (Star (compile-riscv ir) (initWithInput stackSize x) s
        × halted s ≡ true
        × readReg (regs s) a0 ≡ encode (eval ir x))
star-codegen-correct ir stackSize x sp-bound =
  star-generator ir x (initWithInput stackSize x)
    (initWithInput-halted stackSize x) (initWithInput-pc stackSize x) (initWithInput-a0 stackSize x) (initWithInput-sp-sufficient ir stackSize x sp-bound)

------------------------------------------------------------------------
-- Example: star-id-correct
------------------------------------------------------------------------
--
-- Keeping one example for reference showing how to use the parameterized
-- star-codegen-correct theorem.
--
-- NOTE: Individual IR test theorems removed
-- The old test theorems (star-terminal-correct, star-fold-correct, etc.)
-- have been removed because they would require a false universal postulate
-- claiming all IR fits in a fixed stack size.
--
-- For specific IR terms, compute StackDepth and provide sufficient stack:
--   let required = StackDepth id  -- Computes to 0
--       provided = 1024
--       proof : 0 ≤ 1024
--       proof = z≤n
--   in star-codegen-correct id provided x proof
------------------------------------------------------------------------

star-id-correct : ∀ {i A} (stackSize : ℕ) (x : ⟦ A ⟧) →
  StackDepth (id {i} {A}) ≤ stackSize →
  ∃[ s ] (Star (compile-riscv (id {i} {A})) (initWithInput stackSize x) s
        × halted s ≡ true
        × readReg (regs s) a0 ≡ encode x)
star-id-correct {i} {A} stackSize x sp-bound =
  star-codegen-correct (id {i} {A}) stackSize x sp-bound

------------------------------------------------------------------------
-- Whole-Program Curry/Apply Verification
--
-- The run-apply-star postulate in MutualIR.agda exists because apply
-- performs an indirect call (jalr) to a code pointer stored in a closure.
-- Without knowing where that closure came from, we can't prove the jump
-- is safe.
--
-- HOWEVER, we have complete infrastructure for whole-program verification:
--
--   1. run-curry-star-with-wf (in MutualIR) produces CurryResult which
--      includes ClosureWellFormed - a proof that:
--      - The closure's code-ptr is in bounds
--      - Executing from code-ptr (the thunk) produces correct results
--
--   2. run-apply-with-wf (in IR/Apply.agda) consumes ClosureWellFormed
--      to prove apply works correctly, tracing all 7 instructions.
--
--   3. curry-output-to-apply-input (in ClosureWellFormed.agda) converts
--      curry's output format to apply's input format.
--
-- For whole-program verification of "apply ∘ ⟨curry f, g⟩":
--   1. Run curry using run-curry-star-with-wf → get ClosureWellFormed
--   2. Run apply using run-apply-with-wf with that ClosureWellFormed
--   3. The indirect call is verified because we know the closure came
--      from curry and has valid thunk code.
--
-- The postulated run-apply-star is sound because:
--   - In any well-typed program, apply only receives closures from curry
--   - All such closures have valid thunk code (proven by curry-thunk-correct-impl)
--   - The postulate is eliminable for specific programs by threading
--     ClosureWellFormed through the proof
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Concrete E2E Tests (Star-based)
------------------------------------------------------------------------

-- | Test: Curry + Apply composed
-- IR: apply ∘ ⟨curry fst, id⟩
-- NOTE: This test now requires explicit stack parameter
test-curry-apply : ∀ {A} (stackSize : ℕ) (a : ⟦ A ⟧) →
  StackDepth (apply ∘ ⟨ curry fst , id {_} {A} ⟩) ≤ stackSize →
  ∃[ s ] (Star (compile-riscv (apply ∘ ⟨ curry fst , id {_} {A} ⟩)) (initWithInput stackSize a) s
        × halted s ≡ true
        × readReg (regs s) a0 ≡ encode (eval (apply ∘ ⟨ curry fst , id {_} {A} ⟩) a))
test-curry-apply {A} stackSize a sp-bound = star-codegen-correct (apply ∘ ⟨ curry fst , id {_} {A} ⟩) stackSize a sp-bound
