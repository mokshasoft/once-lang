------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.CorrectBridge
--
-- Star-based main correctness theorem for AArch64.
-- No fuel management - pure Star-based proofs throughout.
--
-- Key insight: For standalone programs (prefix=[], suffix=[]):
--   1. run-ir-star-at-offset gives Star ending at compile-length ir
--   2. At that pc, fetch fails (past end of program)
--   3. One more step halts the program
--   4. Result: Star from init to halted state with correct x0
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.CorrectBridge where

open import Once.Type
open import Once.IR
open import Once.Semantics using (⟦_⟧; eval)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen
open import Once.Backend.AArch64.Correct.CompileLength using (compile-length-correct)

open import Once.Backend.AArch64.Correct.Foundation
  using (encode; initWithInput; initWithInput-x0; initWithInput-halted;
         initWithInput-pc; step-end-of-program; readReg-writeReg-x0-x21)
open import Once.Backend.AArch64.Correct.Star
  using (Star; refl*; step*; star-trans; star-single)
open import Once.Backend.AArch64.Correct.StarBase
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-x0)
open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant; x21-unused)
open import Once.Backend.AArch64.Correct.MutualIR
  using (run-ir-star-at-offset)

open import Once.Backend.Common.Fetch using (fetch-past-end)

open import Data.Bool using (false; true)
open import Data.Nat using (ℕ; zero; suc; _>_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Initial state properties
------------------------------------------------------------------------

-- | Initial state has x21 = 0
initWithInput-x21 : ∀ {A : Type} (x : ⟦ A ⟧) →
  readReg (regs (initWithInput x)) x21 ≡ 0
initWithInput-x21 x = readReg-writeReg-x0-x21 emptyRegFile (encode x)

-- | Initial state satisfies StackInvariant (via x21 = 0)
initWithInput-stack-inv : ∀ {A : Type} (x : ⟦ A ⟧) →
  StackInvariant (initWithInput x)
initWithInput-stack-inv x = x21-unused (initWithInput-x21 x)

-- | Initial SP is 8192, which is > 16
initWithInput-sp : ∀ {A : Type} (x : ⟦ A ⟧) →
  readSP (regs (initWithInput x)) ≡ 8192
initWithInput-sp x = refl

-- | 8192 > 16 as a proof
sp-bound-init : 8192 > 16
sp-bound-init = m≤m+n 17 8175

-- | Initial state has SP > 16
initWithInput-sp-bound : ∀ {A : Type} (x : ⟦ A ⟧) →
  readSP (regs (initWithInput x)) > 16
initWithInput-sp-bound x = sp-bound-init

------------------------------------------------------------------------
-- Bridge: Star to halted state
------------------------------------------------------------------------

-- | Add termination step: when execution reaches end of program,
-- the next step halts because fetch fails.
star-add-halt : ∀ {prog : Program} {s s' : State} →
  Star prog s s' →
  halted s' ≡ false →
  pc s' ≡ length prog →
  ∃[ s'' ] (Star prog s s''
          × halted s'' ≡ true
          × regs s'' ≡ regs s')
star-add-halt {prog} {s} {s'} star h-false pc-at-end =
  let -- Fetch at end of program fails
      fetch-fail : fetch prog (pc s') ≡ nothing
      fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc-at-end)
                        (fetch-past-end prog)

      -- Final state with halted = true
      s'' = record s' { halted = true }

      -- Step from s' to s'' (sets halted because fetch fails)
      step-halt : step prog s' ≡ just s''
      step-halt = step-end-of-program prog s' h-false fetch-fail

      -- Extend star with one more step
      star-extended : Star prog s s''
      star-extended = star-trans star (star-single h-false step-halt)

      -- Registers unchanged when halted is set
      regs-eq : regs s'' ≡ regs s'
      regs-eq = refl

  in s'' , star-extended , refl , regs-eq

------------------------------------------------------------------------
-- Main Theorem: Star-based (no fuel!)
------------------------------------------------------------------------

-- | The main correctness theorem for AArch64 code generation.
-- For any IR morphism and input value, executing the compiled code
-- reaches a halted state with the encoded semantic result in x0.
--
-- This is PURELY Star-based - no fuel management needed!
--
-- Proven using:
--   1. run-ir-star-at-offset from MutualIR.agda
--   2. star-add-halt to reach halted state
codegen-aarch64-correct : ∀ {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) →
  let prog = compile-aarch64 ir
      s₀ = initWithInput x
  in ∃[ s ] (Star prog s₀ s
           × halted s ≡ true
           × readReg (regs s) x0 ≡ encode (eval ir x))
codegen-aarch64-correct {A} {B} ir x =
  let s₀ = initWithInput x
      prog = compile-aarch64 ir

      -- Initial state properties
      h-false : halted s₀ ≡ false
      h-false = initWithInput-halted x

      pc-eq : pc s₀ ≡ 0
      pc-eq = initWithInput-pc x

      -- For standalone program: prefix = [], so pc s₀ = 0 = length []
      pc-at-start : pc s₀ ≡ length {A = Instr} []
      pc-at-start = pc-eq

      x0-eq : readReg (regs s₀) x0 ≡ encode x
      x0-eq = initWithInput-x0 x

      stack-inv : StackInvariant s₀
      stack-inv = initWithInput-stack-inv x

      sp>16 : readSP (regs s₀) > 16
      sp>16 = initWithInput-sp-bound x

      -- Run the IR using run-ir-star-at-offset with prefix=[], suffix=[]
      -- ([] ++ prog ++ []) = (prog ++ []) = prog (by ++-identityʳ)
      prog-eq : [] ++ compile-aarch64 ir ++ [] ≡ prog
      prog-eq = ++-identityʳ prog

      (s' , result) = run-ir-star-at-offset ir [] [] x s₀
                        h-false pc-at-start x0-eq stack-inv sp>16

      -- Reindex result to work with prog
      result' : IRStarResult ir prog s₀ s' x 0
      result' = subst (λ p → IRStarResult ir p s₀ s' x 0)
                      prog-eq result

      -- Extract Star and properties
      star : Star prog s₀ s'
      star = ir-star result'

      h' : halted s' ≡ false
      h' = ir-halted result'

      -- pc s' = 0 + compile-length ir = compile-length ir = length prog
      pc-s' : pc s' ≡ compile-length ir
      pc-s' = trans (ir-pc result') (cong (_+ℕ compile-length ir) refl)

      prog-len : length prog ≡ compile-length ir
      prog-len = compile-length-correct ir

      pc-at-end : pc s' ≡ length prog
      pc-at-end = trans pc-s' (sym prog-len)

      -- Add halt step to reach final halted state
      (s'' , star-full , h''-true , regs-eq) = star-add-halt star h' pc-at-end

      -- x0 in final state equals result
      x0-s' : readReg (regs s') x0 ≡ encode (eval ir x)
      x0-s' = ir-x0 result'

      x0-s'' : readReg (regs s'') x0 ≡ encode (eval ir x)
      x0-s'' = trans (cong (λ rf → readReg rf x0) regs-eq) x0-s'

  in s'' , star-full , h''-true , x0-s''

------------------------------------------------------------------------
-- Re-export for use by other modules
------------------------------------------------------------------------

open Once.Backend.AArch64.Correct.Foundation public
  using (initWithInput; initWithInput-x0; initWithInput-halted; initWithInput-pc;
         encode)

open Once.Backend.AArch64.Correct.Star public
  using (Star)
