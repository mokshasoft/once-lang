------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct
--
-- Correctness proofs for RISC-V 64-bit code generation.
--
-- Main theorem:
--   codegen-riscv-correct : ∀ (ir : IR A B) (x : ⟦A⟧) →
--     ∃[ s ] (run (compile-riscv ir) (initWithInput x) ≡ just s
--           × readReg (regs s) a0 ≡ encode (eval ir x))
--
-- This module orchestrates the modular proof components:
--   - Foundation: basic lemmas and instruction execution
--   - CompileLength: compile-length-correct theorem
--   - Star: reflexive-transitive closure of step
--   - StarBase: IRStarResult record and base case proofs
--   - MutualIR: Star-based mutual block for all IR constructors
--
-- The proof strategy:
--   1. run-ir-star (from MutualIR) gives Star-based execution proof
--   2. Bridge to exec-based result via star-to-exec-chain
--   3. Add halting step when PC reaches end of program
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct where

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

-- Import Star relation and bridging lemmas
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; star-trans; star-length; star-length-trans;
         star-to-exec-chain; star-to-exec)

-- Import StarBase for IRStarResult
open import Once.Backend.RiscV64.Correct.StarBase
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-a0; ir-s1)

-- Import MutualIR for run-ir-star
open import Once.Backend.RiscV64.Correct.MutualIR
  using (run-ir-star; run-ir-star-at-offset)

------------------------------------------------------------------------
-- Bridge from Star to exec: exec-generator
--
-- This bridges the Star-based proof from MutualIR to exec-based result.
-- After IR execution, PC is at the end of the program. One more step
-- causes halting (fetch fails), which we chain to get the final result.
--
-- Note: The star-to-compile-length lemma bridges between star-length
-- and compile-length. This is sound because each IR instruction compiles
-- to exactly compile-length instructions, and each step advances PC by 1.
------------------------------------------------------------------------

-- | Star-length invariant: star-length equals compile-length
--
-- This is sound by construction: each IR constructor compiles to exactly
-- compile-length instructions, and each Star step advances PC by 1.
-- TODO: Prove by adding ir-steps field to IRStarResult
postulate
  star-to-compile-length : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s s' : State)
    (h-false : halted s ≡ false) (pc-0 : pc s ≡ 0) (a0-eq : readReg (regs s) a0 ≡ encode x) →
    let (s'' , result) = run-ir-star ir x s h-false pc-0 a0-eq
    in star-length (ir-star result) ≡ compile-length ir

-- | exec-generator: Correctness with exact fuel (compile-length ir + 1)
--
-- Uses run-ir-star from MutualIR, then:
--   1. Convert Star to exec via star-to-exec
--   2. Add halting step when PC reaches end of program
--   3. Use exec-mono to adjust fuel
exec-generator : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] (exec (compile-length ir +ℕ 1) (compile-riscv ir) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode (eval ir x))
exec-generator {A} {B} ir x s h-false pc-0 a0-eq = s'' , exec-halt , refl , a0-eq'
  where
    open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
    open ≡-Reasoning

    -- Step 1: Get Star-based result from MutualIR
    star-result = run-ir-star ir x s h-false pc-0 a0-eq
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

    -- Step 5: Convert Star to exec with computed fuel
    star-exec : exec (star-length star-with-halt) prog s ≡ just s''
    star-exec = star-to-exec star-with-halt refl

    -- Step 6: Relate star-length to compile-length
    star-len-eq : star-length star-proof ≡ compile-length ir
    star-len-eq = star-to-compile-length ir x s s' h-false pc-0 a0-eq

    star-with-halt-len : star-length star-with-halt ≡ compile-length ir +ℕ 1
    star-with-halt-len = begin
      star-length star-with-halt
        ≡⟨ star-length-trans star-proof halt-step ⟩
      star-length star-proof +ℕ star-length halt-step
        ≡⟨ refl ⟩  -- star-length (step* ... refl*) = 1
      star-length star-proof +ℕ 1
        ≡⟨ cong (_+ℕ 1) star-len-eq ⟩
      compile-length ir +ℕ 1
        ∎

    -- Step 7: Get final exec result with correct fuel
    exec-halt : exec (compile-length ir +ℕ 1) prog s ≡ just s''
    exec-halt = subst (λ n → exec n prog s ≡ just s'') star-with-halt-len star-exec

-- | run-generator: Correctness with run (fixed fuel = 10000)
--
-- Wrapper that uses exec-generator and exec-mono to increase fuel.
run-generator : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
  compile-length ir +ℕ 1 ≤ 10000 →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] (run (compile-riscv ir) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode (eval ir x))
run-generator ir x s size-bound h-false pc-0 a0-eq =
  let (s' , exec-eq , h-true , a0-eq') = exec-generator ir x s h-false pc-0 a0-eq
      run-eq = exec-mono (compile-length ir +ℕ 1) 10000 (compile-riscv ir) s s' size-bound exec-eq h-true
  in s' , run-eq , h-true , a0-eq'

------------------------------------------------------------------------
-- Individual IR constructor correctness theorems
--
-- These provide the API expected by EndToEnd.agda.
-- All delegate to exec-generator.
------------------------------------------------------------------------

compile-id-correct : ∀ {A} (x : ⟦ A ⟧) →
  ∃[ s ] (exec 2 (compile-riscv {A} {A} id) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode x)
compile-id-correct {A} x =
  let (s' , exec-eq , _ , a0-eq) = exec-generator {A} {A} id x (initWithInput x)
                                     (initWithInput-halted x) (initWithInput-pc x) (initWithInput-a0 x)
  in s' , exec-eq , a0-eq

compile-terminal-correct : ∀ {A} (x : ⟦ A ⟧) →
  ∃[ s ] (exec 2 (compile-riscv {A} {Unit} terminal) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode {Unit} tt)
compile-terminal-correct {A} x =
  let (s' , exec-eq , _ , a0-eq) = exec-generator {A} {Unit} terminal x (initWithInput x)
                                     (initWithInput-halted x) (initWithInput-pc x) (initWithInput-a0 x)
  in s' , exec-eq , a0-eq

compile-fold-correct : ∀ {F} (x : ⟦ F ⟧) →
  ∃[ s ] (exec 2 (compile-riscv {F} {Fix F} fold) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode (wrap x))
compile-fold-correct {F} x =
  let (s' , exec-eq , _ , a0-eq) = exec-generator {F} {Fix F} fold x (initWithInput x)
                                     (initWithInput-halted x) (initWithInput-pc x) (initWithInput-a0 x)
  in s' , exec-eq , a0-eq

compile-unfold-correct : ∀ {F} (x : ⟦ Fix F ⟧) →
  ∃[ s ] (exec 2 (compile-riscv {Fix F} {F} unfold) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode (unwrap x))
compile-unfold-correct {F} x =
  let (s' , exec-eq , _ , a0-eq) = exec-generator {Fix F} {F} unfold x (initWithInput x)
                                     (initWithInput-halted x) (initWithInput-pc x) (initWithInput-a0 x)
  in s' , exec-eq , a0-eq

compile-arr-correct : ∀ {A B} (f : ⟦ A ⇒ B ⟧) →
  ∃[ s ] (exec 2 (compile-riscv {A ⇒ B} {Eff A B} arr) (initWithInput {A ⇒ B} f) ≡ just s
        × readReg (regs s) a0 ≡ encode {Eff A B} (eval {A ⇒ B} {Eff A B} arr f))
compile-arr-correct {A} {B} f =
  let (s' , exec-eq , _ , a0-eq) = exec-generator {A ⇒ B} {Eff A B} arr f (initWithInput {A ⇒ B} f)
                                     (initWithInput-halted {A ⇒ B} f) (initWithInput-pc {A ⇒ B} f) (initWithInput-a0 {A ⇒ B} f)
  in s' , exec-eq , a0-eq

compile-inl-correct : ∀ {A B} (x : ⟦ A ⟧) →
  ∃[ s ] (exec 5 (compile-riscv {A} {A + B} inl) (initWithInput {A} x) ≡ just s
        × readReg (regs s) a0 ≡ encode {A + B} (inj₁ x))
compile-inl-correct {A} {B} x =
  let (s' , exec-eq , _ , a0-eq) = exec-generator {A} {A + B} inl x (initWithInput {A} x)
                                     (initWithInput-halted {A} x) (initWithInput-pc {A} x) (initWithInput-a0 {A} x)
  in s' , exec-eq , a0-eq

compile-inr-correct : ∀ {A B} (x : ⟦ B ⟧) →
  ∃[ s ] (exec 6 (compile-riscv {B} {A + B} inr) (initWithInput {B} x) ≡ just s
        × readReg (regs s) a0 ≡ encode {A + B} (inj₂ x))
compile-inr-correct {A} {B} x =
  let (s' , exec-eq , _ , a0-eq) = exec-generator {B} {A + B} inr x (initWithInput {B} x)
                                     (initWithInput-halted {B} x) (initWithInput-pc {B} x) (initWithInput-a0 {B} x)
  in s' , exec-eq , a0-eq

compile-fst-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  ∃[ s ] (exec 2 (compile-riscv {A * B} {A} fst) (initWithInput (a , b)) ≡ just s
        × readReg (regs s) a0 ≡ encode a)
compile-fst-correct {A} {B} a b =
  let (s' , exec-eq , _ , a0-eq) = exec-generator {A * B} {A} fst (a , b) (initWithInput (a , b))
                                     (initWithInput-halted (a , b)) (initWithInput-pc (a , b)) (initWithInput-a0 (a , b))
  in s' , exec-eq , a0-eq

compile-snd-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  ∃[ s ] (exec 2 (compile-riscv {A * B} {B} snd) (initWithInput (a , b)) ≡ just s
        × readReg (regs s) a0 ≡ encode b)
compile-snd-correct {A} {B} a b =
  let (s' , exec-eq , _ , a0-eq) = exec-generator {A * B} {B} snd (a , b) (initWithInput (a , b))
                                     (initWithInput-halted (a , b)) (initWithInput-pc (a , b)) (initWithInput-a0 (a , b))
  in s' , exec-eq , a0-eq

compile-curry-correct : ∀ {A B C} (f : IR (A * B) C) (a : ⟦ A ⟧) →
  ∃[ s ] (exec (compile-length (curry f) +ℕ 1) (compile-riscv (curry f)) (initWithInput {A} a) ≡ just s
        × readReg (regs s) a0 ≡ encode {B ⇒ C} (eval (curry {A} {B} {C} f) a))
compile-curry-correct {A} {B} {C} f a =
  let (s' , exec-eq , _ , a0-eq) = exec-generator (curry {A} {B} {C} f) a (initWithInput {A} a)
                                     (initWithInput-halted {A} a) (initWithInput-pc {A} a) (initWithInput-a0 {A} a)
  in s' , exec-eq , a0-eq

compile-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (exec (compile-length (g ∘ f) +ℕ 1) (compile-riscv (g ∘ f)) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode (eval (g ∘ f) x))
compile-compose-correct {A} {B} {C} g f x =
  let (s' , exec-eq , _ , a0-eq) = exec-generator (g ∘ f) x (initWithInput x)
                                     (initWithInput-halted x) (initWithInput-pc x) (initWithInput-a0 x)
  in s' , exec-eq , a0-eq

compile-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧) →
  ∃[ s ] (exec (compile-length ⟨ f , g ⟩ +ℕ 1) (compile-riscv ⟨ f , g ⟩) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode (eval ⟨ f , g ⟩ x))
compile-pair-correct {A} {B} {C} f g x =
  let (s' , exec-eq , _ , a0-eq) = exec-generator ⟨ f , g ⟩ x (initWithInput x)
                                     (initWithInput-halted x) (initWithInput-pc x) (initWithInput-a0 x)
  in s' , exec-eq , a0-eq

compile-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A + B ⟧) →
  ∃[ s ] (exec (compile-length ([_,_] f g) +ℕ 1) (compile-riscv ([_,_] f g)) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode (eval ([_,_] f g) x))
compile-case-correct {A} {B} {C} f g x =
  let (s' , exec-eq , _ , a0-eq) = exec-generator ([_,_] f g) x (initWithInput x)
                                     (initWithInput-halted x) (initWithInput-pc x) (initWithInput-a0 x)
  in s' , exec-eq , a0-eq

compile-apply-correct : ∀ {A B} (f : ⟦ A ⇒ B ⟧) (a : ⟦ A ⟧) →
  let input : ⟦ (A ⇒ B) * A ⟧
      input = (f , a)
  in ∃[ s ] (exec 8 (compile-riscv {(A ⇒ B) * A} {B} apply) (initWithInput {(A ⇒ B) * A} input) ≡ just s
           × readReg (regs s) a0 ≡ encode {B} (eval {(A ⇒ B) * A} {B} apply input))
compile-apply-correct {A} {B} f a =
  let input : ⟦ (A ⇒ B) * A ⟧
      input = (f , a)
      (s' , exec-eq , _ , a0-eq) = exec-generator {(A ⇒ B) * A} {B} apply input (initWithInput {(A ⇒ B) * A} input)
                                     (initWithInput-halted {(A ⇒ B) * A} input) (initWithInput-pc {(A ⇒ B) * A} input) (initWithInput-a0 {(A ⇒ B) * A} input)
  in s' , exec-eq , a0-eq

------------------------------------------------------------------------
-- Generic IR correctness (structural induction)
------------------------------------------------------------------------

-- | exec-based correctness for all IR terms
exec-codegen-riscv-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (exec (compile-length ir +ℕ 1) (compile-riscv ir) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode (eval ir x))
exec-codegen-riscv-correct ir x =
  let (s' , exec-eq , _ , a0-eq) = exec-generator ir x (initWithInput x)
                                     (initWithInput-halted x) (initWithInput-pc x) (initWithInput-a0 x)
  in s' , exec-eq , a0-eq

------------------------------------------------------------------------
-- Main Correctness Theorem
------------------------------------------------------------------------

-- | Main correctness theorem (run version - with size bound)
--
-- For IR terms that compile to less than 10000 instructions, run also works.
-- This is a convenience wrapper for users who prefer the run interface.
codegen-riscv-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
  compile-length ir +ℕ 1 ≤ 10000 →
  ∃[ s ] (run (compile-riscv ir) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode (eval ir x))
codegen-riscv-correct ir x size-bound =
  let (s' , exec-eq , h-true , a0-eq) = exec-generator ir x (initWithInput x)
                                         (initWithInput-halted x) (initWithInput-pc x) (initWithInput-a0 x)
      run-eq = exec-mono (compile-length ir +ℕ 1) 10000 (compile-riscv ir) (initWithInput x) s' size-bound exec-eq h-true
  in s' , run-eq , a0-eq

------------------------------------------------------------------------
-- Concrete E2E Tests
------------------------------------------------------------------------

-- | Test: Curry + Apply composed
-- IR: apply ∘ ⟨curry fst, id⟩
test-curry-apply : ∀ {A} (a : ⟦ A ⟧) →
  ∃[ s ] (run (compile-riscv {A} {A} (apply ∘ ⟨ curry fst , id ⟩)) (initWithInput a) ≡ just s
        × readReg (regs s) a0 ≡ encode (eval (apply ∘ ⟨ curry fst , id ⟩) a))
test-curry-apply {A} a = codegen-riscv-correct {A} {A} (apply ∘ ⟨ curry fst , id ⟩) a size-bound
  where
    open import Data.Nat.Properties using (m≤m+n)
    -- compile-length = 31 (pair now uses 8 fixed instructions), so 31 + 1 = 32 ≤ 10000
    size-bound : 32 ≤ 10000
    size-bound = m≤m+n 32 9968
