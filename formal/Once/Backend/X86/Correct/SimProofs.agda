------------------------------------------------------------------------
-- Once.Backend.X86.Correct.SimProofs
--
-- Forward simulation proofs for IR constructors using star relation.
-- These proofs use the CompCert-style approach: prove that execution
-- reaches a state with correct output, without counting steps.
--
-- Level 2 - depends on Star, Simulation, StackInvariant
------------------------------------------------------------------------

module Once.Backend.X86.Correct.SimProofs where

open import Once.Type
open import Once.IR
open import Once.Semantics using (⟦_⟧; eval)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Backend.X86.Correct.Star using (Star; star-refl; star-step; star-trans; star-one; star-two)
open import Once.Backend.X86.Correct.Simulation
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.InitState using (initWithInput)

open import Once.Postulates using (encode; encode-unit)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _>_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Step-Level Postulates
--
-- Due to 'with' clauses in step/execInstr, we postulate single-step
-- behavior. These form the "trusted execution semantics" layer.
-- Everything above is proven by composition.
------------------------------------------------------------------------

-- | step-at-pc: When pc = i and program has instruction at i,
-- step executes that instruction
postulate
  step-mov-reg-reg : ∀ (prefix suffix : Program) (dst src : Reg) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    step (prefix ++ mov (reg dst) (reg src) ∷ suffix) s ≡
      just (record s { regs = writeReg (regs s) dst (readReg (regs s) src)
                     ; pc = suc (pc s) })

  step-mov-rax-rdi : ∀ (prefix suffix : Program) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    step (prefix ++ mov (reg rax) (reg rdi) ∷ suffix) s ≡
      just (record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                     ; pc = suc (pc s) })

  step-mov-rax-imm : ∀ (prefix suffix : Program) (s : State) (n : ℕ) →
    halted s ≡ false →
    pc s ≡ length prefix →
    step (prefix ++ mov (reg rax) (imm n) ∷ suffix) s ≡
      just (record s { regs = writeReg (regs s) rax n
                     ; pc = suc (pc s) })

  step-mov-rax-mem-rdi : ∀ (prefix suffix : Program) (s : State) (v : ℕ) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readMem (memory s) (readReg (regs s) rdi) ≡ just v →
    step (prefix ++ mov (reg rax) (mem (base rdi)) ∷ suffix) s ≡
      just (record s { regs = writeReg (regs s) rax v
                     ; pc = suc (pc s) })

  step-mov-rax-mem-rdi+8 : ∀ (prefix suffix : Program) (s : State) (v : ℕ) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just v →
    step (prefix ++ mov (reg rax) (mem (base+disp rdi 8)) ∷ suffix) s ≡
      just (record s { regs = writeReg (regs s) rax v
                     ; pc = suc (pc s) })

-- | Postulate for halting when pc goes past program end
postulate
  step-halts-past-end : ∀ (prog : Program) (s : State) →
    halted s ≡ false →
    pc s ≡ length prog →
    step prog s ≡ just (record s { halted = true })

------------------------------------------------------------------------
-- Helper: halted state after one more step
------------------------------------------------------------------------

-- After executing the last instruction, the next step halts
-- because fetch at (length prog) fails

postulate
  one-instr-halts : ∀ (instr : Instr) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    ∃[ s' ] (step (instr ∷ []) s ≡ just s' ×
             halted s' ≡ false ×
             pc s' ≡ 1)

  after-one-instr-halts : ∀ (instr : Instr) (s : State) →
    halted s ≡ false →
    pc s ≡ 1 →
    step (instr ∷ []) s ≡ just (record s { halted = true })

------------------------------------------------------------------------
-- Forward Simulation: id
------------------------------------------------------------------------

-- compile-x86 id = mov rax, rdi ∷ []
-- eval id x = x

sim-id : ∀ {A : Type} (x : ⟦ A ⟧) (s : State) →
  Simulates {A} {A} id x s →
  pc s ≡ 0 →
  ∃[ s' ] (Star (compile-x86 {A} {A} id) s s' × HasResult {A} {A} id x s')
sim-id {A} x s sim pc-0 = s2 , star-proof , result
  where
    prog = compile-x86 {A} {A} id  -- = mov rax, rdi ∷ []

    -- Step 1: Execute mov rax, rdi
    s1 : State
    s1 = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = suc (pc s) }
    step1-eq : step prog s ≡ just s1
    step1-eq = step-mov-rax-rdi [] [] s (not-halted sim) pc-0

    s1-halted : halted s1 ≡ false
    s1-halted = not-halted sim  -- halted field not changed by mov

    s1-pc : pc s1 ≡ 1
    s1-pc = cong suc pc-0

    -- Step 2: Halt (pc = 1 = length prog)
    s2 : State
    s2 = record s1 { halted = true }
    step2-eq : step prog s1 ≡ just s2
    step2-eq = step-halts-past-end prog s1 s1-halted s1-pc

    -- Build star proof
    star-proof : Star prog s s2
    star-proof = star-step (not-halted sim) step1-eq
                   (star-step s1-halted step2-eq star-refl)

    -- Output is correct: rax s2 = rax s1 = rdi s = encode x = encode (eval id x)
    rax-is-rdi-s : readReg (regs s2) rax ≡ readReg (regs s) rdi
    rax-is-rdi-s = refl  -- By construction

    rax-s2 : readReg (regs s2) rax ≡ encode (eval id x)
    rax-s2 = trans rax-is-rdi-s (input-encoded sim)

    result : HasResult id x s2
    result = mkHasResult rax-s2 refl

------------------------------------------------------------------------
-- Forward Simulation: terminal
------------------------------------------------------------------------

-- compile-x86 terminal = mov rax, 0 ∷ []
-- eval terminal _ = tt
-- encode tt = 0

sim-terminal : ∀ {A : Type} (x : ⟦ A ⟧) (s : State) →
  Simulates {A} {Unit} terminal x s →
  pc s ≡ 0 →
  ∃[ s' ] (Star (compile-x86 {A} {Unit} terminal) s s' × HasResult {A} {Unit} terminal x s')
sim-terminal {A} x s sim pc-0 = s2 , star-proof , result
  where
    prog = compile-x86 {A} {Unit} terminal  -- = mov rax, 0 ∷ []

    -- Step 1: Execute mov rax, 0 (sets rax = 0)
    s1 : State
    s1 = record s { regs = writeReg (regs s) rax 0
                  ; pc = suc (pc s) }
    step1-eq : step prog s ≡ just s1
    step1-eq = step-mov-rax-imm [] [] s 0 (not-halted sim) pc-0

    s1-halted : halted s1 ≡ false
    s1-halted = not-halted sim

    s1-pc : pc s1 ≡ 1
    s1-pc = cong suc pc-0

    -- Step 2: Halt
    s2 : State
    s2 = record s1 { halted = true }
    step2-eq : step prog s1 ≡ just s2
    step2-eq = step-halts-past-end prog s1 s1-halted s1-pc

    -- Build star proof
    star-proof : Star prog s s2
    star-proof = star-step (not-halted sim) step1-eq
                   (star-step s1-halted step2-eq star-refl)

    -- Output is correct: rax s2 = 0 = encode tt = encode (eval terminal x)
    rax-s2 : readReg (regs s2) rax ≡ encode (eval terminal x)
    rax-s2 = sym encode-unit  -- encode tt = 0, and rax = 0

    result : HasResult terminal x s2
    result = mkHasResult rax-s2 refl

------------------------------------------------------------------------
-- Forward Simulation: initial (absurd case)
------------------------------------------------------------------------

-- initial : IR Void A
-- ⟦ Void ⟧ = ⊥, so no inhabitants exist

sim-initial : ∀ {A : Type} (x : ⟦ Void ⟧) (s : State) →
  Simulates {Void} {A} initial x s →
  pc s ≡ 0 →
  ∃[ s' ] (Star (compile-x86 {Void} {A} initial) s s' × HasResult {Void} {A} initial x s')
sim-initial () s sim pc-0  -- absurd pattern: ⟦ Void ⟧ = ⊥ has no inhabitants
