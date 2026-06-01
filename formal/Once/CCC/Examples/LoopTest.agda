------------------------------------------------------------------------
-- Once.CCC.Examples.LoopTest
--
-- Plan 0.27: validates that the extended X86-64 CPU model supports a real
-- BACKWARD-jump loop (`jmp` to an earlier `label`). Before the label-based
-- jump fix, `jmp`/`je`/`jne` were forward-only (`pc + 1 + target`), so a
-- loop back-edge was inexpressible. This countdown-sum loop jumps backward
-- each iteration and terminates with the correct result — the control flow
-- the recursion-scheme worklist loops (A2) need.
------------------------------------------------------------------------

module Once.CCC.Examples.LoopTest where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.Target.X86-64.Syntax
open import Once.CCC.Target.X86-64.Semantics

-- rax := rcx + (rcx-1) + … + 1 via a backward-jump loop.
--   label 0:  cmp rcx, 0 ; je 1 ; add rax, rcx ; sub rcx, 1 ; jmp 0
--   label 1:  (end → fetch past program → halt)
sum-prog : Program
sum-prog =
    label 0
  ∷ cmp (reg rcx) (imm 0)
  ∷ je 1                       -- exit loop when rcx = 0
  ∷ add (reg rax) (reg rcx)
  ∷ sub (reg rcx) (imm 1)
  ∷ jmp 0                       -- BACKWARD jump to label 0
  ∷ label 1
  ∷ []

-- Start with rcx = 3 (rax = 0 from emptyRegFile).
start : State
start = record initState { regs = writeReg (State.regs initState) rcx 3 }

-- The loop runs to completion and leaves 3+2+1 = 6 in rax.
loop-runs : map (λ fs → readReg (State.regs fs) rax) (run sum-prog start) ≡ just 6
loop-runs = refl
