------------------------------------------------------------------------
-- Once.CCC.Examples.CaseTest
--
-- Plan 0.27 (C2 prereq): validates the real `case` (sum-elimination) X86-64
-- codegen — heap tag dispatch — by COMPILING `case terminal id` with
-- `compile-ir` and RUNNING it on heap-built sum nodes:
--   inr node (tag 1, payload 42) → `id` branch returns the payload  → 42
--   inl node (tag 0, payload 99) → `terminal` branch returns 0       → 0
-- This is the dispatch a Cata's algebra (and the fold loop's tag test)
-- both need; `case` was previously a `pf ++ pg` stub with no dispatch.
------------------------------------------------------------------------

module Once.CCC.Examples.CaseTest where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Unit)
open import Once.CCC.IR using (IR; case; terminal; id)
open import Once.CCC.Target.X86-64.Syntax
open import Once.CCC.Target.X86-64.Semantics
open import Once.CCC.Target.X86-64.CodeGen.Compile using (compile-ir)

-- case terminal id : IR (Unit + Unit) Unit
--   inl branch = terminal (rax := 0) ; inr branch = id (rax := payload)
prog : Program
prog = compile-ir (case {Unit} {Unit} {Unit} terminal id)

-- inr node at 100: [100]=1 (tag), [108]=42 (payload)
node-inr : Memory
node-inr = writeMem (writeMem emptyMemory 100 1) 108 42

-- inl node at 100: [100]=0 (tag), [108]=99 (payload, ignored by terminal)
node-inl : Memory
node-inl = writeMem (writeMem emptyMemory 100 0) 108 99

start : Memory → State
start m = record initState { regs = writeReg (State.regs initState) rdi 100 ; memory = m }

-- tag 1 → id branch → payload 42
case-inr : map (λ fs → readReg (State.regs fs) rax) (run prog (start node-inr)) ≡ just 42
case-inr = refl

-- tag 0 → terminal branch → 0
case-inl : map (λ fs → readReg (State.regs fs) rax) (run prog (start node-inl)) ≡ just 0
case-inl = refl
