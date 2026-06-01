------------------------------------------------------------------------
-- Once.CCC.Examples.InlrTest
--
-- Plan 0.27 (C2 prereq): validates the real `inl`/`inr` heap-allocation
-- codegen. Compiling `inr` and running it (heap-top r14 = 1000, payload
-- rdi = 42) must build the sum node [1000]=1 (tag), [1008]=42 (payload),
-- return its pointer in rax (1000), and bump r14 to 1016. These nodes are
-- exactly what a Cata algebra's result-layer (and `case`'s input) need.
------------------------------------------------------------------------

module Once.CCC.Examples.InlrTest where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Unit)
open import Once.CCC.IR using (IR; inr; Stack)
open import Once.CCC.Target.X86-64.Syntax
open import Once.CCC.Target.X86-64.Semantics
open import Once.CCC.Target.X86-64.CodeGen.Compile using (compile-ir)

prog : Program
prog = compile-ir (inr {Unit} {Unit} Stack)

start : State
start = record initState
          { regs = writeReg (writeReg (State.regs initState) r14 1000) rdi 42 }

-- node tag = 1 (inr)
inr-tag : map (λ fs → readMem (State.memory fs) 1000) (run prog start) ≡ just (just 1)
inr-tag = refl

-- node payload = 42 (the input)
inr-payload : map (λ fs → readMem (State.memory fs) 1008) (run prog start) ≡ just (just 42)
inr-payload = refl

-- result pointer = the node address (1000)
inr-ptr : map (λ fs → readReg (State.regs fs) rax) (run prog start) ≡ just 1000
inr-ptr = refl

-- heap top bumped by 2 words (1000 → 1016)
inr-bump : map (λ fs → readReg (State.regs fs) r14) (run prog start) ≡ just 1016
inr-bump = refl
