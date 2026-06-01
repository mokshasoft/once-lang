------------------------------------------------------------------------
-- Once.CCC.Examples.CataIsEvenCodegen
--
-- Plan 0.27 (C2 capstone): COMPILES a real catamorphism and RUNS it.
-- `Cata wf-NatF alg-isEven : IR (μ-type NatF) Bool` is compiled by the
-- actual compiler (`compile-ir`) into the worklist/counter fold loop with
-- the algebra spliced, then executed on the verified CPU over a heap-
-- allocated Nat. The result is a heap Bool node whose tag is read:
--   tag 0 = true (even), tag 1 = false (odd).
--
-- isEven via Cata: alg(inl tt)=true ; alg(inr b)=not b.
-- This is end-to-end x86 codegen + execution of structured recursion —
-- the C2 milestone (Cata is no longer a ud2 stub).
------------------------------------------------------------------------

module Once.CCC.Examples.CataIsEvenCodegen where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; _+_; μ-type; NatF)
open import Once.Functor.Translate using (wf-NatF)
open import Once.CCC.IR using (IR; case; inl; inr; Cata; Stack)
open import Once.CCC.Target.X86-64.Syntax
open import Once.CCC.Target.X86-64.Semantics
open import Once.CCC.Target.X86-64.CodeGen.Compile using (compile-ir)

Bool# : Type
Bool# = Unit + Unit

-- not : flip a Bool (Unit+Unit) node
not# : IR Bool# Bool#
not# = case (inr Stack) (inl Stack)

-- isEven algebra over NatF: ⟦NatF⟧T Bool# = Unit + Bool#
--   inl (zero layer) → true ;  inr (suc, child result b) → not b
alg-isEven : IR (Unit + Bool#) Bool#
alg-isEven = case (inl Stack) not#

prog : Program
prog = compile-ir (Cata wf-NatF alg-isEven)

------------------------------------------------------------------------
-- Heap Nats (tagged nodes [tag] / [node+8]=child). r14 (heap top) seeded
-- at 1000, above the input nodes; rdi = root.
------------------------------------------------------------------------
-- Nat 2 = suc (suc zero): zero@8, suc@16→8, suc@32→16  (root 32)
heap2 : Memory
heap2 = writeMem (writeMem (writeMem (writeMem (writeMem
          emptyMemory 8 0) 16 1) 24 8) 32 1) 40 16

-- Nat 3 = suc (suc (suc zero)): + suc@48→32  (root 48)
heap3 : Memory
heap3 = writeMem (writeMem heap2 48 1) 56 32

start : Memory → ℕ → State
start m root = record initState
  { regs = writeReg (writeReg (State.regs initState) r14 1000) rdi root
  ; memory = m }

-- result Bool node tag: read [rax].  even → 0, odd → 1.
result-tag : State → Maybe ℕ
result-tag fs = readMem (State.memory fs) (readReg (State.regs fs) rax)

-- isEven 2 = true  → result node tag 0
isEven-2 : map result-tag (run prog (start heap2 32)) ≡ just (just 0)
isEven-2 = refl

-- isEven 3 = false → result node tag 1
isEven-3 : map result-tag (run prog (start heap3 48)) ≡ just (just 1)
isEven-3 = refl
