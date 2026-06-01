-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Examples.CataIsEvenInduction
--
-- Plan 0.27 (C3): the compiled catamorphism `compile-ir (Cata wf-NatF
-- alg-isEven)` runs correctly for ALL inputs `n` — built on the semantic
-- API `Once.CCC.Target.X86-64.StepLemmas` (everything over OPAQUE states,
-- never destructuring Memory). This is the ∀-n generalisation of
-- `CataIsEvenCodegen` (which is `refl` on n=2,3).
------------------------------------------------------------------------

module Once.CCC.Examples.CataIsEvenInduction where

open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type using (Unit; μ-type; NatF) renaming (_+_ to _⊕_)
open import Once.Functor.Translate using (wf-NatF)
open import Once.CCC.IR using (IR; case; inl; inr; Cata; Stack)
open import Once.CCC.Target.X86-64.Syntax
open import Once.CCC.Target.X86-64.Semantics
open import Once.CCC.Target.X86-64.CodeGen.Compile using (compile-ir)
open import Once.CCC.Target.X86-64.StepLemmas

open State using (regs; memory; flags; pc; halted)

alg-isEven : IR (Unit ⊕ (Unit ⊕ Unit)) (Unit ⊕ Unit)
alg-isEven = case (inl Stack) (case (inr Stack) (inl Stack))

prog : Program
prog = compile-ir (Cata wf-NatF alg-isEven)

------------------------------------------------------------------------
-- One descend-loop iteration on a suc-node (pc 1 → pc 1), via the API.
-- 7 steps: label4 ; mov rcx←[rdi] ; cmp rcx,0 ; je5(not taken) ;
--          add rbx,1 ; mov rdi←[rdi+8] ; jmp4.
-- Reads the node tag (=1) and child pointer from (opaque) memory.
------------------------------------------------------------------------
descend-iter : ∀ (R : ℕ) (s : State) (child : ℕ)
  → pc s ≡ 1
  → halted s ≡ false
  → readMem (memory s) (readReg (regs s) rdi) ≡ just 1
  → readMem (memory s) (readReg (regs s) rdi + 8) ≡ just child
  → exec (7 + R) prog s
    ≡ exec R prog
        (record (record (record (record (record (record (record s
          { pc = pc s + 1 })                                            -- label4
          { regs = writeReg (regs s) rcx 1 ; pc = pc s + 1 + 1 })       -- mov rcx
          { flags = mkflags (1 ≡ᵇ 0) (1 <ᵇ 0) false ; pc = pc s + 1 + 1 + 1 })  -- cmp
          { pc = pc s + 1 + 1 + 1 + 1 })                                -- je not taken
          { regs = writeReg (writeReg (regs s) rcx 1) rbx (readReg (regs s) rbx + 1)
          ; flags = updateFlags (readReg (regs s) rbx + 1) (readReg (regs s) rbx)
          ; pc = pc s + 1 + 1 + 1 + 1 + 1 })                            -- add rbx
          { regs = writeReg (writeReg (writeReg (regs s) rcx 1) rbx (readReg (regs s) rbx + 1)) rdi child
          ; pc = pc s + 1 + 1 + 1 + 1 + 1 + 1 })                        -- mov rdi
          { pc = 1 })                                                   -- jmp4
descend-iter R s child pc-eq hs tag-eq child-eq =
  exec-steps R
    ( (hs , step-label  {prog} {s}  (cong (fetch prog) pc-eq)                        , hs)
    ∷ (hs , step-mov-rm {prog} {s1} (cong (λ p → fetch prog (p + 1)) pc-eq) tag-eq   , hs)
    ∷ (hs , step-cmp-ri {prog} {s2} (cong (λ p → fetch prog (p + 1 + 1)) pc-eq)      , hs)
    ∷ (hs , step-je-not {prog} {s3} (cong (λ p → fetch prog (p + 1 + 1 + 1)) pc-eq) refl , hs)
    ∷ (hs , step-add-ri {prog} {s4} (cong (λ p → fetch prog (p + 1 + 1 + 1 + 1)) pc-eq) , hs)
    ∷ (hs , step-mov-rm {prog} {s5} (cong (λ p → fetch prog (p + 1 + 1 + 1 + 1 + 1)) pc-eq) child-eq , hs)
    ∷ (hs , step-jmp    {prog} {s6} (cong (λ p → fetch prog (p + 1 + 1 + 1 + 1 + 1 + 1)) pc-eq) refl , hs)
    ∷ [])
  where
    s1 = record s  { pc = pc s + 1 }
    s2 = record s1 { regs = writeReg (regs s1) rcx 1 ; pc = pc s1 + 1 }
    s3 = record s2 { flags = mkflags (readReg (regs s2) rcx ≡ᵇ 0)
                                     (readReg (regs s2) rcx <ᵇ 0) false
                   ; pc = pc s2 + 1 }
    s4 = record s3 { pc = pc s3 + 1 }
    s5 = record s4 { regs = writeReg (regs s4) rbx (readReg (regs s4) rbx + 1)
                   ; flags = updateFlags (readReg (regs s4) rbx + 1) (readReg (regs s4) rbx)
                   ; pc = pc s4 + 1 }
    s6 = record s5 { regs = writeReg (regs s5) rdi child ; pc = pc s5 + 1 }
