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

------------------------------------------------------------------------
-- base phase (pc 8 → pc 46): build zero-layer, run alg (tag 0 → true).
-- 17 steps; reads the just-written layer cells via the memory algebra.
------------------------------------------------------------------------
-- per-step states of the base phase (top-level so the conclusion can name
-- the final state). H = heap top = readReg (regs s) r14.
module _ (s : State) where
  b1  = record s   { pc = pc s + 1 }
  b2  = record b1  { regs = writeReg (regs b1) rdi (readReg (regs b1) r14) ; pc = pc b1 + 1 }
  b3  = record b2  { memory = writeMem (memory b2) (readReg (regs b2) r14) 0 ; pc = pc b2 + 1 }
  b4  = record b3  { memory = writeMem (memory b3) (readReg (regs b3) r14 + 8) 0 ; pc = pc b3 + 1 }
  b5  = record b4  { regs = writeReg (regs b4) r14 (readReg (regs b4) r14 + 16)
                   ; flags = updateFlags (readReg (regs b4) r14 + 16) (readReg (regs b4) r14)
                   ; pc = pc b4 + 1 }
  b6  = record b5  { pc = 19 }
  b7  = record b6  { pc = pc b6 + 1 }
  b8  = record b7  { regs = writeReg (regs b7) rcx 0 ; pc = pc b7 + 1 }
  b9  = record b8  { regs = writeReg (regs b8) rdi 0 ; pc = pc b8 + 1 }
  b10 = record b9  { flags = mkflags (readReg (regs b9) rcx ≡ᵇ 0) (readReg (regs b9) rcx <ᵇ 0) false
                   ; pc = pc b9 + 1 }
  b11 = record b10 { pc = pc b10 + 1 }
  b12 = record b11 { regs = writeReg (regs b11) rax (readReg (regs b11) r14) ; pc = pc b11 + 1 }
  b13 = record b12 { memory = writeMem (memory b12) (readReg (regs b12) r14) 0 ; pc = pc b12 + 1 }
  b14 = record b13 { memory = writeMem (memory b13) (readReg (regs b13) r14 + 8) (readReg (regs b13) rdi)
                   ; pc = pc b13 + 1 }
  b15 = record b14 { regs = writeReg (regs b14) r14 (readReg (regs b14) r14 + 16)
                   ; flags = updateFlags (readReg (regs b14) r14 + 16) (readReg (regs b14) r14)
                   ; pc = pc b14 + 1 }
  b16 = record b15 { pc = 45 }
  base-out = record b16 { pc = pc b16 + 1 }

base-phase : ∀ (R : ℕ) (s : State)
  → pc s ≡ 8
  → halted s ≡ false
  → exec (17 + R) prog s ≡ exec R prog (base-out s)
base-phase R s pc-eq hs =
  exec-steps R
    ( (hs , step-label  {prog} {s}      (cong (fetch prog) pc-eq) , hs)
    ∷ (hs , step-mov-rr {prog} {b1 s}   (cong (λ p → fetch prog (p + 1)) pc-eq) , hs)
    ∷ (hs , step-mov-mi {prog} {b2 s}   (cong (λ p → fetch prog (p + 1 + 1)) pc-eq) , hs)
    ∷ (hs , step-mov-mi {prog} {b3 s}   (cong (λ p → fetch prog (p + 1 + 1 + 1)) pc-eq) , hs)
    ∷ (hs , step-add-ri {prog} {b4 s}   (cong (λ p → fetch prog (p + 1 + 1 + 1 + 1)) pc-eq) , hs)
    ∷ (hs , step-jmp    {prog} {b5 s}   (cong (λ p → fetch prog (p + 1 + 1 + 1 + 1 + 1)) pc-eq) refl , hs)
    ∷ (hs , step-label  {prog} {b6 s}   refl , hs)
    ∷ (hs , step-mov-rm {prog} {b7 s}   refl rd-tag , hs)
    ∷ (hs , step-mov-rm {prog} {b8 s}   refl rd-pay , hs)
    ∷ (hs , step-cmp-ri {prog} {b9 s}   refl , hs)
    ∷ (hs , step-jne-not {prog} {b10 s} refl refl , hs)
    ∷ (hs , step-mov-rr {prog} {b11 s}  refl , hs)
    ∷ (hs , step-mov-mi {prog} {b12 s}  refl , hs)
    ∷ (hs , step-mov-mr {prog} {b13 s}  refl , hs)
    ∷ (hs , step-add-ri {prog} {b14 s}  refl , hs)
    ∷ (hs , step-jmp    {prog} {b15 s}  refl refl , hs)
    ∷ (hs , step-label  {prog} {b16 s}  refl , hs)
    ∷ [])
  where
    H = readReg (regs s) r14
    rd-tag : readMem (memory (b7 s)) (readReg (regs (b7 s)) rdi) ≡ just 0
    rd-tag = trans (read-write-diff (writeMem (memory s) H 0) H (H + 8) 0 (self≢plus H 7))
                   (read-write-same (memory s) H 0)
    rd-pay : readMem (memory (b8 s)) (readReg (regs (b8 s)) rdi + 8) ≡ just 0
    rd-pay = read-write-same (writeMem (memory s) H 0) (H + 8) 0
