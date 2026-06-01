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

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc)
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
open Flags using (zf)

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
-- post-iteration state: counter bumped (rbx+1), descended to the child
-- (rdi := child), back at the loop head (pc 1).  Memory / r14 / rax intact.
di-out : State → ℕ → State
di-out s child =
  record (record (record (record (record (record (record s
    { pc = pc s + 1 })                                            -- label4
    { regs = writeReg (regs s) rcx 1 ; pc = pc s + 1 + 1 })       -- mov rcx
    { flags = mkflags (1 ≡ᵇ 0) (1 <ᵇ 0) false ; pc = pc s + 1 + 1 + 1 })  -- cmp
    { pc = pc s + 1 + 1 + 1 + 1 })                                -- je not taken
    { regs = writeReg (writeReg (regs s) rcx 1) rbx (readReg (regs s) rbx + 1)
    ; flags = updateFlags (readReg (regs s) rbx + 1) (readReg (regs s) rbx)
    ; pc = pc s + 1 + 1 + 1 + 1 + 1 })                            -- add rbx
    { regs = writeReg (writeReg (writeReg (regs s) rcx 1) rbx (readReg (regs s) rbx + 1)) rdi child
    ; pc = pc s + 1 + 1 + 1 + 1 + 1 + 1 })                        -- mov rdi
    { pc = 1 }                                                    -- jmp4

descend-iter : ∀ (R : ℕ) (s : State) (child : ℕ)
  → pc s ≡ 1
  → halted s ≡ false
  → readMem (memory s) (readReg (regs s) rdi) ≡ just 1
  → readMem (memory s) (readReg (regs s) rdi + 8) ≡ just child
  → exec (7 + R) prog s ≡ exec R prog (di-out s child)
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

------------------------------------------------------------------------
-- Helpers: the result encoding and the isEven specification.
--
--   booltag b : how a Bool# heap node tags `b` (even/true = 0, odd = 1).
--   notⁿ k b  : `not` applied k times to b — the value of folding k suc
--               layers through the isEven algebra (each layer flips).
--   evenB n   : the cata semantics of isEven over Nat n (zero ↦ true,
--               suc ↦ not), proven equal to `notⁿ n true` below.
------------------------------------------------------------------------
booltag : Bool → ℕ
booltag true  = 0
booltag false = 1

notⁿ : ℕ → Bool → Bool
notⁿ zero    b = b
notⁿ (suc k) b = notⁿ k (not b)

evenB : ℕ → Bool
evenB zero    = true
evenB (suc n) = not (evenB n)

-- `notⁿ` distributes a leading `not` outward.
notⁿ-not : ∀ n b → notⁿ n (not b) ≡ not (notⁿ n b)
notⁿ-not zero    b = refl
notⁿ-not (suc n) b = notⁿ-not n (not b)

-- The compiled fold's value (`notⁿ n true`) is the isEven spec.
notⁿ-evenB : ∀ n → notⁿ n true ≡ evenB n
notⁿ-evenB zero    = refl
notⁿ-evenB (suc n) = trans (notⁿ-not n true) (cong not (notⁿ-evenB n))

-- Read the result node's tag: [rax].  even → 0, odd → 1.
result-tag : State → Maybe ℕ
result-tag fs = readMem (memory fs) (readReg (regs fs) rax)

------------------------------------------------------------------------
-- descend-exit: at a zero node (pc 1, tag 0), branch to lbase (pc 8).
-- 4 steps: label4 ; mov rcx←[rdi]=0 ; cmp rcx,0 (zf=true) ; je5(taken)→pc8.
------------------------------------------------------------------------
module _ (s : State) where
  d1 = record s  { pc = pc s + 1 }                                                   -- label4
  d2 = record d1 { regs = writeReg (regs d1) rcx 0 ; pc = pc d1 + 1 }                -- mov rcx←[rdi]=0
  d3 = record d2 { flags = mkflags (readReg (regs d2) rcx ≡ᵇ 0)
                                   (readReg (regs d2) rcx <ᵇ 0) false
                 ; pc = pc d2 + 1 }                                                  -- cmp rcx,0
  de-out = record d3 { pc = 8 }                                                      -- je5 taken → 8

descend-exit : ∀ (R : ℕ) (s : State)
  → pc s ≡ 1
  → halted s ≡ false
  → readMem (memory s) (readReg (regs s) rdi) ≡ just 0
  → exec (4 + R) prog s ≡ exec R prog (de-out s)
descend-exit R s pc-eq hs tag-eq =
  exec-steps R
    ( (hs , step-label  {prog} {s}     (cong (fetch prog) pc-eq) , hs)
    ∷ (hs , step-mov-rm {prog} {d1 s}  (cong (λ p → fetch prog (p + 1)) pc-eq) tag-eq , hs)
    ∷ (hs , step-cmp-ri {prog} {d2 s}  (cong (λ p → fetch prog (p + 1 + 1)) pc-eq) , hs)
    ∷ (hs , step-je-taken {prog} {d3 s} (cong (λ p → fetch prog (p + 1 + 1 + 1)) pc-eq) refl refl , hs)
    ∷ [])

------------------------------------------------------------------------
-- ascend-iter: one ascend-loop iteration (pc 46 → pc 46), 26 steps.
-- Decrements the counter rbx, builds an `inr` layer at the heap top H
-- (= prev-result A + 16), runs the algebra (flip the prev tag), and
-- produces a fresh result node at H+16 with tag booltag(not b).
--
-- Split into a read-heavy PREFIX (18 steps: suffix-dec + lcomb-build +
-- algebra-dispatch up to the inner cmp) and a read-free TAIL (8 steps:
-- the inner inl/inr build, branching on b).  Heap-top invariant: H = A+16.
------------------------------------------------------------------------

-- The uniform post-iteration state (both b-branches converge here, the
-- written tag being booltag(not b)).  A = prev result ptr = readReg rax.
ai-out : State → Bool → ℕ → State
ai-out s b pay = record s
  { regs = writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (regs s)
             rbx (readReg (regs s) rbx ∸ 1))
             rdi (readReg (regs s) r14))
             r14 (readReg (regs s) r14 + 16))
             rcx 1)
             rdi (readReg (regs s) rax))
             rcx (booltag b))
             rdi pay)
             rax (readReg (regs s) r14 + 16))
             r14 (readReg (regs s) r14 + 16 + 16)
  ; memory = writeMem (writeMem (writeMem (writeMem (memory s)
               (readReg (regs s) r14) 1)
               (readReg (regs s) r14 + 8) (readReg (regs s) rax))
               (readReg (regs s) r14 + 16) (booltag (not b)))
               (readReg (regs s) r14 + 16 + 8) pay
  ; flags = updateFlags (readReg (regs s) r14 + 16 + 16) (readReg (regs s) r14 + 16)
  ; pc = 46
  }

-- shared 18-step prefix; per-step intermediate states named (c1..c18).
module _ (s : State) (b : Bool) (pay : ℕ) where
  c1  = record s   { flags = mkflags (readReg (regs s) rbx ≡ᵇ 0) (readReg (regs s) rbx <ᵇ 0) false
                   ; pc = pc s + 1 }                                            -- cmp rbx,0
  c2  = record c1  { pc = pc c1 + 1 }                                          -- je8 not taken
  c3  = record c2  { regs = writeReg (regs c2) rbx (readReg (regs c2) rbx ∸ 1)
                   ; flags = updateFlags (readReg (regs c2) rbx ∸ 1) (readReg (regs c2) rbx)
                   ; pc = pc c2 + 1 }                                          -- sub rbx,1
  c4  = record c3  { pc = 14 }                                                 -- jmp7 → 14
  c5  = record c4  { pc = pc c4 + 1 }                                          -- label7
  c6  = record c5  { regs = writeReg (regs c5) rdi (readReg (regs c5) r14) ; pc = pc c5 + 1 }  -- mov rdi,r14
  c7  = record c6  { memory = writeMem (memory c6) (readReg (regs c6) r14) 1 ; pc = pc c6 + 1 } -- mov [r14],1
  c8  = record c7  { memory = writeMem (memory c7) (readReg (regs c7) r14 + 8) (readReg (regs c7) rax)
                   ; pc = pc c7 + 1 }                                          -- mov [r14+8],rax
  c9  = record c8  { regs = writeReg (regs c8) r14 (readReg (regs c8) r14 + 16)
                   ; flags = updateFlags (readReg (regs c8) r14 + 16) (readReg (regs c8) r14)
                   ; pc = pc c8 + 1 }                                          -- add r14,16
  c10 = record c9  { pc = pc c9 + 1 }                                          -- label6
  c11 = record c10 { regs = writeReg (regs c10) rcx 1 ; pc = pc c10 + 1 }      -- mov rcx,[rdi]=1
  c12 = record c11 { regs = writeReg (regs c11) rdi (readReg (regs s) rax) ; pc = pc c11 + 1 } -- mov rdi,[rdi+8]=A
  c13 = record c12 { flags = mkflags (readReg (regs c12) rcx ≡ᵇ 0) (readReg (regs c12) rcx <ᵇ 0) false
                   ; pc = pc c12 + 1 }                                          -- cmp rcx,0
  c14 = record c13 { pc = 29 }                                                 -- jne2 taken → 29
  c15 = record c14 { pc = pc c14 + 1 }                                         -- label2
  c16 = record c15 { regs = writeReg (regs c15) rcx (booltag b) ; pc = pc c15 + 1 } -- mov rcx,[rdi]=booltag b
  c17 = record c16 { regs = writeReg (regs c16) rdi pay ; pc = pc c16 + 1 }    -- mov rdi,[rdi+8]=pay
  c18 = record c17 { flags = mkflags (readReg (regs c17) rcx ≡ᵇ 0) (readReg (regs c17) rcx <ᵇ 0) false
                   ; pc = pc c17 + 1 }                                          -- cmp rcx,0

ascend-prefix : ∀ (R k : ℕ) (s : State) (b : Bool) (pay : ℕ)
  → pc s ≡ 46
  → halted s ≡ false
  → readReg (regs s) rbx ≡ suc k
  → readReg (regs s) r14 ≡ readReg (regs s) rax + 16
  → readMem (memory s) (readReg (regs s) rax) ≡ just (booltag b)
  → readMem (memory s) (readReg (regs s) rax + 8) ≡ just pay
  → exec (18 + R) prog s ≡ exec R prog (c18 s b pay)
ascend-prefix R k s b pay pc-eq hs rbx-eq inv tag-eq pay-eq =
  exec-steps R
    ( (hs , step-cmp-ri {prog} {s}        (cong (fetch prog) pc-eq) , hs)
    ∷ (hs , step-je-not {prog} {c1 s b pay} (cong (λ p → fetch prog (p + 1)) pc-eq) zf-false , hs)
    ∷ (hs , step-sub-ri {prog} {c2 s b pay} (cong (λ p → fetch prog (p + 1 + 1)) pc-eq) , hs)
    ∷ (hs , step-jmp    {prog} {c3 s b pay} (cong (λ p → fetch prog (p + 1 + 1 + 1)) pc-eq) refl , hs)
    ∷ (hs , step-label  {prog} {c4 s b pay}  refl , hs)
    ∷ (hs , step-mov-rr {prog} {c5 s b pay}  refl , hs)
    ∷ (hs , step-mov-mi {prog} {c6 s b pay}  refl , hs)
    ∷ (hs , step-mov-mr {prog} {c7 s b pay}  refl , hs)
    ∷ (hs , step-add-ri {prog} {c8 s b pay}  refl , hs)
    ∷ (hs , step-label  {prog} {c9 s b pay}  refl , hs)
    ∷ (hs , step-mov-rm {prog} {c10 s b pay} refl rd1 , hs)
    ∷ (hs , step-mov-rm {prog} {c11 s b pay} refl rd2 , hs)
    ∷ (hs , step-cmp-ri {prog} {c12 s b pay} refl , hs)
    ∷ (hs , step-jne-taken {prog} {c13 s b pay} refl rcx≢0 refl , hs)
    ∷ (hs , step-label  {prog} {c14 s b pay} refl , hs)
    ∷ (hs , step-mov-rm {prog} {c15 s b pay} refl rd3 , hs)
    ∷ (hs , step-mov-rm {prog} {c16 s b pay} refl rd4 , hs)
    ∷ (hs , step-cmp-ri {prog} {c17 s b pay} refl , hs)
    ∷ [])
  where
    H = readReg (regs s) r14
    A = readReg (regs s) rax
    -- the suffix's `cmp rbx,0` sets zf = (rbx ≡ᵇ 0) = false (rbx = suc k).
    zf-false : zf (flags (c1 s b pay)) ≡ false
    zf-false = cong (λ z → z ≡ᵇ 0) rbx-eq
    -- the inner `cmp rcx,0` after reading the layer tag (=1) sets zf = false.
    rcx≢0 : zf (flags (c13 s b pay)) ≡ false
    rcx≢0 = refl
    -- pos20 reads the just-built layer tag [H] = 1 (read-after-write).
    rd1 : readMem (memory (c10 s b pay)) (readReg (regs (c10 s b pay)) rdi) ≡ just 1
    rd1 = trans (read-write-diff (writeMem (memory s) H 1) H (H + 8) A (self≢plus H 7))
                (read-write-same (memory s) H 1)
    -- pos21 reads the layer payload [H+8] = A (read-after-write).
    rd2 : readMem (memory (c11 s b pay)) (readReg (regs (c11 s b pay)) rdi + 8) ≡ just A
    rd2 = read-write-same (writeMem (memory s) H 1) (H + 8) A
    -- A ≢ H and A ≢ H+8 (prev result is disjoint from the new layer).
    A≢H : (A ≡ᵇ H) ≡ false
    A≢H = trans (cong (A ≡ᵇ_) inv) (self≢plus A 15)
    A≢H+8 : (A ≡ᵇ H + 8) ≡ false
    A≢H+8 = trans (cong (λ z → A ≡ᵇ z + 8) inv) (trans (cong (A ≡ᵇ_) (+-assoc A 16 8)) (self≢plus A 23))
    A+8≢H : (A + 8 ≡ᵇ H) ≡ false
    A+8≢H = trans (cong (A + 8 ≡ᵇ_) inv) (+-cancelᵇ A 8 16)
    A+8≢H+8 : (A + 8 ≡ᵇ H + 8) ≡ false
    A+8≢H+8 = trans (cong (λ z → A + 8 ≡ᵇ z + 8) inv)
                    (trans (cong (A + 8 ≡ᵇ_) (+-assoc A 16 8)) (+-cancelᵇ A 8 24))
    -- pos30 reads the prev-result tag [A] = booltag b (through the layer writes).
    rd3 : readMem (memory (c15 s b pay)) (readReg (regs (c15 s b pay)) rdi) ≡ just (booltag b)
    rd3 = trans (read-write-diff (writeMem (memory s) H 1) A (H + 8) A A≢H+8)
                (trans (read-write-diff (memory s) A H 1 A≢H) tag-eq)
    -- pos31 reads the prev-result payload [A+8] = pay (through the layer writes).
    rd4 : readMem (memory (c16 s b pay)) (readReg (regs (c16 s b pay)) rdi + 8) ≡ just pay
    rd4 = trans (read-write-diff (writeMem (memory s) H 1) (A + 8) (H + 8) A A+8≢H+8)
                (trans (read-write-diff (memory s) (A + 8) H 1 A+8≢H) pay-eq)

-- per-step intermediate states of the read-free tail (named so exec-steps
-- need not infer them).  tt* = true branch, tf* = false branch.
module _ (s : State) (pay : ℕ) where
  tt1 = record (c18 s true pay) { pc = pc (c18 s true pay) + 1 }                                 -- jne0 not taken
  tt2 = record tt1 { regs = writeReg (regs tt1) rax (readReg (regs tt1) r14) ; pc = pc tt1 + 1 } -- mov rax,r14
  tt3 = record tt2 { memory = writeMem (memory tt2) (readReg (regs tt2) r14) 1 ; pc = pc tt2 + 1 } -- mov [r14],1
  tt4 = record tt3 { memory = writeMem (memory tt3) (readReg (regs tt3) r14 + 8) (readReg (regs tt3) rdi)
                   ; pc = pc tt3 + 1 }                                                            -- mov [r14+8],rdi
  tt5 = record tt4 { regs = writeReg (regs tt4) r14 (readReg (regs tt4) r14 + 16)
                   ; flags = updateFlags (readReg (regs tt4) r14 + 16) (readReg (regs tt4) r14)
                   ; pc = pc tt4 + 1 }                                                            -- add r14,16
  tt6 = record tt5 { pc = 44 }                                                                    -- jmp1 → 44
  tt7 = record tt6 { pc = pc tt6 + 1 }                                                            -- label1

  tf1 = record (c18 s false pay) { pc = 39 }                                                      -- jne0 taken → 39
  tf2 = record tf1 { pc = pc tf1 + 1 }                                                            -- label0
  tf3 = record tf2 { regs = writeReg (regs tf2) rax (readReg (regs tf2) r14) ; pc = pc tf2 + 1 } -- mov rax,r14
  tf4 = record tf3 { memory = writeMem (memory tf3) (readReg (regs tf3) r14) 0 ; pc = pc tf3 + 1 } -- mov [r14],0
  tf5 = record tf4 { memory = writeMem (memory tf4) (readReg (regs tf4) r14 + 8) (readReg (regs tf4) rdi)
                   ; pc = pc tf4 + 1 }                                                            -- mov [r14+8],rdi
  tf6 = record tf5 { regs = writeReg (regs tf5) r14 (readReg (regs tf5) r14 + 16)
                   ; flags = updateFlags (readReg (regs tf5) r14 + 16) (readReg (regs tf5) r14)
                   ; pc = pc tf5 + 1 }                                                            -- add r14,16
  tf7 = record tf6 { pc = pc tf6 + 1 }                                                            -- label1

-- read-free 8-step tail from c18 (pc 33): the inner inl/inr build, then
-- rejoin at pc 46.  Branches on b (which jne is taken); both converge to
-- ai-out (the written tag is booltag(not b)).
ascend-tail : ∀ (R : ℕ) (s : State) (b : Bool) (pay : ℕ)
  → halted s ≡ false
  → exec (8 + R) prog (c18 s b pay) ≡ exec R prog (ai-out s b pay)
ascend-tail R s true pay hs =
  exec-steps R
    ( (hs , step-jne-not {prog} {c18 s true pay} refl refl , hs)  -- jne0 not taken (zf=true)
    ∷ (hs , step-mov-rr {prog} {tt1 s pay} refl , hs)             -- mov rax,r14
    ∷ (hs , step-mov-mi {prog} {tt2 s pay} refl , hs)             -- mov [r14],1
    ∷ (hs , step-mov-mr {prog} {tt3 s pay} refl , hs)             -- mov [r14+8],rdi
    ∷ (hs , step-add-ri {prog} {tt4 s pay} refl , hs)             -- add r14,16
    ∷ (hs , step-jmp    {prog} {tt5 s pay} refl refl , hs)        -- jmp1 → 44
    ∷ (hs , step-label  {prog} {tt6 s pay} refl , hs)             -- label1
    ∷ (hs , step-label  {prog} {tt7 s pay} refl , hs)             -- label3 → 46
    ∷ [])
ascend-tail R s false pay hs =
  exec-steps R
    ( (hs , step-jne-taken {prog} {c18 s false pay} refl refl refl , hs)  -- jne0 taken (zf=false) → 39
    ∷ (hs , step-label  {prog} {tf1 s pay} refl , hs)            -- label0
    ∷ (hs , step-mov-rr {prog} {tf2 s pay} refl , hs)            -- mov rax,r14
    ∷ (hs , step-mov-mi {prog} {tf3 s pay} refl , hs)            -- mov [r14],0
    ∷ (hs , step-mov-mr {prog} {tf4 s pay} refl , hs)            -- mov [r14+8],rdi
    ∷ (hs , step-add-ri {prog} {tf5 s pay} refl , hs)            -- add r14,16
    ∷ (hs , step-label  {prog} {tf6 s pay} refl , hs)            -- label1
    ∷ (hs , step-label  {prog} {tf7 s pay} refl , hs)            -- label3 → 46
    ∷ [])

ascend-iter : ∀ (R k : ℕ) (s : State) (b : Bool) (pay : ℕ)
  → pc s ≡ 46
  → halted s ≡ false
  → readReg (regs s) rbx ≡ suc k
  → readReg (regs s) r14 ≡ readReg (regs s) rax + 16
  → readMem (memory s) (readReg (regs s) rax) ≡ just (booltag b)
  → readMem (memory s) (readReg (regs s) rax + 8) ≡ just pay
  → exec (26 + R) prog s ≡ exec R prog (ai-out s b pay)
ascend-iter R k s b pay pc-eq hs rbx-eq inv tag-eq pay-eq =
  trans (ascend-prefix (8 + R) k s b pay pc-eq hs rbx-eq inv tag-eq pay-eq)
        (ascend-tail R s b pay hs)

------------------------------------------------------------------------
-- ascend: the ascend loop runs the algebra `k` times (rbx = k), flipping
-- the result tag each iteration, then halts.  Result tag = booltag(notⁿ k b).
------------------------------------------------------------------------
ascend-steps : ℕ → ℕ
ascend-steps zero    = 3
ascend-steps (suc k) = 26 + ascend-steps k

-- running off the end of the program (fetch nothing) halts in one step.
exec-halt : ∀ {R : ℕ} (s : State)
          → halted s ≡ false
          → fetch prog (pc s) ≡ nothing
          → exec (suc R) prog s ≡ just (record s { halted = true })
exec-halt s hs fn rewrite hs | fn = refl

-- ascend-exit: rbx = 0 at pc 46 → cmp(zf true) ; je8(taken)→pc50 ; label8→pc51.
module _ (s : State) where
  ax1 = record s   { flags = mkflags (readReg (regs s) rbx ≡ᵇ 0) (readReg (regs s) rbx <ᵇ 0) false
                   ; pc = pc s + 1 }                                          -- cmp rbx,0
  ax2 = record ax1 { pc = 50 }                                               -- je8 taken → 50
  ax3 = record ax2 { pc = pc ax2 + 1 }                                       -- label8 → 51

ascend-exit : ∀ (R : ℕ) (s : State)
  → pc s ≡ 46 → halted s ≡ false
  → readReg (regs s) rbx ≡ 0
  → exec (3 + R) prog s ≡ exec R prog (ax3 s)
ascend-exit R s pc-eq hs rbx0 =
  exec-steps R
    ( (hs , step-cmp-ri {prog} {s}     (cong (fetch prog) pc-eq) , hs)
    ∷ (hs , step-je-taken {prog} {ax1 s} (cong (λ p → fetch prog (p + 1)) pc-eq) zf-true refl , hs)
    ∷ (hs , step-label {prog} {ax2 s}  refl , hs)
    ∷ [])
  where
    zf-true : zf (flags (ax1 s)) ≡ true
    zf-true = cong (λ z → z ≡ᵇ 0) rbx0

ascend : ∀ (k R : ℕ) (s : State) (b : Bool) (pay : ℕ)
  → pc s ≡ 46
  → halted s ≡ false
  → readReg (regs s) rbx ≡ k
  → readReg (regs s) r14 ≡ readReg (regs s) rax + 16
  → readMem (memory s) (readReg (regs s) rax) ≡ just (booltag b)
  → readMem (memory s) (readReg (regs s) rax + 8) ≡ just pay
  → map result-tag (exec (ascend-steps k + suc R) prog s) ≡ just (just (booltag (notⁿ k b)))

ascend zero R s b pay pc-eq hs rbx-eq inv tag-eq pay-eq =
  trans (cong (map result-tag) (ascend-exit (suc R) s pc-eq hs rbx-eq))
        (trans (cong (map result-tag) (exec-halt {R} (ax3 s) hs refl))
               (cong just tag-eq))

ascend (suc k) R s b pay pc-eq hs rbx-eq inv tag-eq pay-eq =
  trans (cong (map result-tag)
              (ascend-iter (ascend-steps k + suc R) k s b pay pc-eq hs rbx-eq inv tag-eq pay-eq))
        (ascend k R (ai-out s b pay) (not b) pay
          refl hs
          (cong (λ z → z ∸ 1) rbx-eq)
          refl
          tag-eq'
          pay-eq')
  where
    H = readReg (regs s) r14
    A = readReg (regs s) rax
    -- the fresh result node at H+16 has tag booltag(not b) and payload pay,
    -- read through the trailing payload write at H+16+8.
    tag-eq' : readMem (memory (ai-out s b pay)) (readReg (regs (ai-out s b pay)) rax)
              ≡ just (booltag (not b))
    tag-eq' = trans (read-write-diff
                       (writeMem (writeMem (writeMem (memory s) H 1) (H + 8) A) (H + 16) (booltag (not b)))
                       (H + 16) (H + 16 + 8) pay (self≢plus (H + 16) 7))
                    (read-write-same
                       (writeMem (writeMem (memory s) H 1) (H + 8) A) (H + 16) (booltag (not b)))
    pay-eq' : readMem (memory (ai-out s b pay)) (readReg (regs (ai-out s b pay)) rax + 8)
              ≡ just pay
    pay-eq' = read-write-same
                (writeMem (writeMem (writeMem (memory s) H 1) (H + 8) A) (H + 16) (booltag (not b)))
                (H + 16 + 8) pay

------------------------------------------------------------------------
-- Heap representation of a Nat (μ NatF): zero = [ptr]=0 ; suc = [ptr]=1,
-- [ptr+8]=child-ptr.  (Same layout the compiled loop reads while descending.)
------------------------------------------------------------------------
data HeapNat (m : Memory) : ℕ → ℕ → Set where  -- HeapNat m ptr n
  hz : ∀ {ptr}
     → m ptr ≡ just 0
     → HeapNat m ptr 0
  hs : ∀ {ptr child n}
     → m ptr ≡ just 1
     → m (ptr + 8) ≡ just child
     → HeapNat m child n
     → HeapNat m ptr (suc n)

------------------------------------------------------------------------
-- cata-run: the whole fold (descend-count + base + ascend) for a heap Nat
-- of value n, with the running suc-count `acc` already in rbx.  Result tag
-- = booltag(notⁿ (acc + n) true).  Fuel ≤ f(μ-size): linear in n and acc.
------------------------------------------------------------------------
cata-fuel : ℕ → ℕ → ℕ   -- n acc
cata-fuel zero    acc = 4 + (17 + ascend-steps acc)   -- descend-exit + base + ascend
cata-fuel (suc n) acc = 7 + cata-fuel n (acc + 1)     -- descend-iter + rest

cata-run : ∀ (n acc R : ℕ) (s : State)
  → pc s ≡ 1
  → halted s ≡ false
  → readReg (regs s) rbx ≡ acc
  → HeapNat (memory s) (readReg (regs s) rdi) n
  → map result-tag (exec (cata-fuel n acc + suc R) prog s)
    ≡ just (just (booltag (notⁿ (acc + n) true)))

-- bottom (zero node): descend-exit → base (build true result) → ascend.
cata-run zero acc R s pc-eq hlt rbx-eq (hz tag0) =
  trans (cong (map result-tag) (descend-exit (17 + (ascend-steps acc + suc R)) s pc-eq hlt tag0))
        (trans (cong (map result-tag) (base-phase (ascend-steps acc + suc R) (de-out s) refl hlt))
               (trans (ascend acc R (base-out (de-out s)) true 0
                        refl hlt rbx-eq refl tag-eq' pay-eq')
                      (cong (λ z → just (just (booltag (notⁿ z true)))) (sym (+-identityʳ acc)))))
  where
    H = readReg (regs s) r14
    -- the true result node base built at H+16: tag 0 = booltag true, payload 0.
    tag-eq' : readMem (memory (base-out (de-out s))) (readReg (regs (base-out (de-out s))) rax)
              ≡ just (booltag true)
    tag-eq' = trans (read-write-diff
                       (writeMem (writeMem (writeMem (memory s) H 0) (H + 8) 0) (H + 16) 0)
                       (H + 16) (H + 16 + 8) 0 (self≢plus (H + 16) 7))
                    (read-write-same
                       (writeMem (writeMem (memory s) H 0) (H + 8) 0) (H + 16) 0)
    pay-eq' : readMem (memory (base-out (de-out s))) (readReg (regs (base-out (de-out s))) rax + 8)
              ≡ just 0
    pay-eq' = read-write-same
                (writeMem (writeMem (writeMem (memory s) H 0) (H + 8) 0) (H + 16) 0)
                (H + 16 + 8) 0

-- suc node: one descend-iter (bump rbx, chase child), then recurse.
cata-run (suc n) acc R s pc-eq hlt rbx-eq (hs {child = ch} tag1 child-eq heapchild) =
  trans (cong (map result-tag)
              (descend-iter (cata-fuel n (acc + 1) + suc R) s ch pc-eq hlt tag1 child-eq))
        (trans (cata-run n (acc + 1) R (di-out s ch) refl hlt (cong (_+ 1) rbx-eq) heapchild)
               (cong (λ z → just (just (booltag (notⁿ z true)))) (+-assoc acc 1 n)))

------------------------------------------------------------------------
-- The compiled isEven catamorphism is correct for EVERY heap Nat.
-- From the loop head (pc 1, rbx = 0): result tag = booltag (evenB n).
------------------------------------------------------------------------
cata-isEven : ∀ (n R : ℕ) (s : State)
  → pc s ≡ 1
  → halted s ≡ false
  → readReg (regs s) rbx ≡ 0
  → HeapNat (memory s) (readReg (regs s) rdi) n
  → map result-tag (exec (cata-fuel n 0 + suc R) prog s) ≡ just (just (booltag (evenB n)))
cata-isEven n R s pc-eq hlt rbx0 heap =
  trans (cata-run n 0 R s pc-eq hlt rbx0 heap)
        (cong (λ z → just (just (booltag z))) (notⁿ-evenB n))

-- From the program entry (pc 0): the prelude `mov rbx,0` then the fold.
p1 : State → State
p1 s = record s { regs = writeReg (regs s) rbx 0 ; pc = pc s + 1 }

cata-isEven-full : ∀ (n R : ℕ) (s : State)
  → pc s ≡ 0
  → halted s ≡ false
  → HeapNat (memory s) (readReg (regs s) rdi) n
  → map result-tag (exec (suc (cata-fuel n 0) + suc R) prog s) ≡ just (just (booltag (evenB n)))
cata-isEven-full n R s pc-eq hlt heap =
  trans (cong (map result-tag)
              (exec-steps (cata-fuel n 0 + suc R)
                ((hlt , step-mov-ri {prog} {s} (cong (fetch prog) pc-eq) , hlt) ∷ [])))
        (cata-isEven n R (p1 s) (cong (λ p → p + 1) pc-eq) hlt refl heap)

------------------------------------------------------------------------
-- Sanity: the GENERAL theorem reproduces the concrete results that
-- `CataIsEvenCodegen` gets by `refl` (n=2 even → tag 0, n=3 odd → tag 1),
-- but now as instances of the ∀-n proof rather than one-off executions.
------------------------------------------------------------------------
heap2 : Memory
heap2 = writeMem (writeMem (writeMem (writeMem (writeMem emptyMemory 8 0) 16 1) 24 8) 32 1) 40 16

heap3 : Memory
heap3 = writeMem (writeMem heap2 48 1) 56 32

start-at : Memory → ℕ → State
start-at m root = record initState
  { regs = writeReg (writeReg (State.regs initState) r14 1000) rdi root ; memory = m }

heapNat2 : HeapNat heap2 32 2
heapNat2 = hs refl refl (hs refl refl (hz refl))

heapNat3 : HeapNat heap3 48 3
heapNat3 = hs refl refl (hs refl refl (hs refl refl (hz refl)))

-- isEven 2 = true  → result node tag 0
even-2 : map result-tag (exec (suc (cata-fuel 2 0) + suc 0) prog (start-at heap2 32)) ≡ just (just 0)
even-2 = cata-isEven-full 2 0 (start-at heap2 32) refl refl heapNat2

-- isEven 3 = false → result node tag 1
even-3 : map result-tag (exec (suc (cata-fuel 3 0) + suc 0) prog (start-at heap3 48)) ≡ just (just 1)
even-3 = cata-isEven-full 3 0 (start-at heap3 48) refl refl heapNat3
