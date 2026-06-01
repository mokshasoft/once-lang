-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Examples.NatFoldLoopInduction
--
-- Plan 0.27 (C3, POC): the descend-loop refinement, proven for ALL inputs
-- by induction — not a single concrete `refl`-execution.
--
-- `NatFoldLoop` proves `run fold-prog (start 3) ≡ just 3` by `refl` on one
-- fixed heap Nat. C3 needs the general statement: the compiled loop folds
-- *every* heap-Nat correctly, with a fuel bound derived from the value's
-- size (the plan's "fuel ≤ f(μ-size)"). This module establishes exactly
-- that for the descend-counting loop (the NatF depth fold), by induction
-- on the abstract `n` together with the heap-representation predicate
-- `HeapNat`:
--
--   fold-correct : … → HeapNat m ptr n
--                → map rax-of (exec (needed n + extra) fold-prog s) ≡ just (acc + n)
--
-- This is the load-bearing technique for the full `Cata` refinement (C3):
-- (1) a per-iteration reduction lemma `iter` that peels a FIXED number of
-- steps off SYMBOLIC fuel (so the loop body is reasoned once, not unrolled
-- per input), and (2) induction on the μ-value with the fuel bound carried
-- structurally. The full Cata loop adds the ascend/apply-algebra phase on
-- top of this descend skeleton; the proof shape is the same.
------------------------------------------------------------------------

module Once.CCC.Examples.NatFoldLoopInduction where

open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CCC.Target.X86-64.Syntax
open import Once.CCC.Target.X86-64.Semantics

open State using (regs)

------------------------------------------------------------------------
-- The loop (identical to NatFoldLoop.fold-prog): count the sucs of a heap
-- Nat into rax.
--   label 0: mov rcx,[rdi]; cmp rcx,0; je 1; add rax,1; mov rdi,[rdi+8]; jmp 0
--   label 1: end
------------------------------------------------------------------------
fold-prog : Program
fold-prog =
    label 0
  ∷ mov (reg rcx) (mem (base rdi))
  ∷ cmp (reg rcx) (imm 0)
  ∷ je 1
  ∷ add (reg rax) (imm 1)
  ∷ mov (reg rdi) (mem (base+disp rdi 8))
  ∷ jmp 0
  ∷ label 1
  ∷ []

------------------------------------------------------------------------
-- Heap representation of a NatF value (tagged nodes, matching the heap
-- sum-node layout): zero = [ptr]=0 ; suc = [ptr]=1, [ptr+8]=child-ptr.
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
-- A loop-head state at pc 0 (not halted), parameterised by the register
-- file / flags / memory. `halted ≡ false` holds definitionally (it is the
-- literal field), so `exec`/`step` reduce without a side hypothesis; the
-- only neutrals during a run are the memory reads.
------------------------------------------------------------------------
head : RegFile → Flags → Memory → State
head rf fl m = mkstate rf m fl 0 false

-- Read the accumulator.
rax-of : State → ℕ
rax-of s = readReg (regs s) rax

------------------------------------------------------------------------
-- Fuel needed to fold a Nat of value `n`: 6 steps to bottom out on zero,
-- +7 per suc layer. (A concrete `f(μ-size)`.)
------------------------------------------------------------------------
needed : ℕ → ℕ
needed zero    = 6
needed (suc n) = 7 + needed n

------------------------------------------------------------------------
-- One suc-iteration: peel 7 steps off SYMBOLIC fuel R, landing on the
-- child state with the accumulator bumped. Proven by letting `exec` reduce
-- through the (concrete) instructions, rewriting only the two memory reads
-- (tag, child) and the two register reads (rdi, rax). rdi is read at pc 1
-- and again at pc 5, so `rdi-eq` is applied at both exposure points.
------------------------------------------------------------------------
iter : ∀ (R : ℕ) (rf : RegFile) (fl : Flags) (m : Memory) (ptr child acc : ℕ)
     → readReg rf rdi ≡ ptr
     → readReg rf rax ≡ acc
     → m ptr ≡ just 1
     → m (ptr + 8) ≡ just child
     → exec (7 + R) fold-prog (head rf fl m)
       ≡ exec R fold-prog
           (head (writeReg (writeReg (writeReg rf rcx 1) rax (acc + 1)) rdi child)
                 (mkflags ((acc + 1) ≡ᵇ 0) false false) m)
iter R rf fl m ptr child acc rdi-eq rax-eq tag-eq child-eq
  rewrite rdi-eq | tag-eq | rax-eq | rdi-eq | child-eq = refl

------------------------------------------------------------------------
-- The descend-loop refinement, for ALL inputs, by induction on the
-- HeapNat / abstract value.
------------------------------------------------------------------------
fold-correct : ∀ (n extra : ℕ) (rf : RegFile) (fl : Flags) (m : Memory) (ptr acc : ℕ)
             → readReg rf rdi ≡ ptr
             → readReg rf rax ≡ acc
             → HeapNat m ptr n
             → map rax-of (exec (needed n + extra) fold-prog (head rf fl m))
               ≡ just (acc + n)

-- zero: read tag 0, branch to the end label, halt. rax untouched (= acc).
fold-correct zero extra rf fl m ptr acc rdi-eq rax-eq (hz tag0-eq)
  rewrite rdi-eq | tag0-eq | rax-eq | +-identityʳ acc = refl

-- suc k: one iteration (iter) bumps rax and descends to the child; the IH
-- folds the child with accumulator (acc + 1) and (needed k) fuel.
fold-correct (suc k) extra rf fl m ptr acc rdi-eq rax-eq (hs tag-eq child-eq heapchild) =
  trans (cong (map rax-of)
              (iter (needed k + extra) rf fl m ptr _ acc rdi-eq rax-eq tag-eq child-eq))
        (trans (fold-correct k extra
                  (writeReg (writeReg (writeReg rf rcx 1) rax (acc + 1)) rdi _)
                  (mkflags ((acc + 1) ≡ᵇ 0) false false) m _ (acc + 1)
                  refl refl heapchild)
               (cong just (+-assoc acc 1 k)))

------------------------------------------------------------------------
-- Corollary: from a clean accumulator (rax = 0), the fold computes `n`.
------------------------------------------------------------------------
fold-clean : ∀ (n extra : ℕ) (rf : RegFile) (fl : Flags) (m : Memory) (ptr : ℕ)
           → readReg rf rdi ≡ ptr
           → readReg rf rax ≡ 0
           → HeapNat m ptr n
           → map rax-of (exec (needed n + extra) fold-prog (head rf fl m)) ≡ just n
fold-clean n extra rf fl m ptr rdi-eq rax0 h =
  fold-correct n extra rf fl m ptr 0 rdi-eq rax0 h

------------------------------------------------------------------------
-- Sanity: the concrete heap Nat 3 of `NatFoldLoop` (nodes at 8/16/32/48)
-- is a `HeapNat`, and the GENERAL theorem (not a one-off `refl`) folds it
-- to 3. The HeapNat read equations are discharged by `refl` on the
-- concrete memory.
------------------------------------------------------------------------
heap3 : Memory
heap3 = writeMem (writeMem (writeMem (writeMem (writeMem (writeMem (writeMem
          emptyMemory
          8 0) 16 1) 24 8) 32 1) 40 16) 48 1) 56 32

heapNat3 : HeapNat heap3 48 3
heapNat3 = hs refl refl (hs refl refl (hs refl refl (hz refl)))

start3 : State
start3 = head (writeReg (writeReg emptyRegFile rdi 48) rax 0) initFlags heap3

fold-3 : map rax-of (exec (needed 3 + 0) fold-prog start3) ≡ just 3
fold-3 = fold-clean 3 0 (writeReg (writeReg emptyRegFile rdi 48) rax 0) initFlags
                     heap3 48 refl refl heapNat3
