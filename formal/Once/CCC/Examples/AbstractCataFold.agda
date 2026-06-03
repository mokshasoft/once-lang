-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Examples.AbstractCataFold
--
-- Plan 0.30 (N2, test-first): the abstract-machine analogue of
-- `NatFoldLoop` / `CataIsEvenInduction`. Where those run the compiled
-- fold on the real x86-64 CPU (`Semantics.exec`), this one runs the SAME
-- cata descend-loop on the ABSTRACT machine (`exec-trace` / `exec-loop`)
-- and checks it folds a heap-μ-value correctly.
--
-- This ONLY typechecks once `exec-abstract (instr-case-on-tag …)` actually
-- BRANCHES on the scrutinee tag (Plan 0.30 N3). While case-on-tag halted
-- (Plan 0.13.1) the loop body halted on the first node and `Input2` never
-- reached 2 — so this module is the red→green anchor for the branch change.
--
-- Heap layout (NatF = K Unit ⊕ Id, heap nodes = tagged cells, child at +1):
--   rA: [rA,0]=Tag 0                              zero
--   rB: [rB,0]=Tag 1 ; [rB,1]=Ptr rA             suc zero      (= 1)
--   rC: [rC,0]=Tag 1 ; [rC,1]=Ptr rB             suc (suc zero)(= 2)
--
-- The descend-loop counts the `suc`s into the `Input2` depth accumulator:
--   instr-loop (case-on-tag  (tag 0 → scratch:=0, stop)
--                            (tag 1 → depth++, follow child, continue))
-- so folding the root `rC` leaves `Input2 = SV-Tag 2`.
--
-- Parameterised over an arbitrary frame so we needn't build a concrete
-- `StackPointer`/`InStack` — the fold never touches the stack frame.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Examples.AbstractCataFold
  (FS : FrameSemantics)
  (f0 : FrameSemantics.Frame FS)
  where

open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.Machine.SMCore
open MemOps {FS}
open AbstractExec {FS}

------------------------------------------------------------------------
-- Heap: three distinct refs build the μ-value `2 = suc (suc zero)`.
------------------------------------------------------------------------

rA rB rC : HeapRef
rA = mkHeapRef 1
rB = mkHeapRef 2
rC = mkHeapRef 3

heap : HeapMem FS
heap = writeHeapMem (writeHeapMem (writeHeapMem (writeHeapMem (writeHeapMem
         (λ _ → nothing)
         (heap-loc rA 0) (SV-Tag 0))
         (heap-loc rB 0) (SV-Tag 1))
         (heap-loc rB 1) (SV-Ptr (AtDynamic (heap-loc rA 0))))
         (heap-loc rC 0) (SV-Tag 1))
         (heap-loc rC 1) (SV-Ptr (AtDynamic (heap-loc rB 0)))

------------------------------------------------------------------------
-- Start state: Input1 points at the root node (value 2); Input2/Scratch
-- are reset by the trace prefix.
------------------------------------------------------------------------

regs0 : Registers FS
regs0 = mkRegs (SV-Ptr (AtDynamic (heap-loc rC 0)))  -- input1 = root
               (SV-Tag 99)                            -- input2  (reset below)
               (SV-Tag 99)                            -- output
               0                                      -- stackSlot
               (SV-Tag 99)                            -- scratch (set below)

s0 : LocState FS
s0 = mkLocState regs0 (λ _ _ → nothing) heap false

alloc0 : AllocState {FS}
alloc0 = mkAllocState f0 0 0

------------------------------------------------------------------------
-- The cata descend-loop (identical shape to `IRToTrace`'s Cata clause).
------------------------------------------------------------------------

descend-body : AbstractTrace
descend-body =
  instr-case-on-tag
    (instr-reg-op scratch-zero ∷ [])                                    -- tag 0: stop
    (instr-reg-op input2-inc ∷ load-indirect-suc ∷ mov-to-input ∷ [])   -- tag 1: depth++, descend
  ∷ []

fold-trace : AbstractTrace
fold-trace =
    instr-reg-op scratch-one          -- enter loop (Scratch := 1)
  ∷ instr-reg-op input2-zero          -- depth := 0
  ∷ instr-loop descend-body
  ∷ []

result : LocState FS
result = proj₁ (exec-trace fold-trace s0 alloc0)

------------------------------------------------------------------------
-- The abstract fold computes the μ-value's depth: Input2 = 2.
------------------------------------------------------------------------

fold-counts-2 : readReg (regs result) Input2 ≡ SV-Tag 2
fold-counts-2 = refl
