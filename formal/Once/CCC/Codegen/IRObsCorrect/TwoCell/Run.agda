-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.TwoCell.Run
--
-- The TEN-STEP RUN of the two-cell build (`curry`, `Ana` — D190): the trace,
-- its states and the chain. Split from `TwoCellBuild` for the per-module
-- check cap; the facts about the states are there.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.TwoCell.Run (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ; LabelId)
open import Once.CCC.Machine.Locations using (ValueLocation; AtDynamic; AtStack)
open import Once.CCC.Machine.SMCore using (AllocState; next-slot; next-heap-ref; AbstractTrace; mov-to-output; store-at-slot; instr-alloc-heap; mov-to-input; load-from-slot; store-indirect; instr-load-code-addr; store-indirect-suc; LocState; StoredValue; halted; readReg; regs; Output; current-frame; sv-as-loc; Input1)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM


module TwoCellRunC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

  two-cell-trace : ℕ → ℕ → AbstractTrace
  two-cell-trace n l =
    mov-to-output ∷ store-at-slot n ∷ instr-alloc-heap 2 ∷ store-at-slot (suc n) ∷
    mov-to-input ∷ load-from-slot n ∷ store-indirect ∷
    instr-load-code-addr (ℓ o l) ∷ store-indirect-suc ∷ load-from-slot (suc n) ∷ []

  module TwoCellRun
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (two-cell-trace n l))
    where

    cell0-stash obj-stash : ℕ
    cell0-stash     = n
    obj-stash = suc n

    -- D182: this clause's instance of the shared ten-step invariant — the
    -- same shape as `inl`'s, with the two middle rows swapped.
    module TSP = TenStepPres n (load-from-slot n) (instr-load-code-addr (ℓ o l))
                             prog base s alloc cl

    code-lbl : LabelId
    code-lbl = ℓ o l

    fs0 fs1 fs2 fs3 fs4 fs5 fs6 fs7 fs8 fs9 fs10 : FlatState
    fs0  = entry-flat base s alloc cl
    fs1  = flat-exec-instr mov-to-output                  prog fs0
    fs2  = flat-exec-instr (store-at-slot cell0-stash)      prog fs1
    fs3  = flat-exec-instr (instr-alloc-heap 2)           prog fs2
    fs4  = flat-exec-instr (store-at-slot obj-stash)  prog fs3
    fs5  = flat-exec-instr mov-to-input                   prog fs4
    fs6  = flat-exec-instr (load-from-slot cell0-stash)     prog fs5
    fs7  = flat-exec-instr store-indirect                 prog fs6
    fs8  = flat-exec-instr (instr-load-code-addr code-lbl) prog fs7
    fs9  = flat-exec-instr store-indirect-suc             prog fs8
    fs10 = flat-exec-instr (load-from-slot obj-stash) prog fs9

    obj-hl : HeapLocation
    obj-hl = heap-loc (mkHeapRef (next-heap-ref (falloc fs2))) 0

    obj-loc : ValueLocation FS
    obj-loc = AtDynamic obj-hl

    -- ── ROW 6: the env value, stashed at fs1→fs2 and loaded back at fs5.
    -- The only intervening STACK write targets `suc n`, so `n < suc n` keeps
    -- it away; the allocation and `mov-to-input` touch no stack cell.
    cell0v : StoredValue FS
    cell0v = readReg (regs (floc fs1)) Output

    cf-fs5 : current-frame (falloc fs5) ≡ current-frame (falloc fs1)
    cf-fs5 =
      trans (exec-abstract-preserves-frame mov-to-input (floc fs4) (falloc fs4))
     (trans (exec-abstract-preserves-frame (store-at-slot obj-stash) (floc fs3) (falloc fs3))
     (trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc fs2) (falloc fs2))
            (exec-abstract-preserves-frame (store-at-slot cell0-stash) (floc fs1) (falloc fs1))))

    read-cell0-fs2 : SMCore.MemOps.readLoc (floc fs2)
                     (AtStack (current-frame (falloc fs1)) cell0-stash) ≡ just cell0v
    read-cell0-fs2 =
      SMCore.MemOps.writeLoc-read-same-stack (floc fs1) (current-frame (falloc fs1)) cell0-stash cell0v

    read-cell0-fs5 : SMCore.MemOps.readLoc (floc fs5)
                     (AtStack (current-frame (falloc fs1)) cell0-stash) ≡ just cell0v
    read-cell0-fs5 =
      trans (exec-abstract-preserves-stack-slot mov-to-input (floc fs4) (falloc fs4)
               (current-frame (falloc fs1)) cell0-stash nhw-mov-to-input refl)
     (trans (store-at-slot-preserves-below cell0-stash obj-stash (floc fs3) (falloc fs3) (n<1+n _))
     (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc fs2) (falloc fs2)
               (current-frame (falloc fs1)) cell0-stash nhw-instr-alloc-heap refl)
            read-cell0-fs2))

    wf-load-cell0 : InstrWF (floc fs5) (falloc fs5) (load-from-slot cell0-stash)
    wf-load-cell0 =
      cell0v , subst (λ f → SMCore.MemOps.readLoc (floc fs5) (AtStack f cell0-stash) ≡ just cell0v)
                 (sym cf-fs5) read-cell0-fs5

    -- ── ROW 7: the closure pointer must survive the env load.
    rdi-fs5 : sv-as-loc (readReg (regs (floc fs5)) Input1) ≡ just obj-loc
    rdi-fs5 = refl

    input-fs6 : readReg (regs (floc fs6)) Input1 ≡ readReg (regs (floc fs5)) Input1
    input-fs6 = load-slot-preserves-input cell0-stash (floc fs5) (falloc fs5) cell0v
                  (proj₂ wf-load-cell0)

    rdi-fs6 : sv-as-loc (readReg (regs (floc fs6)) Input1) ≡ just obj-loc
    rdi-fs6 = trans (cong sv-as-loc input-fs6) rdi-fs5

    wf-store-ind : InstrWF (floc fs6) (falloc fs6) store-indirect
    wf-store-ind = obj-loc , rdi-fs6

    -- ── ROW 9: …and past the indirect store and the code-address load.
    -- `instr-load-code-addr` writes `Output` and nothing else, so reading
    -- `Input1` through it is definitional.
    input-fs7 : readReg (regs (floc fs7)) Input1 ≡ readReg (regs (floc fs6)) Input1
    input-fs7 = store-ind-preserves-input (floc fs6) (falloc fs6) obj-loc rdi-fs6

    input-fs8 : readReg (regs (floc fs8)) Input1 ≡ readReg (regs (floc fs7)) Input1
    input-fs8 = refl

    rdi-fs8 : sv-as-loc (readReg (regs (floc fs8)) Input1) ≡ just obj-loc
    rdi-fs8 = trans (cong sv-as-loc (trans input-fs8 input-fs7)) rdi-fs6

    wf-store-ind-suc : InstrWF (floc fs8) (falloc fs8) store-indirect-suc
    wf-store-ind-suc = obj-loc , rdi-fs8

    -- ── ROW 10: the CLOSURE pointer, stashed at fs3→fs4 and read at fs9.
    cf-fs9 : current-frame (falloc fs9) ≡ current-frame (falloc fs3)
    cf-fs9 =
      trans (exec-abstract-preserves-frame store-indirect-suc (floc fs8) (falloc fs8))
     (trans (exec-abstract-preserves-frame (instr-load-code-addr code-lbl) (floc fs7) (falloc fs7))
     (trans (exec-abstract-preserves-frame store-indirect (floc fs6) (falloc fs6))
     (trans (exec-abstract-preserves-frame (load-from-slot cell0-stash) (floc fs5) (falloc fs5))
     (trans (exec-abstract-preserves-frame mov-to-input (floc fs4) (falloc fs4))
            (exec-abstract-preserves-frame (store-at-slot obj-stash) (floc fs3) (falloc fs3))))))

    objv : StoredValue FS
    objv = readReg (regs (floc fs3)) Output

    read-obj-fs4 : SMCore.MemOps.readLoc (floc fs4)
                     (AtStack (current-frame (falloc fs3)) obj-stash) ≡ just objv
    read-obj-fs4 =
      SMCore.MemOps.writeLoc-read-same-stack (floc fs3) (current-frame (falloc fs3)) obj-stash objv

    read-obj-fs9 : SMCore.MemOps.readLoc (floc fs9)
                     (AtStack (current-frame (falloc fs3)) obj-stash) ≡ just objv
    read-obj-fs9 =
      trans (store-ind-suc-preserves-slot (floc fs8) (falloc fs8) obj-hl obj-stash rdi-fs8)
     (trans (exec-abstract-preserves-stack-slot (instr-load-code-addr code-lbl) (floc fs7) (falloc fs7)
               (current-frame (falloc fs3)) obj-stash nhw-instr-load-code-addr refl)
     (trans (store-ind-preserves-slot (floc fs6) (falloc fs6) obj-hl obj-stash rdi-fs6)
     (trans (exec-abstract-preserves-stack-slot (load-from-slot cell0-stash) (floc fs5) (falloc fs5)
               (current-frame (falloc fs3)) obj-stash nhw-load-from-slot refl)
     (trans (exec-abstract-preserves-stack-slot mov-to-input (floc fs4) (falloc fs4)
               (current-frame (falloc fs3)) obj-stash nhw-mov-to-input refl)
            read-obj-fs4))))

    wf-load-obj : InstrWF (floc fs9) (falloc fs9) (load-from-slot obj-stash)
    wf-load-obj =
      objv , subst (λ f → SMCore.MemOps.readLoc (floc fs9) (AtStack f obj-stash) ≡ just objv)
                 (sym cf-fs9) read-obj-fs9

    -- ── The ten `halted ≡ false` obligations.
    nh0 : halted (floc fs0) ≡ false
    nh0 = nh
    nh1 : halted (floc fs1) ≡ false
    nh1 = exec-abstract-preserves-halted-WF mov-to-output (floc fs0) (falloc fs0) nh0 tt
    nh2 : halted (floc fs2) ≡ false
    nh2 = exec-abstract-preserves-halted-WF (store-at-slot cell0-stash) (floc fs1) (falloc fs1) nh1 tt
    nh3 : halted (floc fs3) ≡ false
    nh3 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc fs2) (falloc fs2) nh2 tt
    nh4 : halted (floc fs4) ≡ false
    nh4 = exec-abstract-preserves-halted-WF (store-at-slot obj-stash) (floc fs3) (falloc fs3) nh3 tt
    nh5 : halted (floc fs5) ≡ false
    nh5 = exec-abstract-preserves-halted-WF mov-to-input (floc fs4) (falloc fs4) nh4 tt
    nh6 : halted (floc fs6) ≡ false
    nh6 = exec-abstract-preserves-halted-WF (load-from-slot cell0-stash) (floc fs5) (falloc fs5) nh5 wf-load-cell0
    nh7 : halted (floc fs7) ≡ false
    nh7 = exec-abstract-preserves-halted-WF store-indirect (floc fs6) (falloc fs6) nh6 wf-store-ind
    nh8 : halted (floc fs8) ≡ false
    nh8 = exec-abstract-preserves-halted-WF (instr-load-code-addr code-lbl) (floc fs7) (falloc fs7) nh7 tt
    nh9 : halted (floc fs9) ≡ false
    nh9 = exec-abstract-preserves-halted-WF store-indirect-suc (floc fs8) (falloc fs8) nh8 wf-store-ind-suc
    nh10 : halted (floc fs10) ≡ false
    nh10 = exec-abstract-preserves-halted-WF (load-from-slot obj-stash) (floc fs9) (falloc fs9) nh9 wf-load-obj

    run : FlatSteps prog 10 fs0 fs10
    run = (nh0 , span 0 _ refl) ∷ (nh1 , span 1 _ refl) ∷ (nh2 , span 2 _ refl)
        ∷ (nh3 , span 3 _ refl) ∷ (nh4 , span 4 _ refl) ∷ (nh5 , span 5 _ refl)
        ∷ (nh6 , span 6 _ refl) ∷ (nh7 , span 7 _ refl) ∷ (nh8 , span 8 _ refl)
        ∷ (nh9 , span 9 _ refl) ∷ []

