-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.TwoCell.Run
--
-- The TEN-ROW RUN of the two-cell build (`curry`, `in-ν`, `Ana` — D190): a
-- node `[cell 0, code]`, cell 0 the word in `Input1` (D385: a closure's
-- environment word). plan 0.123 B.4 α: the cells are written by `store-at`
-- into the fresh block, so the run is one straight segment, its effect
-- `exec-trace`'s (the two stores in their block, `FlatAlloc.alloc-in`) and its
-- chain `StraightRun.straight-steps`. The facts about the end state are in
-- `TwoCellBuild`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.TwoCell.Run (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (ℓ; LabelId)
open import Once.CCC.Machine.Locations using (ValueLocation; AtDynamic; AtStack)
open import Once.CCC.Machine.SMCore
  using (AllocState; AbstractTrace; mov-to-output; store-at-slot; instr-alloc-heap; mov-to-input; load-from-slot;
         store-at; instr-load-code-addr; LocState; StoredValue; readReg; writeReg; Output; sv-as-loc; Input1;
         SV-Ptr; SV-Code; sucLoc; module LocState; module AllocState; module ExecFinal)
open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames; block-size)
open LocState using (halted; regs)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef)
import Once.CCC.Machine.FlatAlloc as FlatAlloc
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
open import Data.Nat using (z≤n; s≤s)
open import Data.List.Relation.Unary.All using ([]; _∷_)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM


module TwoCellRunC {FS : FrameSemantics} where

  open Core {FS}
  open SMCore.AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-load-from-slot-with-value)
  open SMCore.MemOps {FS} using (writeLoc; writeLoc-halted; writeLoc-regs; writeLoc-preserves-other; writeLoc-read-same-stack)
  open Once.CCC.Machine.SMPrimitives.MemoryOps {FS} using (readLoc-writeLoc-same)
  open FlatEventTrace {FS} using (chain-events-subst)
  module SR = StraightRunAPI {FS}

  two-cell-trace : ℕ → ℕ → AbstractTrace
  two-cell-trace n l =
    mov-to-output ∷ store-at-slot n ∷ instr-alloc-heap 2 ∷ store-at-slot (suc n) ∷
    mov-to-input ∷ load-from-slot n ∷ store-at 0 ∷
    instr-load-code-addr (ℓ o l) ∷ store-at 1 ∷ load-from-slot (suc n) ∷ []

  module TwoCellRun
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (two-cell-trace n l))
    where

    cell0-stash obj-stash : ℕ
    cell0-stash = n
    obj-stash   = suc n

    code-lbl : LabelId
    code-lbl = ℓ o l

    code : StoredValue FS
    code = SV-Code code-lbl

    A₁ = FlatAlloc.alloc-after {FS} 2 alloc
    rd = FlatAlloc.fresh-ref {FS} alloc

    obj-hl : HeapLocation
    obj-hl = heap-loc rd 0

    obj-loc : ValueLocation FS
    obj-loc = AtDynamic obj-hl

    blk : StoredValue FS
    blk = SV-Ptr obj-loc

    cf = current-frame alloc

    -- the rows' states
    t₁ = proj₁ (exec-abstract mov-to-output s alloc)

    -- cell 0's word: what `Input1` held, moved to `Output`
    cell0v : StoredValue FS
    cell0v = readReg (regs t₁) Output

    t₂ = proj₁ (exec-abstract (store-at-slot n) t₁ alloc)
    t₃ = proj₁ (exec-abstract (instr-alloc-heap 2) t₂ alloc)
    t₄ = proj₁ (exec-abstract (store-at-slot (suc n)) t₃ A₁)
    t₅ = proj₁ (exec-abstract mov-to-input t₄ A₁)
    t₆ = record t₅ { regs = writeReg (regs t₅) Output cell0v }
    t₇ = writeLoc t₆ obj-loc cell0v
    t₈ = proj₁ (exec-abstract (instr-load-code-addr code-lbl) t₇ A₁)
    t₉ = writeLoc t₈ (sucLoc obj-loc) code
    t₁₀ = record t₉ { regs = writeReg (regs t₉) Output blk }

    R9 R8 R7 R6 R5 R4 R3 R2 R1 : AbstractTrace
    R1 = load-from-slot (suc n) ∷ []
    R2 = store-at 1 ∷ R1
    R3 = instr-load-code-addr code-lbl ∷ R2
    R4 = store-at 0 ∷ R3
    R5 = load-from-slot n ∷ R4
    R6 = mov-to-input ∷ R5
    R7 = store-at-slot (suc n) ∷ R6
    R8 = instr-alloc-heap 2 ∷ R7
    R9 = store-at-slot n ∷ R8

    h₇ : halted t₇ ≡ false
    h₇ = trans (writeLoc-halted t₆ obj-loc cell0v) nh

    h₉ : halted t₉ ≡ false
    h₉ = trans (writeLoc-halted t₈ (sucLoc obj-loc) code) h₇

    slot-n₅ : SMCore.MemOps.readLoc t₅ (AtStack cf n) ≡ just cell0v
    slot-n₅ =
      trans (writeLoc-preserves-other t₃ (AtStack cf (suc n)) (AtStack cf n) blk
               (λ e → <-irrefl (sym (cong slot-of e)) (n<1+n n)))
            (writeLoc-read-same-stack t₁ cf n cell0v)
      where
        slot-of : ValueLocation FS → ℕ
        slot-of (AtStack _ j) = j
        slot-of (AtDynamic _) = 0

    slot-b₉ : SMCore.MemOps.readLoc t₉ (AtStack cf (suc n)) ≡ just blk
    slot-b₉ =
      trans (writeLoc-preserves-other t₈ (sucLoc obj-loc) (AtStack cf (suc n)) code (λ ()))
     (trans (writeLoc-preserves-other t₆ obj-loc (AtStack cf (suc n)) cell0v (λ ()))
            (writeLoc-read-same-stack t₃ cf (suc n) blk))

    ib0 : InBlk A₁ obj-loc
    ib0 = FlatAlloc.alloc-in {FS} 2 alloc 0 (s≤s z≤n)

    ib1 : InBlk A₁ (sucLoc obj-loc)
    ib1 = FlatAlloc.alloc-in {FS} 2 alloc 1 (s≤s (s≤s z≤n))

    st0 : exec-abstract (store-at 0) t₆ A₁ ≡ (t₇ , A₁)
    st0 = cong (λ b → (ExecFinal.exec-store-in-block {FS} b obj-loc cell0v t₆ , A₁)) ib0

    i1₈ : readReg (regs t₈) Input1 ≡ blk
    i1₈ = cong (λ q → readReg q Input1) (writeLoc-regs t₆ obj-loc cell0v)

    st1 : exec-abstract (store-at 1) t₈ A₁ ≡ (t₉ , A₁)
    st1 = trans (cong (λ v → (ExecFinal.exec-store-at-resolved {FS} (block-size A₁) 1 (sv-as-loc v) code t₈ , A₁)) i1₈)
                (cong (λ b → (ExecFinal.exec-store-in-block {FS} b (sucLoc obj-loc) code t₈ , A₁)) ib1)

    whole : exec-trace (two-cell-trace n l) s alloc ≡ (t₁₀ , A₁)
    whole =
      trans (exec-trace-cons mov-to-output R9 s alloc nh)
     (trans (exec-trace-cons (store-at-slot n) R8 t₁ alloc nh)
     (trans (exec-trace-cons (instr-alloc-heap 2) R7 t₂ alloc nh)
     (trans (exec-trace-cons (store-at-slot (suc n)) R6 t₃ A₁ nh)
     (trans (exec-trace-cons mov-to-input R5 t₄ A₁ nh)
     (trans (exec-trace-cons (load-from-slot n) R4 t₅ A₁ nh)
     (trans (cong (λ mv → exec-trace R4 (proj₁ (exec-load-from-slot-with-value mv t₅ A₁))
                                        (proj₂ (exec-load-from-slot-with-value mv t₅ A₁))) slot-n₅)
     (trans (exec-trace-cons (store-at 0) R3 t₆ A₁ nh)
     (trans (cong (λ r → exec-trace R3 (proj₁ r) (proj₂ r)) st0)
     (trans (exec-trace-cons (instr-load-code-addr code-lbl) R2 t₇ A₁ h₇)
     (trans (exec-trace-cons (store-at 1) R1 t₈ A₁ h₇)
     (trans (cong (λ r → exec-trace R1 (proj₁ r) (proj₂ r)) st1)
     (trans (exec-trace-cons (load-from-slot (suc n)) [] t₉ A₁ h₉)
            (cong (λ mv → exec-load-from-slot-with-value mv t₉ A₁) slot-b₉)))))))))))))

    -- ── THE CHAIN
    fs0 fs10 : FlatState
    fs0  = entry-flat base s alloc cl rs
    fs10 = record fs0 { floc = t₁₀ ; falloc = A₁ ; fpc = 10 + base }

    nh10 : halted (floc fs10) ≡ false
    nh10 = h₉

    he : halted (proj₁ (exec-trace (two-cell-trace n l) s alloc)) ≡ false
    he = trans (cong (λ r → halted (proj₁ r)) whole) h₉

    sts : All StraightStep (two-cell-trace n l)
    sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
          (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []

    evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) (two-cell-trace n l)
    evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
          (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []

    run₀ = SR.straight-steps {prog} (two-cell-trace n l) fs0 sts span nh he

    eq : SR.after (two-cell-trace n l) fs0 ≡ fs10
    eq = cong (λ r → record fs0 { floc = proj₁ r ; falloc = proj₂ r ; fpc = 10 + base }) whole

    run : FlatSteps prog 10 fs0 fs10
    run = subst (FlatSteps prog 10 fs0) eq run₀

    silent : chain-events run ≡ []
    silent = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} (two-cell-trace n l) fs0 sts span nh he evs)
