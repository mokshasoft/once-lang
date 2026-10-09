-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Pair.Place
--
-- D207: the pair's PLACEMENT — the nine-row tail that builds the pair node and
-- where its result lands. Split from `Pair` for the per-module check cap.
------------------------------------------------------------------------


open import Once.CanonicalName using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Pair.Place (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore using (AllocState; next-slot; next-heap-ref; current-frame; readReg; regs; Output; load-from-slot; store-at-slot; instr-alloc-heap; mov-to-input; store-indirect; store-indirect-suc; LocState; sucLoc; StoredValue; SV-Ptr; writeReg-same; sv-as-loc; Input1)
open import Once.IRTy using (IRTy; _*_)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module PairPlaceC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

  ----------------------------------------------------------------------
  -- THE RESULT PLACE (cluster PairPlace).
  --
  -- The tail allocates a two-cell heap node and writes `f`'s result into
  -- cell 0 and `g`'s into cell 1. So `⟨ f , g ⟩`'s residence is `Heap`, its
  -- continuation allocator is the one the tail leaves, and its witness is
  -- `valid-pair-wf` over two `CellAt`s.
  --
  -- PARAMETERISED, not computed: the cluster takes the two settle states and
  -- the two `ResultPlace`s the induction hypotheses hand over, plus exactly
  -- the allocator facts `ValueRealized` now exports about each run
  -- (`frame-pres`, slot stability, heap monotonicity) and the two cross-run
  -- memory facts `g`'s run owes (`mem-F→G`, from its `stack-pres`/`heap-pres`,
  -- and `fst-cell-gs`, its `stack-pres` at `fst-stash`).
  --
  -- NOTE on the frontier the tail is measured against. `PairTail` instantiates
  -- `NineStepPres` at the CALLER's `alloc`, which forces
  -- `next-heap-ref (falloc gs) ≡ next-heap-ref alloc` — false as soon as `f` or
  -- `g` allocates (`f = inl` suffices). This module instantiates it at
  -- `record (falloc gs) { next-slot = snd-stash }` instead, where both of
  -- `NineStepPres`'s premises are `refl`, and weakens the caller's
  -- `BeforeFrontier`s into it with `frontier-monotone`. The nine states are the
  -- same nine either way, so nothing downstream has to choose.
  ----------------------------------------------------------------------
  module PairPlace
    {B C : IRTy}
    (n : ℕ)
    (alloc : AllocState {FS})
    (n≤ : next-slot alloc ≤ n)
    -- the state `f` settled in, and the state `g` settled in (= the tail's
    -- start state)
    (fsF gs : FlatState)
    -- what the two runs did to the allocator: `ValueRealized.frame-pres`
    -- (D210), `flat-run-keeps-next-slot`, and heap monotonicity
    (cf-fsF : current-frame (falloc fsF) ≡ current-frame alloc)
    (cf-gs  : current-frame (falloc gs)  ≡ current-frame alloc)
    (ns-fsF : next-slot (falloc fsF) ≡ next-slot alloc)
    (ns-gs  : next-slot (falloc gs)  ≡ next-slot alloc)
    (hr-gs  : next-heap-ref (falloc fsF) ≤ next-heap-ref (falloc gs))
    -- the two component values and the residences the IHs realized them at
    (vB : ⟦ B ⟧) (vC : ⟦ C ⟧)
    (mf mg : AllocMode) (caf cag : AllocState {FS})
    (placeF : ResultPlace B mf (falloc fsF) caf vB (floc fsF))
    (placeG : ResultPlace C mg (falloc gs)  cag vC (floc gs))
    -- what the two mid rows and `g`'s run leave alone …
    (mem-F→G : ∀ (loc : ValueLocation FS)
             → BeforeFrontier (falloc fsF) loc
             → SMCore.MemOps.readLoc (floc gs) loc ≡ SMCore.MemOps.readLoc (floc fsF) loc)
    -- … and that `f`'s result is still in its stash when `g` is done
    (fst-cell-gs : SMCore.MemOps.readLoc (floc gs)
                     (AtStack (current-frame alloc) (suc n))
                 ≡ just (readReg (regs (floc fsF)) Output))
    where

    fst-stash snd-stash pair-stash : ℕ
    fst-stash  = suc n
    snd-stash  = suc (suc n)
    pair-stash = suc (suc (suc n))

    -- The frontier the tail's own preservation is measured against: `g`'s
    -- allocator with the stash bound. Both of `NineStepPres`'s premises are
    -- `refl` here, which is the point.
    a' : AllocState {FS}
    a' = record (falloc gs) { next-slot = snd-stash }

    -- the literal arguments `WithG` names the tail at (see there)
    module NSP = NineStepPres (suc (suc n))
                   (load-from-slot (suc n))        -- i6
                   (load-from-slot (suc (suc n)))  -- i8
                   gs (floc gs) a' refl refl

    u2 u3 u4 u5 u6 u7 u8 u9 u10 : FlatState
    u2 = NSP.u2 ; u3 = NSP.u3 ; u4 = NSP.u4 ; u5 = NSP.u5 ; u6 = NSP.u6
    u7 = NSP.u7 ; u8 = NSP.u8 ; u9 = NSP.u9 ; u10 = NSP.u10

    hl : HeapLocation
    hl = NSP.hl

    pair-loc : ValueLocation FS
    pair-loc = AtDynamic hl

    FR : Once.CCC.FrameSemantics.FrameSemantics.Frame FS
    FR = current-frame alloc

    -- ── the frame, row by row ────────────────────────────────────────────
    cf-u2 : current-frame (falloc u2) ≡ current-frame alloc
    cf-u2  = trans (exec-abstract-preserves-frame (store-at-slot snd-stash) (floc gs) (falloc gs)) cf-gs
    cf-u3 : current-frame (falloc u3) ≡ current-frame alloc
    cf-u3  = trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc u2) (falloc u2)) cf-u2
    cf-u4 : current-frame (falloc u4) ≡ current-frame alloc
    cf-u4  = trans (exec-abstract-preserves-frame (store-at-slot pair-stash) (floc u3) (falloc u3)) cf-u3
    cf-u5 : current-frame (falloc u5) ≡ current-frame alloc
    cf-u5  = trans (exec-abstract-preserves-frame mov-to-input (floc u4) (falloc u4)) cf-u4
    cf-u6 : current-frame (falloc u6) ≡ current-frame alloc
    cf-u6  = trans (exec-abstract-preserves-frame (load-from-slot fst-stash) (floc u5) (falloc u5)) cf-u5
    cf-u7 : current-frame (falloc u7) ≡ current-frame alloc
    cf-u7  = trans (exec-abstract-preserves-frame store-indirect (floc u6) (falloc u6)) cf-u6
    cf-u8 : current-frame (falloc u8) ≡ current-frame alloc
    cf-u8  = trans (exec-abstract-preserves-frame (load-from-slot snd-stash) (floc u7) (falloc u7)) cf-u7
    cf-u9 : current-frame (falloc u9) ≡ current-frame alloc
    cf-u9  = trans (exec-abstract-preserves-frame store-indirect-suc (floc u8) (falloc u8)) cf-u8
    cf-u10 : current-frame (falloc u10) ≡ current-frame alloc
    cf-u10 = trans (exec-abstract-preserves-frame (load-from-slot pair-stash) (floc u9) (falloc u9)) cf-u9

    -- A stash write above a slot, read at the CALLER's frame rather than the
    -- running allocator's.
    slot-below-at : ∀ (j k : ℕ) (st : LocState FS) (aa : AllocState {FS})
                  → current-frame aa ≡ current-frame alloc → j < k
                  → SMCore.MemOps.readLoc (proj₁ (exec-abstract (store-at-slot k) st aa)) (AtStack FR j)
                    ≡ SMCore.MemOps.readLoc st (AtStack FR j)
    slot-below-at j k st aa cf j<k =
      subst (λ fr → SMCore.MemOps.readLoc (proj₁ (exec-abstract (store-at-slot k) st aa)) (AtStack fr j)
                    ≡ SMCore.MemOps.readLoc st (AtStack fr j))
            cf (store-at-slot-preserves-below j k st aa j<k)

    -- ── the heap frontier ────────────────────────────────────────────────
    heapref-u2 : next-heap-ref (falloc u2) ≡ next-heap-ref (falloc gs)
    heapref-u2 = exec-abstract-preserves-heap-ref (store-at-slot snd-stash) (floc gs) (falloc gs) tt

    heapref-u10 : next-heap-ref (falloc u10) ≡ suc (next-heap-ref (falloc u2))
    heapref-u10 =
      trans (exec-abstract-preserves-heap-ref (load-from-slot pair-stash) (floc u9) (falloc u9) tt)
     (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc u8) (falloc u8) tt)
     (trans (exec-abstract-preserves-heap-ref (load-from-slot snd-stash) (floc u7) (falloc u7) tt)
     (trans (exec-abstract-preserves-heap-ref store-indirect (floc u6) (falloc u6) tt)
     (trans (exec-abstract-preserves-heap-ref (load-from-slot fst-stash) (floc u5) (falloc u5) tt)
     (trans (exec-abstract-preserves-heap-ref mov-to-input (floc u4) (falloc u4) tt)
            (exec-abstract-preserves-heap-ref (store-at-slot pair-stash) (floc u3) (falloc u3) tt))))))

    before : BeforeFrontier (falloc u10) pair-loc
    before = BeforeFrontier.heap-before
               (subst (λ m → next-heap-ref (falloc u2) < m) (sym heapref-u10) (n<1+n _))

    before-suc : BeforeFrontier (falloc u10) (sucLoc pair-loc)
    before-suc = BeforeFrontier.heap-before
                   (subst (λ m → next-heap-ref (falloc u2) < m) (sym heapref-u10) (n<1+n _))

    gs≤u10 : next-heap-ref (falloc gs) ≤ next-heap-ref (falloc u10)
    gs≤u10 =
      subst (λ m → next-heap-ref (falloc gs) ≤ m) (sym heapref-u10)
        (subst (λ r → next-heap-ref (falloc gs) ≤ suc r) (sym heapref-u2) (n≤1+n _))

    -- ── the slot frontier ────────────────────────────────────────────────
    nextslot-u10 : next-slot (falloc u10) ≡ next-slot (falloc gs)
    nextslot-u10 =
      trans (exec-abstract-preserves-next-slot (load-from-slot pair-stash) (floc u9) (falloc u9) tt)
     (trans (exec-abstract-preserves-next-slot store-indirect-suc (floc u8) (falloc u8) tt)
     (trans (exec-abstract-preserves-next-slot (load-from-slot snd-stash) (floc u7) (falloc u7) tt)
     (trans (exec-abstract-preserves-next-slot store-indirect (floc u6) (falloc u6) tt)
     (trans (exec-abstract-preserves-next-slot (load-from-slot fst-stash) (floc u5) (falloc u5) tt)
     (trans (exec-abstract-preserves-next-slot mov-to-input (floc u4) (falloc u4) tt)
     (trans (exec-abstract-preserves-next-slot (store-at-slot pair-stash) (floc u3) (falloc u3) tt)
     (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc u2) (falloc u2) tt)
            (exec-abstract-preserves-next-slot (store-at-slot snd-stash) (floc gs) (falloc gs) tt))))))))

    -- ── the four conditional witnesses, in dependency order ──────────────
    fv gv pv : StoredValue FS
    fv = readReg (regs (floc fsF)) Output   -- f's result, in its stash
    gv = readReg (regs (floc gs))  Output   -- g's result, stashed by row 2
    pv = readReg (regs (floc u3))  Output   -- the node pointer, stashed by row 4

    -- Row 3 hands out the block; rows 4-5 carry the pointer into `Input1`.
    out-u3 : pv ≡ SV-Ptr pair-loc
    out-u3 = writeReg-same (regs (floc u2)) Output (SV-Ptr (AtDynamic hl))

    out-u4 : readReg (regs (floc u4)) Output ≡ SV-Ptr pair-loc
    out-u4 =
      trans (cong (λ r → readReg r Output)
                  (SMCore.MemOps.writeLoc-regs (floc u3)
                     (AtStack (current-frame (falloc u3)) pair-stash) pv))
            out-u3

    rdi-u5 : sv-as-loc (readReg (regs (floc u5)) Input1) ≡ just pair-loc
    rdi-u5 =
      trans (cong sv-as-loc
                  (writeReg-same (regs (floc u4)) Input1 (readReg (regs (floc u4)) Output)))
            (cong sv-as-loc out-u4)

    -- Row 6 reads `fst-stash`. What is there is `f`'s result: rows 2-5 write
    -- `snd-stash`, the heap, `pair-stash` and a register.
    fst-u5 : SMCore.MemOps.readLoc (floc u5) (AtStack FR fst-stash) ≡ just fv
    fst-u5 =
      trans (exec-abstract-preserves-stack-slot mov-to-input (floc u4) (falloc u4)
               FR fst-stash nhw-mov-to-input refl)
     (trans (slot-below-at fst-stash pair-stash (floc u3) (falloc u3) cf-u3 (n≤1+n _))
     (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc u2) (falloc u2)
               FR fst-stash nhw-instr-alloc-heap refl)
     (trans (slot-below-at fst-stash snd-stash (floc gs) (falloc gs) cf-gs ≤-refl)
            fst-cell-gs)))

    wf-load-fst : InstrWF (floc u5) (falloc u5) (load-from-slot fst-stash)
    wf-load-fst =
      fv , subst (λ fr → SMCore.MemOps.readLoc (floc u5) (AtStack fr fst-stash) ≡ just fv)
                 (sym cf-u5) fst-u5

    rdi-u6 : sv-as-loc (readReg (regs (floc u6)) Input1) ≡ just pair-loc
    rdi-u6 =
      trans (cong sv-as-loc
              (load-slot-preserves-input fst-stash (floc u5) (falloc u5) fv (proj₂ wf-load-fst)))
            rdi-u5

    out-u6 : readReg (regs (floc u6)) Output ≡ fv
    out-u6 = load-slot-result fst-stash (floc u5) (falloc u5) fv (proj₂ wf-load-fst)

    -- CELL 0, written by `store-indirect` at row 7.
    cell0-u7 : SMCore.MemOps.readLoc (floc u7) pair-loc ≡ just fv
    cell0-u7 = trans (store-ind-result (floc u6) (falloc u6) hl rdi-u6)
                     (cong just out-u6)

    -- Row 8 reads `snd-stash`, which row 2 wrote with `g`'s result.
    snd-u2 : SMCore.MemOps.readLoc (floc u2) (AtStack FR snd-stash) ≡ just gv
    snd-u2 =
      subst (λ fr → SMCore.MemOps.readLoc (floc u2) (AtStack fr snd-stash) ≡ just gv)
            cf-gs
            (SMCore.MemOps.writeLoc-read-same-stack (floc gs) (current-frame (falloc gs)) snd-stash gv)

    snd-u7 : SMCore.MemOps.readLoc (floc u7) (AtStack FR snd-stash) ≡ just gv
    snd-u7 =
      trans (store-ind-preserves-slot (floc u6) (falloc u6) hl snd-stash rdi-u6)
     (trans (exec-abstract-preserves-stack-slot (load-from-slot fst-stash) (floc u5) (falloc u5)
               FR snd-stash nhw-load-from-slot refl)
     (trans (exec-abstract-preserves-stack-slot mov-to-input (floc u4) (falloc u4)
               FR snd-stash nhw-mov-to-input refl)
     (trans (slot-below-at snd-stash pair-stash (floc u3) (falloc u3) cf-u3 ≤-refl)
     (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc u2) (falloc u2)
               FR snd-stash nhw-instr-alloc-heap refl)
            snd-u2))))

    wf-load-snd : InstrWF (floc u7) (falloc u7) (load-from-slot snd-stash)
    wf-load-snd =
      gv , subst (λ fr → SMCore.MemOps.readLoc (floc u7) (AtStack fr snd-stash) ≡ just gv)
                 (sym cf-u7) snd-u7

    rdi-u7 : sv-as-loc (readReg (regs (floc u7)) Input1) ≡ just pair-loc
    rdi-u7 =
      trans (cong sv-as-loc (store-ind-preserves-input (floc u6) (falloc u6) pair-loc rdi-u6))
            rdi-u6

    rdi-u8 : sv-as-loc (readReg (regs (floc u8)) Input1) ≡ just pair-loc
    rdi-u8 =
      trans (cong sv-as-loc
              (load-slot-preserves-input snd-stash (floc u7) (falloc u7) gv (proj₂ wf-load-snd)))
            rdi-u7

    out-u8 : readReg (regs (floc u8)) Output ≡ gv
    out-u8 = load-slot-result snd-stash (floc u7) (falloc u7) gv (proj₂ wf-load-snd)

    -- CELL 1, written by `store-indirect-suc` at row 9.
    cell1-u9 : SMCore.MemOps.readLoc (floc u9) (sucLoc pair-loc) ≡ just gv
    cell1-u9 = trans (store-ind-suc-result (floc u8) (falloc u8) hl rdi-u8)
                     (cong just out-u8)

    -- …and both cells carried to the end: the only writes left are the OTHER
    -- cell of the same block and two register-only loads.
    cell0-u10 : SMCore.MemOps.readLoc (floc u10) pair-loc ≡ just fv
    cell0-u10 =
      trans (heap-untouched (load-from-slot pair-stash) (floc u9) (falloc u9) hl nhw-load-from-slot)
     (trans (store-ind-suc-preserves-heap (floc u8) (falloc u8) hl hl rdi-u8 (sucHL-≢ hl))
     (trans (heap-untouched (load-from-slot snd-stash) (floc u7) (falloc u7) hl nhw-load-from-slot)
            cell0-u7))

    cell1-u10 : SMCore.MemOps.readLoc (floc u10) (sucLoc pair-loc) ≡ just gv
    cell1-u10 =
      trans (heap-untouched (load-from-slot pair-stash) (floc u9) (falloc u9)
               (sucHL hl) nhw-load-from-slot)
            cell1-u9

    -- THE RESULT POINTER: row 10 loads the stashed node pointer.
    pair-u4 : SMCore.MemOps.readLoc (floc u4) (AtStack FR pair-stash) ≡ just pv
    pair-u4 =
      subst (λ fr → SMCore.MemOps.readLoc (floc u4) (AtStack fr pair-stash) ≡ just pv)
            cf-u3
            (SMCore.MemOps.writeLoc-read-same-stack (floc u3) (current-frame (falloc u3)) pair-stash pv)

    pair-u9 : SMCore.MemOps.readLoc (floc u9) (AtStack FR pair-stash) ≡ just pv
    pair-u9 =
      trans (store-ind-suc-preserves-slot (floc u8) (falloc u8) hl pair-stash rdi-u8)
     (trans (exec-abstract-preserves-stack-slot (load-from-slot snd-stash) (floc u7) (falloc u7)
               FR pair-stash nhw-load-from-slot refl)
     (trans (store-ind-preserves-slot (floc u6) (falloc u6) hl pair-stash rdi-u6)
     (trans (exec-abstract-preserves-stack-slot (load-from-slot fst-stash) (floc u5) (falloc u5)
               FR pair-stash nhw-load-from-slot refl)
     (trans (exec-abstract-preserves-stack-slot mov-to-input (floc u4) (falloc u4)
               FR pair-stash nhw-mov-to-input refl)
            pair-u4))))

    wf-load-pair : InstrWF (floc u9) (falloc u9) (load-from-slot pair-stash)
    wf-load-pair =
      pv , subst (λ fr → SMCore.MemOps.readLoc (floc u9) (AtStack fr pair-stash) ≡ just pv)
                 (sym cf-u9) pair-u9

    out-u10 : readReg (regs (floc u10)) Output ≡ SV-Ptr pair-loc
    out-u10 = trans (load-slot-result pair-stash (floc u9) (falloc u9) pv (proj₂ wf-load-pair))
                    out-u3

    ------------------------------------------------------------------------
    -- THE TRANSPORTS. Each component's validity is stated at its OWN settle
    -- state; the node's is stated at the tail's. Three moves: memory (the
    -- tail's own preservation, composed with what `g`'s run preserves),
    -- frontier (the allocation advanced it), and the `BeforeFrontier`s.
    ------------------------------------------------------------------------
    tail-pres : ∀ (loc : ValueLocation FS) → BeforeFrontier a' loc
              → SMCore.MemOps.readLoc (floc u10) loc ≡ SMCore.MemOps.readLoc (floc gs) loc
    tail-pres = NSP.mem-pres-from nhw-load-from-slot refl nhw-load-from-slot refl
                  ≤-refl rdi-u6 rdi-u8

    bf-weaken-F : ∀ (loc : ValueLocation FS)
                → BeforeFrontier (falloc fsF) loc → BeforeFrontier a' loc
    bf-weaken-F =
      frontier-monotone (falloc fsF) a' (trans cf-fsF (sym cf-gs))
        (≤-trans (≤-reflexive ns-fsF) (≤-trans n≤ (≤-trans (n≤1+n n) (n≤1+n (suc n)))))
        hr-gs

    bf-weaken-G : ∀ (loc : ValueLocation FS)
                → BeforeFrontier (falloc gs) loc → BeforeFrontier a' loc
    bf-weaken-G =
      frontier-monotone (falloc gs) a' refl
        (≤-trans (≤-reflexive ns-gs) (≤-trans n≤ (≤-trans (n≤1+n n) (n≤1+n (suc n)))))
        ≤-refl

    mem-F→u10 : ∀ (loc : ValueLocation FS) → BeforeFrontier (falloc fsF) loc
              → SMCore.MemOps.readLoc (floc u10) loc ≡ SMCore.MemOps.readLoc (floc fsF) loc
    mem-F→u10 loc bf = trans (tail-pres loc (bf-weaken-F loc bf)) (mem-F→G loc bf)

    mem-G→u10 : ∀ (loc : ValueLocation FS) → BeforeFrontier (falloc gs) loc
              → SMCore.MemOps.readLoc (floc u10) loc ≡ SMCore.MemOps.readLoc (floc gs) loc
    mem-G→u10 loc bf = tail-pres loc (bf-weaken-G loc bf)

    transF : ∀ {m'} {E : IRTy} (w : ⟦ E ⟧) (lc : ValueLocation FS)
           → BeforeFrontier (falloc fsF) lc
           → ValidAtWF m' (falloc fsF) {E} w lc (floc fsF)
           → ValidAtWF m' (falloc u10) {E} w lc (floc u10)
    transF w lc bf vd =
      validityWF-frontier-advance w lc (floc u10)
        (trans cf-u10 (sym cf-fsF))
        (≤-reflexive (trans ns-fsF (sym (trans nextslot-u10 ns-gs))))
        (≤-trans hr-gs gs≤u10)
        (validityWF-mem-preserved w lc (floc fsF) (floc u10) bf mem-F→u10 vd)

    transG : ∀ {m'} {E : IRTy} (w : ⟦ E ⟧) (lc : ValueLocation FS)
           → BeforeFrontier (falloc gs) lc
           → ValidAtWF m' (falloc gs) {E} w lc (floc gs)
           → ValidAtWF m' (falloc u10) {E} w lc (floc u10)
    transG w lc bf vd =
      validityWF-frontier-advance w lc (floc u10)
        (trans cf-u10 (sym cf-gs))
        (≤-reflexive (sym nextslot-u10))
        gs≤u10
        (validityWF-mem-preserved w lc (floc gs) (floc u10) bf mem-G→u10 vd)

    bfF-u10 : ∀ (lc : ValueLocation FS)
            → BeforeFrontier (falloc fsF) lc → BeforeFrontier (falloc u10) lc
    bfF-u10 =
      frontier-monotone (falloc fsF) (falloc u10) (trans cf-fsF (sym cf-u10))
        (≤-reflexive (trans ns-fsF (sym (trans nextslot-u10 ns-gs))))
        (≤-trans hr-gs gs≤u10)

    bfG-u10 : ∀ (lc : ValueLocation FS)
            → BeforeFrontier (falloc gs) lc → BeforeFrontier (falloc u10) lc
    bfG-u10 =
      frontier-monotone (falloc gs) (falloc u10) (trans cf-gs (sym cf-u10))
        (≤-reflexive (sym nextslot-u10)) gs≤u10

    ------------------------------------------------------------------------
    -- A `ResultPlace` IS a `CellAt` once the cell holds what `Output` held.
    -- Three residences, three cell shapes (D187): a pointer is `cell-ptr` with
    -- the component's validity carried across; a register literal and a `Unit`
    -- are `cell-inline`, which needs no validity at all.
    --
    -- Written as a helper over the transports rather than twice, because the
    -- two components differ ONLY in which state they came from. (`with` is
    -- unavailable here for the same reason it is in `Sum`: the place is a
    -- module parameter, not a pattern.)
    ------------------------------------------------------------------------
    cell-of : ∀ {D : IRTy} {v : ⟦ D ⟧} {m : AllocMode} {aS ca : AllocState {FS}}
                (src : LocState FS) (cl : ValueLocation FS)
              → SMCore.MemOps.readLoc (floc u10) cl ≡ just (readReg (regs src) Output)
              → (∀ {m'} {E : IRTy} (w : ⟦ E ⟧) (lc : ValueLocation FS)
                 → BeforeFrontier aS lc
                 → ValidAtWF m' aS {E} w lc src
                 → ValidAtWF m' (falloc u10) {E} w lc (floc u10))
              → (∀ (lc : ValueLocation FS) → BeforeFrontier aS lc
                 → BeforeFrontier (falloc u10) lc)
              → ResultPlace D m aS ca v src
              → CellAt (falloc u10) D v cl (floc u10)
    cell-of src cl rd tr bfw (at-loc loc valid bef rax _ _) =
      cell-ptr (trans rd (cong just rax)) (bfw loc bef) (tr _ loc bef valid)
    cell-of src cl rd tr bfw (at-reg fit rax) =
      cell-inline (rep-prim fit) (trans rd (cong just rax))
    cell-of src cl rd tr bfw unit-result =
      cell-inline (rep-unit refl (readReg (regs src) Output)) rd

    cellF : CellAt (falloc u10) B vB pair-loc (floc u10)
    cellF = cell-of (floc fsF) pair-loc cell0-u10 transF bfF-u10 placeF

    cellG : CellAt (falloc u10) C vC (sucLoc pair-loc) (floc u10)
    cellG = cell-of (floc gs) (sucLoc pair-loc) cell1-u10 transG bfG-u10 placeG

    ------------------------------------------------------------------------
    -- THE THREE FIELDS. `out-mode` is `Heap` because the node is a heap block;
    -- `cont-alloc` is the allocator the tail leaves, so the continuation's
    -- copy of the witness is the SAME witness (`inl`/`inr` do this too).
    ------------------------------------------------------------------------
    out-mode : AllocMode
    out-mode = Heap

    cont-alloc : AllocState {FS}
    cont-alloc = falloc u10

    validity : ValidAtWF Heap (falloc u10) {B * C} (vB , vC) pair-loc (floc u10)
    validity = valid-pair-wf tt before-suc cellF cellG

    place : ResultPlace (B * C) Heap (falloc u10) (falloc u10) (vB , vC) (floc u10)
    place = at-loc pair-loc validity before out-u10 validity before


  ----------------------------------------------------------------------
  -- THE PRESERVATION QUARTET (D206 / D208 / D210) for `⟨ f , g ⟩`.
  --
  -- `stack-pres`, `heap-pres`, `frame-pres` and `bf-mono` over the FIVE
  -- segments the clause runs:
  --
  --   prologue (2 rows)  ·  f's run  ·  mid (2 rows)  ·  g's run  ·  tail (9)
  --
  -- THE POINT THAT HAD TO BE CHECKED FIRST, and it HOLDS: the prologue writes
  -- slot `backup = n` and the mid rows write slot `fst-stash = suc n`, both AT
  -- OR ABOVE the fragment's own frontier `n`. The claim is only about what is
  -- STRICTLY BELOW `n` — `BeforeFrontier`'s `stack-before` constructor is
  -- `k < next-slot alloc`, and the record here has `next-slot := n` — so
  -- `store-slot-preserves-before`'s premise `next-slot alloc ≤ k` reads `n ≤ n`
  -- for the prologue's write and `n ≤ suc n` for the mid's. Both are immediate;
  -- neither write is visible. (`stack-ancestor` and `heap-before` locations are
  -- missed by a stack write of ANY index, which is that lemma's other two
  -- clauses.) So there is no blocker here.
  --
  -- WHERE THE TAIL IS MEASURED FROM — and this is a correction to `PairTail`.
  -- `PairTail` instantiates `NineStepPres` at the CALLER's `alloc`, which
  -- forces the premise `next-heap-ref (falloc gs) ≡ next-heap-ref alloc`: "`g`
  -- allocated nothing". That is false for a general `g` (`⟨ f , inl ⟩`
  -- allocates), so `PairTail.tail-mem-pres` cannot be instantiated in the real
  -- clause. The fix costs nothing: instantiate the nine at `g`'s OWN allocator
  -- (`tail-alloc` below), where the two premises are `refl`, and carry the
  -- caller's window over to that allocator with the two induction hypotheses'
  -- `bf-mono` first. `PairTail` is left untouched.
  ----------------------------------------------------------------------

