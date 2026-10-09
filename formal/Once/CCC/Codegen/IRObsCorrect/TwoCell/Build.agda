-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.TwoCell.Build
--
-- The FACTS about the two-cell build's states (`TwoCellRun`): what it
-- reads back, its frontier and what it leaves alone.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.TwoCell.Build (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot)
open import Once.CCC.Machine.Locations using (AtDynamic; ValueLocation)
open import Once.CCC.Machine.SMCore using (AllocState; next-slot; next-heap-ref)
open import Once.Memory.HeapAddress using (sucHL)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.ValueDomain as ValueDomain
import Once.Denotation.TraceMonad as TM

open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Run o tbl

module TwoCellBuildC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open TwoCellRunC {FS}

  module TwoCellBuild
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (two-cell-trace n l))
    where
    open TwoCellRun n l prog base s alloc cl n≤ nh span

    -- ── The frontier: the allocation hands out `next-heap-ref (falloc fs2)`
    -- and moves past it, so the record is BEFORE the frontier it leaves.
    heapref-fs10 : next-heap-ref (falloc fs10) ≡ suc (next-heap-ref (falloc fs2))
    heapref-fs10 =
      trans (exec-abstract-preserves-heap-ref (load-from-slot obj-stash) (floc fs9) (falloc fs9) tt)
     (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc fs8) (falloc fs8) tt)
     (trans (exec-abstract-preserves-heap-ref (instr-load-code-addr code-lbl) (floc fs7) (falloc fs7) tt)
     (trans (exec-abstract-preserves-heap-ref store-indirect (floc fs6) (falloc fs6) tt)
     (trans (exec-abstract-preserves-heap-ref (load-from-slot cell0-stash) (floc fs5) (falloc fs5) tt)
     (trans (exec-abstract-preserves-heap-ref mov-to-input (floc fs4) (falloc fs4) tt)
            (exec-abstract-preserves-heap-ref (store-at-slot obj-stash) (floc fs3) (falloc fs3) tt))))))

    before : BeforeFrontier (falloc fs10) obj-loc
    before = BeforeFrontier.heap-before
               (subst (λ m → next-heap-ref (falloc fs2) < m) (sym heapref-fs10) (n<1+n _))

    before-suc : BeforeFrontier (falloc fs10) (sucLoc obj-loc)
    before-suc = BeforeFrontier.heap-before
                   (subst (λ m → next-heap-ref (falloc fs2) < m) (sym heapref-fs10) (n<1+n _))

    -- ── THE ENV CELL, written by `store-indirect` at fs6→fs7 and carried to
    -- fs10 past the code-address load (registers only) and the second heap
    -- write (a DIFFERENT cell).
    cell0out-fs6 : readReg (regs (floc fs6)) Output ≡ cell0v
    cell0out-fs6 = load-slot-result cell0-stash (floc fs5) (falloc fs5) cell0v (proj₂ wf-load-cell0)

    cell0-fs7 : MemOps.readLoc (floc fs7) obj-loc ≡ just cell0v
    cell0-fs7 = trans (store-ind-result (floc fs6) (falloc fs6) obj-hl rdi-fs6)
                    (cong just cell0out-fs6)

    cell0-fs10 : MemOps.readLoc (floc fs10) obj-loc ≡ just cell0v
    cell0-fs10 =
      trans (heap-untouched (load-from-slot obj-stash) (floc fs9) (falloc fs9)
               obj-hl nhw-load-from-slot)
     (trans (store-ind-suc-preserves-heap (floc fs8) (falloc fs8) obj-hl obj-hl
               rdi-fs8 (sucHL-≢ obj-hl))
     (trans (heap-untouched (instr-load-code-addr code-lbl) (floc fs7) (falloc fs7)
               obj-hl nhw-instr-load-code-addr)
            cell0-fs7))

    -- ── THE CODE CELL, written by `store-indirect-suc` at fs8→fs9.
    codeout-fs8 : readReg (regs (floc fs8)) Output ≡ SV-Code code-lbl
    codeout-fs8 = writeReg-same (regs (floc fs7)) Output (SV-Code code-lbl)

    code-fs10 : MemOps.readLoc (floc fs10) (sucLoc obj-loc) ≡ just (SV-Code code-lbl)
    code-fs10 =
      trans (heap-untouched (load-from-slot obj-stash) (floc fs9) (falloc fs9)
               (sucHL obj-hl) nhw-load-from-slot)
     (trans (store-ind-suc-result (floc fs8) (falloc fs8) obj-hl rdi-fs8)
            (cong just codeout-fs8))

    -- ── THE RESULT POINTER.
    cv≡ptr : objv ≡ SV-Ptr obj-loc
    cv≡ptr = writeReg-same (regs (floc fs2)) Output (SV-Ptr (AtDynamic obj-hl))

    out-eq : readReg (regs (floc fs10)) Output ≡ SV-Ptr obj-loc
    out-eq = trans (load-slot-result obj-stash (floc fs9) (falloc fs9) objv
                      (proj₂ wf-load-obj)) cv≡ptr

    cf-fs10 : current-frame (falloc fs10) ≡ current-frame alloc
    cf-fs10 =
      trans (exec-abstract-preserves-frame (load-from-slot obj-stash) (floc fs9) (falloc fs9))
     (trans cf-fs9
     (trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc fs2) (falloc fs2))
     (trans (exec-abstract-preserves-frame (store-at-slot cell0-stash) (floc fs1) (falloc fs1))
            (exec-abstract-preserves-frame mov-to-output (floc fs0) (falloc fs0)))))

    nextslot-fs10 : next-slot (falloc fs10) ≡ next-slot alloc
    nextslot-fs10 =
      trans (exec-abstract-preserves-next-slot (load-from-slot obj-stash) (floc fs9) (falloc fs9) tt)
     (trans (exec-abstract-preserves-next-slot store-indirect-suc (floc fs8) (falloc fs8) tt)
     (trans (exec-abstract-preserves-next-slot (instr-load-code-addr code-lbl) (floc fs7) (falloc fs7) tt)
     (trans (exec-abstract-preserves-next-slot store-indirect (floc fs6) (falloc fs6) tt)
     (trans (exec-abstract-preserves-next-slot (load-from-slot cell0-stash) (floc fs5) (falloc fs5) tt)
     (trans (exec-abstract-preserves-next-slot mov-to-input (floc fs4) (falloc fs4) tt)
     (trans (exec-abstract-preserves-next-slot (store-at-slot obj-stash) (floc fs3) (falloc fs3) tt)
     (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc fs2) (falloc fs2) tt)
     (trans (exec-abstract-preserves-next-slot (store-at-slot cell0-stash) (floc fs1) (falloc fs1) tt)
            (exec-abstract-preserves-next-slot mov-to-output (floc fs0) (falloc fs0) tt)))))))))

    nextslot-≤ : next-slot alloc ≤ next-slot (falloc fs10)
    nextslot-≤ = ≤-reflexive (sym nextslot-fs10)

    heapref-≤ : next-heap-ref alloc ≤ next-heap-ref (falloc fs10)
    heapref-≤ = subst (λ m → next-heap-ref alloc ≤ m) (sym heapref-fs10) (n≤1+n _)

    bf-advance : ∀ {lc : ValueLocation FS} → BeforeFrontier alloc lc
               → BeforeFrontier (falloc fs10) lc
    bf-advance (BeforeFrontier.stack-before f≡cf k<ns) =
      BeforeFrontier.stack-before (trans f≡cf (sym cf-fs10)) (<-≤-trans k<ns nextslot-≤)
    bf-advance (BeforeFrontier.stack-ancestor cf≺f src) =
      BeforeFrontier.stack-ancestor
        (subst (λ c → Once.CCC.FrameSemantics.FrameSemantics._≺_ FS c _)
               (sym cf-fs10) cf≺f) src
    bf-advance (BeforeFrontier.heap-before r<h) =
      BeforeFrontier.heap-before (<-≤-trans r<h heapref-≤)


    -- D204: what the ten-instruction build LEAVES ALONE. `TenStepPres` already
    -- proved it (it is what `valid-transport` spends below); the obligation
    -- now names it, so both consumers hand it over instead of it staying an
    -- internal step.
    mem-pres : ∀ (loc : ValueLocation FS)
             → BeforeFrontier (record alloc { next-slot = n }) loc
             → MemOps.readLoc (floc fs10) loc ≡ MemOps.readLoc s loc
    mem-pres = TSP.mem-pres nhw-load-from-slot refl nhw-instr-load-code-addr refl
                 n≤ rdi-fs6 rdi-fs8

    -- The input's validity, carried from the entry state to `fs10`. This is
    -- the one place `TenStepPres` is spent, and both consumers spend it the
    -- same way — the pointer residence is the only one that has a sub-value.
    -- `{A}` is PINNED at every application: `⟦_⟧ᴰᴵ` is not constructor-headed
    -- (D180), so nothing here determines it from the value's type.
    valid-transport : ∀ {mIn A} (x : ValueDomain.⟦ A ⟧ᴰᴵ) (loc : ValueLocation FS)
                    → BeforeFrontier alloc loc
                    → ValidAtWF mIn alloc {A} x loc s
                    → ValidAtWF mIn (falloc fs10) {A} x loc (floc fs10)
    valid-transport {A = A} x loc bf valid =
      validityWF-frontier-advance {A = A} x loc (floc fs10)
        cf-fs10 nextslot-≤ heapref-≤
        (validityWF-mem-preserved {A = A} x loc s (floc fs10) bf
           -- D206: `TSP.mem-pres` is now stated at the BUILD's frontier `n`;
           -- the caller's data is below `next-slot alloc ≤ n`, so the
           -- hypothesis weakens upward.
           (λ loc' bf' → TSP.mem-pres nhw-load-from-slot refl
                           nhw-instr-load-code-addr refl n≤ rdi-fs6 rdi-fs8 loc'
                           (frontier-monotone alloc (record alloc { next-slot = n })
                              refl n≤ ≤-refl loc' bf'))
           valid)

