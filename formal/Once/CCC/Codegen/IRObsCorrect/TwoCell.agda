-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.TwoCell
--
-- D200: the TWO-CELL BUILDS — `curry` and `Ana` emit the SAME ten
-- instructions (D190), differing only in what goes in the code cell and where
-- the result is placed, so `TwoCellBuild` is factored out and each clause
-- supplies only its `ResultPlace`.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.TwoCell (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module TwoCellC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

  curry-denot-[] : ∀ {A B C} (body : IR (A * B) C) (m : AllocMode)
                   {x : ⟦ A ⟧} (k : ℕ)
                 → projTrace (evalᴰ (curry body) x) k ≡ []
  curry-denot-[] body m k = refl


  two-cell-trace : ℕ → ℕ → AbstractTrace
  two-cell-trace n l =
    mov-to-output ∷ store-at-slot n ∷ instr-alloc-heap 2 ∷ store-at-slot (suc n) ∷
    mov-to-input ∷ load-from-slot n ∷ store-indirect ∷
    instr-load-code-addr (ℓ o l) ∷ store-indirect-suc ∷ load-from-slot (suc n) ∷ []

  module TwoCellBuild
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

    read-cell0-fs2 : MemOps.readLoc (floc fs2)
                     (AtStack (current-frame (falloc fs1)) cell0-stash) ≡ just cell0v
    read-cell0-fs2 =
      MemOps.writeLoc-read-same-stack (floc fs1) (current-frame (falloc fs1)) cell0-stash cell0v

    read-cell0-fs5 : MemOps.readLoc (floc fs5)
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
      cell0v , subst (λ f → MemOps.readLoc (floc fs5) (AtStack f cell0-stash) ≡ just cell0v)
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

    read-obj-fs4 : MemOps.readLoc (floc fs4)
                     (AtStack (current-frame (falloc fs3)) obj-stash) ≡ just objv
    read-obj-fs4 =
      MemOps.writeLoc-read-same-stack (floc fs3) (current-frame (falloc fs3)) obj-stash objv

    read-obj-fs9 : MemOps.readLoc (floc fs9)
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
      objv , subst (λ f → MemOps.readLoc (floc fs9) (AtStack f obj-stash) ≡ just objv)
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
    valid-transport : ∀ {mIn A} (x : DT.⟦ A ⟧ᴰᴵ) (loc : ValueLocation FS)
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

  obs-correct-curry : ∀ {A B C} (body : IR (A * B) C) → IRObsCorrectF (curry body)
  obs-correct-curry {A} {B} {C} body n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh inp k =
    record
      { traces-agree   = cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 10 TCB.fs10 Heap (falloc TCB.fs10) TCB.run TCB.nh10 refl refl refl place
                   (λ fr j bf' → TCB.mem-pres (AtStack fr j) bf')
                   (λ hl bf' → TCB.mem-pres (AtDynamic hl) bf')
                   TCB.cf-fs10
                   (λ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc TCB.fs10) { next-slot = m })
                                     (sym TCB.cf-fs10) ≤-refl TCB.heapref-≤ loc' bf')
      }
    where
      -- D190: the ten-instruction build is shared with `Ana`; `emitted n l
      -- (curry body)` IS `two-cell-trace n l`, so `span` passes straight in.
      module TCB = TwoCellBuild n l prog base s alloc cl n≤ nh span

      denot-[] : ∀ k → projTrace (evalᴰ (curry body) x) k ≡ []
      denot-[] k = refl

      -- ── THE THREE INPUT RESIDENCES. The env cell receives whatever `Input1`
      -- held, so each residence picks the matching closure witness: a POINTER
      -- env gets `valid-closure-wf`, a register literal and a unit env get
      -- D181's `valid-closure-reg-wf`. Without that constructor the last two —
      -- and a unit env is `main`'s — would be unprovable.
      place-of : InputAt mIn alloc x s
               → ResultPlace (B IRTy.⇛ C) Heap (falloc TCB.fs10) (falloc TCB.fs10)
                             (TM.valueT (evalᴰ (curry body) x) k) (floc TCB.fs10)
      place-of (in-reg fit eq) =
        at-loc TCB.obj-loc (mk-valid eq) TCB.before TCB.out-eq (mk-valid eq) TCB.before
        where
          ev≡in : TCB.cell0v ≡ readReg (regs s) Input1
          ev≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

          mk-valid : ∀ (e : readReg (regs s) Input1 ≡ prim-sv fit x)
                   → ValidAtWF Heap (falloc TCB.fs10)
                       (TM.valueT (evalᴰ (curry body) x) 0) TCB.obj-loc (floc TCB.fs10)
          mk-valid e =
            valid-closure-reg-wf {body = body} {env = x} tt (rep-prim fit)
              (trans TCB.cell0-fs10 (cong just (trans ev≡in e))) TCB.code-fs10 TCB.before-suc
      place-of (in-unit refl) =
        at-loc TCB.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before
        where
          mk-valid : ValidAtWF Heap (falloc TCB.fs10)
                       (TM.valueT (evalᴰ (curry body) x) 0) TCB.obj-loc (floc TCB.fs10)
          mk-valid =
            valid-closure-reg-wf {body = body} {env = x} tt (rep-unit refl TCB.cell0v)
              TCB.cell0-fs10 TCB.code-fs10 TCB.before-suc
      place-of (in-loc loc valid bf eq) =
        at-loc TCB.obj-loc (mk-valid eq) TCB.before TCB.out-eq (mk-valid eq) TCB.before
        where
          ev≡ptr : ∀ (e : readReg (regs s) Input1 ≡ SV-Ptr loc) → TCB.cell0v ≡ SV-Ptr loc
          ev≡ptr e = trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) e

          mk-valid : ∀ (e : readReg (regs s) Input1 ≡ SV-Ptr loc)
                   → ValidAtWF Heap (falloc TCB.fs10)
                       (TM.valueT (evalᴰ (curry body) x) 0) TCB.obj-loc (floc TCB.fs10)
          mk-valid e =
            valid-closure-wf {body = body} {env = x} tt
              (trans TCB.cell0-fs10 (cong just (ev≡ptr e))) TCB.code-fs10
              (TCB.bf-advance bf) TCB.before-suc (TCB.valid-transport x loc bf valid)

      place : ResultPlace (B IRTy.⇛ C) Heap (falloc TCB.fs10) (falloc TCB.fs10)
                          (TM.valueT (evalᴰ (curry body) x) k) (floc TCB.fs10)
      place = place-of inp

  ------------------------------------------------------------------------
  -- D189: `Ana` — DISCHARGED, and it is `obs-correct-curry` with the other
  -- witness.
  --
  -- That is the whole content of the representation decision. A ν is a
  -- suspension: the seed in cell 0, the coalgebra's code address in cell 1.
  -- A closure is a suspension too — the env in cell 0, the body's code
  -- address in cell 1 — so the ten instructions are the same ten, the run is
  -- the same run, and the two clauses differ only in which `ValidAtWF`
  -- constructor they hand the two cells to. `TwoCellBuild` (D190) is
  -- everything before that choice; this clause is the choice.
  --
  -- The seed's residence is where D187's `CellAt` pays: a pointer seed, a
  -- register-sized seed and a `Unit` seed are ONE constructor here, whereas
  -- `curry` still needs `valid-closure-wf`/`valid-closure-reg-wf` to say the
  -- same thing twice.
  ------------------------------------------------------------------------
  obs-correct-Ana : ∀ {F} (wf : WellFormedFI F) {A} (coalg : IR A (⟦ F ⟧TI A))
                  → IRObsCorrectF (Ana wf coalg)
  obs-correct-Ana {F} wf {A} coalg n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh inp k =
    record
      { traces-agree   = cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 10 TCB.fs10 Heap (falloc TCB.fs10) TCB.run TCB.nh10 refl refl refl place
                   (λ fr j bf' → TCB.mem-pres (AtStack fr j) bf')
                   (λ hl bf' → TCB.mem-pres (AtDynamic hl) bf')
                   TCB.cf-fs10
                   (λ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc TCB.fs10) { next-slot = m })
                                     (sym TCB.cf-fs10) ≤-refl TCB.heapref-≤ loc' bf')
      }
    where
      module TCB = TwoCellBuild n l prog base s alloc cl n≤ nh span

      -- Building a suspension RUNS NOTHING: the coalgebra is stored, not
      -- called, so neither side emits. (`Out` is where the events appear.)
      denot-[] : ∀ k → projTrace (evalᴰ (Ana wf coalg) x) k ≡ []
      denot-[] k = refl

      cell0v≡in : TCB.cell0v ≡ readReg (regs s) Input1
      cell0v≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

      -- THE SEED CELL — one clause per residence, one constructor for all three.
      cell-of : InputAt mIn alloc x s
              → CellAt (falloc TCB.fs10) A x TCB.obj-loc (floc TCB.fs10)
      cell-of (in-reg fit eq) =
        cell-inline (rep-prim fit)
          (trans TCB.cell0-fs10 (cong just (trans cell0v≡in eq)))
      cell-of (in-unit refl) =
        cell-inline (rep-unit refl TCB.cell0v) TCB.cell0-fs10
      cell-of (in-loc loc valid bf eq) =
        cell-ptr (trans TCB.cell0-fs10 (cong just (trans cell0v≡in eq)))
                 (TCB.bf-advance bf) (TCB.valid-transport x loc bf valid)

      mk-valid : ValidAtWF Heap (falloc TCB.fs10)
                   (TM.valueT (evalᴰ (Ana wf coalg) x) 0) TCB.obj-loc (floc TCB.fs10)
      mk-valid = valid-ν-susp-wf wf {coalg = coalg} {seed = x} tt
                   (cell-of inp) TCB.code-fs10 TCB.before-suc

      place : ResultPlace (ν-type F) Heap (falloc TCB.fs10) (falloc TCB.fs10)
                          (TM.valueT (evalᴰ (Ana wf coalg) x) k) (floc TCB.fs10)
      place = at-loc TCB.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before

  ------------------------------------------------------------------------
  -- D188: `apply` — DISCHARGED against the block-table premise.
  --
  -- Sixteen instructions build the callee's `(env , arg)` pair on the heap and
  -- point `Input1` at it; the seventeenth calls. Everything about those
  -- seventeen is proved (D183/D185); what the premise supplies is the callee's
  -- own run, and nothing else.
  ------------------------------------------------------------------------

