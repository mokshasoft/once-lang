-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Sum
--
-- D200: `inl` and `inr` — the two heap sum-node builds. They are the largest
-- straight-line clauses in the development (a tag cell and a payload cell,
-- with the full memory-preservation argument for each).
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Sum (o : CanonicalName) where

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

module SumC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

  obs-correct-inl : ∀ {A B} → IRObsCorrectF (inl {A} {B})
  obs-correct-inl {A} {B} n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh inp k =
    record
      { traces-agree   = cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 10 fs10 Heap (falloc fs10) run (λ _ → nh10) (λ _ → refl) (λ ()) refl refl (λ _ → place)
                   -- D204: the ten-instruction build's own preservation, which
                   -- `TenStepPres` already proves and `valid-transport` already
                   -- spends — the obligation just names it now.
                   (λ fr j bf' → TSP.mem-pres nhw-instr-load-tag-lit refl
                                   nhw-load-from-slot refl n≤ rdi-fs6 rdi-fs8
                                   (AtStack fr j) bf')
                   (λ hl bf' → TSP.mem-pres nhw-instr-load-tag-lit refl
                                 nhw-load-from-slot refl n≤ rdi-fs6 rdi-fs8
                                 (AtDynamic hl) bf')
                   cf-fs10
                   (λ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc fs10) { next-slot = m })
                                     (sym cf-fs10) ≤-refl heapref-≤ loc' bf')
      }
    where
      payload-stash sum-stash : ℕ
      payload-stash = n
      sum-stash     = suc n

      -- D182: this clause's instance of the shared ten-step invariant.
      module TSP = TenStepPres n (instr-load-tag-lit 0) (load-from-slot n)
                               prog base s alloc cl

      -- The ten instructions, in emission order (`IRToTrace`'s heap build).
      fs0 fs1 fs2 fs3 fs4 fs5 fs6 fs7 fs8 fs9 fs10 : FlatState
      fs0  = entry-flat base s alloc cl
      fs1  = flat-exec-instr mov-to-output              prog fs0
      fs2  = flat-exec-instr (store-at-slot payload-stash) prog fs1
      fs3  = flat-exec-instr (instr-alloc-heap 2)       prog fs2
      fs4  = flat-exec-instr (store-at-slot sum-stash)  prog fs3
      fs5  = flat-exec-instr mov-to-input               prog fs4
      fs6  = flat-exec-instr (instr-load-tag-lit 0)     prog fs5
      fs7  = flat-exec-instr store-indirect             prog fs6
      fs8  = flat-exec-instr (load-from-slot payload-stash) prog fs7
      fs9  = flat-exec-instr store-indirect-suc         prog fs8
      fs10 = flat-exec-instr (load-from-slot sum-stash) prog fs9

      denot-[] : ∀ k → projTrace (evalᴰ (inl {A} {B}) x) k ≡ []
      denot-[] k = refl

      -- The sum block's address, as `alloc-impl` hands it out at fs2.
      sum-hl : HeapLocation
      sum-hl = heap-loc (mkHeapRef (next-heap-ref (falloc fs2))) 0

      sum-loc : ValueLocation FS
      sum-loc = AtDynamic sum-hl

      -- ── THE FOUR CONDITIONAL WITNESSES, in dependency order.
      --
      -- Row 6 is a pure REGISTER fact and reduces: `instr-alloc-heap` writes
      -- `SV-Ptr (AtDynamic addr)` to Output, `mov-to-input` copies it to
      -- Input1, and `instr-load-tag-lit` writes a different register — and
      -- `writeReg r Output v` is `record r { output = v }`, so reading Input1
      -- through it is definitional.
      rdi-fs6 : sv-as-loc (readReg (regs (floc fs6)) Input1) ≡ just sum-loc
      rdi-fs6 = refl

      wf-store-ind : InstrWF (floc fs6) (falloc fs6) store-indirect
      wf-store-ind = sum-loc , rdi-fs6

      -- The frame never moves: none of the ten is a frame op. NOT
      -- definitional across a nest of `exec-abstract`s, hence the chain.
      cf-fs7 : current-frame (falloc fs7) ≡ current-frame (falloc fs1)
      cf-fs7 =
        trans (exec-abstract-preserves-frame store-indirect (floc fs6) (falloc fs6))
       (trans (exec-abstract-preserves-frame (instr-load-tag-lit 0) (floc fs5) (falloc fs5))
       (trans (exec-abstract-preserves-frame mov-to-input (floc fs4) (falloc fs4))
       (trans (exec-abstract-preserves-frame (store-at-slot sum-stash) (floc fs3) (falloc fs3))
       (trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc fs2) (falloc fs2))
              (exec-abstract-preserves-frame (store-at-slot payload-stash) (floc fs1) (falloc fs1))))))

      -- The payload value, as `mov-to-output` leaves it and
      -- `store-at-slot payload-stash` commits it, read back at fs7. The only
      -- intervening STACK write targets `suc n`, so `n < suc n` keeps it away;
      -- `store-indirect` writes the HEAP, which never disturbs a stack cell.
      pv : StoredValue FS
      pv = readReg (regs (floc fs1)) Output

      read-payload-fs2 : MemOps.readLoc (floc fs2)
                           (AtStack (current-frame (falloc fs1)) payload-stash) ≡ just pv
      read-payload-fs2 =
        MemOps.writeLoc-read-same-stack (floc fs1) (current-frame (falloc fs1)) payload-stash pv

      read-payload-fs7 : MemOps.readLoc (floc fs7)
                           (AtStack (current-frame (falloc fs1)) payload-stash) ≡ just pv
      read-payload-fs7 =
        trans (store-ind-preserves-slot (floc fs6) (falloc fs6) sum-hl payload-stash rdi-fs6)
       (trans (exec-abstract-preserves-stack-slot (instr-load-tag-lit 0) (floc fs5) (falloc fs5)
                 (current-frame (falloc fs1)) payload-stash nhw-instr-load-tag-lit refl)
       (trans (exec-abstract-preserves-stack-slot mov-to-input (floc fs4) (falloc fs4)
                 (current-frame (falloc fs1)) payload-stash nhw-mov-to-input refl)
       (trans (store-at-slot-preserves-below payload-stash sum-stash (floc fs3) (falloc fs3) (n<1+n _))
       (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc fs2) (falloc fs2)
                 (current-frame (falloc fs1)) payload-stash nhw-instr-alloc-heap refl)
              read-payload-fs2))))

      wf-load-payload : InstrWF (floc fs7) (falloc fs7) (load-from-slot payload-stash)
      wf-load-payload =
        pv , subst (λ f → MemOps.readLoc (floc fs7) (AtStack f payload-stash) ≡ just pv)
                   (sym cf-fs7) read-payload-fs7

      -- Row 8: the pointer must SURVIVE the first indirect store and the slot
      -- load. That is what the two new preservation lemmas are for.
      input-fs7 : readReg (regs (floc fs7)) Input1 ≡ readReg (regs (floc fs6)) Input1
      input-fs7 = store-ind-preserves-input (floc fs6) (falloc fs6) sum-loc rdi-fs6

      input-fs8 : readReg (regs (floc fs8)) Input1 ≡ readReg (regs (floc fs7)) Input1
      input-fs8 = load-slot-preserves-input payload-stash (floc fs7) (falloc fs7) pv
                    (proj₂ wf-load-payload)

      rdi-fs8 : sv-as-loc (readReg (regs (floc fs8)) Input1) ≡ just sum-loc
      rdi-fs8 = trans (cong sv-as-loc (trans input-fs8 input-fs7)) rdi-fs6

      wf-store-ind-suc : InstrWF (floc fs8) (falloc fs8) store-indirect-suc
      wf-store-ind-suc = sum-loc , rdi-fs8

      -- Row 9: the SUM pointer, stashed at fs3→fs4 and read back at fs9.
      cf-fs9 : current-frame (falloc fs9) ≡ current-frame (falloc fs3)
      cf-fs9 =
        trans (exec-abstract-preserves-frame store-indirect-suc (floc fs8) (falloc fs8))
       (trans (exec-abstract-preserves-frame (load-from-slot payload-stash) (floc fs7) (falloc fs7))
       (trans (exec-abstract-preserves-frame store-indirect (floc fs6) (falloc fs6))
       (trans (exec-abstract-preserves-frame (instr-load-tag-lit 0) (floc fs5) (falloc fs5))
       (trans (exec-abstract-preserves-frame mov-to-input (floc fs4) (falloc fs4))
              (exec-abstract-preserves-frame (store-at-slot sum-stash) (floc fs3) (falloc fs3))))))

      sv : StoredValue FS
      sv = readReg (regs (floc fs3)) Output

      read-sum-fs4 : MemOps.readLoc (floc fs4)
                       (AtStack (current-frame (falloc fs3)) sum-stash) ≡ just sv
      read-sum-fs4 =
        MemOps.writeLoc-read-same-stack (floc fs3) (current-frame (falloc fs3)) sum-stash sv

      read-sum-fs9 : MemOps.readLoc (floc fs9)
                       (AtStack (current-frame (falloc fs3)) sum-stash) ≡ just sv
      read-sum-fs9 =
        trans (store-ind-suc-preserves-slot (floc fs8) (falloc fs8) sum-hl sum-stash rdi-fs8)
       (trans (exec-abstract-preserves-stack-slot (load-from-slot payload-stash) (floc fs7) (falloc fs7)
                 (current-frame (falloc fs3)) sum-stash nhw-load-from-slot refl)
       (trans (store-ind-preserves-slot (floc fs6) (falloc fs6) sum-hl sum-stash rdi-fs6)
       (trans (exec-abstract-preserves-stack-slot (instr-load-tag-lit 0) (floc fs5) (falloc fs5)
                 (current-frame (falloc fs3)) sum-stash nhw-instr-load-tag-lit refl)
       (trans (exec-abstract-preserves-stack-slot mov-to-input (floc fs4) (falloc fs4)
                 (current-frame (falloc fs3)) sum-stash nhw-mov-to-input refl)
              read-sum-fs4))))

      wf-load-sum : InstrWF (floc fs9) (falloc fs9) (load-from-slot sum-stash)
      wf-load-sum =
        sv , subst (λ f → MemOps.readLoc (floc fs9) (AtStack f sum-stash) ≡ just sv)
                   (sym cf-fs9) read-sum-fs9

      -- The ten `halted ≡ false` obligations. Rows 0-5 are unconditional in
      -- `exec-abstract-preserves-halted-WF`; rows 6-9 carry an `InstrWF`
      -- premise that an EARLIER instruction of this same chain establishes.
      nh0 : halted (floc fs0) ≡ false
      nh0 = nh
      nh1 : halted (floc fs1) ≡ false
      nh1 = exec-abstract-preserves-halted-WF mov-to-output (floc fs0) (falloc fs0) nh0 tt
      nh2 : halted (floc fs2) ≡ false
      nh2 = exec-abstract-preserves-halted-WF (store-at-slot payload-stash) (floc fs1) (falloc fs1) nh1 tt
      nh3 : halted (floc fs3) ≡ false
      nh3 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc fs2) (falloc fs2) nh2 tt
      nh4 : halted (floc fs4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF (store-at-slot sum-stash) (floc fs3) (falloc fs3) nh3 tt
      nh5 : halted (floc fs5) ≡ false
      nh5 = exec-abstract-preserves-halted-WF mov-to-input (floc fs4) (falloc fs4) nh4 tt
      nh6 : halted (floc fs6) ≡ false
      nh6 = exec-abstract-preserves-halted-WF (instr-load-tag-lit 0) (floc fs5) (falloc fs5) nh5 tt
      nh7 : halted (floc fs7) ≡ false
      nh7 = exec-abstract-preserves-halted-WF store-indirect (floc fs6) (falloc fs6) nh6 wf-store-ind
      nh8 : halted (floc fs8) ≡ false
      nh8 = exec-abstract-preserves-halted-WF (load-from-slot payload-stash) (floc fs7) (falloc fs7) nh7 wf-load-payload
      nh9 : halted (floc fs9) ≡ false
      nh9 = exec-abstract-preserves-halted-WF store-indirect-suc (floc fs8) (falloc fs8) nh8 wf-store-ind-suc
      nh10 : halted (floc fs10) ≡ false
      nh10 = exec-abstract-preserves-halted-WF (load-from-slot sum-stash) (floc fs9) (falloc fs9) nh9 wf-load-sum

      run : FlatSteps prog 10 fs0 fs10
      run = (nh0 , span 0 _ refl) ∷ (nh1 , span 1 _ refl) ∷ (nh2 , span 2 _ refl)
          ∷ (nh3 , span 3 _ refl) ∷ (nh4 , span 4 _ refl) ∷ (nh5 , span 5 _ refl)
          ∷ (nh6 , span 6 _ refl) ∷ (nh7 , span 7 _ refl) ∷ (nh8 , span 8 _ refl)
          ∷ (nh9 , span 9 _ refl) ∷ []

      -- D174 / D173's payoff, STATED SO THE TYPECHECKER RULES ON IT.
      -- `instr-alloc-heap 2` runs at fs2→fs3. `AI.alloc-impl n s` is the
      -- concrete bump allocator: it returns `heap-loc (mkHeapRef s) 0` and
      -- leaves `suc s` behind, so the block's ref-id IS the pre-state frontier
      -- and the post-state frontier is its successor. Instructions 3-9 do not
      -- allocate, so `falloc fs10 ≡ falloc fs3` definitionally.
      --
      -- THIS IS WHAT `stack-before` COULD NOT DO. Its premise is
      -- `k < next-slot alloc`, and the emitter writes slot `n` with
      -- `next-slot alloc ≤ n` given — so it would need `k < next-slot ≤ k`.
      -- The heap path inverts it: the allocation MOVES the frontier past the
      -- address it just handed out.
      -- Instructions 3-9 do not allocate, so the frontier they leave is the
      -- one the allocation set. NOT definitional — `falloc fs10` is a nest of
      -- seven `exec-abstract` applications — so it is a `trans` chain over
      -- `exec-abstract-preserves-heap-ref`, whose per-instruction witness is
      -- `tt` for every effect class except `eff-heap-alloc`.
      heapref-fs10 : next-heap-ref (falloc fs10) ≡ suc (next-heap-ref (falloc fs2))
      heapref-fs10 =
        trans (exec-abstract-preserves-heap-ref (load-from-slot sum-stash) (floc fs9) (falloc fs9) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc fs8) (falloc fs8) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot payload-stash) (floc fs7) (falloc fs7) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect (floc fs6) (falloc fs6) tt)
       (trans (exec-abstract-preserves-heap-ref (instr-load-tag-lit 0) (floc fs5) (falloc fs5) tt)
       (trans (exec-abstract-preserves-heap-ref mov-to-input (floc fs4) (falloc fs4) tt)
              (exec-abstract-preserves-heap-ref (store-at-slot sum-stash) (floc fs3) (falloc fs3) tt))))))

      before : BeforeFrontier (falloc fs10) sum-loc
      before = BeforeFrontier.heap-before
                 (subst (λ m → next-heap-ref (falloc fs2) < m) (sym heapref-fs10) (n<1+n _))

      -- ── THE TAG CELL, written by `store-indirect` at fs6→fs7 and carried to
      -- fs10 past one heap write (the payload, a DIFFERENT cell) and two
      -- register-only loads.
      tagout-fs6 : readReg (regs (floc fs6)) Output ≡ SV-Tag 0
      tagout-fs6 = writeReg-same (regs (floc fs5)) Output (SV-Tag 0)

      tag-fs7 : MemOps.readLoc (floc fs7) sum-loc ≡ just (SV-Tag 0)
      tag-fs7 = trans (store-ind-result (floc fs6) (falloc fs6) sum-hl rdi-fs6)
                      (cong just tagout-fs6)

      tag-fs10 : MemOps.readLoc (floc fs10) sum-loc ≡ just (SV-Tag 0)
      tag-fs10 =
        trans (heap-untouched (load-from-slot sum-stash) (floc fs9) (falloc fs9)
                 sum-hl nhw-load-from-slot)
       (trans (store-ind-suc-preserves-heap (floc fs8) (falloc fs8) sum-hl sum-hl
                 rdi-fs8 (sucHL-≢ sum-hl))
       (trans (heap-untouched (load-from-slot payload-stash) (floc fs7) (falloc fs7)
                 sum-hl nhw-load-from-slot)
              tag-fs7))

      -- ── THE PAYLOAD CELL, written by `store-indirect-suc` at fs8→fs9.
      payout-fs8 : readReg (regs (floc fs8)) Output ≡ pv
      payout-fs8 = load-slot-result payload-stash (floc fs7) (falloc fs7) pv
                     (proj₂ wf-load-payload)

      pay-fs10 : MemOps.readLoc (floc fs10) (sucLoc sum-loc) ≡ just pv
      pay-fs10 =
        trans (heap-untouched (load-from-slot sum-stash) (floc fs9) (falloc fs9)
                 (sucHL sum-hl) nhw-load-from-slot)
       (trans (store-ind-suc-result (floc fs8) (falloc fs8) sum-hl rdi-fs8)
              (cong just payout-fs8))

      -- ── THE RESULT POINTER: instruction 9 loads the stashed sum pointer.
      sv≡ptr : sv ≡ SV-Ptr sum-loc
      sv≡ptr = writeReg-same (regs (floc fs2)) Output (SV-Ptr (AtDynamic sum-hl))

      out-eq : readReg (regs (floc fs10)) Output ≡ SV-Ptr sum-loc
      out-eq = trans (load-slot-result sum-stash (floc fs9) (falloc fs9) sv
                        (proj₂ wf-load-sum)) sv≡ptr

      -- `sucHL` keeps the ref, so the successor cell is before the same
      -- frontier by the same proof.
      before-suc : BeforeFrontier (falloc fs10) (sucLoc sum-loc)
      before-suc = BeforeFrontier.heap-before
                     (subst (λ m → next-heap-ref (falloc fs2) < m) (sym heapref-fs10) (n<1+n _))

      -- `validityWF-frontier-advance`'s three premises. None of the ten is a
      -- frame or stack-allocation op, so `current-frame` and `next-slot` are
      -- the same at the end as at the start — but NOT definitionally: the
      -- `with`-blocks in `load-from-slot` and the indirect stores block
      -- reduction, so each is a `trans` chain, exactly like `heapref-fs10`.
      cf-fs10 : current-frame (falloc fs10) ≡ current-frame alloc
      cf-fs10 =
        trans (exec-abstract-preserves-frame (load-from-slot sum-stash) (floc fs9) (falloc fs9))
       (trans (exec-abstract-preserves-frame store-indirect-suc (floc fs8) (falloc fs8))
       (trans (exec-abstract-preserves-frame (load-from-slot payload-stash) (floc fs7) (falloc fs7))
       (trans cf-fs7
              (exec-abstract-preserves-frame mov-to-output (floc fs0) (falloc fs0)))))

      nextslot-fs10 : next-slot (falloc fs10) ≡ next-slot alloc
      nextslot-fs10 =
        trans (exec-abstract-preserves-next-slot (load-from-slot sum-stash) (floc fs9) (falloc fs9) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect-suc (floc fs8) (falloc fs8) tt)
       (trans (exec-abstract-preserves-next-slot (load-from-slot payload-stash) (floc fs7) (falloc fs7) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect (floc fs6) (falloc fs6) tt)
       (trans (exec-abstract-preserves-next-slot (instr-load-tag-lit 0) (floc fs5) (falloc fs5) tt)
       (trans (exec-abstract-preserves-next-slot mov-to-input (floc fs4) (falloc fs4) tt)
       (trans (exec-abstract-preserves-next-slot (store-at-slot sum-stash) (floc fs3) (falloc fs3) tt)
       (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc fs2) (falloc fs2) tt)
       (trans (exec-abstract-preserves-next-slot (store-at-slot payload-stash) (floc fs1) (falloc fs1) tt)
              (exec-abstract-preserves-next-slot mov-to-output (floc fs0) (falloc fs0) tt)))))))))

      nextslot-≤ : next-slot alloc ≤ next-slot (falloc fs10)
      nextslot-≤ = ≤-reflexive (sym nextslot-fs10)

      heapref-≤ : next-heap-ref alloc ≤ next-heap-ref (falloc fs10)
      heapref-≤ = subst (λ m → next-heap-ref alloc ≤ m) (sym heapref-fs10) (n≤1+n _)

      -- …and the same weakening for `BeforeFrontier` itself: the frontier only
      -- ever advances, so anything before it stays before it.
      bf-advance : ∀ {l : ValueLocation FS} → BeforeFrontier alloc l
                 → BeforeFrontier (falloc fs10) l
      bf-advance (BeforeFrontier.stack-before f≡cf k<ns) =
        BeforeFrontier.stack-before (trans f≡cf (sym cf-fs10)) (<-≤-trans k<ns nextslot-≤)
      bf-advance (BeforeFrontier.stack-ancestor cf≺f src) =
        BeforeFrontier.stack-ancestor
          (subst (λ c → Once.CCC.FrameSemantics.FrameSemantics._≺_ FS c _)
                 (sym cf-fs10) cf≺f) src
      bf-advance (BeforeFrontier.heap-before r<h) =
        BeforeFrontier.heap-before (<-≤-trans r<h heapref-≤)

      -- `with inp` is not available: `inp` is bound by the parent clause's
      -- patterns. Take it as an argument instead — the standing preference for
      -- a top-level helper over a with-block.
      place-of : InputAt mIn alloc x s
               → ResultPlace (A IRTy.+ B) Heap (falloc fs10) (falloc fs10)
                             (TM.valueT (evalᴰ (inl {A} {B}) x) k) (floc fs10)
      -- A register-resident payload needs NO payload location and NO payload
      -- validity — stage F's whole point. Fully proved.
      place-of (in-reg fit eq) =
        at-loc sum-loc
          (valid-inl-reg-wf tt tag-fs10 (rep-prim fit)
             (trans pay-fs10 (cong just (trans pv≡in eq))) before-suc)
          before out-eq
          (valid-inl-reg-wf tt tag-fs10 (rep-prim fit)
             (trans pay-fs10 (cong just (trans pv≡in eq))) before-suc)
          before
        where
          pv≡in : pv ≡ readReg (regs s) Input1
          pv≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)
      -- A unit payload has no residence at all (D074): `rep-unit` takes
      -- whatever the cell happens to hold. Fully proved.
      place-of (in-unit refl) =
        at-loc sum-loc
          (valid-inl-reg-wf tt tag-fs10 (rep-unit refl pv) pay-fs10 before-suc)
          before out-eq
          (valid-inl-reg-wf tt tag-fs10 (rep-unit refl pv) pay-fs10 before-suc)
          before
      -- A memory-resident payload: the cell holds `SV-Ptr loc`, and the
      -- INPUT's own validity has to be carried across the chain. That is the
      -- one residual — see `inl-mem-pres` above.
      place-of (in-loc loc valid bf eq) =
        at-loc sum-loc (mk-valid eq) before out-eq (mk-valid eq) before
        where
          pv≡ptr : ∀ (e : readReg (regs s) Input1 ≡ SV-Ptr loc) → pv ≡ SV-Ptr loc
          pv≡ptr e = trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) e

          valid' : ValidAtWF mIn (falloc fs10) x loc (floc fs10)
          valid' =
            validityWF-frontier-advance x loc (floc fs10)
              cf-fs10 nextslot-≤ heapref-≤
              (validityWF-mem-preserved x loc s (floc fs10) bf
                 (λ loc' bf' → TSP.mem-pres nhw-instr-load-tag-lit refl
                                 nhw-load-from-slot refl n≤ rdi-fs6 rdi-fs8 loc'
                                 (frontier-monotone alloc (record alloc { next-slot = n })
                                    refl n≤ ≤-refl loc' bf'))
                 valid)

          mk-valid : ∀ (e : readReg (regs s) Input1 ≡ SV-Ptr loc)
                   → ValidAtWF Heap (falloc fs10) (TM.valueT (evalᴰ (inl {A} {B}) x) 0) sum-loc (floc fs10)
          mk-valid e =
            valid-inl-wf tt tag-fs10 (trans pay-fs10 (cong just (pv≡ptr e)))
              (bf-advance bf) before-suc valid'

      place : ResultPlace (A IRTy.+ B) Heap (falloc fs10) (falloc fs10)
                          (TM.valueT (evalᴰ (inl {A} {B}) x) k) (floc fs10)
      place = place-of inp

  obs-correct-inr : ∀ {A B} → IRObsCorrectF (inr {A} {B})
  obs-correct-inr {A} {B} n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh inp k =
    record
      { traces-agree   = cong (take k) (sym (denot-[] k))
      ; value-realized =
          realized 10 fs10 Heap (falloc fs10) run (λ _ → nh10) (λ _ → refl) (λ ()) refl refl (λ _ → place)
                   -- D204: the ten-instruction build's own preservation, which
                   -- `TenStepPres` already proves and `valid-transport` already
                   -- spends — the obligation just names it now.
                   (λ fr j bf' → TSP.mem-pres nhw-instr-load-tag-lit refl
                                   nhw-load-from-slot refl n≤ rdi-fs6 rdi-fs8
                                   (AtStack fr j) bf')
                   (λ hl bf' → TSP.mem-pres nhw-instr-load-tag-lit refl
                                 nhw-load-from-slot refl n≤ rdi-fs6 rdi-fs8
                                 (AtDynamic hl) bf')
                   cf-fs10
                   (λ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc fs10) { next-slot = m })
                                     (sym cf-fs10) ≤-refl heapref-≤ loc' bf')
      }
    where
      payload-stash sum-stash : ℕ
      payload-stash = n
      sum-stash     = suc n

      -- D182: this clause's instance of the shared ten-step invariant.
      module TSP = TenStepPres n (instr-load-tag-lit 1) (load-from-slot n)
                               prog base s alloc cl

      -- The ten instructions, in emission order (`IRToTrace`'s heap build).
      fs0 fs1 fs2 fs3 fs4 fs5 fs6 fs7 fs8 fs9 fs10 : FlatState
      fs0  = entry-flat base s alloc cl
      fs1  = flat-exec-instr mov-to-output              prog fs0
      fs2  = flat-exec-instr (store-at-slot payload-stash) prog fs1
      fs3  = flat-exec-instr (instr-alloc-heap 2)       prog fs2
      fs4  = flat-exec-instr (store-at-slot sum-stash)  prog fs3
      fs5  = flat-exec-instr mov-to-input               prog fs4
      fs6  = flat-exec-instr (instr-load-tag-lit 1)     prog fs5
      fs7  = flat-exec-instr store-indirect             prog fs6
      fs8  = flat-exec-instr (load-from-slot payload-stash) prog fs7
      fs9  = flat-exec-instr store-indirect-suc         prog fs8
      fs10 = flat-exec-instr (load-from-slot sum-stash) prog fs9

      denot-[] : ∀ k → projTrace (evalᴰ (inr {A} {B}) x) k ≡ []
      denot-[] k = refl

      -- The sum block's address, as `alloc-impl` hands it out at fs2.
      sum-hl : HeapLocation
      sum-hl = heap-loc (mkHeapRef (next-heap-ref (falloc fs2))) 0

      sum-loc : ValueLocation FS
      sum-loc = AtDynamic sum-hl

      -- ── THE FOUR CONDITIONAL WITNESSES, in dependency order.
      --
      -- Row 6 is a pure REGISTER fact and reduces: `instr-alloc-heap` writes
      -- `SV-Ptr (AtDynamic addr)` to Output, `mov-to-input` copies it to
      -- Input1, and `instr-load-tag-lit` writes a different register — and
      -- `writeReg r Output v` is `record r { output = v }`, so reading Input1
      -- through it is definitional.
      rdi-fs6 : sv-as-loc (readReg (regs (floc fs6)) Input1) ≡ just sum-loc
      rdi-fs6 = refl

      wf-store-ind : InstrWF (floc fs6) (falloc fs6) store-indirect
      wf-store-ind = sum-loc , rdi-fs6

      -- The frame never moves: none of the ten is a frame op. NOT
      -- definitional across a nest of `exec-abstract`s, hence the chain.
      cf-fs7 : current-frame (falloc fs7) ≡ current-frame (falloc fs1)
      cf-fs7 =
        trans (exec-abstract-preserves-frame store-indirect (floc fs6) (falloc fs6))
       (trans (exec-abstract-preserves-frame (instr-load-tag-lit 1) (floc fs5) (falloc fs5))
       (trans (exec-abstract-preserves-frame mov-to-input (floc fs4) (falloc fs4))
       (trans (exec-abstract-preserves-frame (store-at-slot sum-stash) (floc fs3) (falloc fs3))
       (trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc fs2) (falloc fs2))
              (exec-abstract-preserves-frame (store-at-slot payload-stash) (floc fs1) (falloc fs1))))))

      -- The payload value, as `mov-to-output` leaves it and
      -- `store-at-slot payload-stash` commits it, read back at fs7. The only
      -- intervening STACK write targets `suc n`, so `n < suc n` keeps it away;
      -- `store-indirect` writes the HEAP, which never disturbs a stack cell.
      pv : StoredValue FS
      pv = readReg (regs (floc fs1)) Output

      read-payload-fs2 : MemOps.readLoc (floc fs2)
                           (AtStack (current-frame (falloc fs1)) payload-stash) ≡ just pv
      read-payload-fs2 =
        MemOps.writeLoc-read-same-stack (floc fs1) (current-frame (falloc fs1)) payload-stash pv

      read-payload-fs7 : MemOps.readLoc (floc fs7)
                           (AtStack (current-frame (falloc fs1)) payload-stash) ≡ just pv
      read-payload-fs7 =
        trans (store-ind-preserves-slot (floc fs6) (falloc fs6) sum-hl payload-stash rdi-fs6)
       (trans (exec-abstract-preserves-stack-slot (instr-load-tag-lit 1) (floc fs5) (falloc fs5)
                 (current-frame (falloc fs1)) payload-stash nhw-instr-load-tag-lit refl)
       (trans (exec-abstract-preserves-stack-slot mov-to-input (floc fs4) (falloc fs4)
                 (current-frame (falloc fs1)) payload-stash nhw-mov-to-input refl)
       (trans (store-at-slot-preserves-below payload-stash sum-stash (floc fs3) (falloc fs3) (n<1+n _))
       (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc fs2) (falloc fs2)
                 (current-frame (falloc fs1)) payload-stash nhw-instr-alloc-heap refl)
              read-payload-fs2))))

      wf-load-payload : InstrWF (floc fs7) (falloc fs7) (load-from-slot payload-stash)
      wf-load-payload =
        pv , subst (λ f → MemOps.readLoc (floc fs7) (AtStack f payload-stash) ≡ just pv)
                   (sym cf-fs7) read-payload-fs7

      -- Row 8: the pointer must SURVIVE the first indirect store and the slot
      -- load. That is what the two new preservation lemmas are for.
      input-fs7 : readReg (regs (floc fs7)) Input1 ≡ readReg (regs (floc fs6)) Input1
      input-fs7 = store-ind-preserves-input (floc fs6) (falloc fs6) sum-loc rdi-fs6

      input-fs8 : readReg (regs (floc fs8)) Input1 ≡ readReg (regs (floc fs7)) Input1
      input-fs8 = load-slot-preserves-input payload-stash (floc fs7) (falloc fs7) pv
                    (proj₂ wf-load-payload)

      rdi-fs8 : sv-as-loc (readReg (regs (floc fs8)) Input1) ≡ just sum-loc
      rdi-fs8 = trans (cong sv-as-loc (trans input-fs8 input-fs7)) rdi-fs6

      wf-store-ind-suc : InstrWF (floc fs8) (falloc fs8) store-indirect-suc
      wf-store-ind-suc = sum-loc , rdi-fs8

      -- Row 9: the SUM pointer, stashed at fs3→fs4 and read back at fs9.
      cf-fs9 : current-frame (falloc fs9) ≡ current-frame (falloc fs3)
      cf-fs9 =
        trans (exec-abstract-preserves-frame store-indirect-suc (floc fs8) (falloc fs8))
       (trans (exec-abstract-preserves-frame (load-from-slot payload-stash) (floc fs7) (falloc fs7))
       (trans (exec-abstract-preserves-frame store-indirect (floc fs6) (falloc fs6))
       (trans (exec-abstract-preserves-frame (instr-load-tag-lit 1) (floc fs5) (falloc fs5))
       (trans (exec-abstract-preserves-frame mov-to-input (floc fs4) (falloc fs4))
              (exec-abstract-preserves-frame (store-at-slot sum-stash) (floc fs3) (falloc fs3))))))

      sv : StoredValue FS
      sv = readReg (regs (floc fs3)) Output

      read-sum-fs4 : MemOps.readLoc (floc fs4)
                       (AtStack (current-frame (falloc fs3)) sum-stash) ≡ just sv
      read-sum-fs4 =
        MemOps.writeLoc-read-same-stack (floc fs3) (current-frame (falloc fs3)) sum-stash sv

      read-sum-fs9 : MemOps.readLoc (floc fs9)
                       (AtStack (current-frame (falloc fs3)) sum-stash) ≡ just sv
      read-sum-fs9 =
        trans (store-ind-suc-preserves-slot (floc fs8) (falloc fs8) sum-hl sum-stash rdi-fs8)
       (trans (exec-abstract-preserves-stack-slot (load-from-slot payload-stash) (floc fs7) (falloc fs7)
                 (current-frame (falloc fs3)) sum-stash nhw-load-from-slot refl)
       (trans (store-ind-preserves-slot (floc fs6) (falloc fs6) sum-hl sum-stash rdi-fs6)
       (trans (exec-abstract-preserves-stack-slot (instr-load-tag-lit 1) (floc fs5) (falloc fs5)
                 (current-frame (falloc fs3)) sum-stash nhw-instr-load-tag-lit refl)
       (trans (exec-abstract-preserves-stack-slot mov-to-input (floc fs4) (falloc fs4)
                 (current-frame (falloc fs3)) sum-stash nhw-mov-to-input refl)
              read-sum-fs4))))

      wf-load-sum : InstrWF (floc fs9) (falloc fs9) (load-from-slot sum-stash)
      wf-load-sum =
        sv , subst (λ f → MemOps.readLoc (floc fs9) (AtStack f sum-stash) ≡ just sv)
                   (sym cf-fs9) read-sum-fs9

      -- The ten `halted ≡ false` obligations. Rows 0-5 are unconditional in
      -- `exec-abstract-preserves-halted-WF`; rows 6-9 carry an `InstrWF`
      -- premise that an EARLIER instruction of this same chain establishes.
      nh0 : halted (floc fs0) ≡ false
      nh0 = nh
      nh1 : halted (floc fs1) ≡ false
      nh1 = exec-abstract-preserves-halted-WF mov-to-output (floc fs0) (falloc fs0) nh0 tt
      nh2 : halted (floc fs2) ≡ false
      nh2 = exec-abstract-preserves-halted-WF (store-at-slot payload-stash) (floc fs1) (falloc fs1) nh1 tt
      nh3 : halted (floc fs3) ≡ false
      nh3 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc fs2) (falloc fs2) nh2 tt
      nh4 : halted (floc fs4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF (store-at-slot sum-stash) (floc fs3) (falloc fs3) nh3 tt
      nh5 : halted (floc fs5) ≡ false
      nh5 = exec-abstract-preserves-halted-WF mov-to-input (floc fs4) (falloc fs4) nh4 tt
      nh6 : halted (floc fs6) ≡ false
      nh6 = exec-abstract-preserves-halted-WF (instr-load-tag-lit 1) (floc fs5) (falloc fs5) nh5 tt
      nh7 : halted (floc fs7) ≡ false
      nh7 = exec-abstract-preserves-halted-WF store-indirect (floc fs6) (falloc fs6) nh6 wf-store-ind
      nh8 : halted (floc fs8) ≡ false
      nh8 = exec-abstract-preserves-halted-WF (load-from-slot payload-stash) (floc fs7) (falloc fs7) nh7 wf-load-payload
      nh9 : halted (floc fs9) ≡ false
      nh9 = exec-abstract-preserves-halted-WF store-indirect-suc (floc fs8) (falloc fs8) nh8 wf-store-ind-suc
      nh10 : halted (floc fs10) ≡ false
      nh10 = exec-abstract-preserves-halted-WF (load-from-slot sum-stash) (floc fs9) (falloc fs9) nh9 wf-load-sum

      run : FlatSteps prog 10 fs0 fs10
      run = (nh0 , span 0 _ refl) ∷ (nh1 , span 1 _ refl) ∷ (nh2 , span 2 _ refl)
          ∷ (nh3 , span 3 _ refl) ∷ (nh4 , span 4 _ refl) ∷ (nh5 , span 5 _ refl)
          ∷ (nh6 , span 6 _ refl) ∷ (nh7 , span 7 _ refl) ∷ (nh8 , span 8 _ refl)
          ∷ (nh9 , span 9 _ refl) ∷ []

      -- D174 / D173's payoff, STATED SO THE TYPECHECKER RULES ON IT.
      -- `instr-alloc-heap 2` runs at fs2→fs3. `AI.alloc-impl n s` is the
      -- concrete bump allocator: it returns `heap-loc (mkHeapRef s) 0` and
      -- leaves `suc s` behind, so the block's ref-id IS the pre-state frontier
      -- and the post-state frontier is its successor. Instructions 3-9 do not
      -- allocate, so `falloc fs10 ≡ falloc fs3` definitionally.
      --
      -- THIS IS WHAT `stack-before` COULD NOT DO. Its premise is
      -- `k < next-slot alloc`, and the emitter writes slot `n` with
      -- `next-slot alloc ≤ n` given — so it would need `k < next-slot ≤ k`.
      -- The heap path inverts it: the allocation MOVES the frontier past the
      -- address it just handed out.
      -- Instructions 3-9 do not allocate, so the frontier they leave is the
      -- one the allocation set. NOT definitional — `falloc fs10` is a nest of
      -- seven `exec-abstract` applications — so it is a `trans` chain over
      -- `exec-abstract-preserves-heap-ref`, whose per-instruction witness is
      -- `tt` for every effect class except `eff-heap-alloc`.
      heapref-fs10 : next-heap-ref (falloc fs10) ≡ suc (next-heap-ref (falloc fs2))
      heapref-fs10 =
        trans (exec-abstract-preserves-heap-ref (load-from-slot sum-stash) (floc fs9) (falloc fs9) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc fs8) (falloc fs8) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot payload-stash) (floc fs7) (falloc fs7) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect (floc fs6) (falloc fs6) tt)
       (trans (exec-abstract-preserves-heap-ref (instr-load-tag-lit 1) (floc fs5) (falloc fs5) tt)
       (trans (exec-abstract-preserves-heap-ref mov-to-input (floc fs4) (falloc fs4) tt)
              (exec-abstract-preserves-heap-ref (store-at-slot sum-stash) (floc fs3) (falloc fs3) tt))))))

      before : BeforeFrontier (falloc fs10) sum-loc
      before = BeforeFrontier.heap-before
                 (subst (λ m → next-heap-ref (falloc fs2) < m) (sym heapref-fs10) (n<1+n _))

      -- ── THE TAG CELL, written by `store-indirect` at fs6→fs7 and carried to
      -- fs10 past one heap write (the payload, a DIFFERENT cell) and two
      -- register-only loads.
      tagout-fs6 : readReg (regs (floc fs6)) Output ≡ SV-Tag 1
      tagout-fs6 = writeReg-same (regs (floc fs5)) Output (SV-Tag 1)

      tag-fs7 : MemOps.readLoc (floc fs7) sum-loc ≡ just (SV-Tag 1)
      tag-fs7 = trans (store-ind-result (floc fs6) (falloc fs6) sum-hl rdi-fs6)
                      (cong just tagout-fs6)

      tag-fs10 : MemOps.readLoc (floc fs10) sum-loc ≡ just (SV-Tag 1)
      tag-fs10 =
        trans (heap-untouched (load-from-slot sum-stash) (floc fs9) (falloc fs9)
                 sum-hl nhw-load-from-slot)
       (trans (store-ind-suc-preserves-heap (floc fs8) (falloc fs8) sum-hl sum-hl
                 rdi-fs8 (sucHL-≢ sum-hl))
       (trans (heap-untouched (load-from-slot payload-stash) (floc fs7) (falloc fs7)
                 sum-hl nhw-load-from-slot)
              tag-fs7))

      -- ── THE PAYLOAD CELL, written by `store-indirect-suc` at fs8→fs9.
      payout-fs8 : readReg (regs (floc fs8)) Output ≡ pv
      payout-fs8 = load-slot-result payload-stash (floc fs7) (falloc fs7) pv
                     (proj₂ wf-load-payload)

      pay-fs10 : MemOps.readLoc (floc fs10) (sucLoc sum-loc) ≡ just pv
      pay-fs10 =
        trans (heap-untouched (load-from-slot sum-stash) (floc fs9) (falloc fs9)
                 (sucHL sum-hl) nhw-load-from-slot)
       (trans (store-ind-suc-result (floc fs8) (falloc fs8) sum-hl rdi-fs8)
              (cong just payout-fs8))

      -- ── THE RESULT POINTER: instruction 9 loads the stashed sum pointer.
      sv≡ptr : sv ≡ SV-Ptr sum-loc
      sv≡ptr = writeReg-same (regs (floc fs2)) Output (SV-Ptr (AtDynamic sum-hl))

      out-eq : readReg (regs (floc fs10)) Output ≡ SV-Ptr sum-loc
      out-eq = trans (load-slot-result sum-stash (floc fs9) (falloc fs9) sv
                        (proj₂ wf-load-sum)) sv≡ptr

      -- `sucHL` keeps the ref, so the successor cell is before the same
      -- frontier by the same proof.
      before-suc : BeforeFrontier (falloc fs10) (sucLoc sum-loc)
      before-suc = BeforeFrontier.heap-before
                     (subst (λ m → next-heap-ref (falloc fs2) < m) (sym heapref-fs10) (n<1+n _))

      -- `validityWF-frontier-advance`'s three premises. None of the ten is a
      -- frame or stack-allocation op, so `current-frame` and `next-slot` are
      -- the same at the end as at the start — but NOT definitionally: the
      -- `with`-blocks in `load-from-slot` and the indirect stores block
      -- reduction, so each is a `trans` chain, exactly like `heapref-fs10`.
      cf-fs10 : current-frame (falloc fs10) ≡ current-frame alloc
      cf-fs10 =
        trans (exec-abstract-preserves-frame (load-from-slot sum-stash) (floc fs9) (falloc fs9))
       (trans (exec-abstract-preserves-frame store-indirect-suc (floc fs8) (falloc fs8))
       (trans (exec-abstract-preserves-frame (load-from-slot payload-stash) (floc fs7) (falloc fs7))
       (trans cf-fs7
              (exec-abstract-preserves-frame mov-to-output (floc fs0) (falloc fs0)))))

      nextslot-fs10 : next-slot (falloc fs10) ≡ next-slot alloc
      nextslot-fs10 =
        trans (exec-abstract-preserves-next-slot (load-from-slot sum-stash) (floc fs9) (falloc fs9) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect-suc (floc fs8) (falloc fs8) tt)
       (trans (exec-abstract-preserves-next-slot (load-from-slot payload-stash) (floc fs7) (falloc fs7) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect (floc fs6) (falloc fs6) tt)
       (trans (exec-abstract-preserves-next-slot (instr-load-tag-lit 1) (floc fs5) (falloc fs5) tt)
       (trans (exec-abstract-preserves-next-slot mov-to-input (floc fs4) (falloc fs4) tt)
       (trans (exec-abstract-preserves-next-slot (store-at-slot sum-stash) (floc fs3) (falloc fs3) tt)
       (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc fs2) (falloc fs2) tt)
       (trans (exec-abstract-preserves-next-slot (store-at-slot payload-stash) (floc fs1) (falloc fs1) tt)
              (exec-abstract-preserves-next-slot mov-to-output (floc fs0) (falloc fs0) tt)))))))))

      nextslot-≤ : next-slot alloc ≤ next-slot (falloc fs10)
      nextslot-≤ = ≤-reflexive (sym nextslot-fs10)

      heapref-≤ : next-heap-ref alloc ≤ next-heap-ref (falloc fs10)
      heapref-≤ = subst (λ m → next-heap-ref alloc ≤ m) (sym heapref-fs10) (n≤1+n _)

      -- …and the same weakening for `BeforeFrontier` itself: the frontier only
      -- ever advances, so anything before it stays before it.
      bf-advance : ∀ {l : ValueLocation FS} → BeforeFrontier alloc l
                 → BeforeFrontier (falloc fs10) l
      bf-advance (BeforeFrontier.stack-before f≡cf k<ns) =
        BeforeFrontier.stack-before (trans f≡cf (sym cf-fs10)) (<-≤-trans k<ns nextslot-≤)
      bf-advance (BeforeFrontier.stack-ancestor cf≺f src) =
        BeforeFrontier.stack-ancestor
          (subst (λ c → Once.CCC.FrameSemantics.FrameSemantics._≺_ FS c _)
                 (sym cf-fs10) cf≺f) src
      bf-advance (BeforeFrontier.heap-before r<h) =
        BeforeFrontier.heap-before (<-≤-trans r<h heapref-≤)

      -- `with inp` is not available: `inp` is bound by the parent clause's
      -- patterns. Take it as an argument instead — the standing preference for
      -- a top-level helper over a with-block.
      place-of : InputAt mIn alloc x s
               → ResultPlace (A IRTy.+ B) Heap (falloc fs10) (falloc fs10)
                             (TM.valueT (evalᴰ (inr {A} {B}) x) k) (floc fs10)
      -- A register-resident payload needs NO payload location and NO payload
      -- validity — stage F's whole point. Fully proved.
      place-of (in-reg fit eq) =
        at-loc sum-loc
          (valid-inr-reg-wf tt tag-fs10 (rep-prim fit)
             (trans pay-fs10 (cong just (trans pv≡in eq))) before-suc)
          before out-eq
          (valid-inr-reg-wf tt tag-fs10 (rep-prim fit)
             (trans pay-fs10 (cong just (trans pv≡in eq))) before-suc)
          before
        where
          pv≡in : pv ≡ readReg (regs s) Input1
          pv≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)
      -- A unit payload has no residence at all (D074): `rep-unit` takes
      -- whatever the cell happens to hold. Fully proved.
      place-of (in-unit refl) =
        at-loc sum-loc
          (valid-inr-reg-wf tt tag-fs10 (rep-unit refl pv) pay-fs10 before-suc)
          before out-eq
          (valid-inr-reg-wf tt tag-fs10 (rep-unit refl pv) pay-fs10 before-suc)
          before
      -- A memory-resident payload: the cell holds `SV-Ptr loc`, and the
      -- INPUT's own validity has to be carried across the chain. That is the
      -- one residual — see `inr-mem-pres` above.
      place-of (in-loc loc valid bf eq) =
        at-loc sum-loc (mk-valid eq) before out-eq (mk-valid eq) before
        where
          pv≡ptr : ∀ (e : readReg (regs s) Input1 ≡ SV-Ptr loc) → pv ≡ SV-Ptr loc
          pv≡ptr e = trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) e

          valid' : ValidAtWF mIn (falloc fs10) x loc (floc fs10)
          valid' =
            validityWF-frontier-advance x loc (floc fs10)
              cf-fs10 nextslot-≤ heapref-≤
              (validityWF-mem-preserved x loc s (floc fs10) bf
                 (λ loc' bf' → TSP.mem-pres nhw-instr-load-tag-lit refl
                                 nhw-load-from-slot refl n≤ rdi-fs6 rdi-fs8 loc'
                                 (frontier-monotone alloc (record alloc { next-slot = n })
                                    refl n≤ ≤-refl loc' bf'))
                 valid)

          mk-valid : ∀ (e : readReg (regs s) Input1 ≡ SV-Ptr loc)
                   → ValidAtWF Heap (falloc fs10) (TM.valueT (evalᴰ (inr {A} {B}) x) 0) sum-loc (floc fs10)
          mk-valid e =
            valid-inr-wf tt tag-fs10 (trans pay-fs10 (cong just (pv≡ptr e)))
              (bf-advance bf) before-suc valid'

      place : ResultPlace (A IRTy.+ B) Heap (falloc fs10) (falloc fs10)
                          (TM.valueT (evalᴰ (inr {A} {B}) x) k) (floc fs10)
      place = place-of inp

  ------------------------------------------------------------------------
  -- D181: `curry` — DISCHARGED, and it is `obs-correct-inl`'s twin.
  --
  -- The emitter builds the closure record with the SAME ten-instruction heap
  -- build as a sum, differing only in what goes into the two cells:
  --   mov-to-output ∷ store-at-slot env-stash ∷ instr-alloc-heap 2 ∷
  --   store-at-slot closure-stash ∷ mov-to-input ∷ load-from-slot env-stash ∷
  --   store-indirect ∷ instr-load-code-addr (ℓ o l) ∷ store-indirect-suc ∷
  --   load-from-slot closure-stash
  -- (`inl` writes a tag then the payload; `curry` writes the ENV then the
  -- body's code address.)
  --
  -- D179 IS WHAT MAKES THE VALUE HALF LAND. `evalᴰ (curry body) x` is
  -- `returnT (λ b → evalᴰ body (x , b))`, and `valid-closure-wf`'s index is
  -- `λ arg → evalᴰ body (env , arg)` — the SAME term, with `env := x`. Before
  -- the re-index the two sides named different semantics and no amount of
  -- machine reasoning could have closed the gap.
  ------------------------------------------------------------------------
  ------------------------------------------------------------------------
  -- D190: THE TWO-CELL HEAP BUILD, ONCE.
  --
  -- `curry` and `Ana` emit the SAME ten instructions. That is not a
  -- coincidence to be noted in a comment: a closure and a ν-suspension are
  -- the same machine object — a value cell plus the code that consumes it —
  -- and the only thing that differs is which `ValidAtWF` constructor the
  -- resulting two cells witness. So everything up to that choice lives here,
  -- and each clause supplies only its `ResultPlace`.
  --
  -- WHAT THIS EXPORTS is the full straight-line story: the ten states, the
  -- run, `halted ≡ false` throughout, the object's location and the fact it
  -- is before the frontier, the two cell reads (`cell0-fs10`, `code-fs10`),
  -- the result pointer (`out-eq`), and `valid-transport` — the input's own
  -- validity carried across the ten steps via D182's `TenStepPres`.
  ------------------------------------------------------------------------

