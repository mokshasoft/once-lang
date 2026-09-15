-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Out
--
-- D200: `Out` — forcing a ν (D199). `apply`'s argument with the pair-packing
-- removed: a suspension IS the callee record, so the setup is three rows, and
-- the hand-off is to `BlockRuns.coalgs`.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Out (o : CanonicalName) where

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

module OutC {FS : FrameSemantics} (program-bound : ℕ) where

  open Core {FS} program-bound
  open Mach {FS} program-bound

  module OutSetupPres
    (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    where

    b0 b1 b2 b3 : FlatState
    b0 = entry-flat base s alloc cl
    b1 = flat-exec-instr instr-save-closure-reg prog b0
    b2 = flat-exec-instr load-indirect          prog b1
    b3 = flat-exec-instr mov-to-input           prog b2

    -- Every proof below is `abstract`: each is a `trans`-chain used only for
    -- its TYPE, and leaving the bodies transparent makes every downstream use
    -- renormalise the four-state machine underneath them.
    abstract

     -- Nothing writes memory, so every cell reads the same at `b3` as at entry.
     mem-pres : ∀ (loc : ValueLocation FS)
             → MemOps.readLoc (floc b3) loc ≡ MemOps.readLoc s loc
     mem-pres loc =
      trans (mem-untouched mov-to-input (floc b2) (falloc b2) loc nhw-mov-to-input refl)
            (mem-untouched load-indirect (floc b1) (falloc b1) loc nhw-load-indirect refl)

     carry : ∀ {mC C} (c : ⟦ C ⟧) (lc : ValueLocation FS)
          → BeforeFrontier alloc lc → ValidAtWF mC alloc {C} c lc s
          → ValidAtWF mC alloc {C} c lc (floc b3)
     carry c lc cb v =
      validityWF-mem-preserved c lc s (floc b3) cb (λ loc' _ → mem-pres loc') v

     -- The closure register holds the ν pointer: row 1 copies `Input1` into it
     -- before row 3 overwrites `Input1` with the seed. That is what the register
     -- is for, and why the save has to precede the load.
     closure-reg : ∀ (ν-loc : ValueLocation FS)
                → readReg (regs s) Input1 ≡ SV-Ptr ν-loc
                → fclosure b3 ≡ SV-Ptr ν-loc
     closure-reg ν-loc rdi = rdi

     -- …and `Input1` ends up holding the SEED CELL's contents, whatever their
     -- representation — which makes the callee's `InputAt` a read-off of the ν's
     -- own `CellAt` rather than a rebuild.
     input1-b3 : ∀ (ν-loc : ValueLocation FS) (sv : StoredValue FS)
              → readReg (regs s) Input1 ≡ SV-Ptr ν-loc
              → MemOps.readLoc s ν-loc ≡ just sv
              → readReg (regs (floc b3)) Input1 ≡ sv
     input1-b3 ν-loc sv rdi cell =
      trans (writeReg-same (regs (floc b2)) Input1 (readReg (regs (floc b2)) Output))
            (exec-abstract-load-indirect-output (floc b1) (falloc b1) ν-loc sv rdi cell)

  obs-correct-Out : ∀ {F} (wf : WellFormedFI F) → IRObsCorrectF (Out wf)
  -- A ν is a two-cell heap object: it fits no register, and it is not `Unit`.
  obs-correct-Out wf _ n l prog base _ cr span mIn x s alloc cl n≤ nh (in-reg () _) k
  obs-correct-Out wf _ n l prog base _ cr span mIn x s alloc cl n≤ nh (in-unit ()) k
  -- D184 pins a suspension to the HEAP, and `do-call` enters on no other
  -- shape, so the stack case is refuted by the witness's own `LocMatchesMode`.
  obs-correct-Out {F} wf _ n l prog base _ cr span mIn x s alloc cl n≤ nh
    (in-loc (AtStack _ _) valid bf rdi) k = stack-refuted valid
    where
      stack-refuted : ValidAtWF mIn alloc {ν-type F} x (AtStack _ _) s
                    → MachineRefinesObsF prog base n l (Out wf) x s alloc cl k
      stack-refuted (valid-ν-susp-wf _ lmm _ _ _) = ⊥-elim lmm
  obs-correct-Out {F} wf _ n l prog base _ cr span mIn x s alloc cl n≤ nh
    (in-loc (AtDynamic ν-hl) valid bf rdi) k = go x valid
    where
      ν-loc : ValueLocation FS
      ν-loc = AtDynamic ν-hl

      module OSP = OutSetupPres prog base s alloc cl

      -- The VALUE is an argument, not the clause's `x`. Matching
      -- `valid-ν-susp-wf` has to FORCE the ν it is a witness for — it is the
      -- constructor's own index — and a variable bound by the enclosing clause
      -- cannot be forced, so the match instead tried to solve the
      -- constructor's `coalg`/`seed` out of an opaque `x` and got stuck. That
      -- is the same stuckness that surfaced earlier as unsolved `_coalg` metas.
      go : ∀ (v : ⟦ ν-type F ⟧)
         → ValidAtWF mIn alloc {ν-type F} v ν-loc s
         → MachineRefinesObsF prog base n l (Out wf) v s alloc cl k
      -- The two functor witnesses — the one on the `Out` node and the one the
      -- suspension was built with — are identified ONCE, by `rewrite`, rather
      -- than transported at each use. Carrying the equation instead costs two
      -- `subst`s whose motives mention `evalᴰ (Out w) x`, and normalising that
      -- motive is what made this clause alone double the module's peak memory.
      go _ (valid-ν-susp-wf {A = A} wf' {coalg = coalg} {seed = seed}
                            {coalg-label = lbl} lmm sc cp slb)
        rewrite WellFormedFI-irrelevant wf' wf = assemble sc
        where
          -- The seed's residence, split exactly as `apply` splits its
          -- argument's — and the MODE comes out of the split too, because a
          -- boxed seed is `in-loc` at the cell's own mode and an inline one is
          -- `in-reg`, which has no mode at all.
          seed-sv-of : CellAt alloc A seed ν-loc s → StoredValue FS
          seed-sv-of (cell-ptr {comp-loc = cl'} _ _ _) = SV-Ptr cl'
          seed-sv-of (cell-inline rep _)               = inline-sv rep seed

          seed-cell-of : (c : CellAt alloc A seed ν-loc s)
                       → MemOps.readLoc s ν-loc ≡ just (seed-sv-of c)
          seed-cell-of (cell-ptr q _ _)  = q
          seed-cell-of (cell-inline _ q) = q

          mode-of : CellAt alloc A seed ν-loc s → AllocMode
          mode-of (cell-ptr {mC = m} _ _ _) = m
          mode-of (cell-inline _ _)         = Heap

          input-of : (c : CellAt alloc A seed ν-loc s)
                   → InputAt {A} (mode-of c) alloc seed (floc OSP.b3)
          input-of (cell-ptr {comp-loc = cl'} q cbf cv) =
            in-loc cl' (OSP.carry seed cl' cbf cv) cbf
                   (OSP.input1-b3 ν-loc (SV-Ptr cl') rdi q)
          input-of (cell-inline (rep-prim fit) q) =
            in-reg fit (OSP.input1-b3 ν-loc (prim-sv fit seed) rdi q)
          input-of (cell-inline (rep-unit ueq sv) q) = in-unit ueq

          ν-val : ⟦ ν-type F ⟧
          ν-val = TM.valueT (evalᴰ (Ana wf coalg) seed) 0

          cinfo = BlockRuns.coalgs cr wf coalg seed lbl
                    (valid-ν-susp-wf wf {coalg = coalg} {seed = seed}
                                     {coalg-label = lbl} lmm sc cp slb) cp

          j      = proj₁ cinfo
          feq    = proj₁ (proj₂ cinfo)
          runner = proj₂ (proj₂ cinfo)

          -- Opaque for `OutSetupPres`'s reason: the call's three-level view is
          -- consumed only through `cong`, never reduced.
          abstract
           code-cell-b3 : MemOps.readLoc (floc OSP.b3) (sucLoc ν-loc)
                        ≡ just (SV-Code lbl)
           code-cell-b3 = trans (OSP.mem-pres (sucLoc ν-loc)) cp

           call-eq : flat-exec-instr instr-call-closure prog OSP.b3
                   ≡ record OSP.b3
                       { falloc = enter-call (falloc OSP.b3)
                       ; fret   = suc (fpc OSP.b3) ∷ fret OSP.b3
                       ; flink  = just (suc (fpc OSP.b3))
                       ; fpc    = j }
           call-eq =
             trans (cong (λ z → do-call-sv prog z OSP.b3) (OSP.closure-reg ν-loc rdi))
             (trans (cong (λ z → do-call-code prog z OSP.b3) code-cell-b3)
                    (cong (λ z → do-call-at z OSP.b3) feq))

          assemble : (c : CellAt alloc A seed ν-loc s)
                   → MachineRefinesObsF prog base n l (Out wf) ν-val s alloc cl k
          assemble c = record
            { value-realized =
                realized (4 + CalleeRun.steps crun) (CalleeRun.settle crun)
                         (CalleeRun.out-mode crun) (CalleeRun.cont-alloc crun)
                         run (CalleeRun.live crun) (CalleeRun.returned crun)
                         (CalleeRun.no-ret crun) (CalleeRun.no-link crun) place
                         (λ fr j bf → mem-pres-out (AtStack fr j) bf)
                         (λ hl bf → mem-pres-out (AtDynamic hl) bf)
                         (CalleeRun.frame-pres crun alloc (cong falloc call-eq))
                         bf-mono-out
            ; traces-agree = trc
            }
            where
              nh1 : halted (floc OSP.b1) ≡ false
              nh1 = nh
              nh2 : halted (floc OSP.b2) ≡ false
              nh2 = exec-abstract-preserves-halted-WF load-indirect
                      (floc OSP.b1) (falloc OSP.b1) nh1
                      (ν-loc , cong sv-as-loc rdi , seed-sv-of c , seed-cell-of c)
              nh3 : halted (floc OSP.b3) ≡ false
              nh3 = exec-abstract-preserves-halted-WF mov-to-input
                      (floc OSP.b2) (falloc OSP.b2) nh2 tt

              crun : CalleeRun prog (flat-exec-instr instr-call-closure prog OSP.b3)
                       (suc (fpc OSP.b3)) (⟦ F ⟧TI (ν-type F))
                       (evalᴰ (Out wf) ν-val) k
              crun = runner (flat-exec-instr instr-call-closure prog OSP.b3)
                       (falloc OSP.b3) (suc (fpc OSP.b3)) k (mode-of c)
                       (trans (cong fpc call-eq) refl)
                       (trans (cong (λ st → halted (floc st)) call-eq) nh3)
                       (trans (cong fret call-eq) refl)
                       (trans (cong falloc call-eq) refl)
                       (subst (λ st → InputAt {A} (mode-of c) (falloc OSP.b3) seed st)
                              (sym (cong floc call-eq)) (input-of c))

              -- D204: what the WHOLE force leaves alone — the three setup rows
              -- (which write no memory at all) composed with the callee's own
              -- preservation. `falloc OSP.b3` IS `alloc` definitionally, so
              -- the `enter-call` premise the callee wants is `refl`.
              -- `falloc OSP.b3` IS `alloc` (neither setup row touches the
              -- allocator), so the frontier only moves at the call.
              bf-mono-out : ∀ (m : ℕ) (loc : ValueLocation FS)
                          → BeforeFrontier (record alloc { next-slot = m }) loc
                          → BeforeFrontier
                              (record (falloc (CalleeRun.settle crun)) { next-slot = m }) loc
              bf-mono-out m loc bf =
                CalleeRun.bf-mono crun alloc m (cong falloc call-eq) loc bf

              mem-pres-out : ∀ (loc : ValueLocation FS)
                           → BeforeFrontier (record alloc { next-slot = n }) loc
                           → MemOps.readLoc (floc (CalleeRun.settle crun)) loc
                             ≡ MemOps.readLoc s loc
              mem-pres-out loc bf =
                trans (CalleeRun.mem-pres crun alloc n
                         (trans (cong falloc call-eq) refl) loc bf)
                      (trans (cong (λ st → MemOps.readLoc (floc st) loc) call-eq)
                             (OSP.mem-pres loc))

              run4 : FlatSteps prog 4 (entry-flat base s alloc cl)
                       (flat-exec-instr instr-call-closure prog OSP.b3)
              run4 = (nh , span 0 _ refl) ∷ (nh1 , span 1 _ refl)
                   ∷ (nh2 , span 2 _ refl) ∷ (nh3 , span 3 _ refl) ∷ []

              run : FlatSteps prog (4 + CalleeRun.steps crun)
                      (entry-flat base s alloc cl) (CalleeRun.settle crun)
              run = FlatSteps-++ run4 (CalleeRun.run crun)

              place : ResultPlace (⟦ F ⟧TI (ν-type F)) (CalleeRun.out-mode crun)
                        (falloc (CalleeRun.settle crun)) (CalleeRun.cont-alloc crun)
                        (TM.valueT (evalᴰ (Out wf) ν-val) k)
                        (floc (CalleeRun.settle crun))
              place = CalleeRun.place crun

              trc : take k (chain-events run)
                  ≡ take k (projTrace (evalᴰ (Out wf) ν-val) k)
              trc = trans (cong (take k) (chain-events-++ run4 (CalleeRun.run crun)))
                          (CalleeRun.events crun)



