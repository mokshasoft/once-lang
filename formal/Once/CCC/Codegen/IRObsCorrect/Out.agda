-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Out
--
-- D200: `Out` — forcing a ν (D199). `apply`'s argument with the pair-packing
-- removed: a suspension IS the callee record, so the setup is three rows, and
-- the hand-off is to the ν's own force (`NuV.nu-force`, plan 0.125 S1).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Out (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore using (AllocState; AbstractTrace; LocState; StoredValue; instr-save-closure-reg; load-indirect; mov-to-input; readReg; Input1; SV-Ptr; writeReg-same; Output; sucLoc; SV-Code; instr-call-closure; sv-as-loc; module LocState)
open LocState using (regs; halted)
open import Once.IRTy using (WellFormedFI; ν-type; ⟦_⟧TI)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IRTy as IRTy′
import Once.IR
open import Data.List.Properties using (++-identityʳ)
open import Once.Internal.Res using (is-stopped)
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Internal.Trace as TM
open import Once.Internal.Res using (returns)
open import Once.Denotation.Approx using (done; NotCut; budgetLeft)

module OutC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

  module OutSetupPres
    (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    where

    b0 b1 b2 b3 : FlatState
    b0 = entry-flat base s alloc cl rs
    b1 = flat-exec-instr instr-save-closure-reg prog b0
    b2 = flat-exec-instr load-indirect          prog b1
    b3 = flat-exec-instr mov-to-input           prog b2

    -- Every proof below is `abstract`: each is a `trans`-chain used only for
    -- its TYPE, and leaving the bodies transparent makes every downstream use
    -- renormalise the four-state machine underneath them.
    abstract

     -- Nothing writes memory, so every cell reads the same at `b3` as at entry.
     mem-pres : ∀ (loc : ValueLocation FS)
             → SMCore.MemOps.readLoc (floc b3) loc ≡ SMCore.MemOps.readLoc s loc
     mem-pres loc =
      trans (mem-untouched mov-to-input (floc b2) (falloc b2) loc nhw-mov-to-input refl)
            (mem-untouched load-indirect (floc b1) (falloc b1) loc nhw-load-indirect refl)

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
              → SMCore.MemOps.readLoc s ν-loc ≡ just sv
              → readReg (regs (floc b3)) Input1 ≡ sv
     input1-b3 ν-loc sv rdi cell =
      trans (writeReg-same (regs (floc b2)) Input1 (readReg (regs (floc b2)) Output))
            (exec-abstract-load-indirect-output (floc b1) (falloc b1) ν-loc sv rdi cell)

  obs-correct-Out : ∀ {F} (wf : WellFormedFI F) → IRObsCorrectF (Out wf)
  -- A ν is a two-cell heap object: it fits no register, and it is not `Unit`.
  obs-correct-Out wf n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh (in-reg () _) k rs
  obs-correct-Out wf n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh (in-unit ()) k rs
  -- D184 pins a suspension to the HEAP, and `do-call` enters on no other
  -- shape, so the stack case is refuted by the witness's own `LocMatchesMode`.
  obs-correct-Out {F} wf n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh
    (in-loc (AtStack _ _) valid bf rdi) k rs = stack-refuted valid
    where
      stack-refuted : ValidAtWF {prog = prog} mIn alloc {ν-type F} x (AtStack _ _) s
                    → MachineRefinesObsF prog base n l (Out wf) x s alloc cl rs k
      stack-refuted (valid-ν-wf nv) = ⊥-elim (nu-heap nv)
  obs-correct-Out {F} wf n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh
    (in-loc (AtDynamic ν-hl) valid bf rdi) k rs = go x valid
    where
      ν-loc : ValueLocation FS
      ν-loc = AtDynamic ν-hl

      module OSP = OutSetupPres prog base s alloc cl rs

      -- The VALUE is an argument, not the clause's `x`. Matching
      -- `valid-ν-susp-wf` has to FORCE the ν it is a witness for — it is the
      -- constructor's own index — and a variable bound by the enclosing clause
      -- cannot be forced, so the match instead tried to solve the
      -- constructor's `coalg`/`seed` out of an opaque `x` and got stuck. That
      -- is the same stuckness that surfaced earlier as unsolved `_coalg` metas.
      go : ∀ (v : ⟦ ν-type F ⟧)
         → ValidAtWF {prog = prog} mIn alloc {ν-type F} v ν-loc s
         → MachineRefinesObsF prog base n l (Out wf) v s alloc cl rs k
      -- plan 0.125 S1: the witness is the ν's FORCE (`NuV`), so the run is
      -- read off the value: the seed cell, the code cell and its label, and
      -- what calling that block on the seed does.
      go v (valid-ν-wf nv) = assemble
        where
          ν-val : ⟦ ν-type F ⟧
          ν-val = v

          lbl     = nu-lbl nv
          j       = nu-j nv
          seed-sv = nu-seed nv
          c0      = nu-cell0 nv
          cp      = nu-cell1 nv
          feq     = nu-code nv

          -- Opaque for `OutSetupPres`'s reason: the call's three-level view is
          -- consumed only through `cong`, never reduced.
          abstract
           code-cell-b3 : SMCore.MemOps.readLoc (floc OSP.b3) (sucLoc ν-loc)
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

          assemble : MachineRefinesObsF prog base n l (Out wf) ν-val s alloc cl rs k
          assemble = record
            { value-realized =
                realized (4 + CalleeRun.steps crun) (CalleeRun.settle crun)
                         (CalleeRun.out-mode crun) (CalleeRun.cont-alloc crun)
                         run (λ p → CalleeRun.live crun (trans st-eq p))
                         (λ p → CalleeRun.returned crun (trans res-eq p))
                         (λ p → proj₁ (CalleeRun.stops crun (trans st-eq p))
                              , trans (proj₂ (CalleeRun.stops crun (trans st-eq p)))
                                      (chain-left run4 (trans (cong (λ st → halted (floc st)) call-eq) nh3)))
                         (λ p → CalleeRun.no-ret crun (trans res-eq p)) (λ nc → CalleeRun.no-link crun (nc′ nc))
                         (trans (CalleeRun.log crun) (cong₂ DL._++_ h-eq (cong proj₁ RE)))
                         place
                         (progress-≤ (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (CalleeRun.run crun)) res-eq (CalleeRun.progress crun))
                                     (ctrls-≤ʳ run4 (CalleeRun.run crun)))
                         (λ nc fr j bf → mem-pres-out nc (AtStack fr j) bf)
                         (λ nc hl bf → mem-pres-out nc (AtDynamic hl) bf)
                         (λ p → CalleeRun.frame-pres crun (trans res-eq p) alloc (cong falloc call-eq))
                         bf-mono-out
                         (λ p → CalleeRun.frames-pres crun (trans res-eq p) alloc (cong falloc call-eq))
            ; traces-agree = trc
            }
            where
              nh1 : halted (floc OSP.b1) ≡ false
              nh1 = nh
              nh2 : halted (floc OSP.b2) ≡ false
              nh2 = exec-abstract-preserves-halted-WF load-indirect
                      (floc OSP.b1) (falloc OSP.b1) nh1
                      (ν-loc , cong sv-as-loc rdi , seed-sv , c0)
              nh3 : halted (floc OSP.b3) ≡ false
              nh3 = exec-abstract-preserves-halted-WF mov-to-input
                      (floc OSP.b2) (falloc OSP.b2) nh2 tt

              crun : CalleeRun prog (flat-exec-instr instr-call-closure prog OSP.b3)
                       (suc (fpc OSP.b3)) rs (⟦ F ⟧TI (ν-type F))
                       (evalᴰ (Out wf) ν-val) k
              crun = crun-map ν-layer-place
                       (nu-force nv wf (flat-exec-instr instr-call-closure prog OSP.b3)
                       (falloc OSP.b3) (suc (fpc OSP.b3)) k rs
                       (trans (cong fpc call-eq) refl)
                       (trans (cong (λ st → halted (floc st)) call-eq) nh3)
                       (trans (cong fret call-eq) refl)
                       (trans (cong falloc call-eq) refl)
                       n≤
                       (λ _ b → b)
                       (λ l _ → trans (cong (λ st → SMCore.MemOps.readLoc (floc st) l) call-eq) (OSP.mem-pres l))
                       (subst (λ st → readReg (regs st) Input1 ≡ seed-sv)
                              (sym (cong floc call-eq)) (OSP.input1-b3 ν-loc seed-sv rdi c0)))

              run4 : FlatSteps prog 4 (entry-flat base s alloc cl rs)
                       (flat-exec-instr instr-call-closure prog OSP.b3)
              run4 = (nh , span 0 _ refl) ∷ (nh1 , span 1 _ refl)
                   ∷ (nh2 , span 2 _ refl) ∷ (nh3 , span 3 _ refl) ∷ []

              run : FlatSteps prog (4 + CalleeRun.steps crun)
                      (entry-flat base s alloc cl rs) (CalleeRun.settle crun)
              run = FlatSteps-++ run4 (CalleeRun.run crun)

              -- plan 0.97: the callee's computation IS `evalᴰ (Out wf) ν-val`
              -- here (no closure equation to spend, unlike `apply`), so the
              -- conditioned fields transfer verbatim.
              -- plan 0.105: …from the caller's log, since the three setup
              -- rows and the call make no call of their own.
              callFs = flat-exec-instr instr-call-closure prog OSP.b3
              h-eq : SMCore.LocState.ev-log (floc callFs) ≡ SMCore.LocState.ev-log s
              h-eq = trans (log-of run4 refl) (++-identityʳ _)

              RE : runAt (floc callFs) (⟪ evalᴰ (Out wf) ν-val ⟫ k) ≡ runAt s (⟪ evalᴰ (Out wf) ν-val ⟫ k)
              RE = runAt-≡ {st = floc callFs} {st′ = s} {m = ⟪ evalᴰ (Out wf) ν-val ⟫ k} {m′ = ⟪ evalᴰ (Out wf) ν-val ⟫ k} h-eq refl

              res-eq : resultAt (floc callFs) (⟪ evalᴰ (Out wf) ν-val ⟫ k) ≡ resultAt s (⟪ evalᴰ (Out wf) ν-val ⟫ k)
              res-eq = cong proj₂ RE

              nc′ : NotCut (resultAt s (⟪ evalᴰ (Out wf) ν-val ⟫ k)) → NotCut (resultAt (floc callFs) (⟪ evalᴰ (Out wf) ν-val ⟫ k))
              nc′ = subst NotCut (sym res-eq)

              st-eq : stopsAt (floc callFs) (⟪ evalᴰ (Out wf) ν-val ⟫ k) ≡ stopsAt s (⟪ evalᴰ (Out wf) ν-val ⟫ k)
              st-eq = cong (λ r → is-stopped (proj₂ r)) RE

              place : ∀ {v r} → resultAt s (⟪ evalᴰ (Out wf) ν-val ⟫ k) ≡ returns (done v r)
                    → ResultPlace (⟦ F ⟧TI (ν-type F)) (CalleeRun.out-mode crun)
                        (falloc (CalleeRun.settle crun)) (CalleeRun.cont-alloc crun)
                        v (floc (CalleeRun.settle crun))
              place p = CalleeRun.place crun (trans (cong proj₂ RE) p)

              trc : chain-events run ≡ eventsAt s (⟪ evalᴰ (Out wf) ν-val ⟫ k)
              trc = trans (chain-events-++ run4 (CalleeRun.run crun))
                          (trans (CalleeRun.events crun) (cong proj₁ RE))

              -- D204: what the WHOLE force leaves alone — the three setup rows
              -- (which write no memory at all) composed with the callee's own
              -- preservation. `falloc OSP.b3` IS `alloc` definitionally, so
              -- the `enter-call` premise the callee wants is `refl`.
              -- `falloc OSP.b3` IS `alloc` (neither setup row touches the
              -- allocator), so the frontier only moves at the call.
              bf-mono-out : NotCut (resultAt s (⟪ evalᴰ (Out wf) ν-val ⟫ k))
                          → ∀ (m : ℕ) (loc : ValueLocation FS)
                          → BeforeFrontier (record alloc { next-slot = m }) loc
                          → BeforeFrontier
                              (record (falloc (CalleeRun.settle crun)) { next-slot = m }) loc
              bf-mono-out nc m loc bf =
                CalleeRun.bf-mono crun (nc′ nc) alloc m (cong falloc call-eq) loc bf

              mem-pres-out : NotCut (resultAt s (⟪ evalᴰ (Out wf) ν-val ⟫ k))
                           → ∀ (loc : ValueLocation FS)
                           → BeforeFrontier (record alloc { next-slot = n }) loc
                           → SMCore.MemOps.readLoc (floc (CalleeRun.settle crun)) loc
                             ≡ SMCore.MemOps.readLoc s loc
              mem-pres-out nc loc bf =
                trans (CalleeRun.mem-pres crun (nc′ nc) alloc n
                         (trans (cong falloc call-eq) refl) loc bf)
                      (trans (cong (λ st → SMCore.MemOps.readLoc (floc st) loc) call-eq)
                             (OSP.mem-pres loc))



