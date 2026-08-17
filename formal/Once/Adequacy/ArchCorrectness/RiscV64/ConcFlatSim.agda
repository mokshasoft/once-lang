-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim
--
-- riscv64 FILLING THE ENGINE'S INTERFACES (plan 0.65 G2).
--
-- x86-64's copy of this file was 1,631 lines. This one is short because the
-- correspondence engine — the fuel induction, the per-instruction dispatch,
-- the invariant, the SigOp reductions — now lives in `FlatCore` and is written
-- once. What is left is exactly what a MACHINE owes, and this module is the
-- measurement of how much that is:
--
--   Emitter    how a trace lowers, and the label scans. Already proved in
--              `RiscV64/FlatComposition` — this only bundles it.
--   Machine    the state readouts plus six equations about `exec`, each `refl`
--              once the boolean is rewritten. riscv64's `exec` has the same
--              five clauses as x86-64's, so these are the same six proofs.
--   TraceLoop  `RiscV64/RunTrace`'s telescope, plus `nonhalt-noncall`.
--
-- `Supply` — the block-steps and the resource bounds — is NOT here yet: ten of
-- the 42 block-steps are still missing at riscv64, four of them behind the
-- CALL WINDOW. See the handoff for the measured list.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.CCC.Target.RiscV64.Syntax using (slot-size)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.CanonicalName using (CanonicalName)
-- imported UNAPPLIED, so the module's own `FS`/`word-eq` can be threaded into
-- the resource parameter's type — a parameter's type is elaborated before the
-- body, where the applied `open import … FS word-eq` has not run.
import Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation as FSimr
import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence as FCr
import Once.Adequacy.ArchCorrectness.FlatCore.RunContext as RCr
import Once.CCC.Target.RiscV64.Semantics as RS
open import Once.CCC.Machine.SMCore using (AbstractTrace; lea-slot)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Target.RiscV64.Syntax using (sp)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (slot-to-disp)
open import Data.Nat using (ℕ; _+_; _<_)
open import Data.Maybe using (just)

module Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim
  (o : CanonicalName)
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  -- THE SLOT ADDRESS DOES NOT WRAP (plan 0.70 class, D087). riscv64 has no
  -- `lea`: it computes a slot's address with `addi`, a REAL add, so its
  -- `block-step-lea-slot` needs a range fact that x86-64's route never had.
  --
  -- CONDITIONED ON `RunAt`, and it took the 2026-07-30 probe to put it there
  -- (2026-08-16). Stated first without the run context — the engine's
  -- `bs-lea-slot` field handed an arch only `(cc, h, ft)`, because that is
  -- what it passed on x86-64 — and in that form it is REFUTABLE: a hand-picked
  -- `prog ≡ lea-slot modulus ∷ []` satisfies the empty-view correspondence
  -- while the conclusion says `modulus * 8 < modulus`. A correspondence does
  -- not bound a slot INDEX; `RunAt` does. See `ResourceBounds.SlotAddrNoWrap`.
  (slot-addr-no-wrap :
     ∀ {hv : FCr.HeapView FS word-eq} (prog : AbstractTrace)
       (fs : FlatMachine.FlatState {FS}) (s : RS.State) (slot : ℕ)
     → RCr.RunAt o FS slot-size word-eq prog fs
     → FSimr.CompiledCorr o FS word-eq hv prog fs s
     → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs) ≡ just (lea-slot slot)
     → RS.readReg (RS.State.regs s) sp + slot-to-disp slot < RS.W.modulus)
  where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong)

open import Once.CCC.Target.RiscV64.Syntax using
  ( Reg; Instr; Program; label
  ; ld; sd; add; sub; addi; li; auipc; lla; mv; beq; bne; jal; jalr; j; ret
  ; call; call-sym; nop; unimp )
import Once.CCC.Target.RiscV64.Semantics as R
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-abstract; compile-trace)
open import Once.Adequacy.ArchCorrectness.RiscV64.RegRoles using (riscv64-roles)
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition FS using
  (is-label?; skip-law; label-hit; label-miss; headView)
open import Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas using (execInstr-ld)
open import Once.Adequacy.CPU.RiscV64 using (ev-riscv64; arith-env-riscv64)
open import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 using (val-riscv64)
open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Arith.Backend.RiscV64.Dispatch using (dispatch-arith)
import Once.Arith.Backend.RiscV64.RunTrace as RTr
import Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface as EI
import Once.Adequacy.ArchCorrectness.FlatCore.EventEngine as Engine
import Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch as Dispatch

------------------------------------------------------------------------
-- HOW FUEL PEELS. Six premise-free readouts of `Semantics.exec`, one branch
-- at a time — the only thing the generic engine needs from its definition.
-- Identical to x86-64's, because the two `exec`s are written identically.
------------------------------------------------------------------------
r-exec-zero : ∀ prog s → R.exec 0 prog s ≡ just s
r-exec-zero prog s = refl

r-exec-halted : ∀ n prog s → R.State.halted s ≡ true → R.exec (suc n) prog s ≡ just s
r-exec-halted n prog s h rewrite h = refl

-- past the end: the machine halts IN PLACE, so whatever `exec` lands on is halted
r-exec-end : ∀ n prog s {s'} → R.State.halted s ≡ false
           → R.fetch prog (R.State.pc s) ≡ nothing
           → R.exec (suc n) prog s ≡ just s' → R.State.halted s' ≡ true
r-exec-end n prog s {s'} h ftn eq =
  sym (cong R.State.halted (just-injective (trans (sym step) eq)))
  where step : R.exec (suc n) prog s ≡ just (record s { halted = true })
        step rewrite h | ftn = refl

-- (`ins` rather than `j` for the fetched instruction: riscv64 HAS an
-- instruction constructor called `j`.)
r-exec-stuck : ∀ n prog s ins → R.State.halted s ≡ false
             → R.fetch prog (R.State.pc s) ≡ just ins
             → R.execInstr prog s ins ≡ nothing → R.exec (suc n) prog s ≡ nothing
r-exec-stuck n prog s ins h ftq exn rewrite h | ftq | exn = refl

r-exec-step-halt : ∀ n prog s ins s₁ → R.State.halted s ≡ false
                 → R.fetch prog (R.State.pc s) ≡ just ins
                 → R.execInstr prog s ins ≡ just s₁ → R.State.halted s₁ ≡ true
                 → R.exec (suc n) prog s ≡ just s₁
r-exec-step-halt n prog s ins s₁ h ftq exq h1 rewrite h | ftq | exq | h1 = refl

r-exec-step-run : ∀ n prog s ins s₁ → R.State.halted s ≡ false
                → R.fetch prog (R.State.pc s) ≡ just ins
                → R.execInstr prog s ins ≡ just s₁ → R.State.halted s₁ ≡ false
                → R.exec (suc n) prog s ≡ R.exec n prog s₁
r-exec-step-run n prog s ins s₁ h ftq exq h1 rewrite h | ftq | exq | h1 = refl

------------------------------------------------------------------------
-- THE ONE ISA ENUMERATION the trace backbone needs: a step that leaves the
-- machine RUNNING was not a `call-sym`, because `execInstr (call-sym _)`
-- always halts. One clause per instruction; the `call-sym` case is the absurd
-- one, ruled out by the halt clash.
------------------------------------------------------------------------
r-nonhalt-noncall : ∀ prog s ins {s₁} → R.execInstr prog s ins ≡ just s₁
                  → R.State.halted s₁ ≡ false → RTr.matchCall ins ≡ nothing
r-nonhalt-noncall prog s (call-sym lbl) eq hnh
  with trans (cong R.State.halted (just-injective eq)) hnh
... | ()
r-nonhalt-noncall prog s (ld _ _ _)   eq hnh = refl
r-nonhalt-noncall prog s (sd _ _ _)   eq hnh = refl
r-nonhalt-noncall prog s (add _ _ _)  eq hnh = refl
r-nonhalt-noncall prog s (sub _ _ _)  eq hnh = refl
r-nonhalt-noncall prog s (addi _ _ _) eq hnh = refl
r-nonhalt-noncall prog s (li _ _)     eq hnh = refl
r-nonhalt-noncall prog s (auipc _ _)  eq hnh = refl
r-nonhalt-noncall prog s (lla _ _)    eq hnh = refl
r-nonhalt-noncall prog s (mv _ _)     eq hnh = refl
r-nonhalt-noncall prog s (beq _ _ _)  eq hnh = refl
r-nonhalt-noncall prog s (bne _ _ _)  eq hnh = refl
r-nonhalt-noncall prog s (jal _ _)    eq hnh = refl
r-nonhalt-noncall prog s (jalr _ _ _) eq hnh = refl
r-nonhalt-noncall prog s (j _)        eq hnh = refl
r-nonhalt-noncall prog s ret          eq hnh = refl
r-nonhalt-noncall prog s (call _)     eq hnh = refl
r-nonhalt-noncall prog s nop          eq hnh = refl
r-nonhalt-noncall prog s unimp        eq hnh = refl
r-nonhalt-noncall prog s (label _)    eq hnh = refl

------------------------------------------------------------------------
-- THE THREE INTERFACE RECORDS.
------------------------------------------------------------------------
riscv64-emitter : EI.Emitter FS Reg
riscv64-emitter = record
  { Instr = Instr
  ; compile-abstract = compile-abstract ; compile-trace = compile-trace
  ; ct-nil = refl ; ct-cons = λ _ _ → refl
  ; mfetch = R.fetch
  ; mfetch-nil = λ _ → refl ; mfetch-zero = λ _ _ → refl ; mfetch-suc = λ _ _ _ → refl
  ; is-label? = is-label? ; mk-label = label ; find-label-go = R.find-label-go
  ; find-label-nil = λ _ _ → refl ; skip-law = skip-law
  ; label-hit = label-hit ; label-miss = label-miss ; headView = headView
  ; find-label = R.find-label ; find-label-def = λ _ _ → refl
  }

riscv64-machine : EI.Machine FS Reg riscv64-emitter
riscv64-machine = record
  { State = R.State ; rreg = λ s r → R.readReg (R.State.regs s) r
  ; memory = R.State.memory
  ; xhalted = R.State.halted ; xpc = R.State.pc
  -- `jalr` writes the LINK REGISTER and nothing else: until the callee's
  -- `sd ra` there is no cell to point at, so the claim ignores the address.
  ; link-claim = FSimr.riscv64-link-claim o FS word-eq
  ; mexecInstr = R.execInstr ; exec = R.exec
  ; exec-zero = r-exec-zero ; exec-halted = r-exec-halted ; exec-end = r-exec-end
  ; exec-stuck = r-exec-stuck ; exec-step-halt = r-exec-step-halt
  ; exec-step-run = r-exec-step-run
  }

riscv64-traceloop : EI.TraceLoop FS Reg riscv64-emitter riscv64-machine
riscv64-traceloop = record
  { Payload = List XInstr × ℕ
  ; matchCall = RTr.matchCall ; ret-past = RTr.ret-past
  ; dispatchArith = uncurry (dispatch-arith val-riscv64)
  ; ev-arch = ev-riscv64 ; arith-env = arith-env-riscv64
  ; sigop-call = call-sym ; sigop-lowering = λ _ → refl ; sigop-matchCall = λ _ → refl
  ; nonhalt-noncall = r-nonhalt-noncall
  }

module EE = Engine o FS slot-size word-eq Reg riscv64-roles R.W.modulus
                   riscv64-emitter riscv64-machine riscv64-traceloop

open EE using (FlatInv; mkFlatInv; inv-wf; inv-closure; inv-regtag; inv-ev; inv-env
              ; inv-run; flat-inv-step; block-run-exec
              ; events-running-end; sigop-concrete-fetch; sigop-run-arith
              ; sigop-run-external; event-of-pure
              -- …and what the five stuck routes name. `CompiledCorr`/`HeapView`
              -- are NOT re-listed: `FlatSimulation` already binds them (the same
              -- instance, by module application), and naming them twice makes
              -- every use ambiguous.
              ; StuckAt; StuckSteps) public

-- the ABSTRACT machine's own vocabulary, which the stuck routes state their
-- premises in (`hiding (Instr)`: this module's `Instr` is the CONCRETE one)
open import Once.CCC.Machine.SMCore hiding (Instr)
open FlatMachine {FS} using (FlatState; fpc; floc; fetch; find-label)
open MemOps {FS} using (readLoc)
open import Once.CCC.Label using (once)
-- (`zero` is BOTH a riscv64 register and `ℕ`'s constructor; the register is
-- renamed so the two never collide in this module.)
open import Once.CCC.Target.RiscV64.Syntax using (a0; t0; t1; s3) renaming (zero to rzero)
open import Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition FS Instr
  compile-abstract compile-trace refl (λ _ _ → refl)
  R.fetch (λ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl)
  is-label? label R.find-label-go (λ _ _ → refl) skip-law
  label-hit label-miss headView
  using (find-label-none-corr)

------------------------------------------------------------------------
-- …AND THE ONE BLOCK-STEP WHOSE SHAPE DIFFERED (plan 0.65 G2).
--
-- `bs-lea-slot` offers `(cc, h, ft, run)`. riscv64's block-step wants a range
-- fact instead of the run context, and this is the arch converting one into
-- the other through its own resource parameter — the pattern the slice-2 note
-- described: the field is the ENGINE's interface, and an arch needing
-- something else derives it here.
--
-- The `RunAt` is in that interface BECAUSE OF THIS ARCH (2026-08-16): without
-- it the bound below is refutable, and x86-64 — which pays nothing, its `lea`
-- needing no range fact — simply drops the argument.
--
-- Stated at exactly the field's type, so `Supply`'s `bs-lea-slot` is this.
------------------------------------------------------------------------
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation o FS word-eq using
  (block-step-lea-slot; CompiledCorr; BlockStep; BlockSteps
  ; block-step-mov-to-output; block-step-mov-to-input
  ; block-step-mov-input2-to-output; block-step-mov-output-to-input2
  ; block-step-scratch-one; block-step-scratch-zero; block-step-count-zero
  ; block-step-scratch-load-count; block-step-c-label; block-step-reclaim-to
  ; block-step-worklist-init; block-step-worklist-check
  ; block-step-save-closure-reg; block-step-load-tag-lit
  ; block-step-load-indirect; block-step-load-indirect-stack
  ; block-step-load-indirect-suc; block-step-load-indirect-suc-stack
  ; block-step-load-from-slot; block-step-restore-input; block-step-worklist-pop
  ; block-step-store-at-slot; block-step-worklist-push
  ; block-step-store-indirect; block-step-store-indirect-stack
  ; block-step-store-indirect-suc; block-step-store-indirect-suc-stack
  ; block-step-c-jmp; block-step-c-branch-scratch-zero; block-step-c-branch-nz
  ; block-step-c-branch-tag-zero; block-step-c-branch-tag-nz
  ; block-step-scratch-dec; block-step-count-inc
  ; block-step-c-thunk; block-step-c-ret
  ; block-step-load-const; block-step-load-const-float
  ; block-step-load-code-addr; block-step-call; block-step-alloc-heap
  ; load-indirect-heap-empty-stuck; load-indirect-suc-heap-empty-stuck
  ; dataCorr; pc-off; HeapView)
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence FS word-eq using
  (HeapView)

riscv64-lea-slot : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s
                 → halted (floc fs) ≡ false
                 → fetch prog (fpc fs) ≡ just (lea-slot slot)
                 → RCr.RunAt o FS slot-size word-eq prog fs
                 → BlockStep hv prog fs s (lea-slot slot)
riscv64-lea-slot prog fs s slot cc h ft run =
  block-step-lea-slot prog fs s slot cc h ft
    (slot-addr-no-wrap prog fs s slot run cc ft)

------------------------------------------------------------------------
-- THE FIVE STUCK ROUTES (plan 0.65 G2).
--
-- `EE.stuck-result` has already discharged the ABSTRACT half of each; what an
-- arch owes is only "nothing more comes out of the concrete machine". Two of
-- the five genuinely STICK (a load through a pointer to an unwritten cell —
-- `execInstr ≡ nothing`); the other three HALT, because `jump-to` with a
-- missing label sets `halted`, so those take one more step and then emit
-- nothing.
--
-- riscv64's branches are ONE instruction where x86-64's are two (no flags),
-- which is why `c-branch-scratch-zero` is shorter here than there.
------------------------------------------------------------------------
stuck-load-indirect : ∀ {hv : HeapView} ev env prog fs s hl → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → EE.CFC.HDom hv hl
  → heapMem (floc fs) hl ≡ nothing
  → StuckAt ev env (compile-trace prog) s
stuck-load-indirect ev env prog fs s hl cc h ftq i-eq dom h-eq =
  1 , EE.RT.run-events-stuck ev env 0 (compile-trace prog) s (ld a0 t0 0)
        (trans (EE.CFC.halt-eq (dataCorr cc)) h)
        (proj₁ stuckp) refl (proj₂ stuckp)
  where stuckp = load-indirect-heap-empty-stuck prog fs s hl cc ftq i-eq dom h-eq

stuck-load-indirect-suc : ∀ {hv : HeapView} ev env prog fs s hl → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → EE.CFC.HDom hv (sucHL hl)
  → heapMem (floc fs) (sucHL hl) ≡ nothing
  → StuckAt ev env (compile-trace prog) s
stuck-load-indirect-suc ev env prog fs s hl cc h ftq i-eq dom h-eq =
  1 , EE.RT.run-events-stuck ev env 0 (compile-trace prog) s (ld a0 t0 slot-size)
        (trans (EE.CFC.halt-eq (dataCorr cc)) h)
        (proj₁ stuckp) refl (proj₂ stuckp)
  where stuckp = load-indirect-suc-heap-empty-stuck prog fs s hl cc ftq i-eq dom h-eq

-- A concrete jump to a MISSING label HALTS (`jump-to`'s `nothing` branch), so
-- it does not stick — it takes one step and then emits nothing.
stuck-c-jmp : ∀ {hv : HeapView} ev env prog fs s m → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp m))
  → find-label prog m ≡ nothing
  → StuckAt ev env (compile-trace prog) s
stuck-c-jmp ev env prog fs s m cc h ftq fl-eq =
  2 , trans (EE.RT.run-events-noncall ev env 1 (compile-trace prog) s
               (j (once m)) halt-s fetch-rv refl step-eq)
            (EE.RT.run-events-halted ev env 0 (compile-trace prog) s' refl)
  where
    halt-s : R.State.halted s ≡ false
    halt-s = trans (EE.CFC.halt-eq (dataCorr cc)) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (j (once m))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) (pc-off cc))
                     (EE.fetch-block-head prog (fpc fs) (instr-ctrl (c-jmp m)) ftq)
    s' : R.State
    s' = record s { halted = true }
    step-eq : R.execInstr (compile-trace prog) s (j (once m)) ≡ just s'
    step-eq rewrite find-label-none-corr prog m fl-eq = refl

-- …and the two TAKEN branches whose label is absent. ONE instruction each on
-- this arch — `beq` reads the register directly, where x86-64 needs `cmp` then
-- `je` because the comparison goes through flags.
stuck-c-branch-scratch-zero : ∀ {hv : HeapView} ev env prog fs s m → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero m))
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag 0
  → find-label prog m ≡ nothing
  → StuckAt ev env (compile-trace prog) s
stuck-c-branch-scratch-zero {hv} ev env prog fs s m cc h ftq sc-eq fl-eq =
  2 , trans (EE.RT.run-events-noncall ev env 1 (compile-trace prog) s
               (beq s3 rzero (once m)) halt-s fetch-rv refl step-eq)
            (EE.RT.run-events-halted ev env 0 (compile-trace prog) s' refl)
  where
    dc = dataCorr cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (EE.CFC.halt-eq dc) h
    s3-0 : R.readReg (R.State.regs s) s3 ≡ 0
    s3-0 = trans (EE.CFC.scratch-eq dc) (cong (EE.CFC.enc-sv hv) sc-eq)
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (beq s3 rzero (once m))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) (pc-off cc))
                     (EE.fetch-block-head prog (fpc fs)
                        (instr-ctrl (c-branch-scratch-zero m)) ftq)
    s' : R.State
    s' = record s { halted = true }
    step-eq : R.execInstr (compile-trace prog) s (beq s3 rzero (once m)) ≡ just s'
    step-eq rewrite s3-0 | find-label-none-corr prog m fl-eq = refl

stuck-c-branch-tag-zero : ∀ {hv : HeapView} ev env prog fs s m loc → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero m))
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
  → readLoc (floc fs) loc ≡ just (SV-Tag 0)
  → R.State.memory s (R.readReg (R.State.regs s) t0 + 0) ≡ just 0
  → find-label prog m ≡ nothing
  → StuckAt ev env (compile-trace prog) s
stuck-c-branch-tag-zero ev env prog fs s m loc cc h ftq i-eq r-eq rd fl-eq =
  3 , trans (EE.RT.run-events-noncall ev env 2 (compile-trace prog) s
               (ld t1 t0 0) halt-s fetch-ld refl step-ld')
      (trans (EE.RT.run-events-noncall ev env 1 (compile-trace prog) post-ld
               (beq t1 rzero (once m)) halt-s fetch-beq refl step-beq)
             (EE.RT.run-events-halted ev env 0 (compile-trace prog) post-beq refl))
  where
    dc = dataCorr cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (EE.CFC.halt-eq dc) h
    fetch-ld : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld t1 t0 0)
    fetch-ld = trans (cong (R.fetch (compile-trace prog)) (pc-off cc))
                     (EE.fetch-block-head prog (fpc fs)
                        (instr-ctrl (c-branch-tag-zero m)) ftq)
    post-ld : R.State
    post-ld = record s { regs = R.writeReg (R.State.regs s) t1 0
                       ; pc = R.State.pc s + 1 }
    step-ld' : R.execInstr (compile-trace prog) s (ld t1 t0 0) ≡ just post-ld
    step-ld' = execInstr-ld (compile-trace prog) s t1 t0 0 0 rd
    fetch-beq : R.fetch (compile-trace prog) (R.State.pc post-ld)
              ≡ just (beq t1 rzero (once m))
    fetch-beq = trans (cong (λ p → R.fetch (compile-trace prog) (p + 1)) (pc-off cc))
                      (EE.fetch-block-2nd prog (fpc fs)
                         (instr-ctrl (c-branch-tag-zero m)) ftq)
    post-beq : R.State
    post-beq = record post-ld { halted = true }
    step-beq : R.execInstr (compile-trace prog) post-ld (beq t1 rzero (once m))
             ≡ just post-beq
    step-beq rewrite find-label-none-corr prog m fl-eq = refl

riscv64-stuck-steps : StuckSteps
riscv64-stuck-steps = record
  { st-load-indirect         = stuck-load-indirect
  ; st-load-indirect-suc     = stuck-load-indirect-suc
  ; st-c-jmp                 = stuck-c-jmp
  ; st-c-branch-scratch-zero = stuck-c-branch-scratch-zero
  ; st-c-branch-tag-zero     = stuck-c-branch-tag-zero
  }

------------------------------------------------------------------------
-- THE BLOCK-STEP SUPPLY — all 42, and the gate that catches slack.
--
-- A field typechecks in isolation however weakly it is stated; only building
-- the record VALUE forces every one of them to line up with what the engine
-- passes. This is that gate for riscv64.
------------------------------------------------------------------------
riscv64-block-steps : BlockSteps
riscv64-block-steps = record
  { bs-mov-to-output        = block-step-mov-to-output
  ; bs-mov-to-input         = block-step-mov-to-input
  ; bs-mov-input2-to-output = block-step-mov-input2-to-output
  ; bs-mov-output-to-input2 = block-step-mov-output-to-input2
  ; bs-scratch-one          = block-step-scratch-one
  ; bs-scratch-zero         = block-step-scratch-zero
  ; bs-count-zero           = block-step-count-zero
  ; bs-scratch-load-count   = block-step-scratch-load-count
  ; bs-c-label              = block-step-c-label
  ; bs-reclaim-to           = block-step-reclaim-to
  ; bs-worklist-init        = block-step-worklist-init
  ; bs-worklist-check       = block-step-worklist-check
  -- the ONE shape that differs: riscv64 computes a slot address with `addi`,
  -- so it converts the field's `RunAt` into its own range fact (see above)
  ; bs-lea-slot             = riscv64-lea-slot
  ; bs-save-closure-reg     = block-step-save-closure-reg
  ; bs-load-tag-lit         = block-step-load-tag-lit
  ; bs-load-indirect            = block-step-load-indirect
  ; bs-load-indirect-stack      = block-step-load-indirect-stack
  ; bs-load-indirect-suc        = block-step-load-indirect-suc
  ; bs-load-indirect-suc-stack  = block-step-load-indirect-suc-stack
  ; bs-load-from-slot           = block-step-load-from-slot
  ; bs-restore-input            = block-step-restore-input
  ; bs-worklist-pop             = block-step-worklist-pop
  ; bs-store-at-slot            = block-step-store-at-slot
  ; bs-worklist-push            = block-step-worklist-push
  ; bs-store-indirect           = block-step-store-indirect
  ; bs-store-indirect-stack     = block-step-store-indirect-stack
  ; bs-store-indirect-suc       = block-step-store-indirect-suc
  ; bs-store-indirect-suc-stack = block-step-store-indirect-suc-stack
  ; bs-c-jmp                    = block-step-c-jmp
  ; bs-c-branch-scratch-zero    = block-step-c-branch-scratch-zero
  ; bs-c-branch-nz              = block-step-c-branch-nz
  ; bs-c-branch-tag-zero        = block-step-c-branch-tag-zero
  ; bs-c-branch-tag-nz          = block-step-c-branch-tag-nz
  ; bs-scratch-dec              = block-step-scratch-dec
  ; bs-count-inc                = block-step-count-inc
  ; bs-c-thunk                  = block-step-c-thunk
  ; bs-c-ret                    = block-step-c-ret
  ; bs-load-const               = block-step-load-const
  ; bs-load-const-float         = block-step-load-const-float
  ; bs-load-code-addr           = block-step-load-code-addr
  ; bs-call                     = block-step-call
  ; bs-alloc-heap               = block-step-alloc-heap
  }
