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
  -- CONDITIONED ON `CompiledCorr` + THE FETCH, and NOT on `RunAt` — not by
  -- preference but by force: the engine's `bs-lea-slot` field hands an arch
  -- only `(cc, h, ft)`, because that is what it passes on x86-64. So this is
  -- strictly stronger than the `AddrNoWrap` family it belongs to, all of which
  -- carry `RunAt`. Before trusting it, check it is not REFUTABLE the way six
  -- residuals were on 2026-07-30; if it is, the honest fix is to give the
  -- field a `RunAt` premise, not to weaken the bound. Recorded in the handoff.
  (slot-addr-no-wrap :
     ∀ {hv : FCr.HeapView FS word-eq} (prog : AbstractTrace)
       (fs : FlatMachine.FlatState {FS}) (s : RS.State) (slot : ℕ)
     → FSimr.CompiledCorr FS word-eq hv prog fs s
     → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs) ≡ just (lea-slot slot)
     → RS.readReg (RS.State.regs s) sp + slot-to-disp slot < RS.W.modulus)
  where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; uncurry)
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
open import Once.Adequacy.CPU.RiscV64 using (ev-riscv64; arith-env-riscv64)
open import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 using (val-riscv64)
open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Arith.Backend.RiscV64.Dispatch using (dispatch-arith)
import Once.Arith.Backend.RiscV64.RunTrace as RTr
import Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface as EI

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

------------------------------------------------------------------------
-- …AND THE ONE BLOCK-STEP WHOSE SHAPE DIFFERED (plan 0.65 G2).
--
-- `bs-lea-slot` offers `(cc, h, ft)` — three premises, because that is what
-- the engine passes. riscv64's block-step wants a fourth. This is the arch
-- closing that gap from its own resource parameter, and it is the pattern the
-- slice-2 note described: the field is the ENGINE's interface, and an arch
-- needing more supplies it here rather than widening the interface for
-- everyone.
--
-- Stated at exactly the field's type, so `Supply`'s `bs-lea-slot` is this.
------------------------------------------------------------------------
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation FS word-eq using
  (block-step-lea-slot; CompiledCorr; BlockStep)
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence FS word-eq using
  (HeapView)
open FlatMachine {FS} using (fpc; floc; fetch)
open import Once.CCC.Machine.SMCore using (halted)

riscv64-lea-slot : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s
                 → halted (floc fs) ≡ false
                 → fetch prog (fpc fs) ≡ just (lea-slot slot)
                 → BlockStep hv prog fs s (lea-slot slot)
riscv64-lea-slot prog fs s slot cc h ft =
  block-step-lea-slot prog fs s slot cc h ft (slot-addr-no-wrap prog fs s slot cc ft)
