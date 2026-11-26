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

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word)
open import Once.CCC.Target.RiscV64.Syntax using (slot-size)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Name using (CanonicalName)
-- imported UNAPPLIED, so the module's own `FS`/`word-eq` can be threaded into
-- the resource parameter's type — a parameter's type is elaborated before the
-- body, where the applied `open import … FS word-eq` has not run.
import Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation as FSimr
import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence as FCr
import Once.Adequacy.ArchCorrectness.FlatCore.RunLow as RLr
import Once.CCC.Target.RiscV64.Semantics as RS
open import Once.CCC.Machine.SMCore using
  (AbstractTrace; lea-slot; instr-ctrl; c-ret; c-start; start-stack-words; instr-load-tag-lit; instr-load-const; instr-room; instr-sigop; module Room)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Target.RiscV64.Syntax using (slots)
open import Once.Target.RiscV64.PhysReg using (sp) renaming (Reg to Reg')
open import Once.Target.RiscV64.PhysReg using (Reg)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (slot-to-disp)
open import Data.Nat using (ℕ; suc; _+_; _<_; _≤_)
open import Once.Type using (fits-int; fits-float)
open import Once.Spec.Float.Dyadic using (binary64)
open import Once.Spec.Float.Decimal using (Decimal)
open import Data.Integer using (ℤ)
open import Data.Maybe using (just)

open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.List.Relation.Unary.All
open import Data.Product using (Σ)
module Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim
  (o : CanonicalName)
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  -- …and the float format pinned to this target's, the companion of `word-eq`
  -- (plan 0.73, D113). Passed straight through to `FlatSimulation`, which is
  -- where the emitter's `round binary64` and the machine's `float-format FS`
  -- have to be shown to be the same number.
  (fmt-eq : FrameSemantics.float-format FS ≡ binary64)
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
     ∀ {hv : FCr.FlatCorrespondence.HeapView FS word-eq} (prog : AbstractTrace)
       (fs : FlatMachine.FlatState {FS}) (s : RS.State) (slot : ℕ)
     → RLr.RunLow o FS slot-size word-eq prog fs
     → FSimr.CompiledCorrespondence.CompiledCorr o FS word-eq fmt-eq hv prog fs s
     → FlatMachine.fetch {FS} prog (FlatMachine.FlatState.fpc {FS} fs) ≡ just (lea-slot slot)
     → RS.readReg (RS.State.regs s) sp + slot-to-disp slot < RS.W.modulus)
  -- …AND THE REST OF THE FAMILY (plan 0.65 G2). Bundled as the two records
  -- `RiscV64/ResourceBounds` defines, exactly as x86-64 threads them (the three
  -- room bounds left with plan 0.123 A.4 step 5): resource bounds are PARAMETERS, never postulates
  -- (D087) — a linker that sizes the image discharges them, and a parameter is
  -- what leaves room for that.
  --
  -- SPELLED OUT, not named from `ResourceBounds` — that module IMPORTS this one
  -- (it is what keeps this file reachable from the four clusters), so naming
  -- its types here is a cycle. x86-64 does the same, and its apex is where the
  -- two meet.
  (reg-range : ∀ {hv : FCr.FlatCorrespondence.HeapView FS word-eq} (prog : AbstractTrace)
                 (fs : FlatMachine.FlatState {FS}) (s : RS.State) (r : Reg')
             → RLr.RunLow o FS slot-size word-eq prog fs
             → FSimr.CompiledCorrespondence.CompiledCorr o FS word-eq fmt-eq hv prog fs s
             → RS.readReg (RS.State.regs s) r < RS.W.modulus)
  -- `suc b`: THE CALLER'S FRAME BASE, not just the frame. See D106.
  (ret-no-wrap : ∀ {hv : FCr.FlatCorrespondence.HeapView FS word-eq} (prog : AbstractTrace)
                   (fs : FlatMachine.FlatState {FS}) (s : RS.State) (b : ℕ)
               → RLr.RunLow o FS slot-size word-eq prog fs
               → FSimr.CompiledCorrespondence.CompiledCorr o FS word-eq fmt-eq hv prog fs s
               → FlatMachine.fetch {FS} prog (FlatMachine.FlatState.fpc {FS} fs)
                   ≡ just (instr-ctrl (c-ret b))
               → RS.readReg (RS.State.regs s) sp + slots (suc b) < RS.W.modulus)
  (tag-fits : ∀ {hv : FCr.FlatCorrespondence.HeapView FS word-eq} (prog : AbstractTrace)
                (fs : FlatMachine.FlatState {FS}) (s : RS.State) (n : ℕ)
            → RLr.RunLow o FS slot-size word-eq prog fs
            → FSimr.CompiledCorrespondence.CompiledCorr o FS word-eq fmt-eq hv prog fs s
            → FlatMachine.fetch {FS} prog (FlatMachine.FlatState.fpc {FS} fs)
                ≡ just (instr-load-tag-lit n)
            → n < RS.W.modulus)
  (lit-fits : ∀ {hv : FCr.FlatCorrespondence.HeapView FS word-eq} (prog : AbstractTrace)
                (fs : FlatMachine.FlatState {FS}) (s : RS.State) (v : ℤ)
            → RLr.RunLow o FS slot-size word-eq prog fs
            → FSimr.CompiledCorrespondence.CompiledCorr o FS word-eq fmt-eq hv prog fs s
            → FlatMachine.fetch {FS} prog (FlatMachine.FlatState.fpc {FS} fs)
                ≡ just (instr-load-const fits-int v)
            → Once.CCC.Machine.SMCore.AbstractExec.lit-value {FS} fits-int v < RS.W.modulus)
  (float-fits : ∀ {hv : FCr.FlatCorrespondence.HeapView FS word-eq} (prog : AbstractTrace)
                  (fs : FlatMachine.FlatState {FS}) (s : RS.State) (v : Decimal)
              → RLr.RunLow o FS slot-size word-eq prog fs
              → FSimr.CompiledCorrespondence.CompiledCorr o FS word-eq fmt-eq hv prog fs s
              → FlatMachine.fetch {FS} prog (FlatMachine.FlatState.fpc {FS} fs)
                  ≡ just (instr-load-const fits-float v)
              → Once.CCC.Machine.SMCore.AbstractExec.lit-value {FS} fits-float v < RS.W.modulus)
  where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong)

open import Once.CCC.Target.RiscV64.Syntax using
  (Instr; label; ld; sd; add; sub; sltu; addi; li; auipc; lla; lla-sym; mv; beq; bne; jal; jalr; j; ret; call; call-sym; nop; unimp; bgeu-fwd; local-1; bgeu-fwd2; local-2)
import Once.CCC.Target.RiscV64.Semantics as R
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-abstract; compile-trace)
open import Once.Adequacy.ArchCorrectness.RiscV64.RegRoles using (riscv64-roles)
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition FS using
  (is-label?; skip-law; label-hit; label-miss; headView)
open import Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas using (execInstr-ld)
open import Once.Adequacy.CPU.RiscV64 using (ev-riscv64; block-env; call-at-riscv64)
import Once.Compile.Emit as Emit
import Once.Adequacy.BlockTable as BT
open import Once.Target.Backend using (file-table)
import Once.Arith.Backend.RiscV64.Emit as AE
open import Once.Adequacy.CPU.RiscV64 using (block-env-hit; block-env-sound)
open import Once.Adequacy.RewriteOwned using (BlockOf; is-block; block-not-in-memory)
import Once.Adequacy.ArchCorrectness.RiscV64.ArithFrame as AF
import Once.Adequacy.ArchCorrectness.RiscV64.ArithBlockValue o FS word-eq fmt-eq as ABV
open import Once.Arith.Backend.XInstr.SpillBound using (SpillsWF; block-spills)
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.Compile using (compile-abs; required-scratch; normalize)
open import Once.Arith.Machine.IR using (mk-block)
open import Once.Arith.Type using (NInt; NFloat)
open import Once.CCC.Codegen.StackDepth using (sigop-scratch; sigop-need)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles using (role-sp; role-clos; role-heap; role-in1; role-out)
open import Data.Nat.Properties using (*-distribʳ-+; *-comm; m≤n+m; m+n≤o⇒n≤o; ≤-trans; +-monoʳ-≤)
open import Data.Nat using (_*_)
open import Data.Empty using (⊥-elim)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.String using (String)
open import Data.Product using (Σ)
open import Once.Denotation.Program using (IRProgram)
open import Once.Arith.Backend.CallAnswer using (answer-at)
open import Once.CCC.Machine.SMCore using (LocState)
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
r-nonhalt-noncall prog s (sltu _ _ _)  eq hnh = refl
r-nonhalt-noncall prog s (addi _ _ _) eq hnh = refl
r-nonhalt-noncall prog s (li _ _)     eq hnh = refl
r-nonhalt-noncall prog s (auipc _ _)  eq hnh = refl
r-nonhalt-noncall prog s (lla _ _)    eq hnh = refl
r-nonhalt-noncall prog s (lla-sym _ _) eq hnh = refl
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
r-nonhalt-noncall prog s (bgeu-fwd _ _) eq hnh = refl
r-nonhalt-noncall prog s local-1      eq hnh = refl
r-nonhalt-noncall prog s (bgeu-fwd2 _ _) eq hnh = refl
r-nonhalt-noncall prog s local-2      eq hnh = refl
r-nonhalt-noncall prog s (label _)    eq hnh = refl

------------------------------------------------------------------------
-- THE THREE INTERFACE RECORDS.
------------------------------------------------------------------------

-- plan 0.119 D5: every control lowering is non-empty.
open import Data.List using (length)
open import Data.Nat using (s≤s; z≤n)
open import Once.CCC.Machine.SMCore using (FlatCtrl; instr-ctrl; c-label; c-jmp; c-branch-tag-zero; c-entry; c-ret; c-call-fn; c-start; c-leave)
ctrl-len-arch : ∀ (c : FlatCtrl) → 1 ≤ length (compile-abstract (instr-ctrl c))
ctrl-len-arch (c-label _) = s≤s z≤n
ctrl-len-arch (c-jmp _) = s≤s z≤n
ctrl-len-arch (c-branch-tag-zero _) = s≤s z≤n
ctrl-len-arch (c-entry _ _) = s≤s z≤n
ctrl-len-arch (c-ret _) = s≤s z≤n
ctrl-len-arch (c-call-fn _) = s≤s z≤n
ctrl-len-arch (c-start b rsv) = st-len (AC.room-fits? (rsv Data.Nat.+ b))
  where
    import Once.CCC.Target.RiscV64.AbstractToRiscV as AC
    import Data.Nat
    open import Data.Bool using (Bool; true; false)
    open import Data.List using (_++_)
    -- D488: the start's check is its code or its call
    st-len : ∀ (c : Bool) → 1 ≤ length (AC.fits-or-out c (AC.room-code (rsv Data.Nat.+ b)) ++ AC.start-tail b rsv)
    st-len true  = s≤s z≤n
    st-len false = s≤s z≤n
ctrl-len-arch c-leave = s≤s z≤n

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
  ; ctrl-len = ctrl-len-arch
  }

riscv64-machine : EI.Machine FS Reg riscv64-emitter
riscv64-machine = record
  { State = R.State ; rreg = λ s r → R.readReg (R.State.regs s) r
  ; memory = R.State.memory
  ; xhalted = R.State.halted ; heap-base = R.heap-base ; xpc = R.State.pc
  -- `jalr` writes the LINK REGISTER and nothing else: until the callee's
  -- `sd ra` there is no cell to point at, so the claim ignores the address.
  ; link-claim = FSimr.riscv64-link-claim o FS word-eq fmt-eq
  ; mexecInstr = R.execInstr ; exec = R.exec
  ; exec-zero = r-exec-zero ; exec-halted = r-exec-halted ; exec-end = r-exec-end
  ; exec-stuck = r-exec-stuck ; exec-step-halt = r-exec-step-halt
  ; exec-step-run = r-exec-step-run
  }


open import Once.SigOp.Info using (SigOpInfo; Internal; External; module SigOpInfo)
open SigOpInfo using (sem)
open import Once.Target.Symbol using (once-symbol-path)

-- Plan 0.107: THE ARITH TABLE IS THE FILE'S — the block table `Once.Compile`
-- emits for the program whose image this is. It was the postulated
-- `arith-env-riscv64`, "read off the code"; the code does not hold it, the file does.
riscv64-arith-table : AbstractTrace → (String → Maybe (List XInstr × ℕ)) → Set
riscv64-arith-table prog env =
  Σ (List ArithBlock) (λ bs → Data.List.Relation.Unary.All.All (BT.SigNamed bs) prog
                                × (env ≡ block-env (file-table AE.block-payload bs))
                                × (∀ {A B} (si : SigOpInfo A B) k → External (sem si) → FlatMachine.fetch {FS} prog k ≡ just (instr-sigop si)
                                     → env (once-symbol-path (SigOpInfo.name si)) ≡ nothing))

riscv64-traceloop : EI.TraceLoop FS Reg riscv64-emitter riscv64-machine
riscv64-traceloop = record
  { Payload = List XInstr × ℕ
  ; matchCall = RTr.matchCall
  -- plan 0.105: an external call returns with the world's answer in `a0`, the
  -- world being the frame semantics' interpretation.
  ; ret-call = RTr.ret-call (answer-at (Once.CCC.FrameSemantics.fs-numerics FS) (Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS) call-at-riscv64)
  ; dispatchArith = uncurry (dispatch-arith val-riscv64)
  ; ev-arch = ev-riscv64 ; ArithTable = riscv64-arith-table
  ; sigop-call = call-sym ; sigop-lowering = λ _ → refl ; sigop-matchCall = λ _ → refl
  ; leave-lowering = refl
  ; nonhalt-noncall = r-nonhalt-noncall
  }

-- `using`, for the same reason as the dispatch's application at the end.
module EE = Engine o FS slot-size word-eq Reg riscv64-roles R.W.modulus
                   riscv64-emitter riscv64-machine riscv64-traceloop
  using ( FlatInv; room-same; mkFlatInv; flat-inv-step; block-run-exec
        ; events-running-end; sigop-concrete-fetch; sigop-run-arith
        ; sigop-run-external; event-of-pure; StuckAt; StuckSteps
        ; stuck-result; Supply
        ; module CFC; module RT; module FlatComposition; module RunContext′ )

open EE using (StuckAt; StuckSteps)

-- the ABSTRACT machine's own vocabulary, which the stuck routes state their
-- premises in (`hiding (Instr)`: this module's `Instr` is the CONCRETE one)
open import Once.CCC.Machine.SMCore hiding (Instr)
open import Once.Memory.HeapAddress using (offsetHL)
open LocState using (halted; regs)
open import Once.CCC.Machine.Locations using (AtDynamic)
open FlatMachine {FS} using (fetch; find-label; flat-exec-instr; module FlatState)
open FlatState using (floc; fpc; falloc)
open ExecFinal {FS} using (in-block?)
open AllocState using (block-size)
open MemOps {FS} using (readLoc)
open import Once.CCC.Label using (once)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {FS} using (event-of)
-- (`zero` is BOTH a riscv64 register and `ℕ`'s constructor; the register is
-- renamed so the two never collide in this module.)
open import Once.Target.RiscV64.PhysReg using (a0; t0; t1) renaming (zero to rzero)
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
import Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation
module FlatSimulation = Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation o FS word-eq fmt-eq using
  (block-step-lea-slot; room-step-riscv64; start-step-riscv64
  ; block-step-mov-to-output; block-step-mov-to-input
  ; block-step-c-label; block-step-reclaim-to; block-step-free-heap
  ; block-step-worklist-init; block-step-worklist-check
  ; block-step-save-closure-reg; block-step-load-tag-lit
  ; block-step-load-indirect; block-step-load-indirect-stack
  ; block-step-load-indirect-suc; block-step-load-indirect-suc-stack
  ; block-step-load-from-slot; block-step-restore-input; block-step-worklist-pop
  ; block-step-store-at-slot; block-step-worklist-push
  ; block-step-store-indirect; block-step-store-indirect-stack
  ; block-step-store-indirect-suc; block-step-store-indirect-suc-stack
  ; block-step-load-at; block-step-store-at; block-step-load-rec; block-step-store-rec; block-step-addr-at; addr-at-no-wrap; block-step-load-at-stack; block-step-store-at-stack
  ; block-step-c-jmp
  ; block-step-c-branch-tag-zero; block-step-c-branch-tag-nz
  ; block-step-c-thunk; block-step-out-nz; block-step-c-ret
  ; block-step-load-const; block-step-load-const-float
  ; block-step-load-code-addr; block-step-call; block-step-call-fn; block-step-alloc-heap
  -- `CompiledCorr`, `dataCorr`, `pc-off`, `BlockStep(s)` come from this copy's
  -- `CompiledCorrespondence` (opened below), not from `EE`: binding them from
  -- both would make every use ambiguous.
  --
  -- `HeapView` is NOT here: it is not exported by `FlatSimulation` at all. Its
  -- real source is the `FlatCorrespondence` import just below.
  ; module CompiledCorrespondence)
open FlatSimulation
open FlatSimulation.CompiledCorrespondence using (CompiledCorr; BlockStep; BlockSteps)
open FlatSimulation.CompiledCorrespondence.CompiledCorr using (dataCorr; pc-off)
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence FS word-eq using
  (module FlatCorrespondence)
open FlatCorrespondence using (HeapView)
-- plan 0.123 α′ (e): the arch-free frame lemma of an arith SigOp's run
module CFr = FCr FS word-eq
  using (module FlatCorrespondence)
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition FS using (module FlatComposition)
open FlatComposition using (blk-off; blk-len; blk-off-suc)
open import Once.Adequacy.ArchCorrectness.FlatCore.SigOpFrame
       o FS slot-size word-eq Reg riscv64-roles R.State (FSimr.rreg' o FS word-eq fmt-eq) R.State.memory R.State.halted R.heap-base
       (FSimr.riscv64-link-claim o FS word-eq fmt-eq) R.State.pc Once.CCC.Target.RiscV64.Syntax.Program compile-trace
       R.find-label blk-off blk-len R.exec R.W.modulus
  using (ArithRun; sigop-arith-step)
open import Data.Nat.Properties using (+-comm)

riscv64-lea-slot : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s
                 → halted (floc fs) ≡ false
                 → fetch prog (fpc fs) ≡ just (lea-slot slot)
                 → slot < AllocState.frame-slots (falloc fs)
                 → RLr.RunLow o FS slot-size word-eq prog fs
                 → BlockStep hv prog fs s (lea-slot slot)
riscv64-lea-slot prog fs s slot cc h ft lt run =
  block-step-lea-slot prog fs s slot cc h ft lt
    (slot-addr-no-wrap prog fs s slot run cc ft)

-- plan 0.123 B.4 α (D385): `addr-at k` is `addi t0, t0, 8k`; its no-wrap
-- fact comes from the target being a mapped cell (below the frontier, which
-- `reg-range` bounds as the heap register's value).
riscv64-addr-at : ∀ {hv : HeapView} prog fs s k hl → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (addr-at k)
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → FCr.FlatCorrespondence.HeapView.HDom hv (offsetHL hl k)
  → in-block? (block-size (falloc fs)) (AtDynamic (offsetHL hl k)) ≡ true
  → RLr.RunLow o FS slot-size word-eq prog fs
  → BlockStep hv prog fs s (addr-at k)
riscv64-addr-at prog fs s k hl cc h ft i-eq live ib run =
  block-step-addr-at prog fs s k hl cc h ft i-eq ib
    (addr-at-no-wrap prog fs s k hl cc i-eq live (λ r → reg-range prog fs s r run cc))

------------------------------------------------------------------------
-- THE TWO STUCK ROUTES (plan 0.65 G2).
--
-- `EE.stuck-result` has already discharged the ABSTRACT half of each; what an
-- arch owes is only "nothing more comes out of the concrete machine". Both
-- HALT, because `jump-to` with a missing label sets `halted`, so they take
-- one more step and then emit nothing. (The two loads through a pointer to an
-- unwritten cell were stuck routes too, until plan 0.123 A.4 step 4.)
------------------------------------------------------------------------
-- A concrete jump to a MISSING label HALTS (`jump-to`'s `nothing` branch), so
-- it does not stick — it takes one step and then emits nothing.
stuck-c-jmp : ∀ {hv : HeapView} ev env prog fs s m → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp m))
  → find-label prog m ≡ nothing
  → StuckAt ev env (compile-trace prog) s
stuck-c-jmp ev env prog fs s m cc h ftq fl-eq = λ lg →
  2 , trans (EE.RT.run-events-noncall ev env lg 1 (compile-trace prog) s
               (j (once m)) halt-s fetch-rv refl step-eq)
            (EE.RT.run-events-halted ev env lg 0 (compile-trace prog) s' refl)
  where
    halt-s : R.State.halted s ≡ false
    halt-s = trans (EE.CFC.FlatCorr.halt-eq (dataCorr cc)) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (j (once m))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) (pc-off cc))
                     (EE.FlatComposition.fetch-block-head prog (fpc fs) (instr-ctrl (c-jmp m)) ftq)
    s' : R.State
    s' = record s { halted = true }
    step-eq : R.execInstr (compile-trace prog) s (j (once m)) ≡ just s'
    step-eq rewrite find-label-none-corr prog m fl-eq = refl


stuck-c-branch-tag-zero : ∀ {hv : HeapView} ev env prog fs s m loc → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero m))
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
  → readLoc (floc fs) loc ≡ just (SV-Tag 0)
  → R.State.memory s (R.readReg (R.State.regs s) t0 + 0) ≡ just 0
  → find-label prog m ≡ nothing
  → StuckAt ev env (compile-trace prog) s
stuck-c-branch-tag-zero ev env prog fs s m loc cc h ftq i-eq r-eq rd fl-eq = λ lg →
  3 , trans (EE.RT.run-events-noncall ev env lg 2 (compile-trace prog) s
               (ld t1 t0 0) halt-s fetch-ld refl step-ld')
      (trans (EE.RT.run-events-noncall ev env lg 1 (compile-trace prog) post-ld
               (beq t1 rzero (once m)) halt-s fetch-beq refl step-beq)
             (EE.RT.run-events-halted ev env lg 0 (compile-trace prog) post-beq refl))
  where
    dc = dataCorr cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (EE.CFC.FlatCorr.halt-eq dc) h
    fetch-ld : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld t1 t0 0)
    fetch-ld = trans (cong (R.fetch (compile-trace prog)) (pc-off cc))
                     (EE.FlatComposition.fetch-block-head prog (fpc fs)
                        (instr-ctrl (c-branch-tag-zero m)) ftq)
    post-ld : R.State
    post-ld = record s { regs = R.writeReg (R.State.regs s) t1 0
                       ; pc = R.State.pc s + 1 }
    step-ld' : R.execInstr (compile-trace prog) s (ld t1 t0 0) ≡ just post-ld
    step-ld' = execInstr-ld (compile-trace prog) s t1 t0 0 0 rd
    fetch-beq : R.fetch (compile-trace prog) (R.State.pc post-ld)
              ≡ just (beq t1 rzero (once m))
    fetch-beq = trans (cong (λ p → R.fetch (compile-trace prog) (p + 1)) (pc-off cc))
                      (EE.FlatComposition.fetch-block-2nd prog (fpc fs)
                         (instr-ctrl (c-branch-tag-zero m)) ftq)
    post-beq : R.State
    post-beq = record post-ld { halted = true }
    step-beq : R.execInstr (compile-trace prog) post-ld (beq t1 rzero (once m))
             ≡ just post-beq
    step-beq rewrite find-label-none-corr prog m fl-eq = refl

riscv64-stuck-steps : StuckSteps
riscv64-stuck-steps = record
  { st-c-jmp                = stuck-c-jmp
  ; st-c-branch-tag-zero     = stuck-c-branch-tag-zero
  }

------------------------------------------------------------------------
-- THE BLOCK-STEP SUPPLY — all 35, and the gate that catches slack.
--
-- A field typechecks in isolation however weakly it is stated; only building
-- the record VALUE forces every one of them to line up with what the engine
-- passes. This is that gate for riscv64.
------------------------------------------------------------------------
riscv64-block-steps : BlockSteps
riscv64-block-steps = record
  { bs-mov-to-output        = block-step-mov-to-output
  ; bs-mov-to-input         = block-step-mov-to-input
  ; bs-c-label              = block-step-c-label
  ; bs-reclaim-to           = block-step-reclaim-to
  ; bs-free-heap            = block-step-free-heap
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
  ; bs-load-at                  = block-step-load-at
  ; bs-store-at                 = block-step-store-at
  ; bs-load-rec                 = block-step-load-rec
  ; bs-store-rec                = block-step-store-rec
  ; bs-addr-at                  = riscv64-addr-at
  ; bs-store-indirect-suc-stack = block-step-store-indirect-suc-stack
  ; bs-c-jmp                    = block-step-c-jmp
  ; bs-load-at-stack            = block-step-load-at-stack
  ; bs-store-at-stack           = block-step-store-at-stack
  ; bs-c-branch-tag-zero        = block-step-c-branch-tag-zero
  ; bs-c-branch-tag-nz          = block-step-c-branch-tag-nz
  ; bs-out-nz                   = block-step-out-nz
  ; bs-c-thunk                  = block-step-c-thunk
  ; bs-c-ret                    = block-step-c-ret
  ; bs-load-const               = block-step-load-const
  ; bs-load-const-float         = block-step-load-const-float
  ; bs-load-code-addr           = block-step-load-code-addr
  ; bs-call                     = block-step-call
  ; bs-call-fn                  = block-step-call-fn
  ; bs-alloc-heap               = block-step-alloc-heap
  }

------------------------------------------------------------------------
-- THE TWO SIGOP CONTRACTS (D061) — the per-(SigOp × target) TRUSTED BASE.
--
-- Postulates here as at x86-64, and for the same reason: what a SigOp's lowered
-- code does is the one thing the compiler does not itself construct. `ev`/`env`
-- are PINNED rather than quantified (2026-07-30): over an arbitrary `env` the
-- arith conclusion `env sym ≡ just pl` is refuted by `λ _ → nothing`, and over
-- an arbitrary `ev` the emission claim is refuted by `λ _ _ → []`.
------------------------------------------------------------------------
postulate
  external-sigop-contract : ∀ {hv : HeapView} (ev : EE.RT.EvExtractor) (env : EE.RT.ArithEnv)
                              prog fs s {A B} (si : SigOpInfo A B)
                          → RLr.RunLow o FS slot-size word-eq prog fs
                          → ev ≡ ev-riscv64
                          → riscv64-arith-table prog env
                          → External (sem si)
                          → CompiledCorr hv prog fs s
                          → fetch prog (fpc fs) ≡ just (instr-sigop si)
                          → (env (once-symbol-path (SigOpInfo.name si)) ≡ nothing)
                            × (ev (once-symbol-path (SigOpInfo.name si)) s
                                ≡ event-of (instr-sigop si) fs)
                            × CompiledCorr hv prog
                                (flat-exec-instr (instr-sigop si) prog fs)
                                (RTr.ret-call (answer-at (Once.CCC.FrameSemantics.fs-numerics FS) (Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS) call-at-riscv64)
                                   (LocState.ev-log (FlatMachine.FlatState.floc {FS} fs)) (once-symbol-path (SigOpInfo.name si)) s)

------------------------------------------------------------------------
-- Plan 0.129 B5: THE LOOKUP HALF IS A THEOREM. A compiler-owned SigOp of the
-- image names a block of the program (`BlockTable.image-owned`), the file's
-- table keeps that block's symbol (`table-has`), and `block-env` finds it.
------------------------------------------------------------------------
arith-sigop-lookup : ∀ (env : EE.RT.ArithEnv) prog fs {A B} (si : SigOpInfo A B)
                   → riscv64-arith-table prog env → Internal (sem si) → fetch prog (fpc fs) ≡ just (instr-sigop si)
                   → Σ (List XInstr × ℕ) (λ pl → env (once-symbol-path (SigOpInfo.name si)) ≡ just pl)
arith-sigop-lookup .(block-env (file-table AE.block-payload bs)) prog fs si (bs , nm , refl , _) int ftq =
  let (b , m , e , _) = FlatMachine.fetch-All {FS} {P = BT.SigNamed bs} {k = fpc fs} nm ftq si refl int
  in subst (λ n → Σ (List XInstr × ℕ) (λ pl → block-env (file-table AE.block-payload bs) (once-symbol-path n) ≡ just pl)) (sym e)
           (block-env-hit (file-table AE.block-payload bs) _ (BT.table-has Emit.block-symbol AE.block-payload bs m))

-- plan 0.123 α′ (f1): …and what it finds is the SigOp's OWN block — the
-- table entry under its symbol is a program block with that symbol, and one
-- symbol is one block (`BlockTable.which-block`, D395).
arith-sigop-block : ∀ (env : EE.RT.ArithEnv) prog fs {A B} (si : SigOpInfo A B)
                  → riscv64-arith-table prog env → Internal (sem si) → fetch prog (fpc fs) ≡ just (instr-sigop si)
                  → ∀ (pl : List XInstr × ℕ) → env (once-symbol-path (SigOpInfo.name si)) ≡ just pl
                  → Σ ArithBlock (λ b → BlockOf si b × pl ≡ AE.block-payload b)
arith-sigop-block .(block-env (file-table AE.block-payload bs)) prog fs si (bs , nm , refl , _) int ftq pl hit =
  let (b , _ , bo , e) = BT.which-block AE.block-payload bs si
                           (FlatMachine.fetch-All {FS} {P = BT.SigNamed bs} {k = fpc fs} nm ftq si refl int)
                           (block-env-sound (file-table AE.block-payload bs) _ hit)
  in b , bo , e

------------------------------------------------------------------------
-- Plan 0.123 α′ (f2): THE FRAME HALF of the block's run is a theorem
-- (`RiscV64.ArithFrame`): the subroutine keeps every role register but the
-- result's, and writes only what its call pushes and its spills — each slot
-- below what its tree asks for (`SpillBound`), which the room check charged
-- (D393).
------------------------------------------------------------------------
private
  fits-W : ∀ n → 8 * n ≤ (5 + n) * 8
  fits-W n = subst (8 * n ≤_) (sym (trans (*-distribʳ-+ 8 5 n) (cong (40 +_) (*-comm n 8)))) (m≤n+m (8 * n) 40)

  frame-run : ∀ s (n : ℕ) (blk : List XInstr) (W v : ℕ)
            → SpillsWF n blk → 8 * n ≤ W → W ≤ FSimr.rreg' o FS word-eq fmt-eq s sp
            → FSimr.rreg' o FS word-eq fmt-eq (dispatch-arith val-riscv64 blk n s) a0 ≡ v
            → ArithRun s (dispatch-arith val-riscv64 blk n s) W v
  frame-run s n blk W v ok fits rm out = record
    { ar-out  = out
    ; ar-role = λ { role-sp _ → Sub.sub-sp ; role-clos _ → Sub.sub-s1 ; role-heap _ → Sub.sub-s2
                  ; role-in1 _ → Sub.sub-t0 ; role-out ne → ⊥-elim (ne refl) }
    ; ar-mem  = Sub.sub-mem
    ; ar-halt = Sub.sub-halt }
    where module Sub = AF.Sub val-riscv64 n blk s W ok fits rm

-- Plan 0.129 B5 / plan 0.123 α′ (f3): THE VALUE half of the block's run — a
-- theorem (`RiscV64.ArithBlockValue`, x86-64's twin): the decoded argument is
-- the block's input at its entry state (D391, D398), its `Int` leaves words
-- (D397), so the dispatch's `a0` is the block's meaning, the SigOp's output.
arith-block-value  : ∀ {hv : HeapView} prog fs s {A B} (si : SigOpInfo A B)
                   → RLr.RunLow o FS slot-size word-eq prog fs
                   → Internal (sem si) → CompiledCorr hv prog fs s → fetch prog (fpc fs) ≡ just (instr-sigop si)
                   → CFr.FlatCorrespondence.HeapView.hfront hv + CFr.FlatCorrespondence.slots (sigop-need si) ≤ FSimr.rreg' o FS word-eq fmt-eq s sp
                   → LocState.halted (floc fs) ≡ false
                   → ∀ (b : ArithBlock) → BlockOf si b
                   → FSimr.rreg' o FS word-eq fmt-eq (uncurry (dispatch-arith val-riscv64) (AE.block-payload b) s) a0
                     ≡ CFr.FlatCorrespondence.enc-sv hv (AbstractExec.exec-sigop-output {FS} si (floc fs))
arith-block-value {hv} prog fs s si r int cc ftq rm h .(mk-block _ NInt e) (is-block {n = NInt} e refl refl eq) =
  ABV.value-int prog fs s si e eq r int cc ftq h
    (≤-trans (+-monoʳ-≤ (CFr.FlatCorrespondence.HeapView.hfront hv)
               (subst (8 * required-scratch (normalize e) ≤_) (sym (cong (λ x → (5 + sigop-scratch x) * 8) eq))
                      (fits-W (required-scratch (normalize e)))))
             rm)
arith-block-value {hv} prog fs s si r int cc ftq rm h .(mk-block _ NFloat e) (is-block {n = NFloat} e refl refl eq) =
  ABV.value-flt prog fs s si e eq r int cc ftq h
    (≤-trans (+-monoʳ-≤ (CFr.FlatCorrespondence.HeapView.hfront hv)
               (subst (8 * required-scratch e ≤_) (sym (cong (λ x → (5 + sigop-scratch x) * 8) eq))
                      (fits-W (required-scratch e))))
             rm)

arith-dispatch-run : ∀ {hv : HeapView} prog fs s {A B} (si : SigOpInfo A B)
                   → RLr.RunLow o FS slot-size word-eq prog fs
                   → Internal (sem si) → CompiledCorr hv prog fs s → fetch prog (fpc fs) ≡ just (instr-sigop si)
                   → CFr.FlatCorrespondence.HeapView.hfront hv + CFr.FlatCorrespondence.slots (sigop-need si) ≤ FSimr.rreg' o FS word-eq fmt-eq s sp
                   → LocState.halted (floc fs) ≡ false
                   -- plan 0.123 α′ (f1): the block run is the SigOp's own (`arith-sigop-block`)
                   → ∀ (b : ArithBlock) → BlockOf si b
                   → ArithRun s (uncurry (dispatch-arith val-riscv64) (AE.block-payload b) s)
                              (CFr.FlatCorrespondence.slots (sigop-need si))
                              (CFr.FlatCorrespondence.enc-sv hv (AbstractExec.exec-sigop-output {FS} si (floc fs)))
arith-dispatch-run {hv} prog fs s si r int cc ftq rm h .(mk-block _ NInt e) bo@(is-block {n = NInt} e eA eB eq) =
  frame-run s (required-scratch (normalize e)) (emit-program (compile-abs (normalize e))) _ _
    (block-spills (normalize e))
    (subst (8 * required-scratch (normalize e) ≤_) (sym (cong (λ x → (5 + sigop-scratch x) * 8) eq)) (fits-W (required-scratch (normalize e))))
    (m+n≤o⇒n≤o (CFr.FlatCorrespondence.HeapView.hfront hv) rm)
    (arith-block-value {hv} prog fs s si r int cc ftq rm h _ bo)
arith-dispatch-run {hv} prog fs s si r int cc ftq rm h .(mk-block _ NFloat e) bo@(is-block {n = NFloat} e eA eB eq) =
  frame-run s (required-scratch e) (emit-program (compile-abs e)) _ _
    (block-spills e)
    (subst (8 * required-scratch e ≤_) (sym (cong (λ x → (5 + sigop-scratch x) * 8) eq)) (fits-W (required-scratch e)))
    (m+n≤o⇒n≤o (CFr.FlatCorrespondence.HeapView.hfront hv) rm)
    (arith-block-value {hv} prog fs s si r int cc ftq rm h _ bo)

------------------------------------------------------------------------
-- Plan 0.123 α′ (e): THE RUN HALF, from the frame lemma — the link, the halt
-- flag and the decode come from the run, the pc from the block offsets.
------------------------------------------------------------------------
arith-sigop-run : ∀ {hv : HeapView} (env : EE.RT.ArithEnv) prog fs s {A B} (si : SigOpInfo A B)
                → RLr.RunLow o FS slot-size word-eq prog fs
                → riscv64-arith-table prog env
                → Internal (sem si) → CompiledCorr hv prog fs s → fetch prog (fpc fs) ≡ just (instr-sigop si)
                → CFr.FlatCorrespondence.HeapView.hfront hv + CFr.FlatCorrespondence.slots (sigop-need si) ≤ FSimr.rreg' o FS word-eq fmt-eq s sp
                → LocState.halted (floc fs) ≡ false
                → ∀ (pl : List XInstr × ℕ) → env (once-symbol-path (SigOpInfo.name si)) ≡ just pl
                → CompiledCorr hv prog (flat-exec-instr (instr-sigop si) prog fs) (uncurry (dispatch-arith val-riscv64) pl s)
arith-sigop-run {hv} env prog fs s si r t int cc ftq rm h pl hit
  with arith-sigop-block env prog fs si t int ftq pl hit
... | b , bo , refl =
  sigop-arith-step prog fs s (uncurry (dispatch-arith val-riscv64) (AE.block-payload b) s) si r int (block-not-in-memory bo) cc ftq h rm
    (arith-dispatch-run {hv} prog fs s si r int cc ftq rm h b bo) refl
    (trans (cong suc (pc-off cc))
           (sym (trans (blk-off-suc prog (fpc fs) (instr-sigop si) ftq) (+-comm (blk-off prog (fpc fs)) 1))))

arith-sigop-contract : ∀ {hv : HeapView} (env : EE.RT.ArithEnv) prog fs s {A B} (si : SigOpInfo A B)
                     → RLr.RunLow o FS slot-size word-eq prog fs
                     → riscv64-arith-table prog env
                     → Internal (sem si) → CompiledCorr hv prog fs s → fetch prog (fpc fs) ≡ just (instr-sigop si)
                     → CFr.FlatCorrespondence.HeapView.hfront hv + CFr.FlatCorrespondence.slots (sigop-need si) ≤ FSimr.rreg' o FS word-eq fmt-eq s sp
                     → LocState.halted (floc fs) ≡ false
                     → Σ (List XInstr × ℕ) (λ pl → env (once-symbol-path (SigOpInfo.name si)) ≡ just pl
                         × CompiledCorr hv prog (flat-exec-instr (instr-sigop si) prog fs) (uncurry (dispatch-arith val-riscv64) pl s))
arith-sigop-contract {hv} env prog fs s si r t int cc ftq rm h =
  let (pl , hit) = arith-sigop-lookup env prog fs si t int ftq
  in pl , hit , arith-sigop-run {hv} env prog fs s si r t int cc ftq rm h pl hit

------------------------------------------------------------------------
-- …AND THE WHOLE SUPPLY, which is what opens the dispatch.
------------------------------------------------------------------------
riscv64-supply : EE.Supply
riscv64-supply = record
  { bss = riscv64-block-steps ; sts = riscv64-stuck-steps
  ; room-step = λ prog fs s k run cc st h ft → room-step-riscv64 prog fs s k cc st h ft
      (reg-range prog fs s sp run cc)
  ; start-step = λ prog fs s b rsv run cc h ft _ nf nst loq → start-step-riscv64 prog fs s b rsv cc h ft
      (reg-range prog fs s sp run cc) nf nst loq
  ; reg-range = reg-range ; ret-no-wrap = ret-no-wrap
  ; tag-fits = tag-fits ; lit-fits = lit-fits ; float-fits = float-fits
  ; arith-sigop-contract = arith-sigop-contract
  ; external-sigop-contract = external-sigop-contract
  }

-- ONE application, of the nested module, restricted to what the arch
-- module consumes: a module application copies every definition it lets
-- through into this interface, and the unrestricted pair copied the whole
-- dispatch twice.
module Dispatch′ = Dispatch.Dispatch o FS slot-size word-eq Reg riscv64-roles RS.W.modulus
                       riscv64-emitter riscv64-machine riscv64-traceloop riscv64-supply
  using (events-agree; events-agree-start; AgreeAt)
