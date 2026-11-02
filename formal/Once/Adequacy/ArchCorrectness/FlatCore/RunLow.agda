-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.RunLow — the run of the LOWERED image.
--
-- Plan 0.123 A.4 step 5 (D371). The backends lower `room-checks t`, the image
-- with the room checks, not `t`. `RunAt` (`RunContext`) and every fact in
-- `RunWF` stay what they were: facts about the run of `t`. A state of the
-- lowered image's run is the LIFT of a state of `t`'s run (`RoomChecksSim`):
-- the same memory, frames and closure register, its pc / return stack / link
-- register moved by the index map. `RunLow` says exactly that, and this module
-- carries each fact the engine needs across the lift:
--
--   * at a check, the fact is vacuous — `instr-room` reads no slot, calls
--     nothing, allocates nothing, jumps nowhere;
--   * anywhere else the lowered image holds `t`'s instruction (`fetch-room`),
--     and the fact is `RunWF`'s, at the state the lift is of.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Name using (CanonicalName)

module Once.Adequacy.ArchCorrectness.FlatCore.RunLow (o : CanonicalName)
  (FS : FrameSemantics)
  (slot-size : ℕ)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.CCC.Codegen.RoomChecksFacts using (φ; module RoomFacts)
open RoomFacts {FS} using (fetch-room)
open import Once.CCC.Codegen.RoomChecksSim using (module RoomSim)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (Sound)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq

-- THE RUN OF THE LOWERED IMAGE: `prog` is `t` with its checks, and `fs` is the
-- lift of a state `t`'s run reaches, at a pc that stands for that state's.
record RunLow (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkRunLow
  field
    run-src  : AbstractTrace
    run-at   : FlatState
    run-p    : ℕ
    run-prog : prog ≡ room-checks run-src
    run-img  : RunAt run-src run-at
    run-lift : fs ≡ RoomSim.lift {FS} run-src run-at run-p
    run-pc   : RoomSim.PcRel {FS} run-src (fpc run-at) run-p
open RunLow public

-- WHAT A LOWERED STATE FETCHES: a check, or `t`'s own instruction at the state
-- the lift is of (and then the lift is AT that state's image).
data LowView (src : AbstractTrace) (fs₀ : FlatState) (p : ℕ) (i : AbstractInstr) : Set where
  at-check : ∀ (k : ℕ) → i ≡ instr-room k → suc p ≡ φ src (fpc fs₀) → LowView src fs₀ p i
  at-image : p ≡ φ src (fpc fs₀) → fetch src (fpc fs₀) ≡ just i → LowView src fs₀ p i

low-view : ∀ (src : AbstractTrace) (fs₀ : FlatState) (p : ℕ) {i : AbstractInstr}
         → RoomSim.PcRel {FS} src (fpc fs₀) p
         → fetch (room-checks src) p ≡ just i → LowView src fs₀ p i
low-view src fs₀ p (inj₂ (sp , k , fk)) f = at-check k (just-injective (trans (sym f) fk)) sp
low-view src fs₀ p (inj₁ refl)          f = at-image refl (trans (sym (fetch-room src (fpc fs₀))) f)

-- a check is no instruction a site fact is about
room≢ : ∀ {k : ℕ} {i : AbstractInstr} → i ≡ instr-room k → (∀ {k′} → i ≡ instr-room k′ → ⊥) → ⊥
room≢ e ne = ne e

open import Once.CCC.Codegen.RoomChecksFacts using (ψ)
open RoomFacts {FS} using (ψ-zero)

------------------------------------------------------------------------
-- THE RUN GOES ON: a step of the lowered image keeps it a lift of `t`'s run.
-- A check only moves the lifted pc on to the state's image; any other step is
-- `t`'s own (`step-lift`), and `t`'s run takes it too (`reach-step`).
------------------------------------------------------------------------
low-step : ∀ (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr) → RunLow prog fs
         → fetch prog (fpc fs) ≡ just i → LocState.halted (floc fs) ≡ false
         → RunLow prog (flat-exec-instr i prog fs)
low-step .(room-checks src) .(RoomSim.lift {FS} src fs₀ p) i (mkRunLow src fs₀ p refl r refl pc) f h
  with low-view src fs₀ p pc f
... | at-check k refl sp = mkRunLow src fs₀ (suc p) refl r refl (inj₁ sp)
... | at-image refl fi with RoomSim.step-lift {FS} src fs₀ i
...   | p′ , e , pr′ =
  mkRunLow src (flat-exec-instr i src fs₀) p′ refl
    (mkRunAt (run-tbl r) (run-ir r) (run-emit r) (run-linked r) (reach-step i fs₀ (run-reach r) fi h))
    e pr′

-- …and NEVER FAULTS (D367 carried across the pass, `sound-room`).
low-sound : ∀ {prog fs} → RunLow prog fs → Sound prog fs
low-sound (mkRunLow src fs₀ p refl r refl pc) = RoomSim.sound-room {FS} src fs₀ p pc (run-sound r)

-- THE START: the lift of `t`'s start state at pc 0 — the start's check.
low-start : ∀ (src : AbstractTrace) (fs₀ : FlatState) → RunAt src fs₀ → fpc fs₀ ≡ 0
          → RunLow (room-checks src) (RoomSim.lift {FS} src fs₀ 0)
low-start src fs₀ r p0 =
  mkRunLow src fs₀ 0 refl r refl
    (inj₂ (subst (λ c → suc 0 ≡ φ src c) (sym p0) (cong suc (sym (ψ-zero src))) , _ , refl))

------------------------------------------------------------------------
-- THE SITE FACTS, LIFTED. Each is `RunWF`'s, at the state the lift is of; a
-- check is never the instruction a fact is about.
------------------------------------------------------------------------
import Once.Adequacy.ArchCorrectness.FlatCore.RunWF o FS slot-size word-eq as RW
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using () renaming (map to mmap)
open import Once.CCC.Machine.Locations using (ValueLocation; AtDynamic; AtStack; Slot)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; module HeapLocation; module HeapRef)
open HeapLocation using (heap-offset; heap-ref)
open HeapRef using (ref-id)
open import Once.CCC.Label using (LabelId; EntryId)
open import Once.Spec.Name using () renaming (CanonicalName to CN)
open import Data.Product using (∃)
open import Data.Nat using (_<_)
open import Once.Type using (fits-int)
open import Once.CCC.Machine.FlatStoreWF FS using (FlatWF)
open import Once.CCC.Machine.FlatStackPtr FS using (StackPtrWF)
open import Once.CCC.Machine.FlatPtrBounds FS using (PtrBoundsWF)
open import Once.CCC.Machine.FrameFree using (ImageI)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open AllocState using (frame-slots; saved-frames; block-size; current-frame)
open MemOps {FS} using (readLoc)
open FrameSemantics FS using (Frame)
open RoomFacts {FS} using (find-entry-room)

private
  module L = RoomSim {FS}

-- a fact about one non-check instruction `I`, from the base run's, when the fact
-- speaks of the state only through what the lift keeps (memory, frames)
lift-site : ∀ (I : AbstractInstr) → (∀ k → I ≡ instr-room k → ⊥) → (C : FlatState → Set)
          → (∀ src fs₀ → RunAt src fs₀ → LocState.halted (floc fs₀) ≡ false → fetch src (fpc fs₀) ≡ just I → C fs₀)
          → (∀ src fs₀ p → C fs₀ → C (L.lift src fs₀ p))
          → ∀ prog fs → RunLow prog fs → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just I → C fs
lift-site I nr C base tr .(room-checks src) .(L.lift src fs₀ p) (mkRunLow src fs₀ p refl r refl pc) h f
  with low-view src fs₀ p pc f
... | at-check k e _  = ⊥-elim (nr k e)
... | at-image _ fi   = tr src fs₀ p (base src fs₀ r h fi)

-- …and the same without the running premise
lift-site′ : ∀ (I : AbstractInstr) → (∀ k → I ≡ instr-room k → ⊥) → (C : FlatState → Set)
           → (∀ src fs₀ → RunAt src fs₀ → fetch src (fpc fs₀) ≡ just I → C fs₀)
           → (∀ src fs₀ p → C fs₀ → C (L.lift src fs₀ p))
           → ∀ prog fs → RunLow prog fs → fetch prog (fpc fs) ≡ just I → C fs
lift-site′ I nr C base tr .(room-checks src) .(L.lift src fs₀ p) (mkRunLow src fs₀ p refl r refl pc) f
  with low-view src fs₀ p pc f
... | at-check k e _  = ⊥-elim (nr k e)
... | at-image _ fi   = tr src fs₀ p (base src fs₀ r fi)

step-ok : ∀ prog (fs : FlatState) (i : AbstractInstr) → RunLow prog fs
        → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just i
        → LocState.faulted (floc (flat-exec-instr i prog fs)) ≡ false
step-ok prog fs i r h f = low-sound r (FlatStepsAPI._∷_ {FS} (h , f) FlatStepsAPI.[])

slot-read-written : ∀ prog (fs : FlatState) (slot : Slot) (i : AbstractInstr) → RunLow prog fs
                  → LocState.halted (floc fs) ≡ false
                  → fetch prog (fpc fs) ≡ just i → RW.SlotRead i slot
                  → LocState.stackMem (floc fs) (current-frame (falloc fs)) slot ≡ nothing → ⊥
slot-read-written .(room-checks src) .(L.lift src fs₀ p) slot i (mkRunLow src fs₀ p refl r refl pc) h f sr
  with low-view src fs₀ p pc f
... | at-check k refl _ = λ _ → no-slot sr
  where no-slot : RW.SlotRead (instr-room k) slot → ⊥
        no-slot ()
... | at-image _ fi = RW.slot-read-written src fs₀ slot i r h fi sr

load-indirect-target-wf : ∀ prog (fs : FlatState) → RunLow prog fs → LocState.halted (floc fs) ≡ false
                        → fetch prog (fpc fs) ≡ just load-indirect
                        → Σ (ValueLocation FS) (λ loc →
                            (readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr loc)
                            × (∀ hl → loc ≡ AtDynamic hl
                               → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))))
load-indirect-target-wf = lift-site load-indirect (λ _ ()) _ RW.load-indirect-target-wf (λ _ _ _ c → c)

load-indirect-suc-target-wf : ∀ prog (fs : FlatState) → RunLow prog fs → LocState.halted (floc fs) ≡ false
                            → fetch prog (fpc fs) ≡ just load-indirect-suc
                            → Σ (ValueLocation FS) (λ loc →
                                (readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr loc)
                                × (∀ hl → loc ≡ AtDynamic hl
                                   → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl)))))
load-indirect-suc-target-wf = lift-site load-indirect-suc (λ _ ()) _ RW.load-indirect-suc-target-wf (λ _ _ _ c → c)

heap-load-written : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunLow prog fs
                  → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just load-indirect
                  → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                  → LocState.heapMem (floc fs) hl ≡ nothing → ⊥
heap-load-written prog fs hl =
  lift-site load-indirect (λ _ ()) (λ g → readReg (LocState.regs (floc g)) Input1 ≡ SV-Ptr (AtDynamic hl)
                                         → LocState.heapMem (floc g) hl ≡ nothing → ⊥)
    (λ src fs₀ r h f → RW.heap-load-written src fs₀ hl r h f) (λ _ _ _ c → c) prog fs

heap-load-suc-written : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunLow prog fs
                      → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just load-indirect-suc
                      → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                      → LocState.heapMem (floc fs) (sucHL hl) ≡ nothing → ⊥
heap-load-suc-written prog fs hl =
  lift-site load-indirect-suc (λ _ ()) (λ g → readReg (LocState.regs (floc g)) Input1 ≡ SV-Ptr (AtDynamic hl)
                                             → LocState.heapMem (floc g) (sucHL hl) ≡ nothing → ⊥)
    (λ src fs₀ r h f → RW.heap-load-suc-written src fs₀ hl r h f) (λ _ _ _ c → c) prog fs

out-nz-output-word : ∀ prog (fs : FlatState) → RunLow prog fs → LocState.halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (instr-reg-op out-nz)
                   → ∃ λ w → readReg (LocState.regs (floc fs)) Output ≡ SV-Lit fits-int w
out-nz-output-word = lift-site (instr-reg-op out-nz) (λ _ ()) _ RW.out-nz-output-word (λ _ _ _ c → c)

store-nonptr-absurd : ∀ prog (fs : FlatState) {v : StoredValue FS} → RunLow prog fs
                    → LocState.halted (floc fs) ≡ false
                    → fetch prog (fpc fs) ≡ just store-indirect
                    → readReg (LocState.regs (floc fs)) Input1 ≡ v
                    → (∀ (loc : ValueLocation FS) → v ≡ SV-Ptr loc → ⊥)
                    → ⊥
store-nonptr-absurd prog fs {v} =
  lift-site store-indirect (λ _ ()) (λ g → readReg (LocState.regs (floc g)) Input1 ≡ v
                                         → (∀ (loc : ValueLocation FS) → v ≡ SV-Ptr loc → ⊥) → ⊥)
    (λ src fs₀ r h f → RW.store-nonptr-absurd src fs₀ r h f) (λ _ _ _ c → c) prog fs

store-suc-nonptr-absurd : ∀ prog (fs : FlatState) {v : StoredValue FS} → RunLow prog fs
                        → LocState.halted (floc fs) ≡ false
                        → fetch prog (fpc fs) ≡ just store-indirect-suc
                        → readReg (LocState.regs (floc fs)) Input1 ≡ v
                        → (∀ (loc : ValueLocation FS) → v ≡ SV-Ptr loc → ⊥)
                        → ⊥
store-suc-nonptr-absurd prog fs {v} =
  lift-site store-indirect-suc (λ _ ()) (λ g → readReg (LocState.regs (floc g)) Input1 ≡ v
                                             → (∀ (loc : ValueLocation FS) → v ≡ SV-Ptr loc → ⊥) → ⊥)
    (λ src fs₀ r h f → RW.store-suc-nonptr-absurd src fs₀ r h f) (λ _ _ _ c → c) prog fs

branch-tag-scrutinee-wf : ∀ prog (fs : FlatState) (m : LabelId) → RunLow prog fs
                        → LocState.halted (floc fs) ≡ false
                        → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero m))
                        → Σ (ValueLocation FS) (λ loc → Σ (StoredValue FS) (λ v →
                            (readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr loc)
                            × (readLoc (floc fs) loc ≡ just v) × RW.TagCell v))
branch-tag-scrutinee-wf prog fs m =
  lift-site (instr-ctrl (c-branch-tag-zero m)) (λ _ ()) _ (λ src fs₀ → RW.branch-tag-scrutinee-wf src fs₀ m)
    (λ _ _ _ c → c) prog fs

store-indirect-inbounds : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunLow prog fs
                        → fetch prog (fpc fs) ≡ just store-indirect
                        → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                        → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))
store-indirect-inbounds prog fs hl =
  lift-site′ store-indirect (λ _ ()) (λ g → readReg (LocState.regs (floc g)) Input1 ≡ SV-Ptr (AtDynamic hl)
                                          → heap-offset hl < block-size (falloc g) (ref-id (heap-ref hl)))
    (λ src fs₀ r f → RW.store-indirect-inbounds src fs₀ hl r f) (λ _ _ _ c → c) prog fs

store-indirect-suc-inbounds : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunLow prog fs
                            → fetch prog (fpc fs) ≡ just store-indirect-suc
                            → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                            → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl)))
store-indirect-suc-inbounds prog fs hl =
  lift-site′ store-indirect-suc (λ _ ()) (λ g → readReg (LocState.regs (floc g)) Input1 ≡ SV-Ptr (AtDynamic hl)
                                              → heap-offset (sucHL hl) < block-size (falloc g) (ref-id (heap-ref (sucHL hl))))
    (λ src fs₀ r f → RW.store-indirect-suc-inbounds src fs₀ hl r f) (λ _ _ _ c → c) prog fs
