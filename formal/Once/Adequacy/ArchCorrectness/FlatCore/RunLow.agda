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
open import Once.CCC.Codegen.RoomChecks using (room-checks; need)
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
open RunLow

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
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; offsetHL; module HeapLocation; module HeapRef)
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

-- plan 0.123 B.4 α: the offset forms' sites
load-at-target-ptr : ∀ prog (fs : FlatState) (k : ℕ) → RunLow prog fs → LocState.halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (load-at k)
                   → Σ (ValueLocation FS) (λ loc → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr loc)
load-at-target-ptr prog fs k =
  lift-site (load-at k) (λ _ ()) _ (λ src fs₀ → RW.load-at-target-ptr src fs₀ k) (λ _ _ _ c → c) prog fs

heap-load-at-written : ∀ prog (fs : FlatState) (k : ℕ) (hl : HeapLocation) → RunLow prog fs
                     → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just (load-at k)
                     → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                     → LocState.heapMem (floc fs) (offsetHL hl k) ≡ nothing → ⊥
heap-load-at-written prog fs k hl =
  lift-site (load-at k) (λ _ ()) (λ g → readReg (LocState.regs (floc g)) Input1 ≡ SV-Ptr (AtDynamic hl)
                                       → LocState.heapMem (floc g) (offsetHL hl k) ≡ nothing → ⊥)
    (λ src fs₀ r h f → RW.heap-load-at-written src fs₀ k hl r h f) (λ _ _ _ c → c) prog fs

store-at-target-ptr : ∀ prog (fs : FlatState) (k : ℕ) → RunLow prog fs → LocState.halted (floc fs) ≡ false
                    → fetch prog (fpc fs) ≡ just (store-at k)
                    → Σ (ValueLocation FS) (λ loc → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr loc)
store-at-target-ptr prog fs k =
  lift-site (store-at k) (λ _ ()) _ (λ src fs₀ → RW.store-at-target-ptr src fs₀ k) (λ _ _ _ c → c) prog fs

store-at-in-block : ∀ prog (fs : FlatState) (k : ℕ) (hl : HeapLocation) → RunLow prog fs
                  → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just (store-at k)
                  → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                  → ExecFinal.in-block? {FS} (block-size (falloc fs)) (AtDynamic (offsetHL hl k)) ≡ true
store-at-in-block prog fs k hl =
  lift-site (store-at k) (λ _ ()) (λ g → readReg (LocState.regs (floc g)) Input1 ≡ SV-Ptr (AtDynamic hl)
                                        → ExecFinal.in-block? {FS} (block-size (falloc g)) (AtDynamic (offsetHL hl k)) ≡ true)
    (λ src fs₀ r h f → RW.store-at-in-block src fs₀ k hl r h f) (λ _ _ _ c → c) prog fs

store-at-inbounds : ∀ prog (fs : FlatState) (k : ℕ) (hl : HeapLocation) → RunLow prog fs
                  → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just (store-at k)
                  → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                  → heap-offset (offsetHL hl k) < block-size (falloc fs) (ref-id (heap-ref (offsetHL hl k)))
store-at-inbounds prog fs k hl =
  lift-site (store-at k) (λ _ ()) (λ g → readReg (LocState.regs (floc g)) Input1 ≡ SV-Ptr (AtDynamic hl)
                                        → heap-offset (offsetHL hl k) < block-size (falloc g) (ref-id (heap-ref (offsetHL hl k))))
    (λ src fs₀ r h f → RW.store-at-inbounds src fs₀ k hl r h f) (λ _ _ _ c → c) prog fs

------------------------------------------------------------------------
-- THE FRAME, LINK AND RETURN FACTS. The lift maps the return stack and the
-- link register element-wise (`ret-map`), so a cons stays a cons and a link
-- stays a link; frames and memory are the base's.
------------------------------------------------------------------------
entry-empty : ∀ prog (fs : FlatState) (ℓ : EntryId) (bb : ℕ) → RunLow prog fs
            → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb))
            → frame-slots (falloc fs) ≡ 0
entry-empty prog fs ℓ bb =
  lift-site′ (instr-ctrl (c-entry ℓ bb)) (λ _ ()) (λ g → frame-slots (falloc g) ≡ 0)
    (λ src fs₀ r f → RW.entry-empty src fs₀ ℓ bb r f) (λ _ _ _ c → c) prog fs

entry-link : ∀ prog (fs : FlatState) (ℓ : EntryId) (bb : ℕ) → RunLow prog fs
           → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb))
           → Σ ℕ (λ r → flink fs ≡ just r)
entry-link prog fs ℓ bb =
  lift-site′ (instr-ctrl (c-entry ℓ bb)) (λ _ ()) (λ g → Σ ℕ (λ r → flink g ≡ just r))
    (λ src fs₀ r f → RW.entry-link src fs₀ ℓ bb r f)
    (λ src fs₀ p (r , e) → L.ret-map src r , cong (mmap (L.ret-map src)) e) prog fs

entry-ret : ∀ prog (fs : FlatState) (ℓ : EntryId) (bb : ℕ) → RunLow prog fs
          → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb))
          → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret fs ≡ rpc ∷ rest))
entry-ret prog fs ℓ bb =
  lift-site′ (instr-ctrl (c-entry ℓ bb)) (λ _ ()) (λ g → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret g ≡ rpc ∷ rest)))
    (λ src fs₀ r f → RW.entry-ret src fs₀ ℓ bb r f)
    (λ src fs₀ p (rpc , rest , e) → L.ret-map src rpc , map (L.ret-map src) rest , cong (map (L.ret-map src)) e)
    prog fs

ret-site-owes : ∀ prog (fs : FlatState) (b : ℕ) → RunLow prog fs
              → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
              → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret fs ≡ rpc ∷ rest))
ret-site-owes prog fs b =
  lift-site′ (instr-ctrl (c-ret b)) (λ _ ()) (λ g → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret g ≡ rpc ∷ rest)))
    (λ src fs₀ r f → RW.ret-site-owes src fs₀ b r f)
    (λ src fs₀ p (rpc , rest , e) → L.ret-map src rpc , map (L.ret-map src) rest , cong (map (L.ret-map src)) e)
    prog fs

ret-budget-matches : ∀ prog (fs : FlatState) (b : ℕ) → RunLow prog fs
                   → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
                   → b ≡ frame-slots (falloc fs)
ret-budget-matches prog fs b =
  lift-site′ (instr-ctrl (c-ret b)) (λ _ ()) (λ g → b ≡ frame-slots (falloc g))
    (λ src fs₀ r f → RW.ret-budget-matches src fs₀ b r f) (λ _ _ _ c → c) prog fs

-- a pending link means a call just happened, and the base run says so at every
-- instruction that is not an entry; a check is never one either
run-link-nothing : ∀ prog (fs : FlatState) → RunLow prog fs → ∀ {i : AbstractInstr}
                 → fetch prog (fpc fs) ≡ just i → (∀ k → i ≡ instr-room k → ⊥)
                 → (∀ (ℓ : EntryId) (bb : ℕ) → fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb)) → ⊥)
                 → flink fs ≡ nothing
run-link-nothing .(room-checks src) .(L.lift src fs₀ p) (mkRunLow src fs₀ p refl r refl pc) f nr ne
  with low-view src fs₀ p pc f
... | at-check k e _ = ⊥-elim (nr k e)
... | at-image refl fi =
  cong (mmap (L.ret-map src))
    (RW.run-link-nothing src fs₀ r (λ ℓ bb fe → ne ℓ bb (trans (fetch-room src (fpc fs₀)) fe)))

-- a return finds a saved frame (the base run's frames, `RetMatch`)
ret-saved : ∀ prog (fs : FlatState) → RunLow prog fs → ∀ rpc rest → fret fs ≡ rpc ∷ rest
          → Σ Frame (λ f₀ → Σ ℕ (λ b₀ → Σ (List (Frame × ℕ)) (λ frs → saved-frames (falloc fs) ≡ (f₀ , b₀) ∷ frs)))
ret-saved .(room-checks src) .(L.lift src fs₀ p) (mkRunLow src fs₀ p refl r refl pc) rpc rest req
  = go (fret fs₀) refl (RW.SegWF.seg-stack (RW.run-seg-wf src fs₀ r)) req
  where
    go : ∀ (rs : List ℕ) → fret fs₀ ≡ rs → RW.RetMatch src 0 (saved-frames (falloc fs₀)) (fret fs₀)
       → map (L.ret-map src) rs ≡ rpc ∷ rest
       → Σ Frame (λ f₀ → Σ ℕ (λ b₀ → Σ (List (Frame × ℕ)) (λ frs → saved-frames (falloc fs₀) ≡ (f₀ , b₀) ∷ frs)))
    go (x ∷ xs) e rm _ = cons (saved-frames (falloc fs₀)) refl (subst (RW.RetMatch src 0 (saved-frames (falloc fs₀))) e rm)
      where
        cons : ∀ (frs′ : List (Frame × ℕ)) → saved-frames (falloc fs₀) ≡ frs′ → RW.RetMatch src 0 frs′ (x ∷ xs)
             → Σ Frame (λ f₀ → Σ ℕ (λ b₀ → Σ (List (Frame × ℕ)) (λ frs → saved-frames (falloc fs₀) ≡ (f₀ , b₀) ∷ frs)))
        cons .((_ , _) ∷ _) e′ (RW.rm-∷ _ _ _) = _ , _ , _ , e′

-- the emitter's fences: what an image instruction may be (a check is one)
frame-op-absurd : ∀ prog (fs : FlatState) (i : AbstractInstr) → RunLow prog fs
                → fetch prog (fpc fs) ≡ just i → (∀ k → i ≡ instr-room k → ⊥) → ImageI i
frame-op-absurd .(room-checks src) .(L.lift src fs₀ p) i (mkRunLow src fs₀ p refl r refl pc) f nr
  with low-view src fs₀ p pc f
... | at-check k e _ = ⊥-elim (nr k e)
... | at-image _ fi = RW.frame-op-absurd src fs₀ i (run-emitted r) fi

-- a slot an instruction names is in the frame (a check names none)
slot-read-in-frame : ∀ prog (fs : FlatState) (slot : Slot) (i : AbstractInstr) → RunLow prog fs
                   → fetch prog (fpc fs) ≡ just i → slot-of i ≡ just slot
                   → slot < frame-slots (falloc fs)
slot-read-in-frame .(room-checks src) .(L.lift src fs₀ p) slot i (mkRunLow src fs₀ p refl r refl pc) f so
  with low-view src fs₀ p pc f
... | at-check k refl _ = ⊥-elim (no-slot so)
  where no-slot : slot-of (instr-room k) ≡ just slot → ⊥
        no-slot ()
... | at-image _ fi = RW.slot-read-in-frame src fs₀ slot i r fi so

-- the state invariants: the lift keeps what they speak of
run-stack-ptr : ∀ prog (fs : FlatState) → RunLow prog fs → StackPtrWF fs
run-stack-ptr .(room-checks src) .(L.lift src fs₀ p) (mkRunLow src fs₀ p refl r refl pc) = RW.run-stack-ptr src fs₀ r

run-ptr-bounds : ∀ prog (fs : FlatState) → RunLow prog fs → PtrBoundsWF fs
run-ptr-bounds .(room-checks src) .(L.lift src fs₀ p) (mkRunLow src fs₀ p refl r refl pc) = RW.run-ptr-bounds src fs₀ r

stack-ptr-current : ∀ prog (fs : FlatState) (f : Frame) (k : Slot) → RunLow prog fs
                  → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
                  → (f ≡ current-frame (falloc fs)) × (k < frame-slots (falloc fs))
stack-ptr-current .(room-checks src) .(L.lift src fs₀ p) f k (mkRunLow src fs₀ p refl r refl pc) =
  RW.stack-ptr-current src fs₀ f k r

stack-ptr-current-suc : ∀ prog (fs : FlatState) (f : Frame) (k : Slot) → RunLow prog fs
                      → readReg (LocState.regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
                      → (f ≡ current-frame (falloc fs)) × (suc k < frame-slots (falloc fs))
stack-ptr-current-suc .(room-checks src) .(L.lift src fs₀ p) f k (mkRunLow src fs₀ p refl r refl pc) =
  RW.stack-ptr-current-suc src fs₀ f k r

-- a direct call resolves (the entry scan commutes with the map)
emitted-call-fn-resolves : ∀ prog (fs : FlatState) (f : CN) → RunLow prog fs
                         → fetch prog (fpc fs) ≡ just (instr-ctrl (c-call-fn f))
                         → Σ ℕ (λ j → find-fn prog f ≡ just j)
emitted-call-fn-resolves .(room-checks src) .(L.lift src fs₀ p) f (mkRunLow src fs₀ p refl r refl pc) ft
  with low-view src fs₀ p pc ft
... | at-check k () _
... | at-image _ fi with RW.emitted-call-fn-resolves src fs₀ f r fi
...   | j , e = φ src j , trans (find-entry-room src (e-fn f)) (cong (mmap (φ src)) e)

-- …and a closure call's shape (the base run's; its scan commutes too)
call-site-shape : ∀ prog (fs : FlatState) → RunLow prog fs
                → fetch prog (fpc fs) ≡ just instr-call-closure
                → Σ HeapLocation (λ hl → Σ LabelId (λ ℓ → Σ ℕ (λ j →
                    (fclosure fs ≡ SV-Ptr (AtDynamic hl))
                    × (LocState.heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ))
                    × (find-thunk prog ℓ ≡ just j))))
call-site-shape .(room-checks src) .(L.lift src fs₀ p) (mkRunLow src fs₀ p refl r refl pc) ft
  with low-view src fs₀ p pc ft
... | at-check k () _
... | at-image _ fi with RW.call-site-shape src fs₀ r fi
...   | hl , ℓ , j , ce , he , fe = hl , ℓ , φ src j , ce , he , trans (find-entry-room src (e-thunk ℓ)) (cong (mmap (φ src)) fe)

-- THE START IS BEHIND US: the base run past its pc 0 never fetches the start
start-behind : ∀ prog (fs : FlatState) (b : ℕ) (r : RunLow prog fs) → (fpc (run-at r) ≡ 0 → ⊥)
             → fetch prog (fpc fs) ≡ just (instr-ctrl (c-start b)) → ⊥
start-behind .(room-checks src) .(L.lift src fs₀ p) b (mkRunLow src fs₀ p refl r refl pc) past ft
  with low-view src fs₀ p pc ft
... | at-check k () _
... | at-image _ fi = past (RW.start-at-zero src (fpc fs₀) b (run-emitted r) fi)

-- THE RUN GOES ON, PAST ITS START: `low-step`, and the base run is still past
-- pc 0 after it (a check leaves the base where it is; any other step is a base
-- step, and no base step lands on pc 0 — `RW.run-step-pc-pos`).
low-step-past : ∀ (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr) (r : RunLow prog fs)
              → fetch prog (fpc fs) ≡ just i → LocState.halted (floc fs) ≡ false
              → (fpc (run-at r) ≡ 0 → ⊥)
              → Σ (RunLow prog (flat-exec-instr i prog fs)) (λ r′ → fpc (run-at r′) ≡ 0 → ⊥)
low-step-past .(room-checks src) .(RoomSim.lift {FS} src fs₀ p) i (mkRunLow src fs₀ p refl r refl pc) f h past
  with low-view src fs₀ p pc f
... | at-check k refl sp = mkRunLow src fs₀ (suc p) refl r refl (inj₁ sp) , past
... | at-image refl fi with RoomSim.step-lift {FS} src fs₀ i
...   | p′ , e , pr′ =
  mkRunLow src (flat-exec-instr i src fs₀) p′ refl
    (mkRunAt (run-tbl r) (run-ir r) (run-emit r) (run-linked r) (reach-step i fs₀ (run-reach r) fi h))
    e pr′
  , RW.run-step-pc-pos src fs₀ i r fi

-- a code address the image loads names a body that exists (the base image's
-- fact, `RW.emitted-code-addr-has-body`; the entry scan commutes)
code-addr-has-body : ∀ prog (fs : FlatState) (ℓ : LabelId) → RunLow prog fs
                   → fetch prog (fpc fs) ≡ just (instr-load-code-addr ℓ)
                   → Σ ℕ (λ j → find-thunk prog ℓ ≡ just j)
code-addr-has-body .(room-checks src) .(L.lift src fs₀ p) ℓ (mkRunLow src fs₀ p refl r refl pc) ft
  with low-view src fs₀ p pc ft
... | at-check k () _
... | at-image _ fi with base
  where
    base : Σ ℕ (λ j → find-thunk src ℓ ≡ just j)
    base = subst (λ pr → Σ ℕ (λ j → find-thunk pr ℓ ≡ just j)) (sym (run-emit r))
             (RW.emitted-code-addr-has-body (run-tbl r) (run-ir r) (fpc fs₀) ℓ
               (subst (λ pr → fetch pr (fpc fs₀) ≡ just (instr-load-code-addr ℓ)) (run-emit r) fi))
...   | j , e = φ src j , trans (find-entry-room src (e-thunk ℓ)) (cong (mmap (φ src)) e)

-- a step that is not a check moves the base run on — past its pc 0, whatever
-- it was before (no base step lands on pc 0, `RW.run-step-pc-pos`)
low-step-image : ∀ (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr) (r : RunLow prog fs)
               → fetch prog (fpc fs) ≡ just i → LocState.halted (floc fs) ≡ false
               → (∀ k → i ≡ instr-room k → ⊥)
               → Σ (RunLow prog (flat-exec-instr i prog fs)) (λ r′ → fpc (run-at r′) ≡ 0 → ⊥)
low-step-image .(room-checks src) .(RoomSim.lift {FS} src fs₀ p) i (mkRunLow src fs₀ p refl r refl pc) f h nr
  with low-view src fs₀ p pc f
... | at-check k e _ = ⊥-elim (nr k e)
... | at-image refl fi with RoomSim.step-lift {FS} src fs₀ i
...   | p′ , e , pr′ =
  mkRunLow src (flat-exec-instr i src fs₀) p′ refl
    (mkRunAt (run-tbl r) (run-ir r) (run-emit r) (run-linked r) (reach-step i fs₀ (run-reach r) fi h))
    e pr′
  , RW.run-step-pc-pos src fs₀ i r fi

-- A RETURN LANDS ON A CHECK (plan 0.123 A.4 step 5, the budget): the base run's
-- return addresses are one past a call (`RetMatch`, D094), the lift maps one past
-- a call to one past its image, and the pass put a check right there.
ret-lands-check : ∀ prog (fs : FlatState) → RunLow prog fs → ∀ rpc rest → fret fs ≡ rpc ∷ rest
                → Σ ℕ (λ k → fetch prog rpc ≡ just (instr-room k))
ret-lands-check .(room-checks src) .(L.lift src fs₀ p) (mkRunLow src fs₀ p refl r refl pc) rpc rest req
  = go (fret fs₀) (saved-frames (falloc fs₀)) (RW.SegWF.seg-stack (RW.run-seg-wf src fs₀ r)) req
  where
    open import Once.CCC.Codegen.RoomChecksFacts using (module NeedFacts)
    open NeedFacts {FS} using (boundary-next; call-boundary)
    go : ∀ (rs : List ℕ) (frs : List (Frame × ℕ)) → RW.RetMatch src 0 frs rs → map (L.ret-map src) rs ≡ rpc ∷ rest
       → Σ ℕ (λ k → fetch (room-checks src) rpc ≡ just (instr-room k))
    go .(_ ∷ _) .(_ ∷ _) (RW.rm-∷ _ (q , refl , c , fq , ci) _) e =
      subst (λ z → Σ ℕ (λ k → fetch (room-checks src) z ≡ just (instr-room k))) (cong head′ e)
        (boundary-next src (φ src q) (trans (fetch-room src q) fq) (call-boundary c ci))
      where head′ : List ℕ → ℕ
            head′ []      = 0
            head′ (x ∷ _) = x

-- A CHECK COVERS EXACTLY WHAT FOLLOWS IT (plan 0.123 A.4 step 5): the run's image
-- is a program image, which has no checks of its own (`image-noroom`), so every
-- check of the lowered image holds the measure past it (`check-k`).
check-need : ∀ prog (fs : FlatState) → RunLow prog fs → ∀ k
           → fetch prog (fpc fs) ≡ just (instr-room k)
           → k ≡ need prog (suc (fpc fs))
check-need .(room-checks src) .(L.lift src fs₀ p) (mkRunLow src fs₀ p refl r refl pc) k f =
  trans (check-k src noroom p k f)
        (cong (λ E → till-check E (Data.List.drop (suc p) (room-checks src))) (sym (max-entry-room src)))
  where
    import Data.List
    open import Data.List.Relation.Unary.All using (All)
    open import Once.CCC.Machine.FrameFree using (ImageI)
    open import Once.CCC.Codegen.RoomChecks using (till-check; max-entry)
    open import Once.CCC.Codegen.RoomChecksFacts using (module CheckK; image-noroom; max-entry-room; NoRoom)
    open CheckK {FS} using (check-k)
    open import Once.CCC.Codegen.ProgramImageFacts o using (image-frame-free)
    noroom : NoRoom src
    noroom = image-noroom src (subst (All ImageI) (sym (RunAt.run-emit r))
                                     (image-frame-free (RunAt.run-tbl r) (RunAt.run-ir r)))
