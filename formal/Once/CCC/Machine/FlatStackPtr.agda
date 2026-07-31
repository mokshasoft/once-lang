-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatStackPtr   (Plan 0.54 rung D, item 2)
--
-- EVERY STACK POINTER IN THE STATE ADDRESSES A LIVE PAIR OF THE CURRENT FRAME:
-- its frame IS `current-frame`, and BOTH its slot and the next one are inside
-- the live window (`suc k < stackSlot`).
--
-- This is the state invariant behind the flat↔x86-64 residuals
-- `stack-ptr-current` and `stack-ptr-current-suc` — "a pointer in `Input1`
-- targets the current frame's live slots" — which the correspondence needs
-- before it can treat a load or store through such a pointer as an ordinary
-- step (an older frame's slots would need `stack-eq` to reach beyond the
-- current frame, and there is no address for them).
--
-- WHY THE PAIR FORM (`suc k < stackSlot`, not `k < stackSlot`): every producer
-- of a stack pointer is a `lea-slot k` addressing the FIRST of two adjacent
-- slots the same prologue reserved — the pair `⟨_,_⟩ Stack` (fst/snd), the
-- closure record `curry _ Stack` (env/code), and the sum payload `inl`/`inr`
-- `Stack` (tag/payload). So the invariant that is actually true is about the
-- pair, and it yields the single-slot form for free.
--
-- WHY IT IS AN INVARIANT AT ALL (and was not, before today): the frame ops are
-- the only instructions that move `current-frame` or `stackSlot`, and
-- `ir-to-trace` emits none of them (`Once.CCC.Codegen.FrameFreeTrace`), so both
-- anchors are FIXED for the whole run. Under a moving frame this predicate
-- would be destroyed by every call.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatStackPtr (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.CCC.Machine.SMCore
open FrameSemantics FS using (Frame)
open MemOps {FS}
open import Once.CCC.Machine.Flat
open FlatMachine {FS}

------------------------------------------------------------------------
-- The per-value predicate. A CATCHALL for the non-stack-pointer shapes, which
-- still reduces on a concrete constructor — and reduces to the CONJUNCTION on
-- `SV-Ptr (AtStack f k)`, so a use site that has the register equation gets
-- both halves with no clash boilerplate.
------------------------------------------------------------------------
StackPtrOK : Frame → ℕ → StoredValue FS → Set
StackPtrOK cf n (SV-Ptr (AtStack f k)) = (f ≡ cf) × (suc k < n)
{-# CATCHALL #-}
StackPtrOK cf n _                      = ⊤

-- …lifted to a memory cell (an unwritten cell holds no pointer at all)
StackPtrOK? : Frame → ℕ → Maybe (StoredValue FS) → Set
StackPtrOK? cf n (just v) = StackPtrOK cf n v
StackPtrOK? cf n nothing  = ⊤

------------------------------------------------------------------------
-- The state invariant: registers, heap cells and stack cells alike. All three
-- are needed — a load moves a value from memory into a register, so an
-- invariant about registers alone is not preserved.
------------------------------------------------------------------------
record StackPtrWF (fs : FlatState) : Set where
  constructor mkStackPtrWF
  field
    sp-regs  : ∀ (r : AbstractReg)
             → StackPtrOK (current-frame (falloc fs)) (stackSlot (regs (floc fs)))
                          (readReg (regs (floc fs)) r)
    sp-heap  : ∀ (hl : HeapLocation)
             → StackPtrOK? (current-frame (falloc fs)) (stackSlot (regs (floc fs)))
                           (heapMem (floc fs) hl)
    sp-stack : ∀ (f : Frame) (k : Slot)
             → StackPtrOK? (current-frame (falloc fs)) (stackSlot (regs (floc fs)))
                           (stackMem (floc fs) f k)
open StackPtrWF public

------------------------------------------------------------------------
-- THE USE-SITE FORMS. `StackPtrOK … (SV-Ptr (AtStack f k))` REDUCES to the
-- conjunction, so a route that knows what `Input1` holds reads both halves off
-- the invariant directly.
------------------------------------------------------------------------
stack-ptr-frame : ∀ (fs : FlatState) (r : AbstractReg) (f : Frame) (k : Slot)
                → StackPtrWF fs
                → readReg (regs (floc fs)) r ≡ SV-Ptr (AtStack f k)
                → f ≡ current-frame (falloc fs)
stack-ptr-frame fs r f k wf eq = proj₁ (subst (StackPtrOK _ _) eq (sp-regs wf r))

-- the PAIR bound: the cell after it is live too
stack-ptr-suc-live : ∀ (fs : FlatState) (r : AbstractReg) (f : Frame) (k : Slot)
                   → StackPtrWF fs
                   → readReg (regs (floc fs)) r ≡ SV-Ptr (AtStack f k)
                   → suc k < stackSlot (regs (floc fs))
stack-ptr-suc-live fs r f k wf eq = proj₂ (subst (StackPtrOK _ _) eq (sp-regs wf r))

-- …hence the cell itself is
stack-ptr-live : ∀ (fs : FlatState) (r : AbstractReg) (f : Frame) (k : Slot)
               → StackPtrWF fs
               → readReg (regs (floc fs)) r ≡ SV-Ptr (AtStack f k)
               → k < stackSlot (regs (floc fs))
stack-ptr-live fs r f k wf eq =
  ≤-trans (n≤1+n (suc k)) (stack-ptr-suc-live fs r f k wf eq)

------------------------------------------------------------------------
-- BRICKS FOR THE PRESERVATION PROOF (`ConcFlatSim.stack-ptr-step`).
--
-- The step lemma is a per-instruction induction, but every case has the same
-- two moves: the ANCHORS (`current-frame`, `stackSlot`) do not move — a
-- frame-free instruction cannot touch either — and the VALUE written is one the
-- invariant already covers (read out of a register or a cell) or a freshly
-- built non-stack-pointer. These bricks are those two moves, stated once.
------------------------------------------------------------------------

-- Reading back a register after a write: either you get the written value, or
-- the write missed you. Enumerated, because `writeReg` dispatches on the
-- register, so each entry holds DEFINITIONALLY.
readReg-write : ∀ (rf : Registers FS) (x r : AbstractReg) (v : StoredValue FS)
              → (readReg (writeReg rf x v) r ≡ v) ⊎ (readReg (writeReg rf x v) r ≡ readReg rf r)
readReg-write rf Input1  Input1  v = inj₁ refl
readReg-write rf Input1  Input2  v = inj₂ refl
readReg-write rf Input1  Output  v = inj₂ refl
readReg-write rf Input1  Scratch v = inj₂ refl
readReg-write rf Input1  Count   v = inj₂ refl
readReg-write rf Input2  Input1  v = inj₂ refl
readReg-write rf Input2  Input2  v = inj₁ refl
readReg-write rf Input2  Output  v = inj₂ refl
readReg-write rf Input2  Scratch v = inj₂ refl
readReg-write rf Input2  Count   v = inj₂ refl
readReg-write rf Output  Input1  v = inj₂ refl
readReg-write rf Output  Input2  v = inj₂ refl
readReg-write rf Output  Output  v = inj₁ refl
readReg-write rf Output  Scratch v = inj₂ refl
readReg-write rf Output  Count   v = inj₂ refl
readReg-write rf Scratch Input1  v = inj₂ refl
readReg-write rf Scratch Input2  v = inj₂ refl
readReg-write rf Scratch Output  v = inj₂ refl
readReg-write rf Scratch Scratch v = inj₁ refl
readReg-write rf Scratch Count   v = inj₂ refl
readReg-write rf Count   Input1  v = inj₂ refl
readReg-write rf Count   Input2  v = inj₂ refl
readReg-write rf Count   Output  v = inj₂ refl
readReg-write rf Count   Scratch v = inj₂ refl
readReg-write rf Count   Count   v = inj₁ refl

-- A register write of an OK value preserves the invariant. `writeReg` leaves
-- both anchors alone (`writeReg-preserves-stackSlot`; the frame lives in the
-- AllocState, which a register write does not touch), so the goal's anchors are
-- the same ones the hypothesis speaks about.
sp-write-reg : ∀ (fs : FlatState) (x : AbstractReg) (v : StoredValue FS)
             → StackPtrOK (current-frame (falloc fs)) (stackSlot (regs (floc fs))) v
             → StackPtrWF fs
             → StackPtrWF (record fs { floc = record (floc fs)
                                         { regs = writeReg (regs (floc fs)) x v } })
sp-write-reg fs x v ok wf = record
  { sp-regs  = λ r → go r (readReg-write (regs (floc fs)) x r v)
  ; sp-heap  = λ hl → subst (λ n → StackPtrOK? (current-frame (falloc fs)) n (heapMem (floc fs) hl))
                            (sym (writeReg-preserves-stackSlot (regs (floc fs)) x v))
                            (sp-heap wf hl)
  ; sp-stack = λ f k → subst (λ n → StackPtrOK? (current-frame (falloc fs)) n (stackMem (floc fs) f k))
                             (sym (writeReg-preserves-stackSlot (regs (floc fs)) x v))
                             (sp-stack wf f k) }
  where
    anchor : stackSlot (writeReg (regs (floc fs)) x v) ≡ stackSlot (regs (floc fs))
    anchor = writeReg-preserves-stackSlot (regs (floc fs)) x v
    go : ∀ (r : AbstractReg)
       → (readReg (writeReg (regs (floc fs)) x v) r ≡ v)
       ⊎ (readReg (writeReg (regs (floc fs)) x v) r ≡ readReg (regs (floc fs)) r)
       → StackPtrOK (current-frame (falloc fs)) (stackSlot (writeReg (regs (floc fs)) x v))
                    (readReg (writeReg (regs (floc fs)) x v) r)
    go r (inj₁ eq) rewrite anchor | eq = ok
    go r (inj₂ eq) rewrite anchor | eq = sp-regs wf r
