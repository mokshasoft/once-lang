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
