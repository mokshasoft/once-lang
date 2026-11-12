-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimE — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: CALLS. A call pushes the return pc and the caller's frame and
-- enters the callee's (one slot down, then its budget: a frame strictly
-- below, `FrameSemantics.shift-≺`, so the caller's slots are another
-- frame's and every callee store misses them); the entry clears the
-- callee's slots; the return pops both.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; _∷_)
open import Data.Maybe using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-call-fn; c-entry; c-ret)
open import Once.CCC.Label using (EntryId)
open import Once.Spec.Name using (CanonicalName)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.LowerSimE {FS : FrameSemantics} where

open FlatMachine {FS}

-- ★ a direct call: the return pc and the caller's frame pushed, the entry's pc
call-step : ∀ prog (fs : FlatState) (f : CanonicalName) {q} → find-fn prog f ≡ just q
          → flat-exec-instr (instr-ctrl (c-call-fn f)) prog fs
            ≡ record fs { falloc = enter-call (falloc fs) ; fret = suc (fpc fs) ∷ fret fs ; flink = just (suc (fpc fs)) ; fpc = q }
call-step prog fs f e = cong (λ m → do-call-at m fs) e

-- ★ an entry: the callee's slots cleared, its frame grown by its budget
entry-step : ∀ prog (fs : FlatState) (e : EntryId) b → flat-exec-instr (instr-ctrl (c-entry e b)) prog fs ≡ do-thunk b fs
entry-step prog fs e b = refl

-- ★ a return: the frame and the return pc popped
ret-step : ∀ prog (fs : FlatState) b {pc rest} → fret fs ≡ pc ∷ rest
         → flat-exec-instr (instr-ctrl (c-ret b)) prog fs
           ≡ record fs { falloc = leave-frame (falloc fs) ; fpc = pc ; fret = rest }
ret-step prog fs b e = cong (λ r → do-ret r fs) e
