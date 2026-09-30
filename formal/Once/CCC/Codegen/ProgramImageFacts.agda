-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.ProgramImageFacts — what holds of a PROGRAM IMAGE because
-- it holds of every unit in it (D244/D245).
--
-- `main`'s unit, then each table entry as its marker and its own unit (emitted
-- under its own name). A per-instruction fact is `main`'s, then per function
-- the marker's and that unit's; the SEGMENT in force is `main`'s budget between
-- functions, because each function's marker pushes its budget over the caller's
-- and its terminator pops it back (`SlotBudget.ir-seg-fold`).
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.ProgramImageFacts (o : CanonicalName) where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; subst)
open import Once.IR using (IR; Unit)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-entry; e-fn)
open import Once.CCC.Machine.FrameFree using (EmittableI)
open import Once.CCC.Codegen.AllocMin o using (AllocMinI)

open import Once.CCC.Codegen.ShapeTable using (heap-moded)
open import Once.CCC.Codegen.ProgramImage using (program-image; fns-image; fn-image; fn-next)
open import Once.Denotation.Program using (IRFun; irProgram; fname; fbody)
import Once.CCC.Codegen.FrameFreeTrace as FFT
import Once.CCC.Codegen.AllocMin as AM
import Once.CCC.Codegen.SlotBudget as SB
import Once.CCC.Codegen.LabelScope as LS
import Once.CCC.Codegen.LabelRange as LR
open import Once.CCC.Codegen.SlotSeg using (AllSeg; mkSeg; allseg-++; sb-none; []; _∷_; SegState; seg-at; fetch-at)
open import Once.CCC.Codegen.LabelSeg using (LabelsIn; SegAgree; mention-at; li-none; ls-weaken; segagree-++; segagree-pre; segagree-nolab)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.SMCore using (AbstractTrace; AbstractInstr; c-label)
open import Once.CCC.Label using (LabelId)
import Once.CCC.Codegen.IRToTrace as IT

-- The counter a list of entries leaves behind, and that it never retreats.
fns-next : ℕ → List IRFun → ℕ
fns-next l []       = l
fns-next l (e ∷ es) = fns-next (fn-next l e) es

fn-mono : ∀ (l : ℕ) (e : IRFun) → l ≤ fn-next l e
fn-mono l e = LR.label-mono (fname e) (fbody e) 0 l

fns-mono : ∀ (l : ℕ) (es : List IRFun) → l ≤ fns-next l es
fns-mono l []       = ≤-refl
fns-mono l (e ∷ es) = ≤-trans (fn-mono l e) (fns-mono (fn-next l e) es)

------------------------------------------------------------------------
-- Per-instruction facts: `main`'s unit, then per function the marker's (it
-- moves only the frame) and its unit's, each at its own owner and counter.
------------------------------------------------------------------------
fns-frame-free : ∀ (l : ℕ) (tbl : List IRFun) → All EmittableI (fns-image l tbl)
fns-frame-free l []       = []
fns-frame-free l (e ∷ es) =
  ++⁺ (tt ∷ FFT.ir-to-trace-lab-frame-free (fname e) (fbody e) (heap-moded (fbody e)) l)
      (fns-frame-free (fn-next l e) es)

image-frame-free : ∀ (tbl : List IRFun) (ir : IR Unit Unit)
                 → All EmittableI (program-image o (irProgram tbl ir))
image-frame-free tbl ir = ++⁺ (FFT.ir-to-trace-frame-free o ir (heap-moded ir)) (fns-frame-free (IT.ir-next-label o 0 ir) tbl)

fns-alloc-min : ∀ (l : ℕ) (tbl : List IRFun) → All AllocMinI (fns-image l tbl)
fns-alloc-min l []       = []
fns-alloc-min l (e ∷ es) =
  ++⁺ (tt ∷ AM.ir-to-trace-lab-alloc-min (fname e) (fbody e) l) (fns-alloc-min (fn-next l e) es)

image-alloc-min : ∀ (tbl : List IRFun) (ir : IR Unit Unit)
                → All AllocMinI (program-image o (irProgram tbl ir))
image-alloc-min tbl ir = ++⁺ (AM.ir-to-trace-alloc-min o ir) (fns-alloc-min (IT.ir-next-label o 0 ir) tbl)

-- …and the SEGMENT in force. `main`'s unit leaves the state where it began
-- (`ir-seg-fold` at an empty saved stack); a function's marker pushes its
-- budget over the caller's, its unit runs there, and its terminator pops back.
fns-slots : ∀ (B l : ℕ) (tbl : List IRFun) → AllSeg (mkSeg B []) (fns-image l tbl)
fns-slots B l []       = []
fns-slots B l (e ∷ es) =
  allseg-++ (sb-none refl ∷ SB.ir-slots-below-under-lab (fname e) (fbody e) l (B ∷ []))
            (subst (λ z → AllSeg z (fns-image (fn-next l e) es))
                   (sym (SB.ir-seg-fold-lab (fname e) (fbody e) l (B ∷ [])))
                   (fns-slots B (fn-next l e) es))

image-slots : ∀ (tbl : List IRFun) (ir : IR Unit Unit)
            → AllSeg (mkSeg (IT.ir-stack-budget o ir) []) (program-image o (irProgram tbl ir))
image-slots tbl ir =
  allseg-++ (SB.ir-slots-below-under o ir [])
            (subst (λ z → AllSeg z (fns-image (IT.ir-next-label o 0 ir) tbl)) (sym (SB.ir-seg-fold o ir []))
                   (fns-slots (IT.ir-stack-budget o ir) (IT.ir-next-label o 0 ir) tbl))

------------------------------------------------------------------------
-- A JUMP LANDS IN THE SEGMENT IT LEFT, over the whole image. Each unit's
-- labels sit in its own counter window (the counter is threaded), so a jump
-- in one unit cannot name a label defined in another — `segagree-++`'s
-- window clash — and inside a unit it is `LabelScope`'s theorem.
------------------------------------------------------------------------
fn-labels : ∀ (l : ℕ) (e : IRFun) → LabelsIn l (fn-next l e) (fn-image l e)
fn-labels l e = li-none refl ∷ LS.linked-labels-lab (fname e) (fbody e) l

fn-agree : ∀ (l : ℕ) (e : IRFun) → SegAgree (fn-image l e)
fn-agree l e =
  segagree-pre (instr-ctrl (c-entry (e-fn (fname e)) (IT.ir-stack-budget-from (fname e) l (fbody e))) ∷ [])
               l l (fn-next l e) (refl ∷ [])
               (LS.linked-labels-lab (fname e) (fbody e) l) ≤-refl
               (LS.linked-agree-lab (fname e) (fbody e) l)

fns-labels : ∀ (l : ℕ) (tbl : List IRFun) → LabelsIn l (fns-next l tbl) (fns-image l tbl)
fns-labels l []       = []
fns-labels l (e ∷ es) =
  ++⁺ (ls-weaken ≤-refl (fns-mono (fn-next l e) es) (fn-labels l e))
      (ls-weaken (fn-mono l e) ≤-refl (fns-labels (fn-next l e) es))

fns-agree : ∀ (l : ℕ) (tbl : List IRFun) → SegAgree (fns-image l tbl)
fns-agree l []       = segagree-nolab [] []
fns-agree l (e ∷ es) =
  segagree-++ (fn-image l e) (fns-image (fn-next l e) es)
              l (fn-next l e) (fns-next (fn-next l e) es)
              (fn-labels l e) (fns-labels (fn-next l e) es)
              (fn-agree l e) (fns-agree (fn-next l e) es)

image-agree : ∀ (tbl : List IRFun) (ir : IR Unit Unit)
            → SegAgree (program-image o (irProgram tbl ir))
image-agree tbl ir =
  segagree-++ (IT.ir-to-trace o ir) (fns-image L tbl) 0 L (fns-next L tbl)
              (LS.linked-labels-lab o ir 0) (fns-labels L tbl)
              (LS.linked-agree-lab o ir 0) (fns-agree L tbl)
  where L = IT.ir-next-label o 0 ir

module _ {FS : FrameSemantics} where
  open FlatMachine {FS} using (find-label; find-label-lands; fetch)

  private
    fetch≡at : ∀ (t : AbstractTrace) (k : ℕ) → fetch t k ≡ fetch-at t k
    fetch≡at []       _       = refl
    fetch≡at (i ∷ is) zero    = refl
    fetch≡at (i ∷ is) (suc k) = fetch≡at is k

  image-jump-in-segment : ∀ (tbl : List IRFun) (ir : IR Unit Unit) (p q : ℕ) (m : LabelId) (st : SegState)
                        → mention-at (program-image o (irProgram tbl ir)) p ≡ just m
                        → find-label (program-image o (irProgram tbl ir)) m ≡ just q
                        → seg-at (program-image o (irProgram tbl ir)) q st
                          ≡ seg-at (program-image o (irProgram tbl ir)) p st
  image-jump-in-segment tbl ir p q m st mq fl =
    image-agree tbl ir p q m st mq
      (trans (sym (fetch≡at (program-image o (irProgram tbl ir)) q))
             (find-label-lands (program-image o (irProgram tbl ir)) m q fl))
