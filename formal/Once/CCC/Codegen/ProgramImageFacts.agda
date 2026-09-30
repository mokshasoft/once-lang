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
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import Once.IR using (IR; Unit)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-entry; e-fn)
open import Once.CCC.Machine.FrameFree using (EmittableI)
open import Once.CCC.Codegen.AllocMin o using (AllocMinI)
open import Once.CCC.Codegen.SlotBudget o using (AllSeg; mkSeg; allseg-++; sb-none; []; _∷_)
open import Once.CCC.Codegen.ShapeTable using (heap-moded)
open import Once.CCC.Codegen.ProgramImage using (program-image; fns-image)
open import Once.Denotation.Program using (IRFun; irProgram; fname; fbody)
import Once.CCC.Codegen.FrameFreeTrace as FFT
import Once.CCC.Codegen.AllocMin as AM
import Once.CCC.Codegen.SlotBudget as SB
import Once.CCC.Codegen.IRToTrace as IT

fns-frame-free : ∀ (tbl : List IRFun) → All EmittableI (fns-image tbl)
fns-frame-free []       = []
fns-frame-free (e ∷ es) =
  ++⁺ (tt ∷ FFT.ir-to-trace-frame-free (fname e) (fbody e) (heap-moded (fbody e))) (fns-frame-free es)

image-frame-free : ∀ (tbl : List IRFun) (ir : IR Unit Unit)
                 → All EmittableI (program-image o (irProgram tbl ir))
image-frame-free tbl ir = ++⁺ (FFT.ir-to-trace-frame-free o ir (heap-moded ir)) (fns-frame-free tbl)

fns-alloc-min : ∀ (tbl : List IRFun) → All AllocMinI (fns-image tbl)
fns-alloc-min []       = []
fns-alloc-min (e ∷ es) =
  ++⁺ (tt ∷ AM.ir-to-trace-alloc-min (fname e) (fbody e)) (fns-alloc-min es)

image-alloc-min : ∀ (tbl : List IRFun) (ir : IR Unit Unit)
                → All AllocMinI (program-image o (irProgram tbl ir))
image-alloc-min tbl ir = ++⁺ (AM.ir-to-trace-alloc-min o ir) (fns-alloc-min tbl)

-- …and the SEGMENT in force. `main`'s unit leaves the state where it began
-- (`ir-seg-fold` at an empty saved stack); a function's marker pushes its
-- budget over the caller's, its unit runs there, and its terminator pops back.
fns-slots : ∀ (B : ℕ) (tbl : List IRFun) → AllSeg (mkSeg B []) (fns-image tbl)
fns-slots B []       = []
fns-slots B (e ∷ es) =
  allseg-++ (sb-none refl ∷ SB.ir-slots-below-under (fname e) (fbody e) (B ∷ []))
            (subst (λ z → AllSeg z (fns-image es))
                   (sym (SB.ir-seg-fold (fname e) (fbody e) (B ∷ [])))
                   (fns-slots B es))

image-slots : ∀ (tbl : List IRFun) (ir : IR Unit Unit)
            → AllSeg (mkSeg (IT.ir-stack-budget o ir) []) (program-image o (irProgram tbl ir))
image-slots tbl ir =
  allseg-++ (SB.ir-slots-below-under o ir [])
            (subst (λ z → AllSeg z (fns-image tbl)) (sym (SB.ir-seg-fold o ir []))
                   (fns-slots (IT.ir-stack-budget o ir) tbl))

