-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimG — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: A DISPATCH THROUGH A CELL'S CODE WORD (D417). The cell's
-- address into `Input1` from its slot, the caller's area into `Output`, the
-- cell saved as the closure, the call through the cell's code word (word 1:
-- `do-call` reads `sucHL` of the closure); then the trampoline's entry, and
-- its two saves: the area (still in `Output`), then the cell.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Nullary using (¬_)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Label using (LabelId; EntryId)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.LowerSimG {FS : FrameSemantics} where

open FlatMachine {FS}
open FlatStepsAPI {FS} using (FlatSteps; step-at)
open import Once.LinCore.Moves {FS} using (Seg; slot; lea-step; mov-out-step; store-step; store-same; store-other; store-frame; restore-step)
open import Once.LinCore.LowerSimE {FS} using (callee-frame; clear-other)
open AllocState using (current-frame; saved-frames; frame-slots; next-heap-ref; block-size)

-- ★ the call through a cell's code word: the trampoline at `q` entered
closure-step : ∀ prog (fs : FlatState) (hl : HeapLocation) (ℓ : LabelId) {q}
             → fclosure fs ≡ SV-Ptr (AtDynamic hl) → LocState.heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ)
             → find-thunk prog ℓ ≡ just q
             → flat-exec-instr instr-call-closure prog fs
               ≡ record fs { falloc = enter-call (falloc fs) ; fret = suc (fpc fs) ∷ fret fs ; flink = just (suc (fpc fs)) ; fpc = q }
closure-step prog fs hl ℓ ceq heq feq =
  trans (cong (λ z → do-call-sv prog z fs) ceq)
    (trans (cong (λ z → do-call-code prog z fs) heq) (cong (λ z → do-call-at z fs) feq))

-- what the dispatch leaves: the trampoline's frame, the caller's saved; the
-- cell in `Input1`, the closure and the first save slot; the area in the second
record ClosIn (fs fs′ : FlatState) (cell : StoredValue FS) (y b s₁ s₂ q : ℕ) : Set where
  field
    cl-frame : current-frame (falloc fs′) ≡ callee-frame (current-frame (falloc fs)) b
    cl-saved : saved-frames (falloc fs′) ≡ (current-frame (falloc fs) , frame-slots (falloc fs)) ∷ saved-frames (falloc fs)
    cl-ret   : fret fs′ ≡ suc (suc (suc (suc (fpc fs)))) ∷ fret fs
    cl-pc    : fpc fs′ ≡ suc (suc (suc (suc q)))
    cl-in    : readReg (LocState.regs (floc fs′)) Input1 ≡ cell
    cl-clo   : fclosure fs′ ≡ cell
    cl-s₁    : LocState.stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s₁ ≡ just cell
    cl-s₂    : LocState.stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s₂
               ≡ just (SV-Ptr (AtStack (current-frame (falloc fs)) y))
    cl-other : ∀ f′ x → ¬ callee-frame (current-frame (falloc fs)) b ≡ f′
             → LocState.stackMem (floc fs′) f′ x ≡ LocState.stackMem (floc fs) f′ x
    cl-heap  : LocState.heapMem (floc fs′) ≡ LocState.heapMem (floc fs)
    cl-next  : next-heap-ref (falloc fs′) ≡ next-heap-ref (falloc fs)
    cl-size  : block-size (falloc fs′) ≡ block-size (falloc fs)
    cl-halt  : LocState.halted (floc fs′) ≡ LocState.halted (floc fs)

-- ★ the dispatch, into a trampoline that saves the area and the cell
closure-in : ∀ prog (fs : FlatState) (x y : ℕ) (hl : HeapLocation) (ℓ : LabelId) (e : EntryId) (q b s₁ s₂ : ℕ) → ¬ s₁ ≡ s₂
           → slot fs x ≡ just (SV-Ptr (AtDynamic hl)) → LocState.heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ)
           → Seg prog (fpc fs) (restore-input x ∷ lea-slot y ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
           → find-thunk prog ℓ ≡ just q
           → Seg prog q (instr-ctrl (c-entry e b) ∷ store-at-slot s₂ ∷ mov-to-output ∷ store-at-slot s₁ ∷ [])
           → LocState.halted (floc fs) ≡ false
           → Σ FlatState λ fs′ → FlatSteps prog 8 fs fs′ × ClosIn fs fs′ (SV-Ptr (AtDynamic hl)) y b s₁ s₂ q
closure-in prog fs x y hl ℓ e q b s₁ s₂ s≢ sx code (g₁ , g₂ , g₃ , g₄ , _) ff (h₁ , h₂ , h₃ , h₄ , _) h =
  fs₈ ,
  step-at fs₁ (h , g₁) (restore-step fs x sx) (step-at fs₂ (h , g₂) (lea-step fs₁ y) (step-at fs₃ (h , g₃) refl
  (step-at fs₄ (h , g₄) (closure-step prog fs₃ hl ℓ refl code ff)
  (step-at fs₅ (h , h₁) refl (step-at fs₆ (h , h₂) (store-step fs₅ s₂)
  (step-at fs₇ (h , h₃) (mov-out-step fs₆) (step-at fs₈ (h , h₄) (store-step fs₇ s₁) FlatStepsAPI.[]))))))) ,
  record { cl-frame = refl ; cl-saved = refl ; cl-ret = refl ; cl-pc = refl ; cl-in = refl ; cl-clo = refl
         ; cl-s₁ = store-same (floc fs₇) cf′ s₁ cell
         ; cl-s₂ = trans (store-other (floc fs₇) cf′ s₁ cell s₂ s≢) (store-same (floc fs₅) cf′ s₂ area)
         ; cl-other = λ f′ x′ ne → trans (store-frame (floc fs₇) cf′ s₁ cell f′ x′ ne)
                                     (trans (store-frame (floc fs₅) cf′ s₂ area f′ x′ ne) (clear-other (LocState.stackMem (floc fs)) cf′ b f′ x′ ne))
         ; cl-heap = refl ; cl-next = refl ; cl-size = refl ; cl-halt = refl }
  where
    cf = current-frame (falloc fs)
    cf′ = callee-frame cf b
    cell = SV-Ptr (AtDynamic hl)
    area = SV-Ptr (AtStack cf y)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Input1 cell } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Output area } ; fpc = suc (fpc fs₁) }
    fs₃ = record fs₂ { fclosure = cell ; fpc = suc (fpc fs₂) }
    fs₄ = record fs₃ { falloc = enter-call (falloc fs₃) ; fret = suc (fpc fs₃) ∷ fret fs₃ ; flink = just (suc (fpc fs₃)) ; fpc = q }
    fs₅ = do-thunk b fs₄
    fs₆ = record fs₅ { floc = MemOps.writeLoc {FS} (floc fs₅) (AtStack cf′ s₂) area ; fpc = suc (fpc fs₅) }
    fs₇ = record fs₆ { floc = record (floc fs₆) { regs = writeReg (LocState.regs (floc fs₆)) Output cell } ; fpc = suc (fpc fs₆) }
    fs₈ = record fs₇ { floc = MemOps.writeLoc {FS} (floc fs₇) (AtStack cf′ s₁) cell ; fpc = suc (fpc fs₇) }
