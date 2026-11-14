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
open import Data.Bool using (false; true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Nullary using (¬_)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Label using (LabelId; EntryId)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; offsetHL)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.LowerSimG {FS : FrameSemantics} where

open FlatMachine {FS}
open FlatStepsAPI {FS} using (FlatSteps; step-at)
open import Once.LinCore.Moves {FS} using (Seg; slot; lea-step; mov-out-step; store-step; store-same; store-other; store-frame; restore-step; addr-step; load-step; mov-in-step)
open import Once.LinCore.LowerSimE {FS} using (callee-frame; clear-other)
open AllocState using (current-frame; saved-frames; frame-slots; next-heap-ref; block-size)
open ExecFinal {FS} using (in-block?)

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
    cl-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)

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
         ; cl-heap = refl ; cl-next = refl ; cl-size = refl ; cl-halt = refl ; cl-log = refl }
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

------------------------------------------------------------------------
-- ★ A MANY-USE DISPATCH (D417, D425, `icallω`): as `closure-in`, into a
-- trampoline that saves only the caller's area (its one save slot); the
-- cell stays in `Input1`.
------------------------------------------------------------------------

record ClosInω (fs fs′ : FlatState) (cell : StoredValue FS) (y b s q : ℕ) : Set where
  field
    cw-frame : current-frame (falloc fs′) ≡ callee-frame (current-frame (falloc fs)) b
    cw-saved : saved-frames (falloc fs′) ≡ (current-frame (falloc fs) , frame-slots (falloc fs)) ∷ saved-frames (falloc fs)
    cw-ret   : fret fs′ ≡ suc (suc (suc (suc (fpc fs)))) ∷ fret fs
    cw-pc    : fpc fs′ ≡ suc (suc q)
    cw-in    : readReg (LocState.regs (floc fs′)) Input1 ≡ cell
    cw-s     : LocState.stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s
               ≡ just (SV-Ptr (AtStack (current-frame (falloc fs)) y))
    cw-other : ∀ f′ x → ¬ callee-frame (current-frame (falloc fs)) b ≡ f′
             → LocState.stackMem (floc fs′) f′ x ≡ LocState.stackMem (floc fs) f′ x
    cw-heap  : LocState.heapMem (floc fs′) ≡ LocState.heapMem (floc fs)
    cw-next  : next-heap-ref (falloc fs′) ≡ next-heap-ref (falloc fs)
    cw-size  : block-size (falloc fs′) ≡ block-size (falloc fs)
    cw-halt  : LocState.halted (floc fs′) ≡ LocState.halted (floc fs)
    cw-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)

closure-inω : ∀ prog (fs : FlatState) (x y : ℕ) (hl : HeapLocation) (ℓ : LabelId) (e : EntryId) (q b s : ℕ)
            → slot fs x ≡ just (SV-Ptr (AtDynamic hl)) → LocState.heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ)
            → Seg prog (fpc fs) (restore-input x ∷ lea-slot y ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [])
            → find-thunk prog ℓ ≡ just q
            → Seg prog q (instr-ctrl (c-entry e b) ∷ store-at-slot s ∷ [])
            → LocState.halted (floc fs) ≡ false
            → Σ FlatState λ fs′ → FlatSteps prog 6 fs fs′ × ClosInω fs fs′ (SV-Ptr (AtDynamic hl)) y b s q
closure-inω prog fs x y hl ℓ e q b s sx code (g₁ , g₂ , g₃ , g₄ , _) ff (h₁ , h₂ , _) h =
  fs₆ ,
  step-at fs₁ (h , g₁) (restore-step fs x sx) (step-at fs₂ (h , g₂) (lea-step fs₁ y) (step-at fs₃ (h , g₃) refl
  (step-at fs₄ (h , g₄) (closure-step prog fs₃ hl ℓ refl code ff)
  (step-at fs₅ (h , h₁) refl (step-at fs₆ (h , h₂) (store-step fs₅ s) FlatStepsAPI.[]))))) ,
  record { cw-frame = refl ; cw-saved = refl ; cw-ret = refl ; cw-pc = refl ; cw-in = refl
         ; cw-s = store-same (floc fs₅) cf′ s area
         ; cw-other = λ f′ x′ ne → trans (store-frame (floc fs₅) cf′ s area f′ x′ ne) (clear-other (LocState.stackMem (floc fs)) cf′ b f′ x′ ne)
         ; cw-heap = refl ; cw-next = refl ; cw-size = refl ; cw-halt = refl ; cw-log = refl }
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
    fs₆ = record fs₅ { floc = MemOps.writeLoc {FS} (floc fs₅) (AtStack cf′ s) area ; fpc = suc (fpc fs₅) }

------------------------------------------------------------------------
-- ★ A FREE'S DISPATCH (D417, `cfree`/`nfree`): the cell's word-2 address
-- the closure (so `do-call` reads word 3, the free trampoline's code), the
-- cell in `Output`; the trampoline's entry with one save slot, the cell.
-- `addr-at 2` is in the cell's block (D424: a written word there).
------------------------------------------------------------------------

record FreeIn (fs fs′ : FlatState) (cell : StoredValue FS) (b s q : ℕ) : Set where
  field
    fr-frame : current-frame (falloc fs′) ≡ callee-frame (current-frame (falloc fs)) b
    fr-saved : saved-frames (falloc fs′) ≡ (current-frame (falloc fs) , frame-slots (falloc fs)) ∷ saved-frames (falloc fs)
    fr-ret   : fret fs′ ≡ suc (suc (suc (suc (suc (suc (suc (fpc fs))))))) ∷ fret fs
    fr-pc    : fpc fs′ ≡ suc (suc q)
    fr-in    : readReg (LocState.regs (floc fs′)) Input1 ≡ cell
    fr-s     : LocState.stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s ≡ just cell
    fr-other : ∀ f′ x → ¬ callee-frame (current-frame (falloc fs)) b ≡ f′
             → LocState.stackMem (floc fs′) f′ x ≡ LocState.stackMem (floc fs) f′ x
    fr-heap  : LocState.heapMem (floc fs′) ≡ LocState.heapMem (floc fs)
    fr-next  : next-heap-ref (falloc fs′) ≡ next-heap-ref (falloc fs)
    fr-size  : block-size (falloc fs′) ≡ block-size (falloc fs)
    fr-halt  : LocState.halted (floc fs′) ≡ LocState.halted (floc fs)
    fr-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)

free-in : ∀ prog (fs : FlatState) (c : ℕ) (hl : HeapLocation) (ℓ : LabelId) (e : EntryId) (q b s : ℕ)
        → slot fs c ≡ just (SV-Ptr (AtDynamic hl))
        → in-block? (block-size (falloc fs)) (offsetLoc (AtDynamic hl) 2) ≡ true
        → LocState.heapMem (floc fs) (sucHL (offsetHL hl 2)) ≡ just (SV-Code ℓ)
        → Seg prog (fpc fs) (restore-input c ∷ addr-at 2 ∷ mov-to-input ∷ instr-save-closure-reg
                             ∷ restore-input c ∷ mov-to-output ∷ instr-call-closure ∷ [])
        → find-thunk prog ℓ ≡ just q
        → Seg prog q (instr-ctrl (c-entry e b) ∷ store-at-slot s ∷ [])
        → LocState.halted (floc fs) ≡ false
        → Σ FlatState λ fs′ → FlatSteps prog 9 fs fs′ × FreeIn fs fs′ (SV-Ptr (AtDynamic hl)) b s q
free-in prog fs c hl ℓ e q b s sx ib code (g₁ , g₂ , g₃ , g₄ , g₅ , g₆ , g₇ , _) ff (h₁ , h₂ , _) h =
  fs₉ ,
  step-at fs₁ (h , g₁) (restore-step fs c sx) (step-at fs₂ (h , g₂) (addr-step fs₁ 2 refl ib)
  (step-at fs₃ (h , g₃) refl (step-at fs₄ (h , g₄) refl
  (step-at fs₅ (h , g₅) (restore-step fs₄ c sx) (step-at fs₆ (h , g₆) refl
  (step-at fs₇ (h , g₇) (closure-step prog fs₆ (offsetHL hl 2) ℓ refl code ff)
  (step-at fs₈ (h , h₁) refl (step-at fs₉ (h , h₂) (store-step fs₈ s) FlatStepsAPI.[])))))))) ,
  record { fr-frame = refl ; fr-saved = refl ; fr-ret = refl ; fr-pc = refl ; fr-in = refl
         ; fr-s = store-same (floc fs₈) cf′ s cell
         ; fr-other = λ f′ x′ ne → trans (store-frame (floc fs₈) cf′ s cell f′ x′ ne) (clear-other (LocState.stackMem (floc fs)) cf′ b f′ x′ ne)
         ; fr-heap = refl ; fr-next = refl ; fr-size = refl ; fr-halt = refl ; fr-log = refl }
  where
    cf = current-frame (falloc fs)
    cf′ = callee-frame cf b
    cell = SV-Ptr (AtDynamic hl)
    w2 = SV-Ptr (AtDynamic (offsetHL hl 2))
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Input1 cell } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Output w2 } ; fpc = suc (fpc fs₁) }
    fs₃ = record fs₂ { floc = record (floc fs₂) { regs = writeReg (LocState.regs (floc fs₂)) Input1 w2 } ; fpc = suc (fpc fs₂) }
    fs₄ = record fs₃ { fclosure = w2 ; fpc = suc (fpc fs₃) }
    fs₅ = record fs₄ { floc = record (floc fs₄) { regs = writeReg (LocState.regs (floc fs₄)) Input1 cell } ; fpc = suc (fpc fs₄) }
    fs₆ = record fs₅ { floc = record (floc fs₅) { regs = writeReg (LocState.regs (floc fs₅)) Output cell } ; fpc = suc (fpc fs₅) }
    fs₇ = record fs₆ { falloc = enter-call (falloc fs₆) ; fret = suc (fpc fs₆) ∷ fret fs₆ ; flink = just (suc (fpc fs₆)) ; fpc = q }
    fs₈ = do-thunk b fs₇
    fs₉ = record fs₈ { floc = MemOps.writeLoc {FS} (floc fs₈) (AtStack cf′ s) cell ; fpc = suc (fpc fs₈) }

------------------------------------------------------------------------
-- ★ A COPY'S DISPATCH (D417, `ccopy`/`ncopy`): the cell's word-1 address
-- the closure (so `do-call` reads word 2, the copy trampoline's code), the
-- caller's destination slot in `Input1`, the cell in `Output`; the
-- trampoline's entry with its saves: the cell, then the destination.
------------------------------------------------------------------------

record CopyIn (fs fs′ : FlatState) (cell : StoredValue FS) (d b s₁ s₂ q : ℕ) : Set where
  field
    cy-frame : current-frame (falloc fs′) ≡ callee-frame (current-frame (falloc fs)) b
    cy-saved : saved-frames (falloc fs′) ≡ (current-frame (falloc fs) , frame-slots (falloc fs)) ∷ saved-frames (falloc fs)
    cy-ret   : fret fs′ ≡ suc (suc (suc (suc (suc (suc (suc (suc (fpc fs)))))))) ∷ fret fs
    cy-pc    : fpc fs′ ≡ suc (suc (suc (suc q)))
    cy-s₁    : LocState.stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s₁
               ≡ just (SV-Ptr (AtStack (current-frame (falloc fs)) d))
    cy-s₂    : LocState.stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s₂ ≡ just cell
    cy-other : ∀ f′ x → ¬ callee-frame (current-frame (falloc fs)) b ≡ f′
             → LocState.stackMem (floc fs′) f′ x ≡ LocState.stackMem (floc fs) f′ x
    cy-heap  : LocState.heapMem (floc fs′) ≡ LocState.heapMem (floc fs)
    cy-next  : next-heap-ref (falloc fs′) ≡ next-heap-ref (falloc fs)
    cy-size  : block-size (falloc fs′) ≡ block-size (falloc fs)
    cy-halt  : LocState.halted (floc fs′) ≡ LocState.halted (floc fs)
    cy-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)

copy-in : ∀ prog (fs : FlatState) (c d : ℕ) (hl : HeapLocation) (ℓ : LabelId) (e : EntryId) (q b s₁ s₂ : ℕ) → ¬ s₁ ≡ s₂
        → slot fs c ≡ just (SV-Ptr (AtDynamic hl))
        → in-block? (block-size (falloc fs)) (offsetLoc (AtDynamic hl) 1) ≡ true
        → LocState.heapMem (floc fs) (sucHL (offsetHL hl 1)) ≡ just (SV-Code ℓ)
        → Seg prog (fpc fs) (restore-input c ∷ addr-at 1 ∷ mov-to-input ∷ instr-save-closure-reg
                             ∷ lea-slot d ∷ mov-to-input ∷ load-from-slot c ∷ instr-call-closure ∷ [])
        → find-thunk prog ℓ ≡ just q
        → Seg prog q (instr-ctrl (c-entry e b) ∷ store-at-slot s₂ ∷ mov-to-output ∷ store-at-slot s₁ ∷ [])
        → LocState.halted (floc fs) ≡ false
        → Σ FlatState λ fs′ → FlatSteps prog 12 fs fs′ × CopyIn fs fs′ (SV-Ptr (AtDynamic hl)) d b s₁ s₂ q
copy-in prog fs c d hl ℓ e q b s₁ s₂ s≢ sx ib code (g₁ , g₂ , g₃ , g₄ , g₅ , g₆ , g₇ , g₈ , _) ff (h₁ , h₂ , h₃ , h₄ , _) h =
  fs₁₂ ,
  step-at fs₁ (h , g₁) (restore-step fs c sx) (step-at fs₂ (h , g₂) (addr-step fs₁ 1 refl ib)
  (step-at fs₃ (h , g₃) (mov-in-step fs₂) (step-at fs₄ (h , g₄) refl
  (step-at fs₅ (h , g₅) (lea-step fs₄ d) (step-at fs₆ (h , g₆) (mov-in-step fs₅)
  (step-at fs₇ (h , g₇) (load-step fs₆ c sx)
  (step-at fs₈ (h , g₈) (closure-step prog fs₇ (offsetHL hl 1) ℓ refl code ff)
  (step-at fs₉ (h , h₁) refl (step-at fs₁₀ (h , h₂) (store-step fs₉ s₂)
  (step-at fs₁₁ (h , h₃) (mov-out-step fs₁₀) (step-at fs₁₂ (h , h₄) (store-step fs₁₁ s₁) FlatStepsAPI.[]))))))))))) ,
  record { cy-frame = refl ; cy-saved = refl ; cy-ret = refl ; cy-pc = refl
         ; cy-s₁ = store-same (floc fs₁₁) cf′ s₁ dst
         ; cy-s₂ = trans (store-other (floc fs₁₁) cf′ s₁ dst s₂ s≢) (store-same (floc fs₉) cf′ s₂ cell)
         ; cy-other = λ f′ x′ ne → trans (store-frame (floc fs₁₁) cf′ s₁ dst f′ x′ ne)
                                     (trans (store-frame (floc fs₉) cf′ s₂ cell f′ x′ ne) (clear-other (LocState.stackMem (floc fs)) cf′ b f′ x′ ne))
         ; cy-heap = refl ; cy-next = refl ; cy-size = refl ; cy-halt = refl ; cy-log = refl }
  where
    cf = current-frame (falloc fs)
    cf′ = callee-frame cf b
    cell = SV-Ptr (AtDynamic hl)
    w1 = SV-Ptr (AtDynamic (offsetHL hl 1))
    dst = SV-Ptr (AtStack cf d)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Input1 cell } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Output w1 } ; fpc = suc (fpc fs₁) }
    fs₃ = record fs₂ { floc = record (floc fs₂) { regs = writeReg (LocState.regs (floc fs₂)) Input1 w1 } ; fpc = suc (fpc fs₂) }
    fs₄ = record fs₃ { fclosure = w1 ; fpc = suc (fpc fs₃) }
    fs₅ = record fs₄ { floc = record (floc fs₄) { regs = writeReg (LocState.regs (floc fs₄)) Output dst } ; fpc = suc (fpc fs₄) }
    fs₆ = record fs₅ { floc = record (floc fs₅) { regs = writeReg (LocState.regs (floc fs₅)) Input1 dst } ; fpc = suc (fpc fs₅) }
    fs₇ = record fs₆ { floc = record (floc fs₆) { regs = writeReg (LocState.regs (floc fs₆)) Output cell } ; fpc = suc (fpc fs₆) }
    fs₈ = record fs₇ { falloc = enter-call (falloc fs₇) ; fret = suc (fpc fs₇) ∷ fret fs₇ ; flink = just (suc (fpc fs₇)) ; fpc = q }
    fs₉ = do-thunk b fs₈
    fs₁₀ = record fs₉ { floc = MemOps.writeLoc {FS} (floc fs₉) (AtStack cf′ s₂) cell ; fpc = suc (fpc fs₉) }
    fs₁₁ = record fs₁₀ { floc = record (floc fs₁₀) { regs = writeReg (LocState.regs (floc fs₁₀)) Output dst } ; fpc = suc (fpc fs₁₀) }
    fs₁₂ = record fs₁₁ { floc = MemOps.writeLoc {FS} (floc fs₁₁) (AtStack cf′ s₁) dst ; fpc = suc (fpc fs₁₁) }
