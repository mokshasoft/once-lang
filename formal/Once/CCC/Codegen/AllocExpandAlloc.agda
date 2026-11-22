-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandAlloc — the alloc's expansion, simulated (D468, 3c3b).
--
-- The primitive alloc hands out the counter's block; its expansion pops the
-- class's list (fourteen steps: the head block, its link the new head) or, at
-- the sentinel, bumps the expanded counter (ten steps). Either way Output is
-- the block and Input1 as it was.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandAlloc {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState; fetch; flat-exec-instr; find-label)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; FlatSteps-++)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rec-loc; blk)
open import Once.CCC.Codegen.AllocExpandRun {FS}
open import Once.CCC.Codegen.AllocExpandFree {FS} using (hw-same; hw-other)
open MemOps {FS} using (writeLocToHeap)

private
  rec≢ : ∀ {i j} → ¬ i ≡ j → ¬ rec-loc i ≡ rec-loc j
  rec≢ ne e = ne (cong HeapLocation.heap-offset e)

  blk≢rec : ∀ b k → ¬ b ≡ 0 → ¬ heap-loc (mkHeapRef b) 0 ≡ rec-loc k
  blk≢rec b k b≢0 e = b≢0 (cong (λ q → HeapRef.ref-id (HeapLocation.heap-ref q)) e)

------------------------------------------------------------------------
-- The pop: the class's head block handed out, its link the new head
------------------------------------------------------------------------

module Pop (prog : AbstractTrace) (x : FlatState) (h b n j₀ : ℕ) (Ld : LabelId) (w : StoredValue FS) (hlw : HeapLocation)
           (f₀ : fetch prog (fpc x) ≡ just mov-to-output)
           (f₁ : fetch prog (1 + fpc x) ≡ just (store-rec w-s1))
           (f₂ : fetch prog (2 + fpc x) ≡ just (load-rec h))
           (f₃ : fetch prog (3 + fpc x) ≡ just mov-to-input)
           (Lb : LabelId)
           (f₄ : fetch prog (4 + fpc x) ≡ just (instr-ctrl (c-branch-tag-zero Lb)))
           (f₅ : fetch prog (5 + fpc x) ≡ just (load-at 0))
           (f₆ : fetch prog (6 + fpc x) ≡ just (store-rec h))
           (f₇ : fetch prog (7 + fpc x) ≡ just mov-to-output)
           (f₈ : fetch prog (8 + fpc x) ≡ just (store-rec w-s2))
           (f₉ : fetch prog (9 + fpc x) ≡ just (load-rec w-s1))
           (f₁₀ : fetch prog (10 + fpc x) ≡ just mov-to-input)
           (f₁₁ : fetch prog (11 + fpc x) ≡ just (load-rec w-s2))
           (f₁₂ : fetch prog (12 + fpc x) ≡ just (instr-ctrl (c-jmp Ld)))
           (fl : find-label prog Ld ≡ just j₀)
           (f₁₃ : fetch prog j₀ ≡ just (instr-ctrl (c-label Ld)))
           (hx : LocState.halted (floc x) ≡ false) (nx : AllocState.next-heap-ref (falloc x) ≡ suc n)
           (hd : LocState.heapMem (floc x) (rec-loc h) ≡ just (blk b))
           (lnk : LocState.heapMem (floc x) (heap-loc (mkHeapRef b) 0) ≡ just w)
           (wp : w ≡ SV-Ptr (AtDynamic hlw))
           (h≢1 : ¬ h ≡ w-s1) (h≢2 : ¬ h ≡ w-s2) (b≢0 : ¬ b ≡ 0) where

  I = readReg (LocState.regs (floc x)) Input1

  x₁  = record x   { floc = record (floc x) { regs = writeReg (LocState.regs (floc x)) Output I } ; fpc = suc (fpc x) }
  x₂  = record x₁  { floc = writeLocToHeap (floc x₁) (rec-loc w-s1) I ; fpc = suc (fpc x₁) }
  x₃  = record x₂  { floc = record (floc x₂) { regs = writeReg (LocState.regs (floc x₂)) Output (blk b) } ; fpc = suc (fpc x₂) }
  x₄  = record x₃  { floc = record (floc x₃) { regs = writeReg (LocState.regs (floc x₃)) Input1 (blk b) } ; fpc = suc (fpc x₃) }
  x₅  = record x₄  { fpc = suc (fpc x₄) }
  x₆  = record x₅  { floc = record (floc x₅) { regs = writeReg (LocState.regs (floc x₅)) Output w } ; fpc = suc (fpc x₅) }
  x₇  = record x₆  { floc = writeLocToHeap (floc x₆) (rec-loc h) w ; fpc = suc (fpc x₆) }
  x₈  = record x₇  { floc = record (floc x₇) { regs = writeReg (LocState.regs (floc x₇)) Output (blk b) } ; fpc = suc (fpc x₇) }
  x₉  = record x₈  { floc = writeLocToHeap (floc x₈) (rec-loc w-s2) (blk b) ; fpc = suc (fpc x₈) }
  x₁₀ = record x₉  { floc = record (floc x₉) { regs = writeReg (LocState.regs (floc x₉)) Output I } ; fpc = suc (fpc x₉) }
  x₁₁ = record x₁₀ { floc = record (floc x₁₀) { regs = writeReg (LocState.regs (floc x₁₀)) Input1 I } ; fpc = suc (fpc x₁₀) }
  x₁₂ = record x₁₁ { floc = record (floc x₁₁) { regs = writeReg (LocState.regs (floc x₁₁)) Output (blk b) } ; fpc = suc (fpc x₁₁) }
  x₁₃ = record x₁₂ { fpc = j₀ }
  x₁₄ = record x₁₃ { fpc = suc j₀ }

  hd₂ : LocState.heapMem (floc x₂) (rec-loc h) ≡ just (blk b)
  hd₂ = trans (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) (rec-loc h) I (rec≢ (λ e → h≢1 (sym e)))) hd

  lnk₂ : LocState.heapMem (floc x₂) (heap-loc (mkHeapRef b) 0) ≡ just w
  lnk₂ = trans (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) (heap-loc (mkHeapRef b) 0) I (λ e → blk≢rec b w-s1 b≢0 (sym e))) lnk

  sc₉ : LocState.heapMem (floc x₉) (rec-loc w-s1) ≡ just I
  sc₉ = trans (hw-other (LocState.heapMem (floc x₇)) (rec-loc w-s2) (rec-loc w-s1) (blk b) (λ ()))
          (trans (hw-other (LocState.heapMem (floc x₂)) (rec-loc h) (rec-loc w-s1) w (rec≢ h≢1))
                 (hw-same (LocState.heapMem (floc x)) (rec-loc w-s1) I))

  s2₁₁ : LocState.heapMem (floc x₁₁) (rec-loc w-s2) ≡ just (blk b)
  s2₁₁ = hw-same (LocState.heapMem (floc x₇)) (rec-loc w-s2) (blk b)

  run : FlatSteps prog 14 x x₁₄
  run = FlatSteps-++ (run-mov-out prog x hx f₀)
       (FlatSteps-++ (run-store-rec prog x₁ w-s1 n nx hx f₁)
       (FlatSteps-++ (run-load-rec prog x₂ h n (blk b) nx hx f₂ hd₂)
       (FlatSteps-++ (run-mov-in prog x₃ hx f₃)
       (FlatSteps-++ (run-branch-not prog x₄ b Lb hlw refl (trans lnk₂ (cong just wp)) hx f₄)
       (FlatSteps-++ (run-load-at0 prog x₅ b w refl lnk₂ hx f₅)
       (FlatSteps-++ (run-store-rec prog x₆ h n nx hx f₆)
       (FlatSteps-++ (run-mov-out prog x₇ hx f₇)
       (FlatSteps-++ (run-store-rec prog x₈ w-s2 n nx hx f₈)
       (FlatSteps-++ (run-load-rec prog x₉ w-s1 n I nx hx f₉ sc₉)
       (FlatSteps-++ (run-mov-in prog x₁₀ hx f₁₀)
       (FlatSteps-++ (run-load-rec prog x₁₁ w-s2 n (blk b) nx hx f₁₁ s2₁₁)
       (FlatSteps-++ (run-jmp prog x₁₂ Ld j₀ fl hx f₁₂)
                     (run-label prog x₁₃ Ld hx f₁₃)))))))))))))

  -- what it leaves
  out-head : LocState.heapMem (floc x₁₄) (rec-loc h) ≡ just w
  out-head = trans (hw-other (LocState.heapMem (floc x₇)) (rec-loc w-s2) (rec-loc h) (blk b) (rec≢ (λ e → h≢2 (sym e))))
                   (hw-same (LocState.heapMem (floc x₂)) (rec-loc h) w)

  out-other : ∀ q → ¬ q ≡ rec-loc h → ¬ q ≡ rec-loc w-s1 → ¬ q ≡ rec-loc w-s2
            → LocState.heapMem (floc x₁₄) q ≡ LocState.heapMem (floc x) q
  out-other q n₁ n₂ n₃ =
    trans (hw-other (LocState.heapMem (floc x₇)) (rec-loc w-s2) q (blk b) (λ e → n₃ (sym e)))
      (trans (hw-other (LocState.heapMem (floc x₂)) (rec-loc h) q w (λ e → n₁ (sym e)))
             (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) q I (λ e → n₂ (sym e))))

------------------------------------------------------------------------
-- The bump: the list empty (its head the sentinel), the counter's block
------------------------------------------------------------------------

module Bump (prog : AbstractTrace) (x : FlatState) (h σ n j₁ m : ℕ) (Lb Ld : LabelId)
            (f₀ : fetch prog (fpc x) ≡ just mov-to-output)
            (f₁ : fetch prog (1 + fpc x) ≡ just (store-rec w-s1))
            (f₂ : fetch prog (2 + fpc x) ≡ just (load-rec h))
            (f₃ : fetch prog (3 + fpc x) ≡ just mov-to-input)
            (f₄ : fetch prog (4 + fpc x) ≡ just (instr-ctrl (c-branch-tag-zero Lb)))
            (fl : find-label prog Lb ≡ just j₁)
            (f₅ : fetch prog j₁ ≡ just (instr-ctrl (c-label Lb)))
            (f₆ : fetch prog (1 + j₁) ≡ just (load-rec w-s1))
            (f₇ : fetch prog (2 + j₁) ≡ just mov-to-input)
            (f₈ : fetch prog (3 + j₁) ≡ just (instr-alloc-heap m))
            (f₉ : fetch prog (4 + j₁) ≡ just (instr-ctrl (c-label Ld)))
            (hx : LocState.halted (floc x) ≡ false) (nx : AllocState.next-heap-ref (falloc x) ≡ suc n)
            (hd : LocState.heapMem (floc x) (rec-loc h) ≡ just (blk σ))
            (sent : LocState.heapMem (floc x) (heap-loc (mkHeapRef σ) 0) ≡ just (SV-Tag 0))
            (h≢1 : ¬ h ≡ w-s1) (σ≢0 : ¬ σ ≡ 0) where

  I = readReg (LocState.regs (floc x)) Input1

  x₁  = record x   { floc = record (floc x) { regs = writeReg (LocState.regs (floc x)) Output I } ; fpc = suc (fpc x) }
  x₂  = record x₁  { floc = writeLocToHeap (floc x₁) (rec-loc w-s1) I ; fpc = suc (fpc x₁) }
  x₃  = record x₂  { floc = record (floc x₂) { regs = writeReg (LocState.regs (floc x₂)) Output (blk σ) } ; fpc = suc (fpc x₂) }
  x₄  = record x₃  { floc = record (floc x₃) { regs = writeReg (LocState.regs (floc x₃)) Input1 (blk σ) } ; fpc = suc (fpc x₃) }
  x₅  = record x₄  { fpc = j₁ }
  x₆  = record x₅  { fpc = suc j₁ }
  x₇  = record x₆  { floc = record (floc x₆) { regs = writeReg (LocState.regs (floc x₆)) Output I } ; fpc = suc (fpc x₆) }
  x₈  = record x₇  { floc = record (floc x₇) { regs = writeReg (LocState.regs (floc x₇)) Input1 I } ; fpc = suc (fpc x₇) }
  x₉  = record x₈  { floc = record (floc x₈) { regs = writeReg (LocState.regs (floc x₈)) Output (blk (AllocState.next-heap-ref (falloc x₈))) }
                   ; falloc = record (falloc x₈) { next-heap-ref = suc (AllocState.next-heap-ref (falloc x₈))
                                                 ; block-size = size-with m (AllocState.next-heap-ref (falloc x₈)) (AllocState.block-size (falloc x₈)) }
                   ; fpc = suc (fpc x₈) }
  x₁₀ = record x₉  { fpc = suc (fpc x₉) }

  hd₂ : LocState.heapMem (floc x₂) (rec-loc h) ≡ just (blk σ)
  hd₂ = trans (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) (rec-loc h) I (rec≢ (λ e → h≢1 (sym e)))) hd

  sent₂ : LocState.heapMem (floc x₂) (heap-loc (mkHeapRef σ) 0) ≡ just (SV-Tag 0)
  sent₂ = trans (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) (heap-loc (mkHeapRef σ) 0) I (λ e → blk≢rec σ w-s1 σ≢0 (sym e))) sent

  sc₆ : LocState.heapMem (floc x₆) (rec-loc w-s1) ≡ just I
  sc₆ = hw-same (LocState.heapMem (floc x)) (rec-loc w-s1) I

  run : FlatSteps prog 10 x x₁₀
  run = FlatSteps-++ (run-mov-out prog x hx f₀)
       (FlatSteps-++ (run-store-rec prog x₁ w-s1 n nx hx f₁)
       (FlatSteps-++ (run-load-rec prog x₂ h n (blk σ) nx hx f₂ hd₂)
       (FlatSteps-++ (run-mov-in prog x₃ hx f₃)
       (FlatSteps-++ (run-branch-taken prog x₄ σ Lb j₁ refl sent₂ fl hx f₄)
       (FlatSteps-++ (run-label prog x₅ Lb hx f₅)
       (FlatSteps-++ (run-load-rec prog x₆ w-s1 n I nx hx f₆ sc₆)
       (FlatSteps-++ (run-mov-in prog x₇ hx f₇)
       (FlatSteps-++ (run-alloc prog x₈ m hx f₈)
                     (run-label prog x₉ Ld hx f₉)))))))))

  out-other : ∀ q → ¬ q ≡ rec-loc w-s1 → LocState.heapMem (floc x₁₀) q ≡ LocState.heapMem (floc x) q
  out-other q ne = hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) q I (λ e → ne (sym e))
