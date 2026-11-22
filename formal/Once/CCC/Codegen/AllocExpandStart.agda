-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandStart — the start's set-up, and the first relation (D468, 3c3b).
--
-- After `c-start` the expansion saves Output and Input1 in the record's
-- scratch words, bumps the sentinel (the expanded run's first block), points
-- every head at it, writes its word (the tag 0) and puts the registers back.
-- The primitive's state after `c-start` and the expanded one after the set-up
-- are related: nothing is live, so the renaming is the identity and the lists
-- are empty.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandStart {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState; fetch; fetch-++-left; fetch-++-right)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; FlatSteps-++)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rec-loc; blk)
open import Once.CCC.Codegen.AllocExpandRun {FS}
open import Once.CCC.Codegen.AllocExpandFree {FS} using (hw-same; hw-other)
open MemOps {FS} using (writeLocToHeap)

module SetupRun (C : Classes) (prog : AbstractTrace) (x : FlatState)
                (fe : ∀ j i → fetch (setup C) j ≡ just i → fetch prog (j + fpc x) ≡ just i)
                (hx : LocState.halted (floc x) ≡ false) (nx : AllocState.next-heap-ref (falloc x) ≡ 1)
                (fr1 : AllocState.freed (falloc x) 1 ≡ false) where

  O = readReg (LocState.regs (floc x)) Output
  I = readReg (LocState.regs (floc x)) Input1

  y₁ = record x  { floc = writeLocToHeap (floc x) (rec-loc w-s1) O ; fpc = suc (fpc x) }
  y₂ = record y₁ { floc = record (floc y₁) { regs = writeReg (LocState.regs (floc y₁)) Output I } ; fpc = suc (fpc y₁) }
  y₃ = record y₂ { floc = writeLocToHeap (floc y₂) (rec-loc w-s2) I ; fpc = suc (fpc y₂) }
  y₄ = record y₃ { floc = record (floc y₃) { regs = writeReg (LocState.regs (floc y₃)) Output (blk (AllocState.next-heap-ref (falloc y₃))) }
                 ; falloc = record (falloc y₃) { next-heap-ref = suc (AllocState.next-heap-ref (falloc y₃))
                                               ; block-size = size-with 1 (AllocState.next-heap-ref (falloc y₃)) (AllocState.block-size (falloc y₃)) }
                 ; fpc = suc (fpc y₃) }

  run₄ : FlatSteps prog 4 x y₄
  run₄ = FlatSteps-++ (run-store-rec prog x w-s1 0 nx hx (fe 0 (store-rec w-s1) refl))
        (FlatSteps-++ (run-mov-out prog y₁ hx (fe 1 mov-to-output refl))
        (FlatSteps-++ (run-store-rec prog y₂ w-s2 0 nx hx (fe 2 (store-rec w-s2) refl))
                      (run-alloc prog y₃ 1 hx (fe 3 (instr-alloc-heap 1) refl))))

  -- the heads, from the sentinel's pointer in Output
  nx₄ : AllocState.next-heap-ref (falloc y₄) ≡ suc 1
  nx₄ = cong suc nx

  rest = mov-to-input ∷ instr-load-tag-lit 0 ∷ store-at 0 ∷ load-rec w-s2 ∷ mov-to-input ∷ load-rec w-s1 ∷ []

  fe-heads : ∀ j i → fetch (heads C (count C)) j ≡ just i → fetch prog (j + fpc y₄) ≡ just i
  fe-heads j i e = subst (λ z → fetch prog z ≡ just i)
                     (trans (cong (_+ fpc x) (Data.Nat.Properties.+-comm 4 j)) (Data.Nat.Properties.+-assoc j 4 (fpc x)))
                     (fe (4 + j) i (fetch-++-left (heads C (count C)) rest j i e))

  HR = heads-run C prog y₄ (count C) 1 nx₄ hx fe-heads
  z  = proj₁ HR
  stH = proj₁ (proj₂ HR)
  H  = proj₂ (proj₂ HR)
  open HeadsOut

  heads-len : ∀ c → length (heads C c) ≡ c
  heads-len zero    = refl
  heads-len (suc c) = cong suc (heads-len c)

  -- the fetches past the heads
  fe-rest : ∀ j i → fetch rest j ≡ just i → fetch prog (j + fpc z) ≡ just i
  fe-rest j i e =
    subst (λ q → fetch prog q ≡ just i)
          (trans (cong (λ t → (4 + (t + j)) + fpc x) (heads-len (count C)))
                 (trans (shuffle (count C) j (fpc x)) (cong (j +_) (sym (h-pc H)))))
          (fe (4 + (length (heads C (count C)) + j)) i (trans (fetch-++-right (heads C (count C)) rest j) e))
    where
      shuffle : ∀ c j′ x′ → (4 + (c + j′)) + x′ ≡ j′ + (c + (4 + x′))
      shuffle = solve-∀

  hz : LocState.halted (floc z) ≡ false
  hz = trans (proj₁ (h-flags H)) hx
  nz : AllocState.next-heap-ref (falloc z) ≡ suc 1
  nz = trans (cong AllocState.next-heap-ref (h-alloc H)) nx₄
  out-z : readReg (LocState.regs (floc z)) Output ≡ blk 1
  out-z = trans (cong (λ rs → readReg rs Output) (h-regs H)) (cong blk nx)

  z₁ = record z  { floc = record (floc z) { regs = writeReg (LocState.regs (floc z)) Input1 (readReg (LocState.regs (floc z)) Output) } ; fpc = suc (fpc z) }
  z₂ = record z₁ { floc = record (floc z₁) { regs = writeReg (LocState.regs (floc z₁)) Output (SV-Tag 0) } ; fpc = suc (fpc z₁) }
  z₃ = record z₂ { floc = writeLocToHeap (floc z₂) (heap-loc (mkHeapRef 1) 0) (SV-Tag 0) ; fpc = suc (fpc z₂) }
  z₄ = record z₃ { floc = record (floc z₃) { regs = writeReg (LocState.regs (floc z₃)) Output I } ; fpc = suc (fpc z₃) }
  z₅ = record z₄ { floc = record (floc z₄) { regs = writeReg (LocState.regs (floc z₄)) Input1 I } ; fpc = suc (fpc z₄) }
  z₆ = record z₅ { floc = record (floc z₅) { regs = writeReg (LocState.regs (floc z₅)) Output O } ; fpc = suc (fpc z₅) }

  private
    head≢ : ∀ k → k < 3 → ∀ c′ → ¬ rec-loc k ≡ rec-loc (head-word c′)
    head≢ k lt c′ e = Data.Nat.Properties.<-irrefl (cong HeapLocation.heap-offset e)
                        (Data.Nat.Properties.<-≤-trans lt (Data.Nat.Properties.m≤m+n 3 c′))
    blk1≢rec : ∀ k → ¬ heap-loc (mkHeapRef 1) 0 ≡ rec-loc k
    blk1≢rec k ()

  -- the scratch words, read back past the heads and the sentinel's word
  s2 : LocState.heapMem (floc z₃) (rec-loc w-s2) ≡ just I
  s2 = trans (hw-other (LocState.heapMem (floc z)) (heap-loc (mkHeapRef 1) 0) (rec-loc w-s2) (SV-Tag 0) (blk1≢rec w-s2))
         (trans (h-other H (rec-loc w-s2) (λ c′ _ → head≢ 2 (s≤s (s≤s (s≤s z≤n))) c′))
                (hw-same (LocState.heapMem (floc y₁)) (rec-loc w-s2) I))
  s1 : LocState.heapMem (floc z₅) (rec-loc w-s1) ≡ just O
  s1 = trans (hw-other (LocState.heapMem (floc z)) (heap-loc (mkHeapRef 1) 0) (rec-loc w-s1) (SV-Tag 0) (blk1≢rec w-s1))
         (trans (h-other H (rec-loc w-s1) (λ c′ _ → head≢ 1 (s≤s (s≤s z≤n)) c′))
           (trans (hw-other (LocState.heapMem (floc y₁)) (rec-loc w-s2) (rec-loc w-s1) I (λ ()))
                  (hw-same (LocState.heapMem (floc x)) (rec-loc w-s1) O)))

  ib : ExecFinal.in-block? {FS} (ExecFinal.live-size {FS} (falloc z₂)) (AtDynamic (heap-loc (mkHeapRef 1) 0)) ≡ true
  ib = trans (cong (λ al → ExecFinal.in-block? {FS} (ExecFinal.live-size {FS} al) (AtDynamic (heap-loc (mkHeapRef 1) 0))) (h-alloc H))
             (live1 false fr1)
    where
      live1 : ∀ b → AllocState.freed (falloc x) 1 ≡ b → ExecFinal.in-block? {FS} (ExecFinal.live-size {FS} (falloc y₄)) (AtDynamic (heap-loc (mkHeapRef 1) 0)) ≡ true
      live1 false e = trans (cong (λ t → 0 Data.Nat.<ᵇ (Data.Bool.if t then 0 else size-with 1 (AllocState.next-heap-ref (falloc x)) (AllocState.block-size (falloc x)) 1)) e)
                            (cong (λ t → 0 Data.Nat.<ᵇ size-with 1 t (AllocState.block-size (falloc x)) 1) nx)
      live1 true  e = ⊥-elim (true≢false (trans (sym e) fr1))
        where
          true≢false : ¬ (true ≡ false)
          true≢false ()

  run-rest : FlatSteps prog 6 z z₆
  run-rest = FlatSteps-++ (run-mov-in prog z hz (fe-rest 0 mov-to-input refl))
            (FlatSteps-++ (run-tag prog z₁ 0 hz (fe-rest 1 (instr-load-tag-lit 0) refl))
            (FlatSteps-++ (run-store-at0 prog z₂ 1 out-z ib hz (fe-rest 2 (store-at 0) refl))
            (FlatSteps-++ (run-load-rec prog z₃ w-s2 1 I nz hz (fe-rest 3 (load-rec w-s2) refl) s2)
            (FlatSteps-++ (run-mov-in prog z₄ hz (fe-rest 4 mov-to-input refl))
                          (run-load-rec prog z₅ w-s1 1 O nz hz (fe-rest 5 (load-rec w-s1) refl) s1)))))

  run : FlatSteps prog (4 + (count C + 6)) x z₆
  run = FlatSteps-++ run₄ (FlatSteps-++ stH run-rest)
