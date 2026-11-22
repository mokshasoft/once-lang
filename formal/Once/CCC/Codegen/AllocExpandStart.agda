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
