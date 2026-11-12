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
open import Data.List using (List; []; _∷_)
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

------------------------------------------------------------------------
-- ★ The callee's frame is not the caller's (nor any frame above it), and
-- clearing it leaves every other frame alone.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (module FrameSemantics)
open FrameSemantics FS using (Frame; shift-frame; _≺_; ≺-irrefl; shift-≺; shift-below; _≟F_)
open import Once.CCC.Machine.SMCore using (StackMem; module MemOps; module AllocState)
open MemOps {FS} using (clear-frame)
open import Data.Nat using (_<_; s≤s; z≤n)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Empty using (⊥-elim)

-- a call's callee frame: one slot down, then its budget
callee-frame : Frame → ℕ → Frame
callee-frame cf b = shift-frame (shift-frame cf 1) b

callee-below : ∀ cf b → callee-frame cf b ≺ cf
callee-below cf b = shift-below b (shift-≺ cf 1 (s≤s z≤n))

callee-≢ : ∀ cf b → ¬ callee-frame cf b ≡ cf
callee-≢ cf b e = ≺-irrefl (subst′ e (callee-below cf b))
  where subst′ : ∀ {f g} → f ≡ g → f ≺ cf → g ≺ cf
        subst′ refl p = p

clear-other : ∀ (mem : StackMem FS) f b f′ k → ¬ f ≡ f′ → clear-frame mem f b f′ k ≡ mem f′ k
clear-other mem f b f′ k ne with f ≟F f′
... | yes e = ⊥-elim (ne e)
... | no  _ = refl

------------------------------------------------------------------------
-- ★ A CALL'S WAY IN (a block that reads no view): the caller's argument
-- area in `Input1`, the call, the entry, the area saved in both save slots.
------------------------------------------------------------------------

open import Once.CCC.Machine.SMCore
  using (lea-slot; mov-to-input; mov-to-output; store-at-slot; SV-Ptr; readReg; writeReg; Input1; Output; module LocState; StoredValue)
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.LinCore.Moves {FS} using (Seg; lea-step; mov-in-step; mov-out-step; store-step; store-same; store-other; store-frame)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; step-at) renaming ([] to done)
open import Data.Bool using (false)
open import Data.Product using (Σ; _×_; _,_)
open LocState using (stackMem; heapMem) renaming (halted to fhalted)
open AllocState using (current-frame; saved-frames; frame-slots; next-heap-ref; block-size)
open import Data.Nat using (_+_)
open import Relation.Binary.PropositionalEquality using (sym)

record CallIn (fs fs′ : FlatState) (a b s₁ s₂ q : ℕ) : Set where
  field
    ci-frame : current-frame (falloc fs′) ≡ callee-frame (current-frame (falloc fs)) b
    ci-saved : saved-frames (falloc fs′) ≡ (current-frame (falloc fs) , frame-slots (falloc fs)) ∷ saved-frames (falloc fs)
    ci-ret   : fret fs′ ≡ suc (suc (suc (fpc fs))) ∷ fret fs
    ci-pc    : fpc fs′ ≡ suc (suc (suc (suc q)))
    ci-in    : readReg (LocState.regs (floc fs′)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) a)
    ci-s₁    : stackMem (floc fs′) (callee-frame (current-frame (falloc fs)) b) s₁ ≡ just (SV-Ptr (AtStack (current-frame (falloc fs)) a))
    ci-other : ∀ f′ x → ¬ callee-frame (current-frame (falloc fs)) b ≡ f′ → stackMem (floc fs′) f′ x ≡ stackMem (floc fs) f′ x
    ci-heap  : heapMem (floc fs′) ≡ heapMem (floc fs)
    ci-next  : next-heap-ref (falloc fs′) ≡ next-heap-ref (falloc fs)
    ci-size  : block-size (falloc fs′) ≡ block-size (falloc fs)
    ci-halt  : fhalted (floc fs′) ≡ fhalted (floc fs)
open CallIn public

call-in : ∀ prog (fs : FlatState) (a : ℕ) (f : CanonicalName) (e : EntryId) (q b s₁ s₂ : ℕ)
        → Seg prog (fpc fs) (lea-slot a ∷ mov-to-input ∷ instr-ctrl (c-call-fn f) ∷ [])
        → find-fn prog f ≡ just q
        → Seg prog q (instr-ctrl (c-entry e b) ∷ store-at-slot s₂ ∷ mov-to-output ∷ store-at-slot s₁ ∷ [])
        → fhalted (floc fs) ≡ false
        → Σ FlatState λ fs′ → FlatSteps prog 7 fs fs′ × CallIn fs fs′ a b s₁ s₂ q
call-in prog fs a f e q b s₁ s₂ (g₁ , g₂ , g₃ , _) ff (h₁ , h₂ , h₃ , h₄ , _) h =
  fs₇ ,
  step-at fs₁ (h , g₁) (lea-step fs a) (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₃ (h , g₃) (call-step prog fs₂ f ff)
  (step-at fs₄ (h , h₁) (entry-step prog fs₃ e b) (step-at fs₅ (h , h₂) (store-step fs₄ s₂)
  (step-at fs₆ (h , h₃) (mov-out-step fs₅) (step-at fs₇ (h , h₄) (store-step fs₆ s₁) done)))))) ,
  record { ci-frame = refl ; ci-saved = refl ; ci-ret = refl ; ci-pc = refl ; ci-in = refl
         ; ci-s₁ = store-same (floc fs₆) cf′ s₁ ptr
         ; ci-other = λ f′ x ne → trans (store-frame (floc fs₆) cf′ s₁ ptr f′ x ne)
                                    (trans (store-frame (floc fs₄) cf′ s₂ ptr f′ x ne) (clear-other (stackMem (floc fs)) cf′ b f′ x ne))
         ; ci-heap = refl ; ci-next = refl ; ci-size = refl ; ci-halt = refl }
  where
    cf = current-frame (falloc fs)
    cf′ = callee-frame cf b
    ptr = SV-Ptr (AtStack cf a)
    fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output ptr } ; fpc = suc (fpc fs) }
    fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 ptr } ; fpc = suc (fpc fs₁) }
    fs₃ = record fs₂ { falloc = enter-call (falloc fs₂) ; fret = suc (fpc fs₂) ∷ fret fs₂ ; flink = just (suc (fpc fs₂)) ; fpc = q }
    fs₄ = do-thunk b fs₃
    fs₅ = record fs₄ { floc = MemOps.writeLoc {FS} (floc fs₄) (AtStack cf′ s₂) ptr ; fpc = suc (fpc fs₄) }
    fs₆ = record fs₅ { floc = record (floc fs₅) { regs = writeReg (LocState.regs (floc fs₅)) Output ptr } ; fpc = suc (fpc fs₅) }
    fs₇ = record fs₆ { floc = MemOps.writeLoc {FS} (floc fs₆) (AtStack cf′ s₁) ptr ; fpc = suc (fpc fs₆) }
