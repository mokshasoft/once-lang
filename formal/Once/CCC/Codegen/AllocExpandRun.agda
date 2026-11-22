-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandRun — the expansion's instructions, one step each (D468, 3c3b).
--
-- What one step of each instruction the expansion emits does, from a state
-- where it is fetched and the run goes on: the record's words read and
-- written (the record handed out: the counter past ref 0), a block's first
-- word, the register moves. The alloc's and the free's runs are these, in
-- order.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandRun {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState; fetch; flat-exec-instr)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; _∷_; [])
open import Once.CCC.Codegen.AllocExpandRen {FS} using (rec-loc; blk)
open MemOps {FS} using (writeLoc; writeLocToHeap; readLoc)

module _ (prog : AbstractTrace) where

  -- one step, by its end state
  one : ∀ {x y} {i : AbstractInstr} → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just i
      → flat-exec-instr i prog x ≡ y → FlatSteps prog 1 x y
  one {x} {y} {i} h f e = (h , f) ∷ subst (λ z → FlatSteps prog 0 z y) (sym e) []

  -- the record's word k, written from Output (the record handed out)
  run-store-rec : ∀ x k n → AllocState.next-heap-ref (falloc x) ≡ suc n → LocState.halted (floc x) ≡ false
                → fetch prog (fpc x) ≡ just (store-rec k)
                → FlatSteps prog 1 x (record x { floc = writeLoc (floc x) (AtDynamic (rec-loc k)) (readReg (LocState.regs (floc x)) Output)
                                               ; fpc = suc (fpc x) })
  run-store-rec x k n nx h f =
    one h f (cong (λ m → record x { floc = ExecFinal.exec-store-via-resolved {FS} (ExecFinal.rec-at {FS} m k) (readReg (LocState.regs (floc x)) Output) (floc x)
                                  ; fpc = suc (fpc x) }) nx)

  -- Output := the record's word k (which holds a value)
  run-load-rec : ∀ x k n v → AllocState.next-heap-ref (falloc x) ≡ suc n → LocState.halted (floc x) ≡ false
               → fetch prog (fpc x) ≡ just (load-rec k) → LocState.heapMem (floc x) (rec-loc k) ≡ just v
               → FlatSteps prog 1 x (record x { floc = record (floc x) { regs = writeReg (LocState.regs (floc x)) Output v }
                                              ; fpc = suc (fpc x) })
  run-load-rec x k n v nx h f e =
    one h f (trans (cong (λ m → record x { floc = ExecFinal.exec-load-via-resolved {FS} Output (ExecFinal.rec-at {FS} m k) (floc x)
                                         ; fpc = suc (fpc x) }) nx)
                   (cong (λ mv → record x { floc = ExecFinal.exec-load-with-value {FS} Output mv (floc x) ; fpc = suc (fpc x) }) e))

  -- the register moves
  run-mov-out : ∀ x → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just mov-to-output
              → FlatSteps prog 1 x (record x { floc = record (floc x) { regs = writeReg (LocState.regs (floc x)) Output (readReg (LocState.regs (floc x)) Input1) }
                                             ; fpc = suc (fpc x) })
  run-mov-out x h f = one h f refl

  run-mov-in : ∀ x → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just mov-to-input
             → FlatSteps prog 1 x (record x { floc = record (floc x) { regs = writeReg (LocState.regs (floc x)) Input1 (readReg (LocState.regs (floc x)) Output) }
                                            ; fpc = suc (fpc x) })
  run-mov-in x h f = one h f refl

  open FlatMachine {FS} using (find-label)

  -- a block's first word, written from Output (Input1 the block, live to the store gate)
  run-store-at0 : ∀ x b → readReg (LocState.regs (floc x)) Input1 ≡ blk b
                → ExecFinal.in-block? {FS} (ExecFinal.live-size {FS} (falloc x)) (AtDynamic (heap-loc (mkHeapRef b) 0)) ≡ true
                → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just (store-at 0)
                → FlatSteps prog 1 x (record x { floc = writeLoc (floc x) (AtDynamic (heap-loc (mkHeapRef b) 0)) (readReg (LocState.regs (floc x)) Output)
                                               ; fpc = suc (fpc x) })
  run-store-at0 x b i ib h f =
    one h f (trans (cong (λ v → record x { floc = ExecFinal.exec-store-at-resolved {FS} (ExecFinal.live-size {FS} (falloc x)) 0
                                                    (ExecFinal.frame-gate {FS} (falloc x) 0 (sv-as-loc v)) (readReg (LocState.regs (floc x)) Output) (floc x)
                                         ; fpc = suc (fpc x) }) i)
                   (cong (λ g → record x { floc = ExecFinal.exec-store-in-block {FS} g (AtDynamic (heap-loc (mkHeapRef b) 0)) (readReg (LocState.regs (floc x)) Output) (floc x)
                                         ; fpc = suc (fpc x) }) ib))

  -- the emptiness test: at the sentinel (tag 0) the branch is taken, at a link (a heap pointer) not
  run-branch-taken : ∀ x b l j → readReg (LocState.regs (floc x)) Input1 ≡ blk b
                   → LocState.heapMem (floc x) (heap-loc (mkHeapRef b) 0) ≡ just (SV-Tag 0)
                   → find-label prog l ≡ just j
                   → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just (instr-ctrl (c-branch-tag-zero l))
                   → FlatSteps prog 1 x (record x { fpc = j })
  run-branch-taken x b l j i e fl h f =
    one h f (trans (cong (λ v → FlatMachine.do-branch-test {FS} (FlatMachine.tag-test {FS} (FlatMachine.flat-read-at {FS} (floc x) (ExecFinal.frame-gate {FS} (falloc x) 0 (sv-as-loc v)))) l prog x) i)
                   (trans (cong (λ mv → FlatMachine.do-branch-test {FS} (FlatMachine.tag-test {FS} mv) l prog x) e)
                          (cong (λ mj → FlatMachine.do-jump {FS} mj x) fl)))

  run-branch-not : ∀ x b l hl → readReg (LocState.regs (floc x)) Input1 ≡ blk b
                 → LocState.heapMem (floc x) (heap-loc (mkHeapRef b) 0) ≡ just (SV-Ptr (AtDynamic hl))
                 → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just (instr-ctrl (c-branch-tag-zero l))
                 → FlatSteps prog 1 x (record x { fpc = suc (fpc x) })
  run-branch-not x b l hl i e h f =
    one h f (trans (cong (λ v → FlatMachine.do-branch-test {FS} (FlatMachine.tag-test {FS} (FlatMachine.flat-read-at {FS} (floc x) (ExecFinal.frame-gate {FS} (falloc x) 0 (sv-as-loc v)))) l prog x) i)
                   (cong (λ mv → FlatMachine.do-branch-test {FS} (FlatMachine.tag-test {FS} mv) l prog x) e))

  run-jmp : ∀ x l j → find-label prog l ≡ just j → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just (instr-ctrl (c-jmp l))
          → FlatSteps prog 1 x (record x { fpc = j })
  run-jmp x l j fl h f = one h f (cong (λ mj → FlatMachine.do-jump {FS} mj x) fl)

  run-label : ∀ x l → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just (instr-ctrl (c-label l))
            → FlatSteps prog 1 x (record x { fpc = suc (fpc x) })
  run-label x l h f = one h f refl

  -- the bump: the counter's block, of the size asked
  run-alloc : ∀ x n → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just (instr-alloc-heap n)
            → FlatSteps prog 1 x (record x { floc = record (floc x) { regs = writeReg (LocState.regs (floc x)) Output (blk (AllocState.next-heap-ref (falloc x))) }
                                           ; falloc = record (falloc x) { next-heap-ref = suc (AllocState.next-heap-ref (falloc x))
                                                                        ; block-size = size-with n (AllocState.next-heap-ref (falloc x)) (AllocState.block-size (falloc x)) }
                                           ; fpc = suc (fpc x) })
  run-alloc x n h f = one h f refl
