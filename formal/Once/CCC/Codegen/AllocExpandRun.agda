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
import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState; fetch; flat-exec-instr)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; _∷_; []; FlatSteps-++)
open import Once.CCC.Codegen.AllocExpandRen {FS} using (rec-loc; blk)
open MemOps {FS} using (writeLoc; writeLocToHeap; readLoc)

-- a heap write is a write of the heap
dyn-write : ∀ (s : LocState FS) hl v → writeLoc s (AtDynamic hl) v ≡ writeLocToHeap s hl v
dyn-write s hl (SV-Ptr (AtStack _ _)) = refl
dyn-write s hl (SV-Ptr (AtDynamic _)) = refl
dyn-write s hl (SV-Tag _)             = refl
dyn-write s hl (SV-Lit _ _)           = refl
dyn-write s hl (SV-Code _)            = refl

module _ (prog : AbstractTrace) where

  -- one step, by its end state
  one : ∀ {x y} {i : AbstractInstr} → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just i
      → flat-exec-instr i prog x ≡ y → FlatSteps prog 1 x y
  one {x} {y} {i} h f e = (h , f) ∷ subst (λ z → FlatSteps prog 0 z y) (sym e) []

  -- the record's word k, written from Output (the record handed out)
  run-store-rec : ∀ x k n → AllocState.next-heap-ref (falloc x) ≡ suc n → LocState.halted (floc x) ≡ false
                → fetch prog (fpc x) ≡ just (store-rec k)
                → FlatSteps prog 1 x (record x { floc = writeLocToHeap (floc x) (rec-loc k) (readReg (LocState.regs (floc x)) Output)
                                               ; fpc = suc (fpc x) })
  run-store-rec x k n nx h f =
    one h f (trans (cong (λ m → record x { floc = ExecFinal.exec-store-via-resolved {FS} (ExecFinal.rec-at {FS} m k) (readReg (LocState.regs (floc x)) Output) (floc x)
                                         ; fpc = suc (fpc x) }) nx)
                   (cong (λ l → record x { floc = l ; fpc = suc (fpc x) }) (dyn-write (floc x) (rec-loc k) (readReg (LocState.regs (floc x)) Output))))

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
                → FlatSteps prog 1 x (record x { floc = writeLocToHeap (floc x) (heap-loc (mkHeapRef b) 0) (readReg (LocState.regs (floc x)) Output)
                                               ; fpc = suc (fpc x) })
  run-store-at0 x b i ib h f =
    one h f (trans (cong (λ v → record x { floc = ExecFinal.exec-store-at-resolved {FS} (ExecFinal.live-size {FS} (falloc x)) 0
                                                    (ExecFinal.frame-gate {FS} (falloc x) 0 (sv-as-loc v)) (readReg (LocState.regs (floc x)) Output) (floc x)
                                         ; fpc = suc (fpc x) }) i)
            (trans (cong (λ g → record x { floc = ExecFinal.exec-store-in-block {FS} g (AtDynamic (heap-loc (mkHeapRef b) 0)) (readReg (LocState.regs (floc x)) Output) (floc x)
                                         ; fpc = suc (fpc x) }) ib)
                   (cong (λ l → record x { floc = l ; fpc = suc (fpc x) }) (dyn-write (floc x) (heap-loc (mkHeapRef b) 0) (readReg (LocState.regs (floc x)) Output)))))

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

  -- Output := a block's first word (Input1 the block, its word a value)
  run-load-at0 : ∀ x b w → readReg (LocState.regs (floc x)) Input1 ≡ blk b
               → LocState.heapMem (floc x) (heap-loc (mkHeapRef b) 0) ≡ just w
               → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just (load-at 0)
               → FlatSteps prog 1 x (record x { floc = record (floc x) { regs = writeReg (LocState.regs (floc x)) Output w } ; fpc = suc (fpc x) })
  run-load-at0 x b w i e h f =
    one h f (trans (cong (λ v → record x { floc = ExecFinal.exec-load-at-resolved {FS} 0 Output (ExecFinal.frame-gate {FS} (falloc x) 0 (sv-as-loc v)) (floc x)
                                         ; fpc = suc (fpc x) }) i)
                   (cong (λ mv → record x { floc = ExecFinal.exec-load-with-value {FS} Output mv (floc x) ; fpc = suc (fpc x) }) e))

  -- Output := a tag
  run-tag : ∀ x n → LocState.halted (floc x) ≡ false → fetch prog (fpc x) ≡ just (instr-load-tag-lit n)
          → FlatSteps prog 1 x (record x { floc = record (floc x) { regs = writeReg (LocState.regs (floc x)) Output (SV-Tag n) } ; fpc = suc (fpc x) })
  run-tag x n h f = one h f refl

-- ★ the start's heads: every head word written from Output
open import Data.Nat using (_+_; _<_)
open import Data.Product using (Σ; _×_)
open import Relation.Nullary using (¬_)
open MemOps {FS} using (writeHeapMem; writeHeapMem-aux)
open import Once.Memory.HeapAddress using (_≟HL_; module HeapLocation)
open import Once.CCC.Codegen.AllocExpand using (Classes; heads; head-word)

private
  hw-same′ : ∀ (h : HeapMem FS) hl v → writeHeapMem h hl v hl ≡ just v
  hw-same′ h hl v = go (hl ≟HL hl)
    where
      go : ∀ (d : Relation.Nullary.Dec (hl ≡ hl)) → writeHeapMem-aux {hl = hl} {hl' = hl} d (h hl) v ≡ just v
      go (Relation.Nullary.yes _) = refl
      go (Relation.Nullary.no ne) = Data.Empty.⊥-elim (ne refl)
        where import Data.Empty

  hw-other′ : ∀ (h : HeapMem FS) hl q v → ¬ hl ≡ q → writeHeapMem h hl v q ≡ h q
  hw-other′ h hl q v ne = go (hl ≟HL q)
    where
      go : ∀ (d : Relation.Nullary.Dec (hl ≡ q)) → writeHeapMem-aux {hl = hl} {hl' = q} d (h q) v ≡ h q
      go (Relation.Nullary.yes e) = Data.Empty.⊥-elim (ne e)
        where import Data.Empty
      go (Relation.Nullary.no _)  = refl

record HeadsOut (x y : FlatState) (c : ℕ) : Set where
  field
    h-pc    : fpc y ≡ c + fpc x
    h-regs  : LocState.regs (floc y) ≡ LocState.regs (floc x)
    h-stack : LocState.stackMem (floc y) ≡ LocState.stackMem (floc x)
    h-flags : (LocState.halted (floc y) ≡ LocState.halted (floc x)) × (LocState.faulted (floc y) ≡ LocState.faulted (floc x))
            × (LocState.left (floc y) ≡ LocState.left (floc x)) × (LocState.ev-log (floc y) ≡ LocState.ev-log (floc x))
    h-alloc : falloc y ≡ falloc x
    h-rest  : (fret y ≡ fret x) × (fclosure y ≡ fclosure x) × (flink y ≡ flink x)
    h-head  : ∀ c′ → c′ < c → LocState.heapMem (floc y) (rec-loc (head-word c′)) ≡ just (readReg (LocState.regs (floc x)) Output)
    h-other : ∀ q → (∀ c′ → c′ < c → ¬ q ≡ rec-loc (head-word c′)) → LocState.heapMem (floc y) q ≡ LocState.heapMem (floc x) q

heads-run : ∀ (C : Classes) prog (x : FlatState) c n → AllocState.next-heap-ref (falloc x) ≡ suc n → LocState.halted (floc x) ≡ false
          → (∀ j i → fetch (heads C c) j ≡ just i → fetch prog (j + fpc x) ≡ just i)
          → Σ FlatState λ y → FlatSteps prog c x y × HeadsOut x y c
heads-run C prog x zero n nx hx fe = x , [] , record
  { h-pc = refl ; h-regs = refl ; h-stack = refl ; h-flags = refl , refl , refl , refl ; h-alloc = refl ; h-rest = refl , refl , refl
  ; h-head = λ c′ () ; h-other = λ q _ → refl }
heads-run C prog x (suc c) n nx hx fe = go (heads-run C prog x₁ c n nx hx (λ j i e → trans (cong (fetch prog) (Data.Nat.Properties.+-suc j (fpc x))) (fe (suc j) i e)))
  where
    import Data.Nat.Properties
    v = readReg (LocState.regs (floc x)) Output
    x₁ = record x { floc = writeLocToHeap (floc x) (rec-loc (head-word c)) v ; fpc = suc (fpc x) }
    st₁ = run-store-rec prog x (head-word c) n nx hx (fe 0 (store-rec (head-word c)) refl)
    go : (Σ FlatState λ y → FlatSteps prog c x₁ y × HeadsOut x₁ y c) → Σ FlatState λ y → FlatSteps prog (suc c) x y × HeadsOut x y (suc c)
    go (y , st , H) = y , FlatSteps-++ st₁ st , record
      { h-pc = trans (HeadsOut.h-pc H) (Data.Nat.Properties.+-suc c (fpc x))
      ; h-regs = HeadsOut.h-regs H ; h-stack = HeadsOut.h-stack H
      ; h-flags = HeadsOut.h-flags H ; h-alloc = HeadsOut.h-alloc H ; h-rest = HeadsOut.h-rest H
      ; h-head = hd
      ; h-other = λ q ne → trans (HeadsOut.h-other H q (λ c′ lt → ne c′ (Data.Nat.Properties.m<n⇒m<1+n lt)))
                                 (hw-other′ (LocState.heapMem (floc x)) (rec-loc (head-word c)) q v (λ e → ne c (Data.Nat.Properties.n<1+n c) (sym e))) }
      where
        hd : ∀ c′ → c′ < suc c → LocState.heapMem (floc y) (rec-loc (head-word c′)) ≡ just v
        hd c′ lt = by (Data.Nat.Properties.m≤n⇒m<n∨m≡n (Data.Nat.Properties.≤-pred lt))
          where
            by : c′ < c Data.Sum.⊎ c′ ≡ c → LocState.heapMem (floc y) (rec-loc (head-word c′)) ≡ just v
            by (Data.Sum.inj₁ lt′) = HeadsOut.h-head H c′ lt′
            by (Data.Sum.inj₂ refl) = trans (HeadsOut.h-other H (rec-loc (head-word c)) (λ c′ lt′ e → Data.Nat.Properties.<-irrefl (sym (suc-inj (suc-inj (suc-inj (cong HeapLocation.heap-offset e))))) lt′))
                                            (hw-same′ (LocState.heapMem (floc x)) (rec-loc (head-word c)) v)
              where
                suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
                suc-inj refl = refl
