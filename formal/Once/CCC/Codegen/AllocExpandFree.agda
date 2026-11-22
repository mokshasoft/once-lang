-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandFree — the free's expansion, simulated (D468, 3c3b).
--
-- The primitive free (gated: a live block's base, of its size) clears the
-- block and marks it; its expansion pushes the renamed block on its class's
-- list: six steps, after which the registers and the frames are as they were,
-- the class's head is the block, the block's first word the old head, and the
-- record's scratch word holds Output. The relation then holds with the block
-- off the renaming's live part and on the list.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandFree {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef; _≟HL_)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState; fetch; flat-exec-instr; block-base?)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; FlatSteps-++)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rec-loc; blk)
open import Once.CCC.Codegen.AllocExpandRun {FS}
open MemOps {FS} using (writeLoc; writeLocToHeap; writeHeapMem; writeHeapMem-aux)

------------------------------------------------------------------------
-- 1. The free's gate, inverted
------------------------------------------------------------------------

private
  inv4 : ∀ a b c d → (a ∧ (b ∧ (c ∧ d))) ≡ true → (a ≡ true) × (b ≡ true) × (c ≡ true) × (d ≡ true)
  inv4 true true true true _ = refl , refl , refl , refl
  not-t : ∀ {a : Bool} → not a ≡ true → a ≡ false
  not-t {false} _ = refl
  ≡ᵇ-t : ∀ {m n} → (m ≡ᵇ n) ≡ true → m ≡ n
  ≡ᵇ-t {m} {n} e = Data.Nat.Properties.≡ᵇ⇒≡ m n (subst Data.Bool.T (sym e) Data.Unit.tt)
    where import Data.Nat.Properties
          import Data.Unit

record Base (al : AllocState {FS}) (k : ℕ) (v : StoredValue FS) : Set where
  field
    b-ref  : ℕ
    b-ptr  : v ≡ blk b-ref
    b-size : AllocState.block-size al b-ref ≡ k
    b-pos  : (0 <ᵇ k) ≡ true
    b-live : AllocState.freed al b-ref ≡ false
open Base public

base-of : ∀ al k v → block-base? k v al ≡ true → Base al k v
base-of al k (SV-Ptr (AtDynamic (heap-loc (mkHeapRef r) o))) e = record
  { b-ref = r
  ; b-ptr = cong (λ z → SV-Ptr (AtDynamic (heap-loc (mkHeapRef r) z))) (≡ᵇ-t (proj₁ i))
  ; b-size = ≡ᵇ-t (proj₁ (proj₂ i))
  ; b-pos = proj₁ (proj₂ (proj₂ i))
  ; b-live = not-t (proj₂ (proj₂ (proj₂ i))) }
  where
    i = inv4 (o ≡ᵇ 0) (AllocState.block-size al r ≡ᵇ k) (0 <ᵇ k) (not (AllocState.freed al r)) e
base-of al k (SV-Ptr (AtStack _ _)) ()
base-of al k (SV-Tag _) ()
base-of al k (SV-Lit _ _) ()
base-of al k (SV-Code _) ()

------------------------------------------------------------------------
-- 2. The expanded free's run
------------------------------------------------------------------------

-- a heap write's cells
hw-same : ∀ (h : HeapMem FS) hl v → writeHeapMem h hl v hl ≡ just v
hw-same h hl v = go (hl ≟HL hl)
  where
    go : ∀ (d : Relation.Nullary.Dec (hl ≡ hl)) → writeHeapMem-aux {hl = hl} {hl' = hl} d (h hl) v ≡ just v
    go (yes _) = refl
    go (no ne) = Data.Empty.⊥-elim (ne refl)
      where import Data.Empty

hw-other : ∀ (h : HeapMem FS) hl q v → ¬ hl ≡ q → writeHeapMem h hl v q ≡ h q
hw-other h hl q v ne = go (hl ≟HL q)
  where
    go : ∀ (d : Relation.Nullary.Dec (hl ≡ q)) → writeHeapMem-aux {hl = hl} {hl' = q} d (h q) v ≡ h q
    go (yes e) = Data.Empty.⊥-elim (ne e)
      where import Data.Empty
    go (no _)  = refl

-- a heap write is a write of the heap only
dyn-heap : ∀ (s : LocState FS) hl v q → LocState.heapMem (writeLoc s (AtDynamic hl) v) q ≡ writeHeapMem (LocState.heapMem s) hl v q
dyn-heap s hl (SV-Ptr (AtStack _ _)) q = refl
dyn-heap s hl (SV-Ptr (AtDynamic _)) q = refl
dyn-heap s hl (SV-Tag _) q = refl
dyn-heap s hl (SV-Lit _ _) q = refl
dyn-heap s hl (SV-Code _) q = refl

dyn-regs : ∀ (s : LocState FS) hl v → LocState.regs (writeLoc s (AtDynamic hl) v) ≡ LocState.regs s
dyn-regs s hl (SV-Ptr (AtStack _ _)) = refl
dyn-regs s hl (SV-Ptr (AtDynamic _)) = refl
dyn-regs s hl (SV-Tag _) = refl
dyn-regs s hl (SV-Lit _ _) = refl
dyn-regs s hl (SV-Code _) = refl

module Run (prog : AbstractTrace) (x : FlatState) (h b n : ℕ) (v₀ : StoredValue FS)
           (f₀ : fetch prog (fpc x) ≡ just (store-rec w-s1))
           (f₁ : fetch prog (suc (fpc x)) ≡ just (load-rec h))
           (f₂ : fetch prog (suc (suc (fpc x))) ≡ just (store-at 0))
           (f₃ : fetch prog (suc (suc (suc (fpc x)))) ≡ just mov-to-output)
           (f₄ : fetch prog (suc (suc (suc (suc (fpc x))))) ≡ just (store-rec h))
           (f₅ : fetch prog (suc (suc (suc (suc (suc (fpc x)))))) ≡ just (load-rec w-s1))
           (hx : LocState.halted (floc x) ≡ false) (nx : AllocState.next-heap-ref (falloc x) ≡ suc n)
           (hd : LocState.heapMem (floc x) (rec-loc h) ≡ just v₀)
           (inx : readReg (LocState.regs (floc x)) Input1 ≡ blk b)
           (ib : ExecFinal.in-block? {FS} (ExecFinal.live-size {FS} (falloc x)) (AtDynamic (heap-loc (mkHeapRef b) 0)) ≡ true)
           (h≢1 : ¬ h ≡ w-s1) (b≢0 : ¬ b ≡ 0) where

  O = readReg (LocState.regs (floc x)) Output

  x₁ = record x  { floc = writeLocToHeap (floc x) (rec-loc w-s1) O ; fpc = suc (fpc x) }
  x₂ = record x₁ { floc = record (floc x₁) { regs = writeReg (LocState.regs (floc x₁)) Output v₀ } ; fpc = suc (fpc x₁) }
  x₃ = record x₂ { floc = writeLocToHeap (floc x₂) (heap-loc (mkHeapRef b) 0) v₀ ; fpc = suc (fpc x₂) }
  x₄ = record x₃ { floc = record (floc x₃) { regs = writeReg (LocState.regs (floc x₃)) Output (readReg (LocState.regs (floc x₃)) Input1) } ; fpc = suc (fpc x₃) }
  x₅ = record x₄ { floc = writeLocToHeap (floc x₄) (rec-loc h) (readReg (LocState.regs (floc x₄)) Output) ; fpc = suc (fpc x₄) }
  x₆ = record x₅ { floc = record (floc x₅) { regs = writeReg (LocState.regs (floc x₅)) Output O } ; fpc = suc (fpc x₅) }

  private
    rec≢ : ∀ {i j} → ¬ i ≡ j → ¬ rec-loc i ≡ rec-loc j
    rec≢ ne e = ne (cong HeapLocation.heap-offset e)
    blk≢rec : ∀ k → ¬ heap-loc (mkHeapRef b) 0 ≡ rec-loc k
    blk≢rec k e = b≢0 (cong (λ q → HeapRef.ref-id (HeapLocation.heap-ref q)) e)

  -- the head word, read past the scratch write
  hd₁ : LocState.heapMem (floc x₁) (rec-loc h) ≡ just v₀
  hd₁ = trans (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) (rec-loc h) O (rec≢ (λ e → h≢1 (sym e)))) hd

  -- the scratch word, read back past the two writes after it
  sc₅ : LocState.heapMem (floc x₅) (rec-loc w-s1) ≡ just O
  sc₅ = trans (hw-other (LocState.heapMem (floc x₄)) (rec-loc h) (rec-loc w-s1) _ (rec≢ h≢1))
          (trans (hw-other (LocState.heapMem (floc x₂)) (heap-loc (mkHeapRef b) 0) (rec-loc w-s1) v₀ (blk≢rec w-s1))
                 (hw-same (LocState.heapMem (floc x)) (rec-loc w-s1) O))

  -- ★ the six steps
  run : FlatSteps prog 6 x x₆
  run = FlatSteps-++ (run-store-rec prog x w-s1 n nx hx f₀)
       (FlatSteps-++ (run-load-rec prog x₁ h n v₀ nx hx f₁ hd₁)
       (FlatSteps-++ (run-store-at0 prog x₂ b inx ib hx f₂)
       (FlatSteps-++ (run-mov-out prog x₃ hx f₃)
       (FlatSteps-++ (run-store-rec prog x₄ h n nx hx f₄)
                     (run-load-rec prog x₅ w-s1 n O nx hx f₅ sc₅)))))

  -- what it leaves: the registers, the head, the block's link, the rest
  out-in : readReg (LocState.regs (floc x₆)) Input1 ≡ readReg (LocState.regs (floc x)) Input1
  out-in = refl

  out-head : LocState.heapMem (floc x₆) (rec-loc h) ≡ just (blk b)
  out-head = trans (hw-same (LocState.heapMem (floc x₄)) (rec-loc h) _) (cong just inx)

  out-link : LocState.heapMem (floc x₆) (heap-loc (mkHeapRef b) 0) ≡ just v₀
  out-link = trans (hw-other (LocState.heapMem (floc x₄)) (rec-loc h) (heap-loc (mkHeapRef b) 0) _ (λ e → blk≢rec h (sym e)))
                   (hw-same (LocState.heapMem (floc x₂)) (heap-loc (mkHeapRef b) 0) v₀)

  out-other : ∀ q → ¬ q ≡ rec-loc h → ¬ q ≡ heap-loc (mkHeapRef b) 0 → ¬ q ≡ rec-loc w-s1
            → LocState.heapMem (floc x₆) q ≡ LocState.heapMem (floc x) q
  out-other q n₁ n₂ n₃ =
    trans (hw-other (LocState.heapMem (floc x₄)) (rec-loc h) q _ (λ e → n₁ (sym e)))
      (trans (hw-other (LocState.heapMem (floc x₂)) (heap-loc (mkHeapRef b) 0) q v₀ (λ e → n₂ (sym e)))
             (hw-other (LocState.heapMem (floc x)) (rec-loc w-s1) q O (λ e → n₃ (sym e))))
