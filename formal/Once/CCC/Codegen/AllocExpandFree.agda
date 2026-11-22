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
open import Data.Empty using (⊥; ⊥-elim)
import Data.Sum
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

------------------------------------------------------------------------
-- 3. The primitive side of a free: the block leaves the live part
------------------------------------------------------------------------

open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Data.Bool using (_∨_)
open import Once.CCC.Codegen.AllocExpandRel {FS} using (Live)
module AE = Once.CCC.Machine.SMCore.AbstractExec {FS}

-- the marks after freeing block r
mark-at : ∀ (fr : ℕ → Bool) r r′ → AE.freeMark (blk r) fr r′ ≡ ((r′ ≡ᵇ r) ∨ fr r′)
mark-at fr r r′ = refl

private
  ≡ᵇ-refl : ∀ r → (r ≡ᵇ r) ≡ true
  ≡ᵇ-refl zero    = refl
  ≡ᵇ-refl (suc r) = ≡ᵇ-refl r

  ≡ᵇ-miss : ∀ a b → ¬ a ≡ b → (a ≡ᵇ b) ≡ false
  ≡ᵇ-miss zero    zero    ne = ⊥-elim (ne refl)
  ≡ᵇ-miss zero    (suc b) ne = refl
  ≡ᵇ-miss (suc a) zero    ne = refl
  ≡ᵇ-miss (suc a) (suc b) ne = ≡ᵇ-miss a b (λ e → ne (cong suc e))

  split∨ : ∀ (a b : Bool) → (a ∨ b) ≡ false → (a ≡ false) × (b ≡ false)
  split∨ false false _ = refl , refl

-- a block live after the free was live before, and is not the freed one
live-after : ∀ (al : AllocState {FS}) r r′
           → Live (record al { freed = AE.freeMark (blk r) (AllocState.freed al) }) r′
           → Live al r′ × ¬ r′ ≡ r
live-after al r r′ (pos , lt , fr) = (pos , lt , proj₂ sp) , ne
  where
    sp = split∨ (r′ ≡ᵇ r) (AllocState.freed al r′) fr
    ne : ¬ r′ ≡ r
    ne e = absurd (trans (sym (≡ᵇ-refl r)) (trans (cong (λ z → z ≡ᵇ r) (sym e)) (proj₁ sp)))
      where
        absurd : true ≡ false → ⊥
        absurd ()

-- …and back: a live block other than the freed one stays live
live-before : ∀ (al : AllocState {FS}) r r′ → Live al r′ → ¬ r′ ≡ r
            → Live (record al { freed = AE.freeMark (blk r) (AllocState.freed al) }) r′
live-before al r r′ (pos , lt , fr) ne = pos , lt , trans (cong (_∨ AllocState.freed al r′) (≡ᵇ-miss r′ r ne)) fr

------------------------------------------------------------------------
-- 4. ★ The free's step
------------------------------------------------------------------------

open import Once.CCC.Codegen.AllocExpandRel {FS} using (Rel; module Rel; Chain)
open import Once.CCC.Codegen.AllocExpandRen {FS} using (rhl; rv)
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off; off-suc; fetch-exp)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open FlatMachine {FS} using (straight-go; straight-at; flat-fault)
import Data.Nat.Properties

module Step (C : Classes) (P : AbstractTrace) (Sz : ℕ → Set)
            (uniform  : ∀ k k′ → Sz k → Sz k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′)
            (fits     : ∀ k → k ≤ bsz C k)
            (in-range : ∀ k → cls C k < count C)
            (sz-free  : ∀ n k → fetch P n ≡ just (instr-free-heap k) → Sz k) where
  open Rel

  E = expand C P

  -- a number below another: the other is a successor
  succ-of : ∀ {a m} → a < m → Σ ℕ λ n → m ≡ suc n
  succ-of {m = suc n} _ = n , refl

  -- the freed block is a live one
  freed-live : ∀ {fs gs} (R : Rel C P Sz fs gs) k (B : Base (falloc fs) k (readReg (LocState.regs (floc fs)) Input1))
             → Live (falloc fs) (b-ref B)
  freed-live {fs} R k B = pos , below , b-live B
    where
      k>0 : 0 < k
      k>0 = Data.Nat.Properties.<ᵇ⇒< 0 k (subst Data.Bool.T (sym (b-pos B)) Data.Unit.tt)
        where import Data.Unit
      pos : 0 < b-ref B
      pos = nz (b-ref B) refl
        where
          nz : ∀ r → b-ref B ≡ r → 0 < b-ref B
          nz (suc r) e = subst (0 <_) (sym e) (s≤s z≤n)
          nz zero    e = ⊥-elim (Data.Nat.Properties.<-irrefl refl (subst (0 <_) (trans (sym (b-size B)) (trans (cong (AllocState.block-size (falloc fs)) e) (r-rec0 R))) k>0))
      below : b-ref B < AllocState.next-heap-ref (falloc fs)
      below = Data.Nat.Properties.≰⇒> λ ge → Data.Nat.Properties.<-irrefl refl (subst (0 <_) (trans (sym (b-size B)) (r-unsized R (b-ref B) ge)) k>0)

  -- a chain read through a heap that agrees on its cells
  chain-frame : ∀ (h h′ : HeapMem FS) σ (bs : List ℕ) v
              → (∀ b → b ∈ bs → h′ (heap-loc (mkHeapRef b) 0) ≡ h (heap-loc (mkHeapRef b) 0))
              → Chain h σ bs v → Chain h′ σ bs v
  chain-frame h h′ σ []       v same c = c
  chain-frame h h′ σ (b ∷ bs) v same (e , w , hw , c) =
    e , w , trans (same b (here refl)) hw , chain-frame h h′ σ bs w (λ b′ m → same b′ (there m)) c

  -- a list with the block pushed on its class
  push-at : ∀ {c c′ : ℕ} → Relation.Nullary.Dec (c ≡ c′) → ℕ → List ℕ → List ℕ
  push-at (yes _) b bs = b ∷ bs
  push-at (no _)  b bs = bs

  push-mem : ∀ {c c′ : ℕ} (d : Relation.Nullary.Dec (c ≡ c′)) b bs x → x ∈ push-at d b bs → (c ≡ c′ × x ≡ b) Data.Sum.⊎ x ∈ bs
  push-mem (yes e) b bs .b (here refl) = Data.Sum.inj₁ (e , refl)
  push-mem (yes e) b bs x  (there m)   = Data.Sum.inj₂ m
  push-mem (no _)  b bs x  m           = Data.Sum.inj₂ m

  -- the cleared block's cells are empty; another block's are as they were
  free-hit : ∀ (mem : HeapMem FS) r hl → ref-of hl ≡ r → AE.freeMem (blk r) mem hl ≡ nothing
  free-hit mem r hl e = go (HeapRef.ref-id (HeapLocation.heap-ref hl) Data.Nat.≟ r)
    where
      go : ∀ (d : Relation.Nullary.Dec (ref-of hl ≡ r)) → MemOps.clearBlock-aux {FS} d (mem hl) ≡ nothing
      go (yes _) = refl
      go (no ne) = ⊥-elim (ne e)

  free-miss : ∀ (mem : HeapMem FS) r hl → ¬ ref-of hl ≡ r → AE.freeMem (blk r) mem hl ≡ mem hl
  free-miss mem r hl ne = AE.freeMem-miss mem (heap-loc (mkHeapRef r) 0) r hl ne refl

  -- ★ the free: its push, and the relation after
  step-free : ∀ {fs gs} (R : Rel C P Sz fs gs) k → fetch P (fpc fs) ≡ just (instr-free-heap k) → LocState.halted (floc fs) ≡ false
            → LocState.faulted (floc (flat-exec-instr (instr-free-heap k) P fs)) ≡ false
            → Σ FlatState λ gs′ → FlatSteps E 6 gs gs′ × Rel C P Sz (flat-exec-instr (instr-free-heap k) P fs) gs′
  step-free {fs} {gs} R k f hx nf = go (block-base? k (readReg (LocState.regs (floc fs)) Input1) (falloc fs)) refl nf
    where
      go : ∀ b → block-base? k (readReg (LocState.regs (floc fs)) Input1) (falloc fs) ≡ b
         → LocState.faulted (floc (straight-at b (instr-free-heap k) fs)) ≡ false
         → Σ FlatState λ gs′ → FlatSteps E 6 gs gs′ × Rel C P Sz (straight-at b (instr-free-heap k) fs) gs′
      go false _ ()
      go true e _ = RR.x₆ , RR.run , R′
        where
          B = base-of (falloc fs) k (readReg (LocState.regs (floc fs)) Input1) e
          r = b-ref B
          lv = freed-live R k B
          c₀ = cls C k
          h = head-word c₀
          pc = fpc fs
          -- the expansion's fetches
          fe : ∀ j i → fetch (free-code C k) j ≡ just i → fetch E (j + fpc gs) ≡ just i
          fe j i e′ = subst (λ z → fetch E z ≡ just i)
                            (trans (Data.Nat.Properties.+-comm (off C 0 P pc) j) (cong (j +_) (sym (r-pc R))))
                            (fetch-exp C 0 P pc (instr-free-heap k) f j i e′)
          f0 = fe 0 (store-rec w-s1) refl
          f1 = fe 1 (load-rec h) refl
          f2 = fe 2 (store-at 0) refl
          f3 = fe 3 mov-to-output refl
          f4 = fe 4 (store-rec h) refl
          f5 = fe 5 (load-rec w-s1) refl
          hg : LocState.halted (floc gs) ≡ false
          hg = trans (L.LRel.l-halt (r-loc R)) hx
          rb = r-below R r lv
          n = proj₁ (succ-of (proj₂ rb))
          nx = proj₂ (succ-of (proj₂ rb))
          hds = r-heads R c₀ (in-range k)
          v₀ = proj₁ hds
          hd = proj₁ (proj₂ hds)
          inx : readReg (LocState.regs (floc gs)) Input1 ≡ blk (ρ R r)
          inx = trans (L.LRel.l-regs (r-loc R) Input1) (cong (rv (ρ R)) (b-ptr B))
          b≢0 : ¬ ρ R r ≡ 0
          b≢0 e′ = Data.Nat.Properties.<-irrefl (sym e′) (proj₁ rb)
          -- the renamed block passes the store gate: its size at least the class's, at least 1
          ib : ExecFinal.in-block? {FS} (ExecFinal.live-size {FS} (falloc gs)) (AtDynamic (heap-loc (mkHeapRef (ρ R r)) 0)) ≡ true
          ib = of-T (Data.Nat.Properties.<⇒<ᵇ (Data.Nat.Properties.<-≤-trans k>0
                 (Data.Nat.Properties.≤-trans (fits k)
                   (subst (λ z → bsz C z ≤ ExecFinal.live-size {FS} (falloc gs) (ρ R r)) (b-size B)
                     (subst (bsz C (AllocState.block-size (falloc fs) r) ≤_)
                            (sym (cong (λ fr → Data.Bool.if fr then 0 else AllocState.block-size (falloc gs) (ρ R r)) (r-nofree R (ρ R r))))
                            (r-csize R r lv))))))
            where
              k>0 : 0 < k
              k>0 = Data.Nat.Properties.<ᵇ⇒< 0 k (subst Data.Bool.T (sym (b-pos B)) Data.Unit.tt)
                where import Data.Unit
              of-T : ∀ {b : Bool} → Data.Bool.T b → b ≡ true
              of-T {true} _ = refl
          module RR = Run E gs h (ρ R r) n v₀ f0 f1 f2 f3 f4 f5 hg nx hd inx ib (λ ()) b≢0
          G = RR.x₆
          fs′ = straight-go (instr-free-heap k) fs
          v₁ = readReg (LocState.regs (floc fs)) Input1
          -- liveness after the free: before, minus the freed block
          to′ : ∀ r′ → Live (falloc fs′) r′ → Live (falloc fs) r′ × ¬ r′ ≡ r
          to′ r′ l = live-after (falloc fs) r r′
                       (subst (λ v → Live (record (falloc fs) { freed = AE.freeMark v (AllocState.freed (falloc fs)) }) r′) (b-ptr B) l)
          fro′ : ∀ r′ → Live (falloc fs) r′ → ¬ r′ ≡ r → Live (falloc fs′) r′
          fro′ r′ l ne = subst (λ v → Live (record (falloc fs) { freed = AE.freeMark v (AllocState.freed (falloc fs)) }) r′) (sym (b-ptr B))
                           (live-before (falloc fs) r r′ l ne)
          -- the heap after the free, by the freed block's
          heap′ : ∀ hl → LocState.heapMem (floc fs′) hl ≡ AE.freeMem (blk r) (LocState.heapMem (floc fs)) hl
          heap′ hl = cong (λ v → AE.freeMem v (LocState.heapMem (floc fs)) hl) (b-ptr B)
          inj′ : ∀ a b′ → Live (falloc fs′) a → Live (falloc fs′) b′ → ρ R a ≡ ρ R b′ → a ≡ b′
          inj′ a b′ la lb = r-inj R a b′ (proj₁ (to′ a la)) (proj₁ (to′ b′ lb))
          -- the expanded words no live block is renamed to, and those the run wrote
          ref≢ : ∀ q j → 0 < ref-of q → ¬ q ≡ rec-loc j
          ref≢ q j p e′ = Data.Nat.Properties.<-irrefl (sym (cong ref-of e′)) p
          blk≢ : ∀ q → ¬ ref-of q ≡ ρ R r → ¬ q ≡ heap-loc (mkHeapRef (ρ R r)) 0
          blk≢ q ne e′ = ne (cong ref-of e′)
          kept : ∀ q → 0 < ref-of q → ¬ ref-of q ≡ ρ R r → LocState.heapMem (floc G) q ≡ LocState.heapMem (floc gs) q
          kept q p ne = RR.out-other q (ref≢ q h p) (blk≢ q ne) (ref≢ q w-s1 p)
          lists′ : ℕ → List ℕ
          lists′ c = push-at (c Data.Nat.≟ c₀) (ρ R r) (lists R c)
          -- a list's old blocks: their links are as they were
          chain-kept : ∀ c v → Chain (LocState.heapMem (floc gs)) (σ R) (lists R c) v → Chain (LocState.heapMem (floc G)) (σ R) (lists R c) v
          chain-kept c v ch = chain-frame (LocState.heapMem (floc gs)) (LocState.heapMem (floc G)) (σ R) (lists R c) v
                                (λ b′ m → kept (heap-loc (mkHeapRef b′) 0) (r-lpos R c b′ m) (λ e′ → r-not-free R r c b′ lv m (sym e′))) ch
          heads′ : ∀ c → c < count C → Σ (StoredValue FS) λ v → LocState.heapMem (floc G) (rec-loc (head-word c)) ≡ just v
                                                             × Chain (LocState.heapMem (floc G)) (σ R) (lists′ c) v
          heads′ c c< = hd′ (c Data.Nat.≟ c₀)
            where
              hd′ : ∀ (d : Relation.Nullary.Dec (c ≡ c₀)) → Σ (StoredValue FS) λ v → LocState.heapMem (floc G) (rec-loc (head-word c)) ≡ just v
                                                                                × Chain (LocState.heapMem (floc G)) (σ R) (push-at d (ρ R r) (lists R c)) v
              hd′ (yes refl) = blk (ρ R r) , RR.out-head , refl , v₀ , RR.out-link , chain-kept c₀ v₀ (proj₂ (proj₂ hds))
              hd′ (no ne) = old (r-heads R c c<)
                where
                  old : (Σ (StoredValue FS) λ v → LocState.heapMem (floc gs) (rec-loc (head-word c)) ≡ just v
                                                × Chain (LocState.heapMem (floc gs)) (σ R) (lists R c) v)
                      → Σ (StoredValue FS) λ v → LocState.heapMem (floc G) (rec-loc (head-word c)) ≡ just v
                                                × Chain (LocState.heapMem (floc G)) (σ R) (lists R c) v
                  old (v , e′ , ch) = v , trans (RR.out-other (rec-loc (head-word c)) (λ e″ → ne (suc-inj (suc-inj (suc-inj (cong HeapLocation.heap-offset e″)))))
                                                   (λ e″ → b≢0 (sym (cong ref-of e″))) (λ ()) ) e′
                                    , chain-kept c v ch
                    where
                      suc-inj : ∀ {a b′} → suc a ≡ suc b′ → a ≡ b′
                      suc-inj refl = refl
          R′ : Rel C P Sz fs′ G
          R′ = record
            { ρ = ρ R ; σ = σ R ; lists = lists′
            ; r-pc = trans (cong (λ z → suc (suc (suc (suc (suc (suc z)))))) (r-pc R))
                           (sym (trans (off-suc C 0 P pc (instr-free-heap k) f) (Data.Nat.Properties.+-comm (off C 0 P pc) 6)))
            ; r-ret = r-ret R ; r-link = r-link R
            ; r-frame = r-frame R ; r-saved = r-saved R ; r-slots = r-slots R ; r-next-slot = r-next-slot R
            ; r-inj = inj′
            ; r-loc = record
                { l-regs = λ { Input1 → L.LRel.l-regs (r-loc R) Input1 ; Output → L.LRel.l-regs (r-loc R) Output }
                ; l-stack = L.LRel.l-stack (r-loc R)
                ; l-heap = λ hl v l e′ → let tl = to′ (ref-of hl) l in
                    trans (kept (rhl (ρ R) hl) (proj₁ (r-below R (ref-of hl) (proj₁ tl)))
                                (λ e″ → proj₂ tl (r-inj R (ref-of hl) r (proj₁ tl) lv e″)))
                          (L.LRel.l-heap (r-loc R) hl v (proj₁ tl) (trans (sym (free-miss (LocState.heapMem (floc fs)) r hl (proj₂ tl))) (trans (sym (heap′ hl)) e′)))
                ; l-live = λ hl v e′ → live′ hl v e′
                ; l-halt = L.LRel.l-halt (r-loc R) ; l-fault = L.LRel.l-fault (r-loc R)
                ; l-left = L.LRel.l-left (r-loc R) ; l-log = L.LRel.l-log (r-loc R) }
            ; r-clo = r-clo R
            ; r-size = r-size R
            ; r-below = λ r′ l → r-below R r′ (proj₁ (to′ r′ l))
            ; r-not-σ = λ r′ l → r-not-σ R r′ (proj₁ (to′ r′ l))
            ; r-not-free = λ r′ c b′ l m → nfree r′ c b′ l (push-mem (c Data.Nat.≟ c₀) (ρ R r) (lists R c) b′ m)
            ; r-heads = heads′
            ; r-sent = trans (kept (heap-loc (mkHeapRef (σ R)) 0) (r-σpos R) (λ e″ → r-not-σ R r lv (sym e″))) (r-sent R)
            ; r-lpos = λ c b′ m → lpos c b′ (push-mem (c Data.Nat.≟ c₀) (ρ R r) (lists R c) b′ m)
            ; r-σpos = r-σpos R
            ; r-nofree = r-nofree R
            ; r-unsized = r-unsized R
            ; r-rec0 = r-rec0 R
            ; r-csize = λ r′ l → r-csize R r′ (proj₁ (to′ r′ l))
            ; r-lsize = λ c b′ m k′ z ec → lsize c b′ (push-mem (c Data.Nat.≟ c₀) (ρ R r) (lists R c) b′ m) k′ z ec
            ; r-lbelow = λ c b′ m → lbelow c b′ (push-mem (c Data.Nat.≟ c₀) (ρ R r) (lists R c) b′ m)
            ; r-lσ = λ c b′ m → lσ c b′ (push-mem (c Data.Nat.≟ c₀) (ρ R r) (lists R c) b′ m)
            ; r-luniq = λ c → luniq c (c Data.Nat.≟ c₀)
            ; r-lone = λ c c′ b′ m m′ → lone c c′ b′ (push-mem (c Data.Nat.≟ c₀) (ρ R r) (lists R c) b′ m) (push-mem (c′ Data.Nat.≟ c₀) (ρ R r) (lists R c′) b′ m′)
            ; r-σbelow = r-σbelow R ; r-pnext = r-pnext R
            ; r-pfresh = λ r′ le → subst (λ v → AE.freeMark v (AllocState.freed (falloc fs)) r′ ≡ false) (sym (b-ptr B))
                                     (trans (cong (_∨ AllocState.freed (falloc fs) r′) (≡ᵇ-miss r′ r (λ e′ → Data.Nat.Properties.<-irrefl (sym e′) (Data.Nat.Properties.<-≤-trans (proj₁ (proj₂ lv)) le))))
                                            (r-pfresh R r′ le)) }
            where
              lbelow : ∀ c b′ → (c ≡ c₀ × b′ ≡ ρ R r) Data.Sum.⊎ b′ ∈ lists R c → b′ < AllocState.next-heap-ref (falloc G)
              lbelow c b′ (Data.Sum.inj₁ (_ , refl)) = proj₂ rb
              lbelow c b′ (Data.Sum.inj₂ m) = r-lbelow R c b′ m
              lσ : ∀ c b′ → (c ≡ c₀ × b′ ≡ ρ R r) Data.Sum.⊎ b′ ∈ lists R c → ¬ b′ ≡ σ R
              lσ c b′ (Data.Sum.inj₁ (_ , refl)) = r-not-σ R r lv
              lσ c b′ (Data.Sum.inj₂ m) = r-lσ R c b′ m
              -- the pushed block was on no list
              off-lists : ∀ c → All (λ y → ¬ ρ R r ≡ y) (lists R c)
              off-lists c = Data.List.Relation.Unary.All.tabulate (λ {y} m e′ → r-not-free R r c y lv m e′)
              luniq : ∀ c (d : Relation.Nullary.Dec (c ≡ c₀)) → Unique (push-at d (ρ R r) (lists R c))
              luniq c (yes _) = off-lists c ∷ r-luniq R c
              luniq c (no _)  = r-luniq R c
              lone : ∀ c c′ b′ → (c ≡ c₀ × b′ ≡ ρ R r) Data.Sum.⊎ b′ ∈ lists R c → (c′ ≡ c₀ × b′ ≡ ρ R r) Data.Sum.⊎ b′ ∈ lists R c′ → c ≡ c′
              lone c c′ b′ (Data.Sum.inj₁ (e₁ , _)) (Data.Sum.inj₁ (e₂ , _)) = trans e₁ (sym e₂)
              lone c c′ b′ (Data.Sum.inj₁ (_ , refl)) (Data.Sum.inj₂ m′) = ⊥-elim (r-not-free R r c′ (ρ R r) lv m′ refl)
              lone c c′ b′ (Data.Sum.inj₂ m) (Data.Sum.inj₁ (_ , refl)) = ⊥-elim (r-not-free R r c (ρ R r) lv m refl)
              lone c c′ b′ (Data.Sum.inj₂ m) (Data.Sum.inj₂ m′) = r-lone R c c′ b′ m m′
              live′ : ∀ hl v → LocState.heapMem (floc fs′) hl ≡ just v → Live (falloc fs′) (ref-of hl)
              live′ hl v e′ = by (ref-of hl Data.Nat.≟ r)
                where
                  by : Relation.Nullary.Dec (ref-of hl ≡ r) → Live (falloc fs′) (ref-of hl)
                  by (yes eq) = ⊥-elim (nothing≢ (trans (sym (free-hit (LocState.heapMem (floc fs)) r hl eq)) (trans (sym (heap′ hl)) e′)))
                    where
                      nothing≢ : ¬ (nothing ≡ just v)
                      nothing≢ ()
                  by (no ne) = fro′ (ref-of hl) (L.LRel.l-live (r-loc R) hl v (trans (sym (free-miss (LocState.heapMem (floc fs)) r hl ne)) (trans (sym (heap′ hl)) e′))) ne
              nfree : ∀ r′ c b′ → Live (falloc fs′) r′ → (c ≡ c₀ × b′ ≡ ρ R r) Data.Sum.⊎ b′ ∈ lists R c → ¬ ρ R r′ ≡ b′
              nfree r′ c b′ l (Data.Sum.inj₁ (_ , refl)) e′ = proj₂ (to′ r′ l) (r-inj R r′ r (proj₁ (to′ r′ l)) lv e′)
              nfree r′ c b′ l (Data.Sum.inj₂ m) = r-not-free R r′ c b′ (proj₁ (to′ r′ l)) m
              lpos : ∀ c b′ → (c ≡ c₀ × b′ ≡ ρ R r) Data.Sum.⊎ b′ ∈ lists R c → 0 < b′
              lpos c b′ (Data.Sum.inj₁ (_ , refl)) = proj₁ rb
              lpos c b′ (Data.Sum.inj₂ m) = r-lpos R c b′ m
              lsize : ∀ c b′ → (c ≡ c₀ × b′ ≡ ρ R r) Data.Sum.⊎ b′ ∈ lists R c → ∀ k′ → Sz k′ → cls C k′ ≡ c → bsz C k′ ≤ AllocState.block-size (falloc G) b′
              lsize c b′ (Data.Sum.inj₁ (refl , refl)) k′ z ec =
                subst (_≤ AllocState.block-size (falloc gs) (ρ R r))
                      (sym (trans (uniform k′ k z (sz-free pc k f) ec) (cong (bsz C) refl)))
                      (subst (λ m → bsz C m ≤ AllocState.block-size (falloc gs) (ρ R r)) (b-size B) (r-csize R r lv))
              lsize c b′ (Data.Sum.inj₂ m) k′ z ec = r-lsize R c b′ m k′ z ec
