-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatInitWF   (Plan 0.123 A.4 step 4, part 2)
--
-- EVERY BLOCK IS WRITTEN BEFORE IT IS READ, as a fact about the run. The
-- emitted code's half is `Codegen.InitWindow` (each allocation is followed
-- by a window that writes both cells before anything reads through the new
-- pointer). This module is the run's half, built as `FlatPtrBounds` is.
--
-- Part A, here: `Full` (every in-bounds cell of every allocated block is
-- written) survives every step that is not an allocation, because such a
-- step keeps the allocation counter and every block's size and never
-- un-writes a cell (`Keeps`).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatInitWF (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_; s≤s; z≤n)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; drop)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n; <⇒≢)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; _≟HL_; module HeapRef; module HeapLocation)
open HeapLocation using (heap-offset; heap-ref)
open HeapRef using (ref-id)
open import Once.CCC.Machine.SMCore
open AllocState using (block-size; next-heap-ref)
open LocState using (heapMem; stackMem; regs)
open AllocState using (current-frame)
open import Once.CCC.FrameSemantics using (module FrameSemantics)
open FrameSemantics FS using (Frame; _≟F_)
open import Once.CCC.Machine.Locations using (Slot)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Once.CCC.Machine.Locations using (AtDynamic; AtStack; ValueLocation)
open MemOps {FS}
open ExecFinal {FS}
open AbstractExec {FS}
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open import Once.CCC.Machine.FrameFree using (EmittableI; ImageI)
open import Once.CCC.Codegen.InitWindow using (Apart; Win; WinFrom; InitDisc; not-alloc?; []; _∷_; alloc
  ; w-done; w-stash; w-store-slot; w-mov-in; w-load-stash; w-load-slot; w-restore-stash; w-restore-slot
  ; w-load; w-load-suc; w-store; w-store-suc; w-tag; w-code)
open import Data.Bool using (T)
open import Once.CCC.Machine.FlatStoreWF FS using (StoreWF; sv-below; svm-below; module StoreWF)
open StoreWF using (wf-regs; wf-heap; wf-stack)
open import Once.CCC.Machine.FlatPtrBounds FS using (size-with-new; size-with-old)
open import Once.CCC.Machine.FlatStackPtr FS using (SPInv; StackPtrOK; module SPInv)
open SPInv using (sp-regs)
open import Once.CCC.Machine.SMPrimitives using (module InstrPrimitives; nhw-load-indirect; nhw-load-indirect-suc; nhw-instr-sigop; nhw-instr-reg-op)
open InstrPrimitives {FS} using (exec-abstract-preserves-heapMem)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

------------------------------------------------------------------------
-- The invariant's closed form, and what a step must keep for it.
------------------------------------------------------------------------
Full : AllocState {FS} → LocState FS → Set
Full al ls = ∀ (hl : HeapLocation)
           → ref-id (heap-ref hl) < next-heap-ref al
           → heap-offset hl < block-size al (ref-id (heap-ref hl))
           → Σ (StoredValue FS) (λ w → heapMem ls hl ≡ just w)

-- a written cell stays written
-- (a record, so its two states are inferable from its type)
record HeapGrows (a b : LocState FS) : Set where
  constructor mkGrows
  field grows : ∀ (hl : HeapLocation) (w : StoredValue FS)
              → heapMem a hl ≡ just w → Σ (StoredValue FS) (λ w' → heapMem b hl ≡ just w')
open HeapGrows

Keeps : FlatState → FlatState → Set
Keeps a b = (next-heap-ref (falloc b) ≡ next-heap-ref (falloc a))
          × (∀ r → block-size (falloc b) r ≡ block-size (falloc a) r)
          × HeapGrows (floc a) (floc b)

full-keep : ∀ {a b : FlatState} → Keeps a b → Full (falloc a) (floc a) → Full (falloc b) (floc b)
full-keep {a} {b} (nx , bs , gr) full hl lt ib with full hl
  (subst (ref-id (heap-ref hl) <_) nx lt)
  (subst (heap-offset hl <_) (bs (ref-id (heap-ref hl))) ib)
... | w , eq = grows gr hl w eq

grows-eq : ∀ {a b : LocState FS} → heapMem b ≡ heapMem a → HeapGrows a b
grows-eq {a} {b} e = mkGrows (λ hl w eq → w , trans (cong-app′ e hl) eq)
  where cong-app′ : ∀ {f g : HeapMem FS} → f ≡ g → ∀ x → f x ≡ g x
        cong-app′ refl x = refl

------------------------------------------------------------------------
-- A heap write writes `just`: no cell is ever un-written.
------------------------------------------------------------------------
writeHeapMem-grows : ∀ (m : HeapMem FS) (hl : HeapLocation) (v : StoredValue FS)
                   → ∀ hl' w → m hl' ≡ just w
                   → Σ (StoredValue FS) (λ w' → writeHeapMem m hl v hl' ≡ just w')
writeHeapMem-grows m hl v hl' w eq with hl ≟HL hl'
... | yes _ = v , refl
... | no  _ = w , eq

writeLoc-grows : ∀ (ls : LocState FS) (loc : ValueLocation FS) (v : StoredValue FS)
               → HeapGrows ls (writeLoc ls loc v)
writeLoc-grows ls (AtStack f k)  v                      = mkGrows (λ hl w eq → w , eq)
writeLoc-grows ls (AtDynamic h) (SV-Ptr (AtStack f k))  = mkGrows (writeHeapMem-grows (heapMem ls) h _)
writeLoc-grows ls (AtDynamic h) (SV-Ptr (AtDynamic x))  = mkGrows (writeHeapMem-grows (heapMem ls) h _)
writeLoc-grows ls (AtDynamic h) (SV-Tag t)              = mkGrows (writeHeapMem-grows (heapMem ls) h _)
writeLoc-grows ls (AtDynamic h) (SV-Lit p x)            = mkGrows (writeHeapMem-grows (heapMem ls) h _)
writeLoc-grows ls (AtDynamic h) (SV-Code c)             = mkGrows (writeHeapMem-grows (heapMem ls) h _)

store-grows : ∀ (ml : Maybe (ValueLocation FS)) (v : StoredValue FS) (ls : LocState FS)
            → HeapGrows ls (exec-store-via-resolved ml v ls)
store-grows (just loc) v ls = writeLoc-grows ls loc v
store-grows nothing    v ls = mkGrows (λ hl w eq → w , eq)

store-suc-grows : ∀ (ml : Maybe (ValueLocation FS)) (v : StoredValue FS) (ls : LocState FS)
                → HeapGrows ls (exec-store-suc-via-resolved ml v ls)
store-suc-grows (just loc) v ls = writeLoc-grows ls (sucLoc loc) v
store-suc-grows nothing    v ls = mkGrows (λ hl w eq → w , eq)

------------------------------------------------------------------------
-- Every straight-line instruction but the allocation keeps the counter and
-- the sizes and grows the heap. Enumerated over the emittable ones (a
-- catch-all would not reduce `exec-abstract`'s case tree).
------------------------------------------------------------------------
KeepsA : AbstractInstr → LocState FS → AllocState {FS} → Set
KeepsA i ls al = (next-heap-ref (proj₂ (exec-abstract i ls al)) ≡ next-heap-ref al)
               × (∀ r → block-size (proj₂ (exec-abstract i ls al)) r ≡ block-size al r)
               × HeapGrows ls (proj₁ (exec-abstract i ls al))

private
  same : ∀ {ls ls' : LocState FS} {al : AllocState {FS}}
       → heapMem ls' ≡ heapMem ls
       → (next-heap-ref al ≡ next-heap-ref al) × (∀ r → block-size al r ≡ block-size al r) × HeapGrows ls ls'
  same e = refl , (λ _ → refl) , grows-eq e

  lfs-al : ∀ (mv : Maybe (StoredValue FS)) (s : LocState FS) (al : AllocState {FS})
         → (proj₂ (exec-load-from-slot-with-value mv s al) ≡ al)
           × (heapMem (proj₁ (exec-load-from-slot-with-value mv s al)) ≡ heapMem s)
  lfs-al (just v) s al = refl , refl
  lfs-al nothing  s al = refl , refl

  ri-al : ∀ (mv : Maybe (StoredValue FS)) (s : LocState FS) (al : AllocState {FS})
        → (proj₂ (exec-restore-input-with-value mv s al) ≡ al)
          × (heapMem (proj₁ (exec-restore-input-with-value mv s al)) ≡ heapMem s)
  ri-al (just v) s al = refl , refl
  ri-al nothing  s al = refl , refl

  via : ∀ {ls ls' : LocState FS} {al al' : AllocState {FS}}
      → al' ≡ al → heapMem ls' ≡ heapMem ls
      → (next-heap-ref al' ≡ next-heap-ref al) × (∀ r → block-size al' r ≡ block-size al r) × HeapGrows ls ls'
  via {al = al} refl e = same {al = al} e

keeps-abstract : ∀ (i : AbstractInstr) (ls : LocState FS) (al : AllocState {FS})
               → EmittableI i → (∀ n → ¬ (i ≡ instr-alloc-heap n)) → KeepsA i ls al
keeps-abstract mov-to-output          ls al e na = same {al = al} refl
keeps-abstract mov-to-input           ls al e na = same {al = al} refl
keeps-abstract load-indirect          ls al e na =
  refl , (λ _ → refl) , grows-eq (exec-abstract-preserves-heapMem load-indirect ls al nhw-load-indirect)
keeps-abstract load-indirect-suc      ls al e na =
  refl , (λ _ → refl) , grows-eq (exec-abstract-preserves-heapMem load-indirect-suc ls al nhw-load-indirect-suc)
keeps-abstract (load-from-slot k)     ls al e na = via (proj₁ (lfs-al mv ls al)) (proj₂ (lfs-al mv ls al))
  where mv = readLoc ls (AtStack (AllocState.current-frame al) k)
keeps-abstract (store-at-slot k)      ls al e na =
  refl , (λ _ → refl) , writeLoc-grows ls (AtStack (AllocState.current-frame al) k) (readReg (LocState.regs ls) Output)
keeps-abstract store-indirect         ls al e na =
  refl , (λ _ → refl) , store-grows (sv-as-loc (readReg (LocState.regs ls) Input1)) (readReg (LocState.regs ls) Output) ls
keeps-abstract store-indirect-suc     ls al e na =
  refl , (λ _ → refl) , store-suc-grows (sv-as-loc (readReg (LocState.regs ls) Input1)) (readReg (LocState.regs ls) Output) ls
keeps-abstract (lea-slot k)           ls al e na = same {al = al} refl
keeps-abstract (restore-input k)      ls al e na = via (proj₁ (ri-al mv ls al)) (proj₂ (ri-al mv ls al))
  where mv = readLoc ls (AtStack (AllocState.current-frame al) k)
keeps-abstract (instr-reclaim-to k)   ls al e na = same {al = al} refl
keeps-abstract instr-call-closure     ls al e na = same {al = al} refl
keeps-abstract (worklist-init k)      ls al e na = same {al = al} refl
keeps-abstract (worklist-push k)      ls al e na =
  refl , (λ _ → refl) , writeLoc-grows ls (AtStack (AllocState.current-frame al) k) (readReg (LocState.regs ls) Output)
keeps-abstract (worklist-pop k)       ls al e na = via (proj₁ (lfs-al mv ls al)) (proj₂ (lfs-al mv ls al))
  where mv = readLoc ls (AtStack (AllocState.current-frame al) k)
keeps-abstract (worklist-check k)     ls al e na = same {al = al} refl
keeps-abstract (instr-sigop si)       ls al e na =
  refl , (λ _ → refl) , grows-eq (exec-abstract-preserves-heapMem (instr-sigop si) ls al nhw-instr-sigop)
keeps-abstract (instr-load-const p v) ls al e na = same {al = al} refl
keeps-abstract (instr-load-code-addr k) ls al e na = same {al = al} refl
keeps-abstract instr-save-closure-reg ls al e na = same {al = al} refl
keeps-abstract (instr-load-tag-lit k) ls al e na = same {al = al} refl
keeps-abstract (instr-reg-op op)      ls al e na =
  refl , (λ _ → refl) , grows-eq (exec-abstract-preserves-heapMem (instr-reg-op op) ls al nhw-instr-reg-op)
keeps-abstract (instr-ctrl c)         ls al e na = same {al = al} refl
keeps-abstract (instr-alloc-heap n)   ls al e na = ⊥-elim (na n refl)
keeps-abstract (lea-indexed k)        ls al () na
keeps-abstract (instr-alloc-stack n)  ls al () na
keeps-abstract (instr-dealloc-stack n) ls al () na
keeps-abstract (instr-free-heap n)    ls al () na
keeps-abstract (instr-room n)         ls al e na = same {al = al} refl
keeps-abstract (instr-push-frame c)   ls al () na
keeps-abstract instr-pop-frame        ls al () na
keeps-abstract (instr-loop b)         ls al () na
keeps-abstract (instr-case-on-tag f g) ls al () na

------------------------------------------------------------------------
-- Lifted to the flat machine: the control steps move the pc, the frames and
-- the halt flag only; the frame moves keep the counter and sizes
-- (`leave-frame-heap-ref`, `leave-frame-block-size`, and the record updates
-- of `grow-frame`/`enter-call`).
------------------------------------------------------------------------
private
  k-jump : ∀ (mpc : Maybe ℕ) (fs : FlatState) → Keeps fs (do-jump mpc fs)
  k-jump (just pc') fs = refl , (λ _ → refl) , grows-eq {floc fs} refl
  k-jump nothing    fs = refl , (λ _ → refl) , grows-eq {floc fs} refl

  k-branch : ∀ (b : Bool) (mj : Maybe ℕ) (fs : FlatState) → Keeps fs (do-branch-at b mj fs)
  k-branch true  mj fs = k-jump mj fs
  k-branch false mj fs = refl , (λ _ → refl) , grows-eq {floc fs} refl

  k-call-at : ∀ (mj : Maybe ℕ) (fs : FlatState) → Keeps fs (do-call-at mj fs)
  k-call-at (just j) fs = refl , (λ _ → refl) , grows-eq {floc fs} refl
  k-call-at nothing  fs = refl , (λ _ → refl) , grows-eq {floc fs} refl

  k-ret : ∀ (r : List ℕ) (fs : FlatState) → Keeps fs (do-ret r fs)
  k-ret []           fs = leave-frame-heap-ref (falloc fs)
                        , (λ r → cong (λ b → b r) (leave-frame-block-size (falloc fs)))
                        , grows-eq {floc fs} refl
  k-ret (pc' ∷ rest) fs = leave-frame-heap-ref (falloc fs)
                        , (λ r → cong (λ b → b r) (leave-frame-block-size (falloc fs)))
                        , grows-eq {floc fs} refl

  k-call : ∀ (prog : AbstractTrace) (fs : FlatState) → Keeps fs (do-call prog fs)
  k-call prog fs = go (callView prog fs)
    where go : CallPost prog fs → Keeps fs (do-call prog fs)
          go (cp-halt e)         rewrite e = refl , (λ _ → refl) , grows-eq {floc fs} refl
          go (cp-enter ℓ j fq e) rewrite e = refl , (λ _ → refl) , grows-eq {floc fs} refl

keeps-flat : ∀ (i : AbstractInstr) (prog : AbstractTrace) (fs : FlatState)
           → ImageI i → (∀ n → ¬ (i ≡ instr-alloc-heap n))
           → Keeps fs (flat-exec-instr i prog fs)
keeps-flat (instr-ctrl (c-label m))               prog fs ff na = refl , (λ _ → refl) , grows-eq {floc fs} refl
keeps-flat (instr-ctrl (c-entry m b))             prog fs ff na = refl , (λ _ → refl) , grows-eq {floc fs} refl
keeps-flat (instr-ctrl (c-start b))               prog fs ff na = refl , (λ _ → refl) , grows-eq {floc fs} refl
keeps-flat (instr-ctrl c-leave)                   prog fs ff na = refl , (λ _ → refl) , grows-eq {floc fs} refl
keeps-flat (instr-ctrl (c-call-fn f))             prog fs ff na = k-call-at (find-fn prog f) fs
keeps-flat (instr-ctrl (c-ret b))                 prog fs ff na = k-ret (fret fs) fs
keeps-flat (instr-ctrl (c-jmp m))                 prog fs ff na = k-jump (find-label prog m) fs
keeps-flat (instr-ctrl (c-branch-scratch-zero m)) prog fs ff na =
  k-branch (sv-is-zero (readReg (LocState.regs (floc fs)) Scratch)) (find-label prog m) fs
keeps-flat (instr-ctrl (c-branch-tag-zero m))     prog fs ff na =
  k-branch (tag-zf (flat-read-tag (floc fs))) (find-label prog m) fs
keeps-flat instr-call-closure       prog fs ff na = k-call prog fs
keeps-flat instr-save-closure-reg   prog fs ff na = refl , (λ _ → refl) , grows-eq {floc fs} refl
keeps-flat (instr-alloc-stack n)    prog fs () na
keeps-flat (instr-dealloc-stack n)  prog fs () na
keeps-flat (instr-push-frame cap)   prog fs () na
keeps-flat instr-pop-frame          prog fs () na
keeps-flat mov-to-output            prog fs ff na = keeps-abstract mov-to-output (floc fs) (falloc fs) ff na
keeps-flat mov-to-input             prog fs ff na = keeps-abstract mov-to-input (floc fs) (falloc fs) ff na
keeps-flat load-indirect            prog fs ff na = keeps-abstract load-indirect (floc fs) (falloc fs) ff na
keeps-flat load-indirect-suc        prog fs ff na = keeps-abstract load-indirect-suc (floc fs) (falloc fs) ff na
keeps-flat (load-from-slot k)       prog fs ff na = keeps-abstract (load-from-slot k) (floc fs) (falloc fs) ff na
keeps-flat (store-at-slot k)        prog fs ff na = keeps-abstract (store-at-slot k) (floc fs) (falloc fs) ff na
keeps-flat store-indirect           prog fs ff na = keeps-abstract store-indirect (floc fs) (falloc fs) ff na
keeps-flat store-indirect-suc       prog fs ff na = keeps-abstract store-indirect-suc (floc fs) (falloc fs) ff na
keeps-flat (lea-slot k)             prog fs ff na = keeps-abstract (lea-slot k) (floc fs) (falloc fs) ff na
keeps-flat (restore-input k)        prog fs ff na = keeps-abstract (restore-input k) (floc fs) (falloc fs) ff na
keeps-flat (lea-indexed k)          prog fs ff na = keeps-abstract (lea-indexed k) (floc fs) (falloc fs) ff na
keeps-flat (instr-free-heap n)      prog fs ff na = keeps-abstract (instr-free-heap n) (floc fs) (falloc fs) ff na
keeps-flat (instr-room n)           prog fs ff na = keeps-abstract (instr-room n) (floc fs) (falloc fs) ff na
keeps-flat (instr-loop b)           prog fs ff na = keeps-abstract (instr-loop b) (floc fs) (falloc fs) ff na
keeps-flat (instr-case-on-tag f g)  prog fs ff na = keeps-abstract (instr-case-on-tag f g) (floc fs) (falloc fs) ff na
keeps-flat (instr-reclaim-to k)     prog fs ff na = keeps-abstract (instr-reclaim-to k) (floc fs) (falloc fs) ff na
keeps-flat (worklist-init k)        prog fs ff na = keeps-abstract (worklist-init k) (floc fs) (falloc fs) ff na
keeps-flat (worklist-push k)        prog fs ff na = keeps-abstract (worklist-push k) (floc fs) (falloc fs) ff na
keeps-flat (worklist-pop k)         prog fs ff na = keeps-abstract (worklist-pop k) (floc fs) (falloc fs) ff na
keeps-flat (worklist-check k)       prog fs ff na = keeps-abstract (worklist-check k) (floc fs) (falloc fs) ff na
keeps-flat (instr-sigop si)         prog fs ff na = keeps-abstract (instr-sigop si) (floc fs) (falloc fs) ff na
keeps-flat (instr-load-const p v)   prog fs ff na = keeps-abstract (instr-load-const p v) (floc fs) (falloc fs) ff na
keeps-flat (instr-load-code-addr k) prog fs ff na = keeps-abstract (instr-load-code-addr k) (floc fs) (falloc fs) ff na
keeps-flat (instr-load-tag-lit k)   prog fs ff na = keeps-abstract (instr-load-tag-lit k) (floc fs) (falloc fs) ff na
keeps-flat (instr-alloc-heap k)     prog fs ff na = ⊥-elim (na k refl)
keeps-flat (instr-reg-op op)        prog fs ff na = keeps-abstract (instr-reg-op op) (floc fs) (falloc fs) ff na

------------------------------------------------------------------------
-- Part B: THE OPEN WINDOW. Between an allocation and the second write of its
-- block `blk` (the newest), every older block is full; the window's static
-- record (`Codegen.InitWindow.Win`) says where `blk`'s pointer may be —
-- `Output` (`o`), `Input1` (`i`), the stash slot (`p`) — and which cells are
-- written (`w0`, `w1`); no other place holds a pointer into `blk`.
------------------------------------------------------------------------
Written : LocState FS → HeapLocation → Set
Written ls hl = Σ (StoredValue FS) (λ w → heapMem ls hl ≡ just w)

fresh : ℕ → StoredValue FS
fresh b = SV-Ptr (AtDynamic (heap-loc (mkHeapRef b) 0))

-- a value that is no pointer into block `b`
Avoids : ℕ → StoredValue FS → Set
Avoids b (SV-Ptr (AtDynamic hl)) = ¬ (ref-id (heap-ref hl) ≡ b)
Avoids b (SV-Ptr (AtStack _ _))  = ⊤
Avoids b (SV-Tag _)              = ⊤
Avoids b (SV-Lit _ _)            = ⊤
Avoids b (SV-Code _)             = ⊤

Avoids? : ℕ → Maybe (StoredValue FS) → Set
Avoids? b (just v) = Avoids b v
Avoids? b nothing  = ⊤

-- a register the window tracks: exactly the fresh pointer, or none into `b`
Holds : Bool → ℕ → StoredValue FS → Set
Holds true  b v = v ≡ fresh b
Holds false b v = Avoids b v

-- the stash slot, in the current frame
IsStash : Maybe ℕ → Frame → Frame → Slot → Set
IsStash nothing  cf f k = ⊥
IsStash (just q) cf f k = (f ≡ cf) × (k ≡ q)

StashHolds : Maybe ℕ → ℕ → StackMem FS → Frame → Set
StashHolds nothing  b sm cf = ⊤
StashHolds (just q) b sm cf = sm cf q ≡ just (fresh b)

record Open (o i : Bool) (p : Maybe ℕ) (w0 w1 : Bool) (fs : FlatState) : Set where
  field
    blk    : ℕ
    nx     : next-heap-ref (falloc fs) ≡ suc blk
    sz     : block-size (falloc fs) blk ≡ 2
    older  : ∀ (hl : HeapLocation) → ref-id (heap-ref hl) < blk
           → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl)) → Written (floc fs) hl
    cell0  : w0 ≡ true → Written (floc fs) (heap-loc (mkHeapRef blk) 0)
    cell1  : w1 ≡ true → Written (floc fs) (heap-loc (mkHeapRef blk) 1)
    out    : Holds o blk (readReg (regs (floc fs)) Output)
    in1    : Holds i blk (readReg (regs (floc fs)) Input1)
    scr    : Avoids blk (readReg (regs (floc fs)) Scratch)
    cnt    : Avoids blk (readReg (regs (floc fs)) Count)
    clos   : Avoids blk (fclosure fs)
    heap   : ∀ (hl : HeapLocation) → Avoids? blk (heapMem (floc fs) hl)
    stash  : StashHolds p blk (stackMem (floc fs)) (current-frame (falloc fs))
    stack  : ∀ (f : Frame) (k : Slot) → ¬ IsStash p (current-frame (falloc fs)) f k
           → Avoids? blk (stackMem (floc fs) f k)
open Open

-- both cells written: the window closes, and the state is full
private
  cell-of : ∀ (hl : HeapLocation) {b : ℕ} {ls : LocState FS}
          → ref-id (heap-ref hl) ≡ b → heap-offset hl < 2
          → Written ls (heap-loc (mkHeapRef b) 0) → Written ls (heap-loc (mkHeapRef b) 1)
          → Written ls hl
  cell-of (heap-loc (mkHeapRef r) zero)          refl _ c0 c1 = c0
  cell-of (heap-loc (mkHeapRef r) (suc zero))    refl _ c0 c1 = c1
  cell-of (heap-loc (mkHeapRef r) (suc (suc k))) refl (s≤s (s≤s ())) c0 c1

close-done : ∀ {o i p} {fs : FlatState} → Open o i p true true fs → Full (falloc fs) (floc fs)
close-done {fs = fs} op hl lt ib
  with m<1+n⇒m<n∨m≡n (subst (ref-id (heap-ref hl) <_) (nx op) lt)
... | inj₁ r<b = older op hl r<b ib
... | inj₂ r≡b = cell-of hl {ls = floc fs} r≡b
                   (subst (heap-offset hl <_) (trans (cong (block-size (falloc fs)) r≡b) (sz op)) ib)
                   (cell0 op refl) (cell1 op refl)

------------------------------------------------------------------------
-- An allocation from a full state OPENS the window: the fresh block is the
-- newest, its pointer is in `Output` only (`StoreWF`: every value points
-- below the counter, so none points at the new block), nothing is written.
------------------------------------------------------------------------
below-avoids : ∀ {n : ℕ} (v : StoredValue FS) → sv-below n v → Avoids n v
below-avoids (SV-Ptr (AtDynamic hl)) lt = <⇒≢ lt
below-avoids (SV-Ptr (AtStack _ _))  _  = tt
below-avoids (SV-Tag _)              _  = tt
below-avoids (SV-Lit _ _)            _  = tt
below-avoids (SV-Code _)             _  = tt

belowm-avoids : ∀ {n : ℕ} (mv : Maybe (StoredValue FS)) → svm-below n mv → Avoids? n mv
belowm-avoids (just v) b = below-avoids v b
belowm-avoids nothing  _ = tt

open-alloc : ∀ (prog : AbstractTrace) (fs : FlatState)
           → Full (falloc fs) (floc fs)
           → StoreWF (next-heap-ref (falloc fs)) (floc fs)
           → sv-below (next-heap-ref (falloc fs)) (fclosure fs)
           → Open true false nothing false false (flat-exec-instr (instr-alloc-heap 2) prog fs)
open-alloc prog fs full wf cl = record
  { blk   = st
  ; nx    = refl
  ; sz    = size-with-new 2 st bs
  ; older = λ hl lt ib → full hl lt
              (subst (heap-offset hl <_) (size-with-old 2 st bs (ref-id (heap-ref hl)) (<⇒≢ lt)) ib)
  ; cell0 = λ ()
  ; cell1 = λ ()
  ; out   = refl
  ; in1   = below-avoids _ (wf-regs wf Input1)
  ; scr   = below-avoids _ (wf-regs wf Scratch)
  ; cnt   = below-avoids _ (wf-regs wf Count)
  ; clos  = below-avoids _ cl
  ; heap  = λ hl → belowm-avoids (heapMem (floc fs) hl) (wf-heap wf hl)
  ; stash = tt
  ; stack = λ f k _ → belowm-avoids (stackMem (floc fs) f k) (wf-stack wf f k)
  }
  where st = next-heap-ref (falloc fs)
        bs = block-size (falloc fs)

------------------------------------------------------------------------
-- The window's steps. Each changes one register, one stack slot or one heap
-- cell (or halts); one helper per kind of change carries every other field.
------------------------------------------------------------------------
Halted : FlatState → Set
Halted fs = LocState.halted (floc fs) ≡ true

set-out : ∀ {o i p w0 w1} (fs : FlatState) (op : Open o i p w0 w1 fs) (v : StoredValue FS) (o' : Bool)
        → Holds o' (blk op) v
        → Open o' i p w0 w1 (record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v }
                                     ; fpc = suc (fpc fs) })
set-out fs op v o' h = record
  { blk = blk op ; nx = nx op ; sz = sz op ; older = older op ; cell0 = cell0 op ; cell1 = cell1 op
  ; out = h ; in1 = in1 op ; scr = scr op ; cnt = cnt op ; clos = clos op ; heap = heap op
  ; stash = stash op ; stack = stack op }

set-in1 : ∀ {o i p w0 w1} (fs : FlatState) (op : Open o i p w0 w1 fs) (v : StoredValue FS) (i' : Bool)
        → Holds i' (blk op) v
        → Open o i' p w0 w1 (record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Input1 v }
                                     ; fpc = suc (fpc fs) })
set-in1 fs op v i' h = record
  { blk = blk op ; nx = nx op ; sz = sz op ; older = older op ; cell0 = cell0 op ; cell1 = cell1 op
  ; out = out op ; in1 = h ; scr = scr op ; cnt = cnt op ; clos = clos op ; heap = heap op
  ; stash = stash op ; stack = stack op }

-- a value a tracked register held is avoided, if the register is not tracked
holds-false : ∀ {b} {v : StoredValue FS} → Holds false b v → Avoids b v
holds-false h = h

private
  apart→nis : ∀ {p : Maybe ℕ} {cf : Frame} {s : Slot} → Apart s p → ¬ IsStash p cf cf s
  apart→nis {nothing} _  ()
  apart→nis {just q}  ne (_ , eq) = ne eq

-- Output := a literal / a code address: no pointer
step-tag : ∀ {o i p w0 w1} prog fs n → (op : Open o i p w0 w1 fs)
         → Open false i p w0 w1 (flat-exec-instr (instr-load-tag-lit n) prog fs)
step-tag prog fs n op = set-out fs op (SV-Tag n) false tt

step-code : ∀ {o i p w0 w1} prog fs l → (op : Open o i p w0 w1 fs)
          → Open false i p w0 w1 (flat-exec-instr (instr-load-code-addr l) prog fs)
step-code prog fs l op = set-out fs op (SV-Code l) false tt

-- Input1 := Output: it holds what Output held
step-mov-in : ∀ {o i p w0 w1} prog fs → (op : Open o i p w0 w1 fs)
            → Open o o p w0 w1 (flat-exec-instr mov-to-input prog fs)
step-mov-in prog fs op = set-in1 fs op (readReg (regs (floc fs)) Output) _ (out op)

-- Output := the stash: the fresh pointer
-- the two slot reads, as functions of the value read
LFS : FlatState → Maybe (StoredValue FS) → FlatState
LFS fs mv = record fs { floc   = proj₁ (exec-load-from-slot-with-value mv (floc fs) (falloc fs))
                      ; falloc = proj₂ (exec-load-from-slot-with-value mv (floc fs) (falloc fs))
                      ; fpc    = suc (fpc fs) }

RIS : FlatState → Maybe (StoredValue FS) → FlatState
RIS fs mv = record fs { floc   = proj₁ (exec-restore-input-with-value mv (floc fs) (falloc fs))
                      ; falloc = proj₂ (exec-restore-input-with-value mv (floc fs) (falloc fs))
                      ; fpc    = suc (fpc fs) }

lfs-eq : ∀ prog fs s → flat-exec-instr (load-from-slot s) prog fs
                     ≡ LFS fs (stackMem (floc fs) (current-frame (falloc fs)) s)
lfs-eq prog fs s = refl

ris-eq : ∀ prog fs s → flat-exec-instr (restore-input s) prog fs
                     ≡ RIS fs (stackMem (floc fs) (current-frame (falloc fs)) s)
ris-eq prog fs s = refl

-- Output := the stash: the fresh pointer
step-load-stash : ∀ {o i s w0 w1} prog fs → (op : Open o i (just s) w0 w1 fs)
                → Open true i (just s) w0 w1 (flat-exec-instr (load-from-slot s) prog fs)
step-load-stash {o} {i} {s} {w0} {w1} prog fs op =
  subst (Open true i (just s) w0 w1) (sym (trans (lfs-eq prog fs s) (cong (LFS fs) (stash op))))
        (set-out fs op (fresh (blk op)) true refl)

-- Output := another slot: no pointer into the block (or the run halts)
step-load-slot : ∀ {o i p w0 w1} prog fs s → (op : Open o i p w0 w1 fs) → Apart s p
               → Halted (flat-exec-instr (load-from-slot s) prog fs)
                 ⊎ Open false i p w0 w1 (flat-exec-instr (load-from-slot s) prog fs)
step-load-slot {o} {i} {p} {w0} {w1} prog fs s op ap = go (stackMem (floc fs) cf s) refl
  where
    cf = current-frame (falloc fs)
    go : ∀ mv → stackMem (floc fs) cf s ≡ mv
       → Halted (flat-exec-instr (load-from-slot s) prog fs)
         ⊎ Open false i p w0 w1 (flat-exec-instr (load-from-slot s) prog fs)
    go (just v) e = inj₂ (subst (Open false i p w0 w1) (sym (trans (lfs-eq prog fs s) (cong (LFS fs) e)))
                              (set-out fs op v false (subst (Avoids? (blk op)) e (stack op cf s (apart→nis ap)))))
    go nothing  e = inj₁ (subst Halted (sym (trans (lfs-eq prog fs s) (cong (LFS fs) e))) refl)

step-restore-stash : ∀ {o i s w0 w1} prog fs → (op : Open o i (just s) w0 w1 fs)
                   → Open o true (just s) w0 w1 (flat-exec-instr (restore-input s) prog fs)
step-restore-stash {o} {i} {s} {w0} {w1} prog fs op =
  subst (Open o true (just s) w0 w1) (sym (trans (ris-eq prog fs s) (cong (RIS fs) (stash op))))
        (set-in1 fs op (fresh (blk op)) true refl)

step-restore-slot : ∀ {o i p w0 w1} prog fs s → (op : Open o i p w0 w1 fs) → Apart s p
                  → Halted (flat-exec-instr (restore-input s) prog fs)
                    ⊎ Open o false p w0 w1 (flat-exec-instr (restore-input s) prog fs)
step-restore-slot {o} {i} {p} {w0} {w1} prog fs s op ap = go (stackMem (floc fs) cf s) refl
  where
    cf = current-frame (falloc fs)
    go : ∀ mv → stackMem (floc fs) cf s ≡ mv
       → Halted (flat-exec-instr (restore-input s) prog fs)
         ⊎ Open o false p w0 w1 (flat-exec-instr (restore-input s) prog fs)
    go (just v) e = inj₂ (subst (Open o false p w0 w1) (sym (trans (ris-eq prog fs s) (cong (RIS fs) e)))
                              (set-in1 fs op v false (subst (Avoids? (blk op)) e (stack op cf s (apart→nis ap)))))
    go nothing  e = inj₁ (subst Halted (sym (trans (ris-eq prog fs s) (cong (RIS fs) e))) refl)

------------------------------------------------------------------------
-- The slot stores: into the stash (the fresh pointer is parked) or into
-- another slot (no pointer into the block is stored).
------------------------------------------------------------------------
wsm-read : ∀ (m : StackMem FS) (f : Frame) (k : Slot) (v : StoredValue FS) (f' : Frame) (k' : Slot)
         → ((f ≡ f') × (k ≡ k') × (writeStackMem m f k v f' k' ≡ just v))
           ⊎ (¬ ((f ≡ f') × (k ≡ k')) × (writeStackMem m f k v f' k' ≡ m f' k'))
wsm-read m f k v f' k' with f ≟F f' | k ≟ k'
... | yes ef | yes ek = inj₁ (ef , ek , refl)
... | yes ef | no nk  = inj₂ ((λ { (_ , ek) → nk ek }) , refl)
... | no nf  | _      = inj₂ ((λ { (ef , _) → nf ef }) , refl)

set-stack : ∀ {o i p w0 w1} (p' : Maybe ℕ) (fs : FlatState) (op : Open o i p w0 w1 fs) (sm : StackMem FS)
          → StashHolds p' (blk op) sm (current-frame (falloc fs))
          → (∀ f k → ¬ IsStash p' (current-frame (falloc fs)) f k → Avoids? (blk op) (sm f k))
          → Open o i p' w0 w1 (record fs { floc = record (floc fs) { stackMem = sm } ; fpc = suc (fpc fs) })
set-stack p' fs op sm sh st = record
  { blk = blk op ; nx = nx op ; sz = sz op ; older = older op ; cell0 = cell0 op ; cell1 = cell1 op
  ; out = out op ; in1 = in1 op ; scr = scr op ; cnt = cnt op ; clos = clos op ; heap = heap op
  ; stash = sh ; stack = st }

sas-eq : ∀ prog fs s → flat-exec-instr (store-at-slot s) prog fs
                     ≡ record fs { floc = record (floc fs)
                                     { stackMem = writeStackMem (stackMem (floc fs)) (current-frame (falloc fs)) s
                                                    (readReg (regs (floc fs)) Output) }
                                 ; fpc = suc (fpc fs) }
sas-eq prog fs s = refl

-- stash the fresh pointer (it is in Output, and no slot held it yet)
step-stash : ∀ {i w0 w1} prog fs s → (op : Open true i nothing w0 w1 fs)
           → Open true i (just s) w0 w1 (flat-exec-instr (store-at-slot s) prog fs)
step-stash {i} {w0} {w1} prog fs s op =
  subst (Open true i (just s) w0 w1) (sym (sas-eq prog fs s))
        (set-stack (just s) fs op sm sh st)
  where
    cf = current-frame (falloc fs)
    v  = readReg (regs (floc fs)) Output
    sm = writeStackMem (stackMem (floc fs)) cf s v
    sh : sm cf s ≡ just (fresh (blk op))
    sh with wsm-read (stackMem (floc fs)) cf s v cf s
    ... | inj₁ (_ , _ , e) = trans e (cong just (out op))
    ... | inj₂ (ne , _)    = ⊥-elim (ne (refl , refl))
    st : ∀ f k → ¬ IsStash (just s) cf f k → Avoids? (blk op) (sm f k)
    st f k nis with wsm-read (stackMem (floc fs)) cf s v f k
    ... | inj₁ (ef , ek , _) = ⊥-elim (nis (sym ef , sym ek))
    ... | inj₂ (_ , e)       = subst (Avoids? (blk op)) (sym e) (stack op f k (λ ()))

-- any other slot store stores no pointer into the block, and spares the stash
step-store-slot : ∀ {i p w0 w1} prog fs s → (op : Open false i p w0 w1 fs) → Apart s p
                → Open false i p w0 w1 (flat-exec-instr (store-at-slot s) prog fs)
step-store-slot {i} {p} {w0} {w1} prog fs s op ap =
  subst (Open false i p w0 w1) (sym (sas-eq prog fs s))
        (set-stack p fs op sm (sh p ap (stash op)) st)
  where
    cf = current-frame (falloc fs)
    v  = readReg (regs (floc fs)) Output
    sm = writeStackMem (stackMem (floc fs)) cf s v
    sh : ∀ (p₀ : Maybe ℕ) → Apart s p₀ → StashHolds p₀ (blk op) (stackMem (floc fs)) cf
       → StashHolds p₀ (blk op) sm cf
    sh nothing  _  _ = tt
    sh (just q) ne h with wsm-read (stackMem (floc fs)) cf s v cf q
    ... | inj₁ (_ , ek , _) = ⊥-elim (ne ek)
    ... | inj₂ (_ , e)      = trans e h
    st : ∀ f k → ¬ IsStash p cf f k → Avoids? (blk op) (sm f k)
    st f k nis with wsm-read (stackMem (floc fs)) cf s v f k
    ... | inj₁ (_ , _ , e) = subst (Avoids? (blk op)) (sym e) (out op)
    ... | inj₂ (_ , e)     = subst (Avoids? (blk op)) (sym e) (stack op f k nis)

------------------------------------------------------------------------
-- The heap loads through Input1 (no stack pointer exists: `StackPtrWF`).
-- The value loaded is a heap cell's, so it points nowhere into the block.
------------------------------------------------------------------------
LV : FlatState → Maybe (StoredValue FS) → FlatState
LV fs mv = record fs { floc = exec-load-with-value Output mv (floc fs) ; fpc = suc (fpc fs) }

LI : FlatState → StoredValue FS → FlatState
LI fs v = record fs { floc = exec-load-via-resolved Output (sv-as-loc v) (floc fs) ; fpc = suc (fpc fs) }

LIS : FlatState → StoredValue FS → FlatState
LIS fs v = record fs { floc = exec-load-suc-via-resolved Output (sv-as-loc v) (floc fs) ; fpc = suc (fpc fs) }

li-eq : ∀ prog fs → flat-exec-instr load-indirect prog fs ≡ LI fs (readReg (regs (floc fs)) Input1)
li-eq prog fs = refl

lis-eq : ∀ prog fs → flat-exec-instr load-indirect-suc prog fs ≡ LIS fs (readReg (regs (floc fs)) Input1)
lis-eq prog fs = refl

-- the cell a load reads: the value, or a halt
private
  load-cell : ∀ {o i p w0 w1} (fs : FlatState) (op : Open o i p w0 w1 fs) (hl : HeapLocation)
            → ∀ mv → heapMem (floc fs) hl ≡ mv
            → Halted (LV fs mv) ⊎ Open false i p w0 w1 (LV fs mv)
  load-cell fs op hl (just v) e = inj₂ (set-out fs op v false (subst (Avoids? (blk op)) e (heap op hl)))
  load-cell fs op hl nothing  e = inj₁ refl

step-load : ∀ {o p w0 w1} prog fs → (op : Open o false p w0 w1 fs) → SPInv (floc fs)
          → Halted (flat-exec-instr load-indirect prog fs)
            ⊎ Open false false p w0 w1 (flat-exec-instr load-indirect prog fs)
step-load {o} {p} {w0} {w1} prog fs op sp =
  go (readReg (regs (floc fs)) Input1) refl (sp-regs sp Input1)
  where
    R = λ (x : FlatState) → Halted x ⊎ Open false false p w0 w1 x
    go : ∀ v → readReg (regs (floc fs)) Input1 ≡ v → StackPtrOK v → R (flat-exec-instr load-indirect prog fs)
    go (SV-Ptr (AtDynamic hl)) e _ =
      subst R (sym (trans (li-eq prog fs) (cong (LI fs) e)))
        (load-cell fs op hl (heapMem (floc fs) hl) refl)
    go (SV-Ptr (AtStack f k)) e ()
    go (SV-Tag t)   e _ = inj₁ (subst Halted (sym (trans (li-eq prog fs) (cong (LI fs) e))) refl)
    go (SV-Lit q x) e _ = inj₁ (subst Halted (sym (trans (li-eq prog fs) (cong (LI fs) e))) refl)
    go (SV-Code c)  e _ = inj₁ (subst Halted (sym (trans (li-eq prog fs) (cong (LI fs) e))) refl)

step-load-suc : ∀ {o p w0 w1} prog fs → (op : Open o false p w0 w1 fs) → SPInv (floc fs)
              → Halted (flat-exec-instr load-indirect-suc prog fs)
                ⊎ Open false false p w0 w1 (flat-exec-instr load-indirect-suc prog fs)
step-load-suc {o} {p} {w0} {w1} prog fs op sp =
  go (readReg (regs (floc fs)) Input1) refl (sp-regs sp Input1)
  where
    R = λ (x : FlatState) → Halted x ⊎ Open false false p w0 w1 x
    go : ∀ v → readReg (regs (floc fs)) Input1 ≡ v → StackPtrOK v → R (flat-exec-instr load-indirect-suc prog fs)
    go (SV-Ptr (AtDynamic hl)) e _ =
      subst R (sym (trans (lis-eq prog fs) (cong (LIS fs) e)))
        (load-cell fs op (sucHL hl) (heapMem (floc fs) (sucHL hl)) refl)
    go (SV-Ptr (AtStack f k)) e ()
    go (SV-Tag t)   e _ = inj₁ (subst Halted (sym (trans (lis-eq prog fs) (cong (LIS fs) e))) refl)
    go (SV-Lit q x) e _ = inj₁ (subst Halted (sym (trans (lis-eq prog fs) (cong (LIS fs) e))) refl)
    go (SV-Code c)  e _ = inj₁ (subst Halted (sym (trans (lis-eq prog fs) (cong (LIS fs) e))) refl)

------------------------------------------------------------------------
-- The heap stores through Input1: through the fresh pointer they write the
-- block's cell (0, or 1 for the `-suc` form); otherwise an older block's.
-- Either way the value stored is no pointer into the block (`o` is false).
------------------------------------------------------------------------
wl-dyn : ∀ (ls : LocState FS) (hl : HeapLocation) (w : StoredValue FS)
       → writeLoc ls (AtDynamic hl) w ≡ record ls { heapMem = writeHeapMem (heapMem ls) hl w }
wl-dyn ls hl (SV-Ptr (AtStack f k))  = refl
wl-dyn ls hl (SV-Ptr (AtDynamic x))  = refl
wl-dyn ls hl (SV-Tag t)              = refl
wl-dyn ls hl (SV-Lit p x)            = refl
wl-dyn ls hl (SV-Code c)             = refl

private
  HW : FlatState → HeapLocation → StoredValue FS → FlatState
  HW fs hl w = record fs { floc = record (floc fs) { heapMem = writeHeapMem (heapMem (floc fs)) hl w }
                         ; fpc = suc (fpc fs) }

  written-grows : ∀ (ls : LocState FS) (hl : HeapLocation) (w : StoredValue FS) (hl' : HeapLocation)
                → Written ls hl' → Σ (StoredValue FS) (λ w' → writeHeapMem (heapMem ls) hl w hl' ≡ just w')
  written-grows ls hl w hl' (w₀ , e) = writeHeapMem-grows (heapMem ls) hl w hl' w₀ e

  written-here : ∀ (m : HeapMem FS) (hl : HeapLocation) (w : StoredValue FS)
               → Σ (StoredValue FS) (λ w' → writeHeapMem m hl w hl ≡ just w')
  written-here m hl w with hl ≟HL hl
  ... | yes _ = w , refl
  ... | no ne = ⊥-elim (ne refl)

  avoid-write : ∀ {b} (m : HeapMem FS) (hl : HeapLocation) (w : StoredValue FS)
              → Avoids b w → (∀ hl' → Avoids? b (m hl')) → ∀ hl' → Avoids? b (writeHeapMem m hl w hl')
  avoid-write m hl w aw am hl' with hl ≟HL hl'
  ... | yes _ = aw
  ... | no  _ = am hl'

  -- the open window after writing `w` at `hl`, given which cells it has written
  heap-write : ∀ {o i p w0 w1} (w0' w1' : Bool) (fs : FlatState) (op : Open o i p w0 w1 fs)
             → (hl : HeapLocation) (w : StoredValue FS) → Avoids (blk op) w
             → (w0' ≡ true → Written (record (floc fs) { heapMem = writeHeapMem (heapMem (floc fs)) hl w })
                                     (heap-loc (mkHeapRef (blk op)) 0))
             → (w1' ≡ true → Written (record (floc fs) { heapMem = writeHeapMem (heapMem (floc fs)) hl w })
                                     (heap-loc (mkHeapRef (blk op)) 1))
             → Open o i p w0' w1' (HW fs hl w)
  heap-write w0' w1' fs op hl w aw c0 c1 = record
    { blk = blk op ; nx = nx op ; sz = sz op
    ; older = λ hl' lt ib → written-grows (floc fs) hl w hl' (older op hl' lt ib)
    ; cell0 = c0 ; cell1 = c1
    ; out = out op ; in1 = in1 op ; scr = scr op ; cnt = cnt op ; clos = clos op
    ; heap = avoid-write (heapMem (floc fs)) hl w aw (heap op)
    ; stash = stash op ; stack = stack op }

ST : FlatState → StoredValue FS → FlatState
ST fs v = record fs { floc = exec-store-via-resolved (sv-as-loc v) (readReg (regs (floc fs)) Output) (floc fs)
                    ; fpc = suc (fpc fs) }

STS : FlatState → StoredValue FS → FlatState
STS fs v = record fs { floc = exec-store-suc-via-resolved (sv-as-loc v) (readReg (regs (floc fs)) Output) (floc fs)
                     ; fpc = suc (fpc fs) }

st-eq : ∀ prog fs → flat-exec-instr store-indirect prog fs ≡ ST fs (readReg (regs (floc fs)) Input1)
st-eq prog fs = refl

sts-eq : ∀ prog fs → flat-exec-instr store-indirect-suc prog fs ≡ STS fs (readReg (regs (floc fs)) Input1)
sts-eq prog fs = refl

private
  ptr-inj : ∀ {a b : HeapLocation} → SV-Ptr {FS} (AtDynamic a) ≡ SV-Ptr (AtDynamic b) → a ≡ b
  ptr-inj refl = refl

  -- the post-state of a heap write, in the form `heap-write` produces
  to-HW : ∀ (fs : FlatState) (hl : HeapLocation) (w : StoredValue FS)
        → record fs { floc = writeLoc (floc fs) (AtDynamic hl) w ; fpc = suc (fpc fs) } ≡ HW fs hl w
  to-HW fs hl w = cong (λ l → record fs { floc = l ; fpc = suc (fpc fs) }) (wl-dyn (floc fs) hl w)

-- through the fresh pointer the write is the block's cell `c`; otherwise an older block's
private
  store-here0 : ∀ {p w0 w1} (i : Bool) (fs : FlatState) (op : Open false i p w0 w1 fs) (hl : HeapLocation)
              → Holds i (blk op) (SV-Ptr (AtDynamic hl))
              → Open false i p (i ∨ w0) w1 (HW fs hl (readReg (regs (floc fs)) Output))
  store-here0 {p} {w0} {w1} true fs op hl h = heap-write true w1 fs op hl Ov (out op)
    (λ _ → subst (Written (record (floc fs) { heapMem = writeHeapMem (heapMem (floc fs)) hl Ov })) (ptr-inj h)
                 (written-here (heapMem (floc fs)) hl Ov))
    (λ t → written-grows (floc fs) hl Ov _ (cell1 op t))
    where Ov = readReg (regs (floc fs)) Output
  store-here0 {p} {w0} {w1} false fs op hl h = heap-write w0 w1 fs op hl Ov (out op)
    (λ t → written-grows (floc fs) hl Ov _ (cell0 op t))
    (λ t → written-grows (floc fs) hl Ov _ (cell1 op t))
    where Ov = readReg (regs (floc fs)) Output

-- `w0` records a write through the fresh pointer: `i ∨ w0`
step-store : ∀ {i p w0 w1} prog fs → (op : Open false i p w0 w1 fs) → SPInv (floc fs)
           → Halted (flat-exec-instr store-indirect prog fs)
             ⊎ Open false i p (i ∨ w0) w1 (flat-exec-instr store-indirect prog fs)
step-store {i} {p} {w0} {w1} prog fs op sp = go (readReg (regs (floc fs)) Input1) refl (sp-regs sp Input1)
  where
    Ov = readReg (regs (floc fs)) Output
    R = λ (x : FlatState) → Halted x ⊎ Open false i p (i ∨ w0) w1 x
    post : ∀ v → readReg (regs (floc fs)) Input1 ≡ v → flat-exec-instr store-indirect prog fs ≡ ST fs v
    post v e = trans (st-eq prog fs) (cong (ST fs) e)
    go : ∀ v → readReg (regs (floc fs)) Input1 ≡ v → StackPtrOK v → R (flat-exec-instr store-indirect prog fs)
    go (SV-Ptr (AtDynamic hl)) e _ =
      inj₂ (subst (Open false i p (i ∨ w0) w1) (sym (trans (post _ e) (to-HW fs hl Ov)))
                  (store-here0 i fs op hl (subst (Holds i (blk op)) e (in1 op))))
    go (SV-Ptr (AtStack f k)) e ()
    go (SV-Tag t)   e _ = inj₁ (subst Halted (sym (post _ e)) refl)
    go (SV-Lit q x) e _ = inj₁ (subst Halted (sym (post _ e)) refl)
    go (SV-Code c)  e _ = inj₁ (subst Halted (sym (post _ e)) refl)

private
  store-here1 : ∀ {p w0 w1} (i : Bool) (fs : FlatState) (op : Open false i p w0 w1 fs) (hl : HeapLocation)
              → Holds i (blk op) (SV-Ptr (AtDynamic hl))
              → Open false i p w0 (i ∨ w1) (HW fs (sucHL hl) (readReg (regs (floc fs)) Output))
  store-here1 {p} {w0} {w1} true fs op hl h = heap-write w0 true fs op (sucHL hl) Ov (out op)
    (λ t → written-grows (floc fs) (sucHL hl) Ov _ (cell0 op t))
    (λ _ → subst (Written (record (floc fs) { heapMem = writeHeapMem (heapMem (floc fs)) (sucHL hl) Ov }))
                 (cong sucHL (ptr-inj h)) (written-here (heapMem (floc fs)) (sucHL hl) Ov))
    where Ov = readReg (regs (floc fs)) Output
  store-here1 {p} {w0} {w1} false fs op hl h = heap-write w0 w1 fs op (sucHL hl) Ov (out op)
    (λ t → written-grows (floc fs) (sucHL hl) Ov _ (cell0 op t))
    (λ t → written-grows (floc fs) (sucHL hl) Ov _ (cell1 op t))
    where Ov = readReg (regs (floc fs)) Output

-- `w1` records a write through the fresh pointer: `i ∨ w1`
step-store-suc : ∀ {i p w0 w1} prog fs → (op : Open false i p w0 w1 fs) → SPInv (floc fs)
               → Halted (flat-exec-instr store-indirect-suc prog fs)
                 ⊎ Open false i p w0 (i ∨ w1) (flat-exec-instr store-indirect-suc prog fs)
step-store-suc {i} {p} {w0} {w1} prog fs op sp = go (readReg (regs (floc fs)) Input1) refl (sp-regs sp Input1)
  where
    Ov = readReg (regs (floc fs)) Output
    R = λ (x : FlatState) → Halted x ⊎ Open false i p w0 (i ∨ w1) x
    post : ∀ v → readReg (regs (floc fs)) Input1 ≡ v → flat-exec-instr store-indirect-suc prog fs ≡ STS fs v
    post v e = trans (sts-eq prog fs) (cong (STS fs) e)
    go : ∀ v → readReg (regs (floc fs)) Input1 ≡ v → StackPtrOK v → R (flat-exec-instr store-indirect-suc prog fs)
    go (SV-Ptr (AtDynamic hl)) e _ =
      inj₂ (subst (Open false i p w0 (i ∨ w1)) (sym (trans (post _ e) (to-HW fs (sucHL hl) Ov)))
                  (store-here1 i fs op hl (subst (Holds i (blk op)) e (in1 op))))
    go (SV-Ptr (AtStack f k)) e ()
    go (SV-Tag t)   e _ = inj₁ (subst Halted (sym (post _ e)) refl)
    go (SV-Lit q x) e _ = inj₁ (subst Halted (sym (post _ e)) refl)
    go (SV-Code c)  e _ = inj₁ (subst Halted (sym (post _ e)) refl)

------------------------------------------------------------------------
-- Part C: THE INVARIANT OF A RUN, over a program the code generator
-- emitted (`InitDisc`, part 1): halted, or full, or a window open with the
-- code from the pc on the rest of its `Win`.
------------------------------------------------------------------------
data OpenAt (prog : AbstractTrace) (fs : FlatState) : Set where
  mkOA : ∀ {o i p w0 w1} → Open o i p w0 w1 fs → Win o i p w0 w1 (drop (fpc fs) prog) → OpenAt prog fs

Inv : AbstractTrace → FlatState → Set
Inv prog fs = Halted fs ⊎ (Full (falloc fs) (floc fs) ⊎ OpenAt prog fs)

drop-fetch : ∀ (prog : AbstractTrace) (k : ℕ) (x : AbstractInstr)
           → fetch prog k ≡ just x → drop k prog ≡ x ∷ drop (suc k) prog
drop-fetch []       k       x ()
drop-fetch (y ∷ ys) zero    x refl = refl
drop-fetch (y ∷ ys) (suc k) x e    = drop-fetch ys k x e

-- what the emitted code says at a fetched position: no allocation, or a
-- pair allocation with its window after it
init-view : ∀ {prog : AbstractTrace} (k : ℕ) {x : AbstractInstr}
          → InitDisc prog → fetch prog k ≡ just x
          → T (not-alloc? x) ⊎ ((x ≡ instr-alloc-heap 2) × WinFrom (drop (suc k) prog))
init-view k       []          ()
init-view zero    (na ∷ d)    refl = inj₁ na
init-view (suc k) (na ∷ d)    e    = init-view k d e
init-view zero    (alloc w d) refl = inj₂ (refl , w)
init-view (suc k) (alloc w d) e    = init-view k d e

na-sound : ∀ (x : AbstractInstr) → T (not-alloc? x) → ∀ n → ¬ (x ≡ instr-alloc-heap n)
na-sound x t n refl = t

-- From a full state: an allocation opens a window, anything else keeps it full.
full-step : ∀ (prog : AbstractTrace) (fs : FlatState) (x : AbstractInstr)
          → InitDisc prog → Full (falloc fs) (floc fs) → fetch prog (fpc fs) ≡ just x → ImageI x
          → StoreWF (next-heap-ref (falloc fs)) (floc fs) → sv-below (next-heap-ref (falloc fs)) (fclosure fs)
          → Inv prog (flat-exec-instr x prog fs)
full-step prog fs x d full ft ff wf cl with init-view (fpc fs) d ft
... | inj₁ t        = inj₂ (inj₁ (full-keep {fs} {flat-exec-instr x prog fs} (keeps-flat x prog fs ff (na-sound x t)) full))
... | inj₂ (refl , w) = inj₂ (inj₂ (mkOA (open-alloc prog fs full wf cl) w))

private
  lift : ∀ {prog : AbstractTrace} {fs' : FlatState} {o i p w0 w1}
       → Halted fs' ⊎ Open o i p w0 w1 fs' → Win o i p w0 w1 (drop (fpc fs') prog) → Inv prog fs'
  lift (inj₁ h)  w = inj₁ h
  lift (inj₂ op) w = inj₂ (inj₂ (mkOA op w))

-- An open window steps by its `Win` constructor; `w-done` closes it first.
open-step : ∀ (prog : AbstractTrace) (fs : FlatState) (x : AbstractInstr) {o i p w0 w1}
          → InitDisc prog → fetch prog (fpc fs) ≡ just x → ImageI x
          → StoreWF (next-heap-ref (falloc fs)) (floc fs) → sv-below (next-heap-ref (falloc fs)) (fclosure fs)
          → SPInv (floc fs)
          → Open o i p w0 w1 fs → Win o i p w0 w1 (x ∷ drop (suc (fpc fs)) prog)
          → Inv prog (flat-exec-instr x prog fs)
open-step prog fs x d ft ff wf cl sp op w-done = full-step prog fs x d (close-done op) ft ff wf cl
open-step prog fs _ d ft ff wf cl sp op (w-stash {s = s} w)           = lift (inj₂ (step-stash prog fs s op)) w
open-step prog fs _ d ft ff wf cl sp op (w-store-slot {s = s} a w)    = lift (inj₂ (step-store-slot prog fs s op a)) w
open-step prog fs _ d ft ff wf cl sp op (w-mov-in w)                  = lift (inj₂ (step-mov-in prog fs op)) w
open-step prog fs _ d ft ff wf cl sp op (w-load-stash w)              = lift (inj₂ (step-load-stash prog fs op)) w
open-step prog fs _ d ft ff wf cl sp op (w-load-slot {s = s} a w)     = lift (step-load-slot prog fs s op a) w
open-step prog fs _ d ft ff wf cl sp op (w-restore-stash w)           = lift (inj₂ (step-restore-stash prog fs op)) w
open-step prog fs _ d ft ff wf cl sp op (w-restore-slot {s = s} a w)  = lift (step-restore-slot prog fs s op a) w
open-step prog fs _ d ft ff wf cl sp op (w-load w)                    = lift (step-load prog fs op sp) w
open-step prog fs _ d ft ff wf cl sp op (w-load-suc w)                = lift (step-load-suc prog fs op sp) w
open-step prog fs _ d ft ff wf cl sp op (w-store w)                   = lift (step-store prog fs op sp) w
open-step prog fs _ d ft ff wf cl sp op (w-store-suc w)               = lift (step-store-suc prog fs op sp) w
open-step prog fs _ d ft ff wf cl sp op (w-tag {n = n} w)             = lift (inj₂ (step-tag prog fs n op)) w
open-step prog fs _ d ft ff wf cl sp op (w-code {l = l} w)            = lift (inj₂ (step-code prog fs l op)) w

-- THE STEP: the invariant survives every step of a running machine.
inv-step : ∀ (prog : AbstractTrace) (fs : FlatState) (x : AbstractInstr)
         → InitDisc prog → Inv prog fs
         → fetch prog (fpc fs) ≡ just x → LocState.halted (floc fs) ≡ false → ImageI x
         → StoreWF (next-heap-ref (falloc fs)) (floc fs) → sv-below (next-heap-ref (falloc fs)) (fclosure fs)
         → SPInv (floc fs)
         → Inv prog (flat-exec-instr x prog fs)
inv-step prog fs x d (inj₁ hd) ft h ff wf cl sp with trans (sym hd) h
... | ()
inv-step prog fs x d (inj₂ (inj₁ full)) ft h ff wf cl sp = full-step prog fs x d full ft ff wf cl
inv-step prog fs x d (inj₂ (inj₂ (mkOA op w))) ft h ff wf cl sp =
  open-step prog fs x d ft ff wf cl sp op (subst (Win _ _ _ _ _) (drop-fetch prog (fpc fs) x ft) w)

------------------------------------------------------------------------
-- THE CONSUMER: a load through `Input1` reads a written cell. Full, the
-- cell is in an allocated block; open, `Win` allows the load only when
-- `Input1` is not the fresh pointer, so the cell is in an older block.
------------------------------------------------------------------------
private
  older-of : ∀ {o i p w0 w1} {fs : FlatState} (op : Open o i p w0 w1 fs) (hl : HeapLocation)
           → ref-id (heap-ref hl) < next-heap-ref (falloc fs) → ¬ (ref-id (heap-ref hl) ≡ blk op)
           → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl)) → Written (floc fs) hl
  older-of op hl lt ne ib with m<1+n⇒m<n∨m≡n (subst (ref-id (heap-ref hl) <_) (nx op) lt)
  ... | inj₁ r<b = older op hl r<b ib
  ... | inj₂ r≡b = ⊥-elim (ne r≡b)

  -- the cell `g hl` a load reads, where `g` keeps the block (`id` or `sucHL`)
  reads : ∀ (prog : AbstractTrace) (fs : FlatState) (x : AbstractInstr) (g : HeapLocation → HeapLocation)
        → (∀ hl → ref-id (heap-ref (g hl)) ≡ ref-id (heap-ref hl))
        → (∀ {o p w0 w1 t} → Win o true p w0 w1 (x ∷ t) → w0 ≡ true × w1 ≡ true)
        → Inv prog fs → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just x
        → (hl : HeapLocation) → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
        → ref-id (heap-ref hl) < next-heap-ref (falloc fs)
        → heap-offset (g hl) < block-size (falloc fs) (ref-id (heap-ref (g hl)))
        → Written (floc fs) (g hl)
  reads prog fs x g gr only (inj₁ hd) h ft hl eq lt ib with trans (sym hd) h
  ... | ()
  reads prog fs x g gr only (inj₂ (inj₁ full)) h ft hl eq lt ib =
    full (g hl) (subst (_< next-heap-ref (falloc fs)) (sym (gr hl)) lt) ib
  reads prog fs x g gr only (inj₂ (inj₂ (mkOA {o} {i} {p} {w0} {w1} op w))) h ft hl eq lt ib =
    go i op (subst (Win o i p w0 w1) (drop-fetch prog (fpc fs) x ft) w)
    where
      lt' = subst (_< next-heap-ref (falloc fs)) (sym (gr hl)) lt
      go : ∀ (i' : Bool) (op' : Open o i' p w0 w1 fs)
         → Win o i' p w0 w1 (x ∷ drop (suc (fpc fs)) prog) → Written (floc fs) (g hl)
      go false op' _ = older-of op' (g hl) lt'
                         (λ e → subst (Avoids (blk op')) eq (in1 op') (trans (sym (gr hl)) e)) ib
      go true  op' wn with only wn
      ... | refl , refl = close-done op' (g hl) lt' ib

private
  only-ld : ∀ {o p w0 w1 t} → Win o true p w0 w1 (load-indirect ∷ t) → (w0 ≡ true) × (w1 ≡ true)
  only-ld w-done = refl , refl

  only-lds : ∀ {o p w0 w1 t} → Win o true p w0 w1 (load-indirect-suc ∷ t) → (w0 ≡ true) × (w1 ≡ true)
  only-lds w-done = refl , refl

load-written : ∀ (prog : AbstractTrace) (fs : FlatState) → Inv prog fs → LocState.halted (floc fs) ≡ false
             → fetch prog (fpc fs) ≡ just load-indirect
             → (hl : HeapLocation) → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
             → ref-id (heap-ref hl) < next-heap-ref (falloc fs)
             → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))
             → Written (floc fs) hl
load-written prog fs iv h ft = reads prog fs load-indirect (λ hl → hl) (λ _ → refl) only-ld iv h ft

load-suc-written : ∀ (prog : AbstractTrace) (fs : FlatState) → Inv prog fs → LocState.halted (floc fs) ≡ false
                 → fetch prog (fpc fs) ≡ just load-indirect-suc
                 → (hl : HeapLocation) → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                 → ref-id (heap-ref hl) < next-heap-ref (falloc fs)
                 → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl)))
                 → Written (floc fs) (sucHL hl)
load-suc-written prog fs iv h ft = reads prog fs load-indirect-suc sucHL (λ _ → refl) only-lds iv h ft
