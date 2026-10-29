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
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n)
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
open FrameSemantics FS using (Frame)
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
keeps-abstract (instr-room n)         ls al () na
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

StashHolds : Maybe ℕ → ℕ → LocState FS → Frame → Set
StashHolds nothing  b ls cf = ⊤
StashHolds (just q) b ls cf = stackMem ls cf q ≡ just (fresh b)

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
    stash  : StashHolds p blk (floc fs) (current-frame (falloc fs))
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
