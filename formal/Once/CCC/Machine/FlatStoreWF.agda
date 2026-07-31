-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatStoreWF
--
-- STORE WELL-FORMEDNESS of the abstract machine: "no forward pointers".
--
-- Every value the machine holds (in a register, a heap cell or a stack slot)
-- references only blocks the allocator has ALREADY handed out (ref-id below
-- `next-heap-ref`), and no cell of a not-yet-allocated block has ever been
-- written. This is a property of the ABSTRACT machine alone — no target, no
-- correspondence — and it is exactly what an allocation step needs: the block
-- about to be handed out is referenced by nothing, so extending the target's
-- address map at that block is invisible to every existing value
-- (`Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.enc-ext`), and its cells
-- are unwritten on the abstract side.
--
-- Proved by induction over `exec-abstract`, mirroring its mutual block (so the
-- nested `instr-case-on-tag` / `instr-loop` traces are covered), and bundled
-- with the frontier-MONOTONICITY the loop case needs (`next-heap-ref` never
-- decreases). Lifted to the flat machine's `flat-exec-instr` at the end.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatStoreWF (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; s≤s; z≤n; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-irrefl; n≤1+n; ≤-step)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; heap-ref; ref-id; sucHL)
open import Once.SigOp.Info using (SigOpInfo; effect; EffectShape; Pure; Emits; Halts)
open import Once.Type using (Type; FitsInReg; fits-in-reg?)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.Machine.SMCore
open FrameSemantics FS using (Frame; _≟F_)
open MemOps {FS}
open ExecFinal {FS}
open AbstractExec {FS}
open import Once.CCC.Machine.Flat
open FlatMachine {FS}

------------------------------------------------------------------------
-- "Below the allocation frontier": a value/location references no block the
-- allocator has not handed out yet. Non-pointers are unconstrained.
------------------------------------------------------------------------
loc-below : ℕ → ValueLocation FS → Set
loc-below n (AtDynamic hl)  = ref-id (heap-ref hl) < n
loc-below n (AtStack _ _)   = ⊤

sv-below : ℕ → StoredValue FS → Set
sv-below n (SV-Ptr loc)   = loc-below n loc
sv-below n (SV-Tag _)     = ⊤
sv-below n (SV-Lit _ _)   = ⊤
sv-below n (SV-Code _)    = ⊤

svm-below : ℕ → Maybe (StoredValue FS) → Set
svm-below n (just v) = sv-below n v
svm-below n nothing  = ⊤

mloc-below : ℕ → Maybe (ValueLocation FS) → Set
mloc-below n (just loc) = loc-below n loc
mloc-below n nothing    = ⊤

-- Monotone in the frontier (which only grows).
loc-mono : ∀ {m n} (loc : ValueLocation FS) → m ≤ n → loc-below m loc → loc-below n loc
loc-mono (AtDynamic hl) m≤n lt = ≤-trans lt m≤n
loc-mono (AtStack _ _)  _   _  = tt

sv-mono : ∀ {m n} (v : StoredValue FS) → m ≤ n → sv-below m v → sv-below n v
sv-mono (SV-Ptr loc) m≤n b = loc-mono loc m≤n b
sv-mono (SV-Tag _)   _   _ = tt
sv-mono (SV-Lit _ _) _   _ = tt
sv-mono (SV-Code _)  _   _ = tt

svm-mono : ∀ {m n} (mv : Maybe (StoredValue FS)) → m ≤ n → svm-below m mv → svm-below n mv
svm-mono (just v) m≤n b = sv-mono v m≤n b
svm-mono nothing  _   _ = tt

-- `sv-as-loc` never invents a pointer (stated directly on `sv-as-loc v`, so the
-- call sites need no equation to rewrite with).
sv-as-loc-below : ∀ (n : ℕ) (v : StoredValue FS) → sv-below n v → mloc-below n (sv-as-loc v)
sv-as-loc-below n (SV-Ptr (AtDynamic hl)) b = b
sv-as-loc-below n (SV-Ptr (AtStack f k))  b = tt
sv-as-loc-below n (SV-Tag _)              _ = tt
sv-as-loc-below n (SV-Lit _ _)            _ = tt
sv-as-loc-below n (SV-Code _)             _ = tt

slot-base-below : ∀ (n : ℕ) (mv : Maybe (StoredValue FS)) → svm-below n mv
                → mloc-below n (slot-base mv)
slot-base-below n (just v) b = sv-as-loc-below n v b
slot-base-below n nothing  _ = tt

-- Same block ⇒ same ref-id, so offsets stay below.
sucLoc-below : ∀ (n : ℕ) (loc : ValueLocation FS) → loc-below n loc → loc-below n (sucLoc loc)
sucLoc-below n (AtDynamic (heap-loc r o)) b = b
sucLoc-below n (AtStack f k)              _ = tt

offsetLoc-below : ∀ (n : ℕ) (loc : ValueLocation FS) (i : ℕ)
                → loc-below n loc → loc-below n (offsetLoc loc i)
offsetLoc-below n (AtDynamic (heap-loc r o)) i b = b
offsetLoc-below n (AtStack f k)              i _ = tt

-- tags stay tags
sv-succ-below : ∀ (n : ℕ) (v : StoredValue FS) → sv-below n (sv-succ v)
sv-succ-below n (SV-Tag _)   = tt
sv-succ-below n (SV-Ptr _)   = tt
sv-succ-below n (SV-Lit _ _) = tt
sv-succ-below n (SV-Code _)  = tt

sv-pred-below : ∀ (n : ℕ) (v : StoredValue FS) → sv-below n (sv-pred v)
sv-pred-below n (SV-Tag zero)    = tt
sv-pred-below n (SV-Tag (suc _)) = tt
sv-pred-below n (SV-Ptr _)       = tt
sv-pred-below n (SV-Lit _ _)     = tt
sv-pred-below n (SV-Code _)      = tt

------------------------------------------------------------------------
-- The invariant.
------------------------------------------------------------------------
-- Indexed by the FRONTIER (`next-heap-ref`), not by the AllocState: the many
-- instructions that update `next-slot`/`current-frame` leave the frontier alone,
-- and a record indexed by the whole AllocState would not transport across them.
record StoreWF (n : ℕ) (ls : LocState FS) : Set where
  field
    wf-regs  : ∀ (r : AbstractReg) → sv-below n (readReg (regs ls) r)
    wf-heap  : ∀ (hl : HeapLocation) → svm-below n (heapMem ls hl)
    wf-stack : ∀ (f : Frame) (k : Slot) → svm-below n (stackMem ls f k)
    -- Cells of blocks the allocator has NOT handed out are untouched.
    wf-fresh : ∀ (hl : HeapLocation) → n ≤ ref-id (heap-ref hl)
             → heapMem ls hl ≡ nothing
open StoreWF public

------------------------------------------------------------------------
-- Structural helpers: one machine effect at a time.
------------------------------------------------------------------------

-- read-after-write on the four registers (both indices concrete ⇒ definitional).
rw-below : ∀ (n : ℕ) (rf : Registers FS) (x y : AbstractReg) (v : StoredValue FS)
         → sv-below n v → sv-below n (readReg rf y)
         → sv-below n (readReg (writeReg rf x v) y)
rw-below n rf Input1  Input1  v bv _  = bv
rw-below n rf Input1  Input2  v _  bo = bo
rw-below n rf Input1  Output  v _  bo = bo
rw-below n rf Input1  Scratch v _  bo = bo
rw-below n rf Input2  Input1  v _  bo = bo
rw-below n rf Input2  Input2  v bv _  = bv
rw-below n rf Input2  Output  v _  bo = bo
rw-below n rf Input2  Scratch v _  bo = bo
rw-below n rf Output  Input1  v _  bo = bo
rw-below n rf Output  Input2  v _  bo = bo
rw-below n rf Output  Output  v bv _  = bv
rw-below n rf Output  Scratch v _  bo = bo
rw-below n rf Scratch Input1  v _  bo = bo
rw-below n rf Scratch Input2  v _  bo = bo
rw-below n rf Scratch Output  v _  bo = bo
rw-below n rf Scratch Scratch v bv _  = bv
rw-below n rf Input1  Count   v _  bo = bo
rw-below n rf Input2  Count   v _  bo = bo
rw-below n rf Output  Count   v _  bo = bo
rw-below n rf Scratch Count   v _  bo = bo
rw-below n rf Count   Input1  v _  bo = bo
rw-below n rf Count   Input2  v _  bo = bo
rw-below n rf Count   Output  v _  bo = bo
rw-below n rf Count   Scratch v _  bo = bo
rw-below n rf Count   Count   v bv _  = bv

wf-write-reg : ∀ {n ls} (x : AbstractReg) (v : StoredValue FS)
             → StoreWF n ls → sv-below (n) v
             → StoreWF n (record ls { regs = writeReg (regs ls) x v })
wf-write-reg {n} {ls} x v wf bv = record
  { wf-regs  = λ y → rw-below (n) (regs ls) x y v bv (wf-regs wf y)
  ; wf-heap  = wf-heap wf ; wf-stack = wf-stack wf ; wf-fresh = wf-fresh wf }

-- halting touches only the `halted` flag.
wf-halt : ∀ {n ls} → StoreWF n ls → StoreWF n (record ls { halted = true })
wf-halt wf = record { wf-regs = wf-regs wf ; wf-heap = wf-heap wf
                    ; wf-stack = wf-stack wf ; wf-fresh = wf-fresh wf }

-- the SigOp shape: one register write AND a halt-flag update.
wf-write-reg-halt : ∀ {n ls} (x : AbstractReg) (v : StoredValue FS) (b : Bool)
                  → StoreWF n ls → sv-below (n) v
                  → StoreWF n (record ls { regs = writeReg (regs ls) x v ; halted = b })
wf-write-reg-halt {n} {ls} x v b wf bv = record
  { wf-regs  = λ y → rw-below (n) (regs ls) x y v bv (wf-regs wf y)
  ; wf-heap  = wf-heap wf ; wf-stack = wf-stack wf ; wf-fresh = wf-fresh wf }

-- the stack-slot counter is not a stored value: any `stackSlot`-only update
-- leaves every register's CONTENT alone.
regs-ss : ∀ (n : ℕ) (rf : Registers FS) (m : ℕ) (y : AbstractReg)
        → sv-below n (readReg rf y) → sv-below n (readReg (record rf { stackSlot = m }) y)
regs-ss n rf m Input1  b = b
regs-ss n rf m Input2  b = b
regs-ss n rf m Output  b = b
regs-ss n rf m Scratch b = b
regs-ss n rf m Count   b = b

wf-stack-slot : ∀ {n ls} (m : ℕ) → StoreWF n ls
              → StoreWF n (record ls { regs = record (regs ls) { stackSlot = m } })
wf-stack-slot {n} {ls} m wf = record
  { wf-regs = λ y → regs-ss (n) (regs ls) m y (wf-regs wf y)
  ; wf-heap = wf-heap wf ; wf-stack = wf-stack wf ; wf-fresh = wf-fresh wf }

-- STACK write: only the written slot changes, and it gets a below value.
wsm-below : ∀ (n : ℕ) {f f' : Frame} {k k' : Slot}
            (df : Dec (f ≡ f')) (dk : Dec (k ≡ k'))
            (old : Maybe (StoredValue FS)) (v : StoredValue FS)
          → svm-below n old → sv-below n v
          → svm-below n (writeStackMem-aux df dk old v)
wsm-below n (no _)  _       old v bo _  = bo
wsm-below n (yes _) (yes _) old v _  bv = bv
wsm-below n (yes _) (no _)  old v bo _  = bo

wf-write-stack : ∀ {n ls} (f : Frame) (k : Slot) (v : StoredValue FS)
               → StoreWF n ls → sv-below (n) v
               → StoreWF n (writeLocToStack ls f k v)
wf-write-stack {n} {ls} f k v wf bv = record
  { wf-regs = wf-regs wf ; wf-heap = wf-heap wf ; wf-fresh = wf-fresh wf
  ; wf-stack = λ f' k' → wsm-below (n) (f ≟F f') (k ≟ k')
                           (stackMem ls f' k') v (wf-stack wf f' k') bv }

-- HEAP write at a cell BELOW the frontier.
whm-below : ∀ (n : ℕ) {hl hl' : HeapLocation} (d : Dec (hl ≡ hl'))
            (old : Maybe (StoredValue FS)) (v : StoredValue FS)
          → svm-below n old → sv-below n v → svm-below n (writeHeapMem-aux d old v)
whm-below n (yes _) old v _  bv = bv
whm-below n (no _)  old v bo _  = bo

whm-fresh : ∀ (n : ℕ) {hl hl' : HeapLocation} (d : Dec (hl ≡ hl'))
            (old : Maybe (StoredValue FS)) (v : StoredValue FS)
          → ref-id (heap-ref hl) < n → n ≤ ref-id (heap-ref hl') → old ≡ nothing
          → writeHeapMem-aux d old v ≡ nothing
whm-fresh n {hl} (yes refl) old v lt le _ = ⊥-elim (<-irrefl refl (≤-trans lt le))
whm-fresh n (no _)  old v _  _  o = o

wf-write-heap : ∀ {n ls} (hl : HeapLocation) (v : StoredValue FS)
              → StoreWF n ls → ref-id (heap-ref hl) < n
              → sv-below (n) v
              → StoreWF n (writeLocToHeap ls hl v)
wf-write-heap {n} {ls} hl v wf lt bv = record
  { wf-regs = wf-regs wf ; wf-stack = wf-stack wf
  ; wf-heap = λ hl' → whm-below (n) (hl ≟HL hl')
                        (heapMem ls hl') v (wf-heap wf hl') bv
  ; wf-fresh = λ hl' le → whm-fresh (n) (hl ≟HL hl')
                            (heapMem ls hl') v lt le (wf-fresh wf hl' le) }

-- A `writeLoc` at ANY below-frontier location (the stack branch and the heap
-- branch; since 2026-07-31 a stack pointer stored into a heap cell is an
-- ordinary heap write, not a no-op — `sv-below` holds of it vacuously, since it
-- references no block at all).
wf-write-loc : ∀ {n ls} (loc : ValueLocation FS) (v : StoredValue FS)
             → StoreWF n ls → loc-below (n) loc
             → sv-below (n) v
             → StoreWF n (writeLoc ls loc v)
wf-write-loc (AtStack f k)  v                        wf _  bv = wf-write-stack f k v wf bv
wf-write-loc (AtDynamic hl) (SV-Ptr (AtStack f k))   wf lt bv = wf-write-heap hl _ wf lt bv
wf-write-loc (AtDynamic hl) (SV-Ptr (AtDynamic hl')) wf lt bv = wf-write-heap hl _ wf lt bv
wf-write-loc (AtDynamic hl) (SV-Tag t)               wf lt bv = wf-write-heap hl _ wf lt bv
wf-write-loc (AtDynamic hl) (SV-Lit p x)             wf lt bv = wf-write-heap hl _ wf lt bv
wf-write-loc (AtDynamic hl) (SV-Code c)              wf lt bv = wf-write-heap hl _ wf lt bv

-- reading a below-frontier location yields a below-frontier value.
readLoc-below : ∀ {n ls} (loc : ValueLocation FS) → StoreWF n ls
              → svm-below (n) (readLoc ls loc)
readLoc-below (AtStack f k)  wf = wf-stack wf f k
readLoc-below (AtDynamic hl) wf = wf-heap wf hl

------------------------------------------------------------------------
-- The resolved load/store helpers.
------------------------------------------------------------------------
wf-load-value : ∀ {n ls} (dst : AbstractReg) (mv : Maybe (StoredValue FS))
              → StoreWF n ls → svm-below (n) mv
              → StoreWF n (exec-load-with-value dst mv ls)
wf-load-value dst (just v) wf b = wf-write-reg dst v wf b
wf-load-value dst nothing  wf _ = wf-halt wf

wf-load-resolved : ∀ {n ls} (dst : AbstractReg) (mloc : Maybe (ValueLocation FS))
                 → StoreWF n ls → mloc-below (n) mloc
                 → StoreWF n (exec-load-via-resolved dst mloc ls)
wf-load-resolved dst (just loc) wf _ = wf-load-value dst (readLoc _ loc) wf (readLoc-below loc wf)
wf-load-resolved dst nothing    wf _ = wf-halt wf

wf-load-suc-resolved : ∀ {n ls} (dst : AbstractReg) (mloc : Maybe (ValueLocation FS))
                     → StoreWF n ls → mloc-below (n) mloc
                     → StoreWF n (exec-load-suc-via-resolved dst mloc ls)
wf-load-suc-resolved {n} {ls} dst (just loc) wf b =
  wf-load-value dst (readLoc ls (sucLoc loc)) wf (readLoc-below (sucLoc loc) wf)
wf-load-suc-resolved dst nothing wf _ = wf-halt wf

wf-store-resolved : ∀ {n ls} (mloc : Maybe (ValueLocation FS)) (v : StoredValue FS)
                  → StoreWF n ls → mloc-below (n) mloc
                  → sv-below (n) v
                  → StoreWF n (exec-store-via-resolved mloc v ls)
wf-store-resolved (just loc) v wf b bv = wf-write-loc loc v wf b bv
wf-store-resolved nothing    v wf _ _  = wf-halt wf

wf-store-suc-resolved : ∀ {n ls} (mloc : Maybe (ValueLocation FS)) (v : StoredValue FS)
                      → StoreWF n ls → mloc-below (n) mloc
                      → sv-below (n) v
                      → StoreWF n (exec-store-suc-via-resolved mloc v ls)
wf-store-suc-resolved {n} {ls} (just loc) v wf b bv =
  wf-write-loc (sucLoc loc) v wf (sucLoc-below (n) loc b) bv
wf-store-suc-resolved nothing v wf _ _ = wf-halt wf

wf-lea-indexed : ∀ {n ls} (mloc : Maybe (ValueLocation FS)) (i : ℕ)
               → StoreWF n ls → mloc-below (n) mloc
               → StoreWF n (exec-lea-indexed-via mloc i ls)
wf-lea-indexed {n} {ls} (just loc) i wf b =
  wf-write-reg Input1 (SV-Ptr (offsetLoc loc i)) wf
    (offsetLoc-below (n) loc i b)
wf-lea-indexed nothing i wf _ = wf-halt wf

-- load-from-slot / restore-input share this shape (they also thread `alloc`).
wf-slot-load : ∀ {n ls} (dst : AbstractReg) (mv : Maybe (StoredValue FS))
             → StoreWF n ls → svm-below (n) mv
             → StoreWF n (exec-load-with-value dst mv ls)
wf-slot-load = wf-load-value

------------------------------------------------------------------------
-- The SigOp output. `Emits`/`Halts` produce `unit-storedvalue`; a `Pure`
-- SigOp's output is a literal (`SV-Lit`) except for the postulated
-- non-register-fittable case, which gets the companion axiom below — the same
-- trusted base as `structured-pure-sigop-output` itself (D061).
------------------------------------------------------------------------
postulate
  structured-pure-sigop-below :
    ∀ (n : ℕ) {A B} (si : SigOpInfo A B) (ls : LocState FS)
    → sv-below n (structured-pure-sigop-output si ls)

pure-out-val-below : ∀ (n : ℕ) {A B} (si : SigOpInfo A B) (fitB : FitsInReg B) (ma : Maybe ⟦ A ⟧)
                   → sv-below n (pure-sigop-out-val si fitB ma)
pure-out-val-below n si fitB (just a) = tt
pure-out-val-below n si fitB nothing  = tt

sigop-output-below : ∀ (n : ℕ) {A B} (si : SigOpInfo A B) (ls : LocState FS)
                   → sv-below n (exec-sigop-output si ls)
sigop-output-below n {A} {B} si ls = go (effect si)
  where
    aux : ∀ (mf : Maybe (FitsInReg B)) (ml : Maybe (ValueLocation FS))
        → sv-below n (pure-sigop-out-aux si ls mf ml)
    aux (just fitB) (just in-loc) = pure-out-val-below n si fitB (readTyped A in-loc ls)
    aux (just fitB) nothing       = pure-out-val-below n si fitB (readReg-typed A (readReg (regs ls) Input1))
    aux nothing     _             = structured-pure-sigop-below n si ls
    go : ∀ (e : EffectShape B) → sv-below n (exec-sigop-output-of e si ls)
    go Pure      = aux (fits-in-reg? B) (sv-as-loc (readReg (regs ls) Input1))
    go (Emits _) = tt
    go (Halts _) = tt

------------------------------------------------------------------------
-- Slot loads (they thread `alloc` through, so they need their own shape).
------------------------------------------------------------------------
wf-slot-load-out : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
                 → StoreWF (next-heap-ref alloc) ls → svm-below (next-heap-ref alloc) mv
                 → StoreWF (next-heap-ref (proj₂ (exec-load-from-slot-with-value mv ls alloc)))
                           (proj₁ (exec-load-from-slot-with-value mv ls alloc))
                   × (next-heap-ref alloc
                      ≤ next-heap-ref (proj₂ (exec-load-from-slot-with-value mv ls alloc)))
wf-slot-load-out (just v) ls alloc wf b = wf-write-reg Output v wf b , ≤-refl
wf-slot-load-out nothing  ls alloc wf _ = wf-halt wf , ≤-refl

wf-slot-load-in1 : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
                 → StoreWF (next-heap-ref alloc) ls → svm-below (next-heap-ref alloc) mv
                 → StoreWF (next-heap-ref (proj₂ (exec-restore-input-with-value mv ls alloc)))
                           (proj₁ (exec-restore-input-with-value mv ls alloc))
                   × (next-heap-ref alloc
                      ≤ next-heap-ref (proj₂ (exec-restore-input-with-value mv ls alloc)))
wf-slot-load-in1 (just v) ls alloc wf b = wf-write-reg Input1 v wf b , ≤-refl
wf-slot-load-in1 nothing  ls alloc wf _ = wf-halt wf , ≤-refl

------------------------------------------------------------------------
-- THE INVARIANT IS PRESERVED, bundled with frontier monotonicity (which the
-- loop case needs: it re-anchors the pre-state's stack into the post-state).
------------------------------------------------------------------------
Preserves : (ls : LocState FS) (alloc : AllocState {FS})
          → LocState FS × AllocState {FS} → Set
Preserves ls alloc (ls' , alloc') =
  StoreWF (next-heap-ref alloc') ls' × (next-heap-ref alloc ≤ next-heap-ref alloc')

mutual
  wf-abstract : ∀ (i : AbstractInstr) (ls : LocState FS) (alloc : AllocState {FS})
              → StoreWF (next-heap-ref alloc) ls → Preserves ls alloc (exec-abstract i ls alloc)
  wf-abstract mov-to-output ls alloc wf =
    wf-write-reg Output (readReg (regs ls) Input1) wf (wf-regs wf Input1) , ≤-refl
  wf-abstract mov-to-input ls alloc wf =
    wf-write-reg Input1 (readReg (regs ls) Output) wf (wf-regs wf Output) , ≤-refl
  wf-abstract mov-output-to-input2 ls alloc wf =
    wf-write-reg Input2 (readReg (regs ls) Output) wf (wf-regs wf Output) , ≤-refl
  wf-abstract mov-input2-to-output ls alloc wf =
    wf-write-reg Output (readReg (regs ls) Input2) wf (wf-regs wf Input2) , ≤-refl
  wf-abstract load-indirect ls alloc wf =
    wf-load-resolved Output (sv-as-loc (readReg (regs ls) Input1)) wf
      (sv-as-loc-below (next-heap-ref alloc) (readReg (regs ls) Input1) (wf-regs wf Input1)) , ≤-refl
  wf-abstract load-indirect-suc ls alloc wf =
    wf-load-suc-resolved Output (sv-as-loc (readReg (regs ls) Input1)) wf
      (sv-as-loc-below (next-heap-ref alloc) (readReg (regs ls) Input1) (wf-regs wf Input1)) , ≤-refl
  wf-abstract (load-from-slot slot) ls alloc wf =
    wf-slot-load-out (readLoc ls (AtStack (current-frame alloc) slot)) ls alloc wf
      (readLoc-below (AtStack (current-frame alloc) slot) wf)
  wf-abstract (store-at-slot slot) ls alloc wf =
    wf-write-loc (AtStack (current-frame alloc) slot) (readReg (regs ls) Output) wf tt
      (wf-regs wf Output) , ≤-refl
  wf-abstract store-indirect ls alloc wf =
    wf-store-resolved (sv-as-loc (readReg (regs ls) Input1)) (readReg (regs ls) Output) wf
      (sv-as-loc-below (next-heap-ref alloc) (readReg (regs ls) Input1) (wf-regs wf Input1)) (wf-regs wf Output) , ≤-refl
  wf-abstract store-indirect-suc ls alloc wf =
    wf-store-suc-resolved (sv-as-loc (readReg (regs ls) Input1)) (readReg (regs ls) Output) wf
      (sv-as-loc-below (next-heap-ref alloc) (readReg (regs ls) Input1) (wf-regs wf Input1)) (wf-regs wf Output) , ≤-refl
  wf-abstract (lea-slot slot) ls alloc wf =
    wf-write-reg Output (SV-Ptr (AtStack (current-frame alloc) slot)) wf tt , ≤-refl
  wf-abstract (restore-input slot) ls alloc wf =
    wf-slot-load-in1 (readLoc ls (AtStack (current-frame alloc) slot)) ls alloc wf
      (readLoc-below (AtStack (current-frame alloc) slot) wf)
  wf-abstract (lea-indexed slot) ls alloc wf =
    wf-lea-indexed (slot-base (readLoc ls (AtStack (current-frame alloc) slot)))
      (sv-tag-val (readReg (regs ls) Scratch)) wf
      (slot-base-below (next-heap-ref alloc) (readLoc ls (AtStack (current-frame alloc) slot))
        (readLoc-below (AtStack (current-frame alloc) slot) wf)) , ≤-refl
  wf-abstract (instr-alloc-stack n) ls alloc wf =
    wf-stack-slot (stackSlot (regs ls) + n) wf , ≤-refl
  wf-abstract (instr-dealloc-stack n) ls alloc wf =
    wf-stack-slot (stackSlot (regs ls) ∸ n) wf , ≤-refl
  wf-abstract (instr-reclaim-to n) ls alloc wf = wf , ≤-refl
  wf-abstract (instr-push-frame cap) ls alloc wf = wf-stack-slot 0 wf , ≤-refl
  wf-abstract instr-pop-frame ls alloc wf = wf , ≤-refl
  wf-abstract instr-call-closure ls alloc wf = wf , ≤-refl
  wf-abstract (worklist-init slot) ls alloc wf = wf , ≤-refl
  wf-abstract (worklist-push slot) ls alloc wf =
    wf-write-loc (AtStack (current-frame alloc) slot) (readReg (regs ls) Output) wf tt
      (wf-regs wf Output) , ≤-refl
  wf-abstract (worklist-pop slot) ls alloc wf =
    wf-slot-load-out (readLoc ls (AtStack (current-frame alloc) slot)) ls alloc wf
      (readLoc-below (AtStack (current-frame alloc) slot) wf)
  wf-abstract (worklist-check slot) ls alloc wf = wf , ≤-refl
  wf-abstract (instr-sigop si) ls alloc wf =
    wf-write-reg-halt Output (exec-sigop-output si ls) (exec-sigop-halts si ls) wf
      (sigop-output-below (next-heap-ref alloc) si ls) , ≤-refl
  wf-abstract (instr-load-const p v) ls alloc wf = wf-write-reg Output (SV-Lit p v) wf tt , ≤-refl
  wf-abstract (instr-load-code-addr n) ls alloc wf = wf-write-reg Output (SV-Code n) wf tt , ≤-refl
  wf-abstract instr-save-closure-reg ls alloc wf = wf , ≤-refl
  wf-abstract (instr-load-tag-lit n) ls alloc wf = wf-write-reg Output (SV-Tag n) wf tt , ≤-refl
  wf-abstract (instr-case-on-tag f g) ls alloc wf = wf-case (case-tag-at ls) f g ls alloc wf
  -- THE ALLOCATION: the fresh block is handed out (its ref is the OLD frontier,
  -- so it is below the NEW one), and every pre-existing value stays below by
  -- monotonicity. `wf-fresh` shrinks to the cells beyond the new frontier.
  wf-abstract (instr-alloc-heap n) ls alloc wf =
    record
      { wf-regs = λ y → rw-below (suc (next-heap-ref alloc)) (regs ls) Output y
                          (SV-Ptr (AtDynamic (heap-loc (mkHeapRef (next-heap-ref alloc)) 0)))
                          ≤-refl (sv-mono (readReg (regs ls) y) (n≤1+n (next-heap-ref alloc))
                                          (wf-regs wf y))
      ; wf-heap = λ hl → svm-mono (heapMem ls hl) (n≤1+n (next-heap-ref alloc)) (wf-heap wf hl)
      ; wf-stack = λ f k → svm-mono (stackMem ls f k) (n≤1+n (next-heap-ref alloc)) (wf-stack wf f k)
      ; wf-fresh = λ hl le → wf-fresh wf hl (≤-trans (n≤1+n (next-heap-ref alloc)) le)
      } , n≤1+n (next-heap-ref alloc)
  wf-abstract (instr-loop body) ls alloc wf = wf-loop 1000000 body ls alloc wf
  wf-abstract (instr-reg-op scratch-one) ls alloc wf = wf-write-reg Scratch (SV-Tag 1) wf tt , ≤-refl
  wf-abstract (instr-reg-op scratch-zero) ls alloc wf = wf-write-reg Scratch (SV-Tag 0) wf tt , ≤-refl
  wf-abstract (instr-reg-op scratch-dec) ls alloc wf =
    wf-write-reg Scratch (sv-pred (readReg (regs ls) Scratch)) wf
      (sv-pred-below (next-heap-ref alloc) (readReg (regs ls) Scratch)) , ≤-refl
  wf-abstract (instr-reg-op scratch-load-count) ls alloc wf =
    wf-write-reg Scratch (readReg (regs ls) Count) wf (wf-regs wf Count) , ≤-refl
  wf-abstract (instr-reg-op count-zero) ls alloc wf = wf-write-reg Count (SV-Tag 0) wf tt , ≤-refl
  wf-abstract (instr-reg-op count-inc) ls alloc wf =
    wf-write-reg Count (sv-succ (readReg (regs ls) Count)) wf
      (sv-succ-below (next-heap-ref alloc) (readReg (regs ls) Count)) , ≤-refl
  wf-abstract (instr-ctrl c) ls alloc wf = wf , ≤-refl

  wf-trace : ∀ (t : AbstractTrace) (ls : LocState FS) (alloc : AllocState {FS})
           → StoreWF (next-heap-ref alloc) ls → Preserves ls alloc (exec-trace t ls alloc)
  wf-trace [] ls alloc wf = wf , ≤-refl
  wf-trace (i ∷ is) ls alloc wf with halted ls
  ... | true  = wf , ≤-refl
  ... | false =
    let step = wf-abstract i ls alloc wf
        rest = wf-trace is (proj₁ (exec-abstract i ls alloc)) (proj₂ (exec-abstract i ls alloc))
                        (proj₁ step)
    in proj₁ rest , ≤-trans (proj₂ step) (proj₂ rest)

  wf-case : ∀ (mv : Maybe (StoredValue FS)) (f g : AbstractTrace)
              (ls : LocState FS) (alloc : AllocState {FS})
          → StoreWF (next-heap-ref alloc) ls → Preserves ls alloc (exec-case-dispatch mv f g ls alloc)
  wf-case (just (SV-Tag zero))    f g ls alloc wf = wf-trace f ls alloc wf
  wf-case (just (SV-Tag (suc _))) f g ls alloc wf = wf-trace g ls alloc wf
  wf-case (just (SV-Ptr _))       f g ls alloc wf = wf-halt wf , ≤-refl
  wf-case (just (SV-Lit _ _))     f g ls alloc wf = wf-halt wf , ≤-refl
  wf-case (just (SV-Code _))      f g ls alloc wf = wf-halt wf , ≤-refl
  wf-case nothing                 f g ls alloc wf = wf-halt wf , ≤-refl

  -- Mirrors `exec-loop`'s own TERMINATING recursion (fuel decreases, but the
  -- decrease is lost across the `exec-trace body` boundary — same argument).
  {-# TERMINATING #-}
  wf-loop : ∀ (fuel : ℕ) (body : AbstractTrace) (ls : LocState FS) (alloc : AllocState {FS})
          → StoreWF (next-heap-ref alloc) ls → Preserves ls alloc (exec-loop fuel body ls alloc)
  wf-loop zero body ls alloc wf = wf-halt wf , ≤-refl
  wf-loop (suc n) body ls alloc wf with halted ls
  ... | true  = wf , ≤-refl
  ... | false with readReg (regs ls) Scratch
  ...   | SV-Tag zero    = wf , ≤-refl
  ...   | SV-Tag (suc m) = wf-loop-go n body ls alloc wf
  ...   | SV-Ptr _       = wf-loop-go n body ls alloc wf
  ...   | SV-Lit _ _     = wf-loop-go n body ls alloc wf
  ...   | SV-Code _      = wf-loop-go n body ls alloc wf

  -- one iteration: run the body, RE-ANCHOR the stack/frame (the loop restores
  -- them), recurse on fuel. The re-anchored stack is the PRE-state's, so its
  -- values need the frontier monotonicity the body's step provides.
  wf-loop-go : ∀ (n : ℕ) (body : AbstractTrace) (ls : LocState FS) (alloc : AllocState {FS})
             → StoreWF (next-heap-ref alloc) ls
             → Preserves ls alloc
                 (exec-loop n body
                   (record (proj₁ (exec-trace body ls alloc)) { stackMem = stackMem ls })
                   (record (proj₂ (exec-trace body ls alloc))
                     { current-frame = current-frame alloc ; next-slot = next-slot alloc }))
  wf-loop-go n body ls alloc wf =
    proj₁ rec , ≤-trans (proj₂ step) (proj₂ rec)
    where
      step = wf-trace body ls alloc wf
      ls'  = proj₁ (exec-trace body ls alloc)
      al'  = proj₂ (exec-trace body ls alloc)
      ls'' = record ls' { stackMem = stackMem ls }
      al'' = record al' { current-frame = current-frame alloc ; next-slot = next-slot alloc }
      wf'' : StoreWF (next-heap-ref al'') ls''
      wf'' = record
        { wf-regs  = wf-regs (proj₁ step)
        ; wf-heap  = wf-heap (proj₁ step)
        ; wf-stack = λ f k → svm-mono (stackMem ls f k) (proj₂ step) (wf-stack wf f k)
        ; wf-fresh = wf-fresh (proj₁ step) }
      rec = wf-loop n body ls'' al'' wf''

------------------------------------------------------------------------
-- Lifted to the FLAT machine: the same invariant, indexed by a FlatState.
------------------------------------------------------------------------
FlatWF : FlatState → Set
FlatWF fs = StoreWF (next-heap-ref (falloc fs)) (floc fs)

wf-jump : ∀ (mpc : Maybe ℕ) (fs : FlatState) → FlatWF fs → FlatWF (do-jump mpc fs)
wf-jump (just pc') fs wf = wf
wf-jump nothing    fs wf = wf-halt wf

wf-branch : ∀ (b : Bool) (m : ℕ) (prog : AbstractTrace) (fs : FlatState)
          → FlatWF fs → FlatWF (do-branch b m prog fs)
wf-branch true  m prog fs wf = wf-jump (find-label prog m) fs wf
wf-branch false m prog fs wf = wf

-- ONE flat step preserves store well-formedness. Control flow only moves the
-- pc (or halts); everything else is `exec-abstract`, i.e. `wf-abstract`.
flat-wf-step : ∀ (i : AbstractInstr) (prog : AbstractTrace) (fs : FlatState)
             → FlatWF fs → FlatWF (flat-exec-instr i prog fs)
flat-wf-step (instr-ctrl (c-label m))               prog fs wf = wf
flat-wf-step (instr-ctrl (c-jmp m))                 prog fs wf = wf-jump (find-label prog m) fs wf
flat-wf-step (instr-ctrl (c-branch-scratch-zero m)) prog fs wf =
  wf-branch (sv-is-zero (readReg (regs (floc fs)) Scratch)) m prog fs wf
flat-wf-step (instr-ctrl (c-branch-tag-zero m))     prog fs wf =
  wf-branch (tag-zf (flat-read-tag (floc fs))) m prog fs wf
-- The straight-line cases are ENUMERATED (a catch-all would not reduce
-- `flat-exec-instr`'s own catch-all in the case tree); each is `wf-abstract`.
flat-wf-step mov-to-output            prog fs wf = proj₁ (wf-abstract mov-to-output (floc fs) (falloc fs) wf)
flat-wf-step mov-to-input             prog fs wf = proj₁ (wf-abstract mov-to-input (floc fs) (falloc fs) wf)
flat-wf-step mov-output-to-input2     prog fs wf = proj₁ (wf-abstract mov-output-to-input2 (floc fs) (falloc fs) wf)
flat-wf-step mov-input2-to-output     prog fs wf = proj₁ (wf-abstract mov-input2-to-output (floc fs) (falloc fs) wf)
flat-wf-step load-indirect            prog fs wf = proj₁ (wf-abstract load-indirect (floc fs) (falloc fs) wf)
flat-wf-step load-indirect-suc        prog fs wf = proj₁ (wf-abstract load-indirect-suc (floc fs) (falloc fs) wf)
flat-wf-step (load-from-slot k)       prog fs wf = proj₁ (wf-abstract (load-from-slot k) (floc fs) (falloc fs) wf)
flat-wf-step (store-at-slot k)        prog fs wf = proj₁ (wf-abstract (store-at-slot k) (floc fs) (falloc fs) wf)
flat-wf-step store-indirect           prog fs wf = proj₁ (wf-abstract store-indirect (floc fs) (falloc fs) wf)
flat-wf-step store-indirect-suc       prog fs wf = proj₁ (wf-abstract store-indirect-suc (floc fs) (falloc fs) wf)
flat-wf-step (lea-slot k)             prog fs wf = proj₁ (wf-abstract (lea-slot k) (floc fs) (falloc fs) wf)
flat-wf-step (restore-input k)        prog fs wf = proj₁ (wf-abstract (restore-input k) (floc fs) (falloc fs) wf)
flat-wf-step (lea-indexed k)          prog fs wf = proj₁ (wf-abstract (lea-indexed k) (floc fs) (falloc fs) wf)
flat-wf-step (instr-alloc-stack k)    prog fs wf = proj₁ (wf-abstract (instr-alloc-stack k) (floc fs) (falloc fs) wf)
-- Plan 0.61: the flat machine MOVES THE FRAME on dealloc-stack / pop-frame.
-- `StoreWF` is indexed by the allocation FRONTIER and quantifies over ALL
-- frames, so the move is invisible to it — only the frontier term has to be
-- transported through `leave-frame` (`enter-frame` is a record update, so
-- alloc-stack / push-frame need nothing).
flat-wf-step (instr-dealloc-stack k)  prog fs wf =
  subst (λ n → StoreWF n (proj₁ (exec-abstract (instr-dealloc-stack k) (floc fs) (falloc fs))))
        (sym (leave-frame-heap-ref (proj₂ (exec-abstract (instr-dealloc-stack k) (floc fs) (falloc fs)))))
        (proj₁ (wf-abstract (instr-dealloc-stack k) (floc fs) (falloc fs) wf))
flat-wf-step (instr-reclaim-to k)     prog fs wf = proj₁ (wf-abstract (instr-reclaim-to k) (floc fs) (falloc fs) wf)
flat-wf-step (instr-push-frame k)     prog fs wf = proj₁ (wf-abstract (instr-push-frame k) (floc fs) (falloc fs) wf)
flat-wf-step instr-pop-frame          prog fs wf =
  subst (λ n → StoreWF n (proj₁ (exec-abstract instr-pop-frame (floc fs) (falloc fs))))
        (sym (leave-frame-heap-ref (proj₂ (exec-abstract instr-pop-frame (floc fs) (falloc fs)))))
        (proj₁ (wf-abstract instr-pop-frame (floc fs) (falloc fs) wf))
flat-wf-step instr-call-closure       prog fs wf = proj₁ (wf-abstract instr-call-closure (floc fs) (falloc fs) wf)
flat-wf-step (worklist-init k)        prog fs wf = proj₁ (wf-abstract (worklist-init k) (floc fs) (falloc fs) wf)
flat-wf-step (worklist-push k)        prog fs wf = proj₁ (wf-abstract (worklist-push k) (floc fs) (falloc fs) wf)
flat-wf-step (worklist-pop k)         prog fs wf = proj₁ (wf-abstract (worklist-pop k) (floc fs) (falloc fs) wf)
flat-wf-step (worklist-check k)       prog fs wf = proj₁ (wf-abstract (worklist-check k) (floc fs) (falloc fs) wf)
flat-wf-step (instr-sigop si)         prog fs wf = proj₁ (wf-abstract (instr-sigop si) (floc fs) (falloc fs) wf)
flat-wf-step (instr-load-const p v)   prog fs wf = proj₁ (wf-abstract (instr-load-const p v) (floc fs) (falloc fs) wf)
flat-wf-step (instr-load-code-addr k) prog fs wf = proj₁ (wf-abstract (instr-load-code-addr k) (floc fs) (falloc fs) wf)
flat-wf-step instr-save-closure-reg   prog fs wf = proj₁ (wf-abstract instr-save-closure-reg (floc fs) (falloc fs) wf)
flat-wf-step (instr-load-tag-lit k)   prog fs wf = proj₁ (wf-abstract (instr-load-tag-lit k) (floc fs) (falloc fs) wf)
flat-wf-step (instr-case-on-tag f g)  prog fs wf = proj₁ (wf-abstract (instr-case-on-tag f g) (floc fs) (falloc fs) wf)
flat-wf-step (instr-alloc-heap k)     prog fs wf = proj₁ (wf-abstract (instr-alloc-heap k) (floc fs) (falloc fs) wf)
flat-wf-step (instr-loop body)        prog fs wf = proj₁ (wf-abstract (instr-loop body) (floc fs) (falloc fs) wf)
flat-wf-step (instr-reg-op op)        prog fs wf = proj₁ (wf-abstract (instr-reg-op op) (floc fs) (falloc fs) wf)
