-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatPtrBounds   (Plan 0.54 rung D, item 5)
--
-- EVERY DYNAMIC POINTER IN THE STATE IS IN-BOUNDS FOR ITS BLOCK — in the
-- PAIR form: the cell it addresses AND the next one are inside the block
-- (`suc (heap-offset hl) < block-size (ref-id (heap-ref hl))`).
--
-- This is the state invariant behind the flat↔x86-64 dereference residuals
-- `store-indirect{,-suc}-inbounds` and the in-bounds conjunct of
-- `load-indirect{,-suc}-target-wf` (D073): the correspondence needs the
-- store/load target to lie inside its block before `FlatCorr.dom-sized` can
-- turn it into the mapped-cell fact the block-steps consume.
--
-- WHY THE PAIR FORM: every producer of a heap pointer is `instr-alloc-heap n`
-- handing out the block START (offset 0) of a block of `n ≥ 2` cells — the
-- pair `⟨_,_⟩ Heap` (fst/snd), the sum node (tag/payload), the closure record
-- (env/code) and the cata payload-stack nodes are all 2-cell blocks — so the
-- invariant that is actually true is about the pair, and it is exactly what
-- the `-suc` residuals need (`heap-offset (sucHL hl) ≡ suc (heap-offset hl)`
-- definitionally).
--
-- WHY IT IS AN INVARIANT: `block-size` is written ONLY by `instr-alloc-heap`
-- (`size-with` — the fresh ref gets `n`, older refs keep their sizes), and the
-- freshness half of `FlatStoreWF` says no live value references the fresh ref
-- (every pointer's ref-id is BELOW the frontier, and the fresh block IS the
-- frontier's) — so an allocation cannot shrink the block under any pointer
-- the state holds. That is why the preservation lemma takes `StoreWF` as a
-- hypothesis; ConcFlatSim carries both invariants through one `Reachable`
-- induction.
--
-- The per-instruction premise `2 ≤ n` at an alloc site is the EMITTER's
-- discipline (`Once.CCC.Codegen.AllocMin` — every emitted `instr-alloc-heap`
-- is literally `instr-alloc-heap 2`). `instr-case-on-tag` is unemittable
-- since item 6 (`case` compiles to flat control). `lea-indexed` — the one
-- instruction that could fabricate an interior pointer — is UNEMITTABLE
-- (2026-08-01, `FrameFreeI`), so its route is `⊥`-elim.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatPtrBounds (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; n≤1+n; <⇒≢)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Once.Memory.HeapAddress
  using (HeapLocation; heap-loc; mkHeapRef; heap-ref; heap-offset; ref-id; _≟HL_)
open import Once.SigOp.Info using (SigOpInfo; effect; EffectShape; Pure; Emits; Halts)
open import Once.Type using (Type; FitsInReg; fits-in-reg?)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.Machine.SMCore
open FrameSemantics FS using (Frame; _≟F_)
open MemOps {FS}
open ExecFinal {FS}
open AbstractExec {FS}
open import Once.CCC.Machine.FrameFree using (FrameFreeI)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
-- the shared bricks: the register read-after-write enumeration and the
-- `writeLoc` fold-back
open import Once.CCC.Machine.FlatStackPtr FS using (readReg-write; writeLoc-dyn)
open import Once.CCC.Machine.FlatStoreWF FS
  using (StoreWF; wf-regs; wf-heap; wf-stack; sv-below; svm-below)

------------------------------------------------------------------------
-- The per-value predicate, over the block-size map alone (it reads NOTHING
-- from the LocState — unlike `StackPtrOK` there is no anchor to transport).
-- CATCHALL on the non-heap-pointer shapes, reducing on every constructor.
------------------------------------------------------------------------
PtrB : (ℕ → ℕ) → StoredValue FS → Set
PtrB bs (SV-Ptr (AtDynamic hl)) = suc (heap-offset hl) < bs (ref-id (heap-ref hl))
{-# CATCHALL #-}
PtrB bs _                       = ⊤

PtrB? : (ℕ → ℕ) → Maybe (StoredValue FS) → Set
PtrB? bs (just v) = PtrB bs v
PtrB? bs nothing  = ⊤

------------------------------------------------------------------------
-- The state invariant: registers, heap cells and stack cells alike (a load
-- moves memory into a register). Stated over the LocState with the block-size
-- map explicit; `PtrBoundsWF` is its FlatState instance.
------------------------------------------------------------------------
record PBInv (bs : ℕ → ℕ) (ls : LocState FS) : Set where
  constructor mkPtrBounds
  field
    pb-regs  : ∀ (r : AbstractReg) → PtrB bs (readReg (regs ls) r)
    pb-heap  : ∀ (hl : HeapLocation) → PtrB? bs (heapMem ls hl)
    pb-stack : ∀ (f : Frame) (k : Slot) → PtrB? bs (stackMem ls f k)
open PBInv public

PtrBoundsWF : FlatState → Set
PtrBoundsWF fs = PBInv (block-size (falloc fs)) (floc fs)

------------------------------------------------------------------------
-- THE USE-SITE FORMS: a register that holds a dynamic pointer addresses an
-- in-bounds pair — both the cell and its successor.
------------------------------------------------------------------------
ptr-bounds-suc : ∀ (fs : FlatState) (r : AbstractReg) (hl : HeapLocation)
               → PtrBoundsWF fs
               → readReg (regs (floc fs)) r ≡ SV-Ptr (AtDynamic hl)
               → suc (heap-offset hl) < block-size (falloc fs) (ref-id (heap-ref hl))
ptr-bounds-suc fs r hl wf eq = subst (PtrB _) eq (pb-regs wf r)

ptr-bounds-cell : ∀ (fs : FlatState) (r : AbstractReg) (hl : HeapLocation)
                → PtrBoundsWF fs
                → readReg (regs (floc fs)) r ≡ SV-Ptr (AtDynamic hl)
                → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))
ptr-bounds-cell fs r hl wf eq =
  ≤-trans (n≤1+n (suc (heap-offset hl))) (ptr-bounds-suc fs r hl wf eq)

------------------------------------------------------------------------
-- THE EXTENSION LEMMAS for `instr-alloc-heap`. `size-with n st bs` gives the
-- fresh ref `n` and keeps every other size; `sv-below st` (FlatStoreWF's
-- freshness) is what puts every live pointer's ref STRICTLY below `st`.
------------------------------------------------------------------------
size-with-new : ∀ (n st : ℕ) (bs : ℕ → ℕ) → size-with n st bs st ≡ n
size-with-new n st bs with st ≟ st
... | yes _  = refl
... | no ¬p  = ⊥-elim (¬p refl)

size-with-old : ∀ (n st : ℕ) (bs : ℕ → ℕ) (r : ℕ) → ¬ (r ≡ st)
              → size-with n st bs r ≡ bs r
size-with-old n st bs r ne with r ≟ st
... | yes p = ⊥-elim (ne p)
... | no _  = refl

ptrb-ext : ∀ (n st : ℕ) (bs : ℕ → ℕ) (v : StoredValue FS)
         → sv-below st v → PtrB bs v → PtrB (size-with n st bs) v
ptrb-ext n st bs (SV-Ptr (AtDynamic hl)) fr b =
  subst (suc (heap-offset hl) <_)
        (sym (size-with-old n st bs (ref-id (heap-ref hl)) (<⇒≢ fr))) b
ptrb-ext n st bs (SV-Ptr (AtStack _ _)) _ _ = tt
ptrb-ext n st bs (SV-Tag _)             _ _ = tt
ptrb-ext n st bs (SV-Lit _ _)           _ _ = tt
ptrb-ext n st bs (SV-Code _)            _ _ = tt

pbm-ext : ∀ (n st : ℕ) (bs : ℕ → ℕ) (mv : Maybe (StoredValue FS))
        → svm-below st mv → PtrB? bs mv → PtrB? (size-with n st bs) mv
pbm-ext n st bs (just v) fr b = ptrb-ext n st bs v fr b
pbm-ext n st bs nothing  _ _  = tt

------------------------------------------------------------------------
-- BRICKS. `PtrB` reads nothing from the LocState, so — unlike `SPInv` — no
-- anchor transports: each brick is the read-back case split alone.
------------------------------------------------------------------------
pb-halt : ∀ (bs : ℕ → ℕ) (ls : LocState FS) (b : Bool)
        → PBInv bs ls → PBInv bs (record ls { halted = b })
pb-halt bs ls b wf = record
  { pb-regs = pb-regs wf ; pb-heap = pb-heap wf ; pb-stack = pb-stack wf }

pb-write-reg : ∀ (bs : ℕ → ℕ) (ls : LocState FS) (x : AbstractReg) (v : StoredValue FS)
             → PtrB bs v → PBInv bs ls
             → PBInv bs (record ls { regs = writeReg (regs ls) x v })
pb-write-reg bs ls x v ok wf = record
  { pb-regs  = λ r → go r (readReg-write (regs ls) x r v)
  ; pb-heap  = pb-heap wf
  ; pb-stack = pb-stack wf }
  where
    go : ∀ (r : AbstractReg)
       → (readReg (writeReg (regs ls) x v) r ≡ v)
       ⊎ (readReg (writeReg (regs ls) x v) r ≡ readReg (regs ls) r)
       → PtrB bs (readReg (writeReg (regs ls) x v) r)
    go r (inj₁ eq) rewrite eq = ok
    go r (inj₂ eq) rewrite eq = pb-regs wf r

pb-write-reg-halt : ∀ (bs : ℕ → ℕ) (ls : LocState FS) (x : AbstractReg)
                      (v : StoredValue FS) (b : Bool)
                  → PtrB bs v → PBInv bs ls
                  → PBInv bs (record ls { regs = writeReg (regs ls) x v ; halted = b })
pb-write-reg-halt bs ls x v b ok wf =
  pb-halt bs (record ls { regs = writeReg (regs ls) x v }) b
          (pb-write-reg bs ls x v ok wf)

pb-wsm-aux : ∀ {bs : ℕ → ℕ} {f f' : Frame} {k k' : Slot}
             (df : Dec (f ≡ f')) (dk : Dec (k ≡ k'))
             (old : Maybe (StoredValue FS)) (v : StoredValue FS)
           → PtrB? bs old → PtrB bs v
           → PtrB? bs (writeStackMem-aux df dk old v)
pb-wsm-aux (no _)  _       old v po pv = po
pb-wsm-aux (yes _) (yes _) old v po pv = pv
pb-wsm-aux (yes _) (no _)  old v po pv = po

pb-whm-aux : ∀ {bs : ℕ → ℕ} {hl hl' : HeapLocation}
             (d : Dec (hl ≡ hl'))
             (old : Maybe (StoredValue FS)) (v : StoredValue FS)
           → PtrB? bs old → PtrB bs v
           → PtrB? bs (writeHeapMem-aux d old v)
pb-whm-aux (yes _) old v po pv = pv
pb-whm-aux (no _)  old v po pv = po

pb-write-stack : ∀ (bs : ℕ → ℕ) (ls : LocState FS) (f : Frame) (k : Slot) (v : StoredValue FS)
               → PtrB bs v → PBInv bs ls
               → PBInv bs (writeLocToStack ls f k v)
pb-write-stack bs ls f k v ok wf = record
  { pb-regs  = pb-regs wf
  ; pb-heap  = pb-heap wf
  ; pb-stack = λ f' k' → pb-wsm-aux (f ≟F f') (k ≟ k') (stackMem ls f' k') v
                                    (pb-stack wf f' k') ok }

pb-write-heap : ∀ (bs : ℕ → ℕ) (ls : LocState FS) (hl : HeapLocation) (v : StoredValue FS)
              → PtrB bs v → PBInv bs ls
              → PBInv bs (writeLocToHeap ls hl v)
pb-write-heap bs ls hl v ok wf = record
  { pb-regs  = pb-regs wf
  ; pb-heap  = λ hl' → pb-whm-aux (hl ≟HL hl') (heapMem ls hl') v
                                  (pb-heap wf hl') ok
  ; pb-stack = pb-stack wf }

pb-write-mem : ∀ (bs : ℕ → ℕ) (ls : LocState FS) (loc : ValueLocation FS) (v : StoredValue FS)
             → PtrB bs v → PBInv bs ls
             → PBInv bs (writeLoc ls loc v)
pb-write-mem bs ls (AtStack f k)  v ok wf = pb-write-stack bs ls f k v ok wf
pb-write-mem bs ls (AtDynamic hl) v ok wf =
  subst (PBInv bs) (sym (writeLoc-dyn ls hl v)) (pb-write-heap bs ls hl v ok wf)

pb-read-loc : ∀ (bs : ℕ → ℕ) (ls : LocState FS) → PBInv bs ls
            → ∀ (loc : ValueLocation FS) → PtrB? bs (readLoc ls loc)
pb-read-loc bs ls wf (AtStack f k)  = pb-stack wf f k
pb-read-loc bs ls wf (AtDynamic hl) = pb-heap wf hl

------------------------------------------------------------------------
-- The aux-style helpers `exec-abstract` routes through.
------------------------------------------------------------------------
pb-load-value : ∀ (bs : ℕ → ℕ) (ls : LocState FS) (dst : AbstractReg)
                  (mv : Maybe (StoredValue FS))
              → PtrB? bs mv → PBInv bs ls
              → PBInv bs (exec-load-with-value dst mv ls)
pb-load-value bs ls dst (just v) ok wf = pb-write-reg bs ls dst v ok wf
pb-load-value bs ls dst nothing  ok wf = pb-halt bs ls true wf

pb-load-resolved : ∀ (bs : ℕ → ℕ) (ls : LocState FS) (dst : AbstractReg)
                     (ml : Maybe (ValueLocation FS))
                 → PBInv bs ls
                 → PBInv bs (exec-load-via-resolved dst ml ls)
pb-load-resolved bs ls dst nothing    wf = pb-halt bs ls true wf
pb-load-resolved bs ls dst (just loc) wf =
  pb-load-value bs ls dst (readLoc ls loc) (pb-read-loc bs ls wf loc) wf

pb-load-suc-resolved : ∀ (bs : ℕ → ℕ) (ls : LocState FS) (dst : AbstractReg)
                         (ml : Maybe (ValueLocation FS))
                     → PBInv bs ls
                     → PBInv bs (exec-load-suc-via-resolved dst ml ls)
pb-load-suc-resolved bs ls dst nothing    wf = pb-halt bs ls true wf
pb-load-suc-resolved bs ls dst (just loc) wf =
  pb-load-value bs ls dst (readLoc ls (sucLoc loc))
                (pb-read-loc bs ls wf (sucLoc loc)) wf

pb-store-resolved : ∀ (bs : ℕ → ℕ) (ls : LocState FS)
                      (ml : Maybe (ValueLocation FS)) (v : StoredValue FS)
                  → PtrB bs v → PBInv bs ls
                  → PBInv bs (exec-store-via-resolved ml v ls)
pb-store-resolved bs ls nothing    v ok wf = pb-halt bs ls true wf
pb-store-resolved bs ls (just loc) v ok wf = pb-write-mem bs ls loc v ok wf

pb-store-suc-resolved : ∀ (bs : ℕ → ℕ) (ls : LocState FS)
                          (ml : Maybe (ValueLocation FS)) (v : StoredValue FS)
                      → PtrB bs v → PBInv bs ls
                      → PBInv bs (exec-store-suc-via-resolved ml v ls)
pb-store-suc-resolved bs ls nothing    v ok wf = pb-halt bs ls true wf
pb-store-suc-resolved bs ls (just loc) v ok wf = pb-write-mem bs ls (sucLoc loc) v ok wf

pb-from-slot : ∀ (ls : LocState FS) (alloc : AllocState {FS}) (mv : Maybe (StoredValue FS))
             → PtrB? (block-size alloc) mv
             → PBInv (block-size alloc) ls
             → PBInv (block-size (proj₂ (exec-load-from-slot-with-value mv ls alloc)))
                     (proj₁ (exec-load-from-slot-with-value mv ls alloc))
pb-from-slot ls alloc (just v) ok wf = pb-write-reg (block-size alloc) ls Output v ok wf
pb-from-slot ls alloc nothing  ok wf = pb-halt (block-size alloc) ls true wf

pb-restore : ∀ (ls : LocState FS) (alloc : AllocState {FS}) (mv : Maybe (StoredValue FS))
           → PtrB? (block-size alloc) mv
           → PBInv (block-size alloc) ls
           → PBInv (block-size (proj₂ (exec-restore-input-with-value mv ls alloc)))
                   (proj₁ (exec-restore-input-with-value mv ls alloc))
pb-restore ls alloc (just v) ok wf = pb-write-reg (block-size alloc) ls Input1 v ok wf
pb-restore ls alloc nothing  ok wf = pb-halt (block-size alloc) ls true wf

-- `sv-pred` / `sv-succ` produce a TAG on every input shape.
pb-pred : ∀ (bs : ℕ → ℕ) (v : StoredValue FS) → PtrB bs (sv-pred v)
pb-pred bs (SV-Tag zero)    = tt
pb-pred bs (SV-Tag (suc m)) = tt
pb-pred bs (SV-Ptr l)       = tt
pb-pred bs (SV-Lit p x)     = tt
pb-pred bs (SV-Code c)      = tt

pb-succ : ∀ (bs : ℕ → ℕ) (v : StoredValue FS) → PtrB bs (sv-succ v)
pb-succ bs (SV-Tag m)   = tt
pb-succ bs (SV-Ptr l)   = tt
pb-succ bs (SV-Lit p x) = tt
pb-succ bs (SV-Code c)  = tt

pb-reg-op : ∀ (bs : ℕ → ℕ) (ls : LocState FS) (op : RegOp)
          → PBInv bs ls → PBInv bs (exec-reg-op op ls)
pb-reg-op bs ls scratch-one        wf = pb-write-reg bs ls Scratch (SV-Tag 1) tt wf
pb-reg-op bs ls scratch-zero       wf = pb-write-reg bs ls Scratch (SV-Tag 0) tt wf
pb-reg-op bs ls scratch-dec        wf =
  pb-write-reg bs ls Scratch (sv-pred (readReg (regs ls) Scratch))
               (pb-pred bs (readReg (regs ls) Scratch)) wf
pb-reg-op bs ls scratch-load-count wf =
  pb-write-reg bs ls Scratch (readReg (regs ls) Count) (pb-regs wf Count) wf
pb-reg-op bs ls count-zero         wf = pb-write-reg bs ls Count (SV-Tag 0) tt wf
pb-reg-op bs ls count-inc          wf =
  pb-write-reg bs ls Count (sv-succ (readReg (regs ls) Count))
               (pb-succ bs (readReg (regs ls) Count)) wf

------------------------------------------------------------------------
-- THE SIGOP OUTPUT: `Emits`/`Halts` produce `unit-storedvalue`; a `Pure`
-- SigOp's register-fittable output is a literal; the non-fittable case gets
-- the companion axiom below — the same trusted base as
-- `structured-pure-sigop-output` itself (D061), and the same shape as
-- `FlatStoreWF.structured-pure-sigop-below` / `FlatStackPtr`'s `-no-stack`.
------------------------------------------------------------------------
postulate
  structured-pure-sigop-inbounds :
    ∀ (bs : ℕ → ℕ) {A B} (si : SigOpInfo A B) (ls : LocState FS)
    → PtrB bs (structured-pure-sigop-output si ls)

sigop-output-pb : ∀ (bs : ℕ → ℕ) {A B} (si : SigOpInfo A B) (ls : LocState FS)
                → PtrB bs (exec-sigop-output si ls)
sigop-output-pb bs {A} {B} si ls = go (effect si)
  where
    pov : ∀ (fitB : FitsInReg B) (ma : Maybe ⟦ A ⟧)
        → PtrB bs (pure-sigop-out-val si fitB ma)
    pov fitB (just a) = tt
    pov fitB nothing  = tt
    aux : ∀ (mf : Maybe (FitsInReg B)) (ml : Maybe (ValueLocation FS))
        → PtrB bs (pure-sigop-out-aux si ls mf ml)
    aux (just fitB) (just in-loc) = pov fitB (readTyped A in-loc ls)
    aux (just fitB) nothing       = pov fitB (readReg-typed A (readReg (regs ls) Input1))
    aux nothing     _             = structured-pure-sigop-inbounds bs si ls
    go : ∀ (e : EffectShape B) → PtrB bs (exec-sigop-output-of e si ls)
    go Pure      = aux (fits-in-reg? B) (sv-as-loc (readReg (regs ls) Input1))
    go (Emits _) = tt
    go (Halts _) = tt

------------------------------------------------------------------------
-- THE PER-INSTRUCTION PRESERVATION over the structured semantics. The one
-- clause with content is `instr-alloc-heap`: the fresh pointer is the pair
-- start of an `n ≥ 2` block (the emitter premise), and every OLD value keeps
-- its bound because its ref lies below the frontier (the `StoreWF` premise) —
-- `size-with` only writes the frontier's ref.
------------------------------------------------------------------------
pb-abstract : ∀ (i : AbstractInstr) (ls : LocState FS) (alloc : AllocState {FS})
            → FrameFreeI i
            → (∀ n → i ≡ instr-alloc-heap n → 2 ≤ n)
            → StoreWF (next-heap-ref alloc) ls
            → PBInv (block-size alloc) ls
            → PBInv (block-size (proj₂ (exec-abstract i ls alloc)))
                    (proj₁ (exec-abstract i ls alloc))
pb-abstract mov-to-output ls alloc ff am wfS wf =
  pb-write-reg _ ls Output (readReg (regs ls) Input1) (pb-regs wf Input1) wf
pb-abstract mov-to-input ls alloc ff am wfS wf =
  pb-write-reg _ ls Input1 (readReg (regs ls) Output) (pb-regs wf Output) wf
pb-abstract mov-output-to-input2 ls alloc ff am wfS wf =
  pb-write-reg _ ls Input2 (readReg (regs ls) Output) (pb-regs wf Output) wf
pb-abstract mov-input2-to-output ls alloc ff am wfS wf =
  pb-write-reg _ ls Output (readReg (regs ls) Input2) (pb-regs wf Input2) wf
pb-abstract load-indirect ls alloc ff am wfS wf =
  pb-load-resolved _ ls Output (sv-as-loc (readReg (regs ls) Input1)) wf
pb-abstract load-indirect-suc ls alloc ff am wfS wf =
  pb-load-suc-resolved _ ls Output (sv-as-loc (readReg (regs ls) Input1)) wf
pb-abstract (load-from-slot slot) ls alloc ff am wfS wf =
  pb-from-slot ls alloc (readLoc ls (AtStack (current-frame alloc) slot))
               (pb-read-loc _ ls wf (AtStack (current-frame alloc) slot)) wf
pb-abstract (store-at-slot slot) ls alloc ff am wfS wf =
  pb-write-mem _ ls (AtStack (current-frame alloc) slot)
               (readReg (regs ls) Output) (pb-regs wf Output) wf
pb-abstract store-indirect ls alloc ff am wfS wf =
  pb-store-resolved _ ls (sv-as-loc (readReg (regs ls) Input1))
                    (readReg (regs ls) Output) (pb-regs wf Output) wf
pb-abstract store-indirect-suc ls alloc ff am wfS wf =
  pb-store-suc-resolved _ ls (sv-as-loc (readReg (regs ls) Input1))
                        (readReg (regs ls) Output) (pb-regs wf Output) wf
-- a stack pointer is unconstrained by this invariant
pb-abstract (lea-slot slot) ls alloc ff am wfS wf =
  pb-write-reg _ ls Output (SV-Ptr (AtStack (current-frame alloc) slot)) tt wf
pb-abstract (restore-input slot) ls alloc ff am wfS wf =
  pb-restore ls alloc (readLoc ls (AtStack (current-frame alloc) slot))
             (pb-read-loc _ ls wf (AtStack (current-frame alloc) slot)) wf
-- `lea-indexed` is unemittable (2026-08-01) — `⊥` in `FrameFreeI`
pb-abstract (lea-indexed slot) ls alloc () am wfS wf
-- the frame ops and the loop are unemittable — `⊥` in `FrameFreeI`
pb-abstract (instr-alloc-stack n)   ls alloc () am wfS wf
pb-abstract (instr-dealloc-stack n) ls alloc () am wfS wf
pb-abstract (instr-push-frame cap)  ls alloc () am wfS wf
pb-abstract instr-pop-frame         ls alloc () am wfS wf
pb-abstract (instr-loop body)       ls alloc () am wfS wf
-- the case is unemittable since item 6 (`case` compiles to flat control)
pb-abstract (instr-case-on-tag f g) ls alloc () am wfS wf
pb-abstract (instr-reclaim-to n)  ls alloc ff am wfS wf = wf
pb-abstract instr-call-closure    ls alloc ff am wfS wf = wf
pb-abstract (worklist-init slot)  ls alloc ff am wfS wf = wf
pb-abstract (worklist-push slot)  ls alloc ff am wfS wf =
  pb-write-mem _ ls (AtStack (current-frame alloc) slot)
               (readReg (regs ls) Output) (pb-regs wf Output) wf
pb-abstract (worklist-pop slot)   ls alloc ff am wfS wf =
  pb-from-slot ls alloc (readLoc ls (AtStack (current-frame alloc) slot))
               (pb-read-loc _ ls wf (AtStack (current-frame alloc) slot)) wf
pb-abstract (worklist-check slot) ls alloc ff am wfS wf = wf
pb-abstract (instr-sigop si) ls alloc ff am wfS wf =
  pb-write-reg-halt _ ls Output (exec-sigop-output si ls) (exec-sigop-halts si ls)
                    (sigop-output-pb _ si ls) wf
pb-abstract (instr-load-const p v)   ls alloc ff am wfS wf =
  pb-write-reg _ ls Output (SV-Lit p v) tt wf
pb-abstract (instr-load-code-addr n) ls alloc ff am wfS wf =
  pb-write-reg _ ls Output (SV-Code n) tt wf
pb-abstract instr-save-closure-reg   ls alloc ff am wfS wf = wf
pb-abstract (instr-load-tag-lit n)   ls alloc ff am wfS wf =
  pb-write-reg _ ls Output (SV-Tag n) tt wf
-- THE PRODUCER: fresh block start, `n ≥ 2` cells (the emitter premise);
-- everything old keeps its size (`StoreWF` freshness + `size-with-old`).
pb-abstract (instr-alloc-heap n) ls alloc ff am wfS wf = record
  { pb-regs  = λ r → go r (readReg-write (regs ls) Output r fresh)
  ; pb-heap  = λ hl → pbm-ext n st bs (heapMem ls hl) (wf-heap wfS hl) (pb-heap wf hl)
  ; pb-stack = λ f k → pbm-ext n st bs (stackMem ls f k) (wf-stack wfS f k) (pb-stack wf f k) }
  where
    st = next-heap-ref alloc
    bs = block-size alloc
    fresh : StoredValue FS
    fresh = SV-Ptr (AtDynamic (heap-loc (mkHeapRef st) 0))
    fresh-ok : PtrB (size-with n st bs) fresh
    fresh-ok = subst (1 <_) (sym (size-with-new n st bs)) (am n refl)
    go : ∀ (r : AbstractReg)
       → (readReg (writeReg (regs ls) Output fresh) r ≡ fresh)
       ⊎ (readReg (writeReg (regs ls) Output fresh) r ≡ readReg (regs ls) r)
       → PtrB (size-with n st bs) (readReg (writeReg (regs ls) Output fresh) r)
    go r (inj₁ eq) rewrite eq = fresh-ok
    go r (inj₂ eq) rewrite eq = ptrb-ext n st bs (readReg (regs ls) r) (wf-regs wfS r) (pb-regs wf r)
pb-abstract (instr-reg-op op)        ls alloc ff am wfS wf =
  pb-reg-op _ ls op wf
pb-abstract (instr-ctrl c)           ls alloc ff am wfS wf = wf

------------------------------------------------------------------------
-- Lifted to the FLAT machine. The control cases move `fpc`/`halted` only;
-- the straight-line cases are `pb-abstract`; the unemittable instructions and
-- the case are `⊥`-elim / excluded. Enumerated — a catch-all would not reduce
-- `flat-exec-instr`'s own catch-all in the case tree.
------------------------------------------------------------------------
pb-jump : ∀ (mpc : Maybe ℕ) (fs : FlatState)
        → PtrBoundsWF fs → PtrBoundsWF (do-jump mpc fs)
pb-jump (just pc') fs wf = wf
pb-jump nothing    fs wf = pb-halt _ (floc fs) true wf

pb-branch : ∀ (b : Bool) (m : ℕ) (prog : AbstractTrace) (fs : FlatState)
          → PtrBoundsWF fs → PtrBoundsWF (do-branch b m prog fs)
pb-branch true  m prog fs wf = pb-jump (find-label prog m) fs wf
pb-branch false m prog fs wf = wf

flat-ptr-bounds : ∀ (i : AbstractInstr) (prog : AbstractTrace) (fs : FlatState)
                → FrameFreeI i
                → (∀ n → i ≡ instr-alloc-heap n → 2 ≤ n)
                → StoreWF (next-heap-ref (falloc fs)) (floc fs)
                → PtrBoundsWF fs → PtrBoundsWF (flat-exec-instr i prog fs)
flat-ptr-bounds (instr-ctrl (c-label m))               prog fs ff am wfS wf = wf
flat-ptr-bounds (instr-ctrl (c-jmp m))                 prog fs ff am wfS wf =
  pb-jump (find-label prog m) fs wf
flat-ptr-bounds (instr-ctrl (c-branch-scratch-zero m)) prog fs ff am wfS wf =
  pb-branch (sv-is-zero (readReg (regs (floc fs)) Scratch)) m prog fs wf
flat-ptr-bounds (instr-ctrl (c-branch-tag-zero m))     prog fs ff am wfS wf =
  pb-branch (tag-zf (flat-read-tag (floc fs))) m prog fs wf
flat-ptr-bounds (instr-alloc-stack n)   prog fs () am wfS wf
flat-ptr-bounds (instr-dealloc-stack n) prog fs () am wfS wf
flat-ptr-bounds (instr-push-frame cap)  prog fs () am wfS wf
flat-ptr-bounds instr-pop-frame         prog fs () am wfS wf
flat-ptr-bounds (instr-loop body)       prog fs () am wfS wf
flat-ptr-bounds (lea-indexed k)         prog fs () am wfS wf
flat-ptr-bounds (instr-case-on-tag f g) prog fs () am wfS wf
flat-ptr-bounds mov-to-output            prog fs ff am wfS wf =
  pb-abstract mov-to-output (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds mov-to-input             prog fs ff am wfS wf =
  pb-abstract mov-to-input (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds mov-output-to-input2     prog fs ff am wfS wf =
  pb-abstract mov-output-to-input2 (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds mov-input2-to-output     prog fs ff am wfS wf =
  pb-abstract mov-input2-to-output (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds load-indirect            prog fs ff am wfS wf =
  pb-abstract load-indirect (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds load-indirect-suc        prog fs ff am wfS wf =
  pb-abstract load-indirect-suc (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (load-from-slot k)       prog fs ff am wfS wf =
  pb-abstract (load-from-slot k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (store-at-slot k)        prog fs ff am wfS wf =
  pb-abstract (store-at-slot k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds store-indirect           prog fs ff am wfS wf =
  pb-abstract store-indirect (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds store-indirect-suc       prog fs ff am wfS wf =
  pb-abstract store-indirect-suc (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (lea-slot k)             prog fs ff am wfS wf =
  pb-abstract (lea-slot k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (restore-input k)        prog fs ff am wfS wf =
  pb-abstract (restore-input k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (instr-reclaim-to k)     prog fs ff am wfS wf =
  pb-abstract (instr-reclaim-to k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds instr-call-closure       prog fs ff am wfS wf =
  pb-abstract instr-call-closure (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (worklist-init k)        prog fs ff am wfS wf =
  pb-abstract (worklist-init k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (worklist-push k)        prog fs ff am wfS wf =
  pb-abstract (worklist-push k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (worklist-pop k)         prog fs ff am wfS wf =
  pb-abstract (worklist-pop k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (worklist-check k)       prog fs ff am wfS wf =
  pb-abstract (worklist-check k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (instr-sigop si)         prog fs ff am wfS wf =
  pb-abstract (instr-sigop si) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (instr-load-const p v)   prog fs ff am wfS wf =
  pb-abstract (instr-load-const p v) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (instr-load-code-addr k) prog fs ff am wfS wf =
  pb-abstract (instr-load-code-addr k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds instr-save-closure-reg   prog fs ff am wfS wf =
  pb-abstract instr-save-closure-reg (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (instr-load-tag-lit k)   prog fs ff am wfS wf =
  pb-abstract (instr-load-tag-lit k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (instr-alloc-heap k)     prog fs ff am wfS wf =
  pb-abstract (instr-alloc-heap k) (floc fs) (falloc fs) ff am wfS wf
flat-ptr-bounds (instr-reg-op op)        prog fs ff am wfS wf =
  pb-abstract (instr-reg-op op) (floc fs) (falloc fs) ff am wfS wf
