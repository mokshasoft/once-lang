-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatStackPtr   (Plan 0.54 rung D, item 2)
--
-- EVERY STACK POINTER IN THE STATE ADDRESSES A LIVE PAIR OF THE CURRENT FRAME:
-- its frame IS `current-frame`, and BOTH its slot and the next one are inside
-- the live window (`suc k < frame-slots`).
--
-- This is the state invariant behind the flat↔x86-64 residuals
-- `stack-ptr-current` and `stack-ptr-current-suc` — "a pointer in `Input1`
-- targets the current frame's live slots" — which the correspondence needs
-- before it can treat a load or store through such a pointer as an ordinary
-- step (an older frame's slots would need `stack-eq` to reach beyond the
-- current frame, and there is no address for them).
--
-- WHY THE PAIR FORM (`suc k < frame-slots`, not `k < frame-slots`): every producer
-- of a stack pointer is a `lea-slot k` addressing the FIRST of two adjacent
-- slots the same prologue reserved — the pair `⟨_,_⟩ Stack` (fst/snd), the
-- closure record `curry _ Stack` (env/code), and the sum payload `inl`/`inr`
-- `Stack` (tag/payload). So the invariant that is actually true is about the
-- pair, and it yields the single-slot form for free.
--
-- WHY IT IS AN INVARIANT AT ALL (and was not, before today): the frame ops are
-- the only instructions that move `current-frame` or `frame-slots`, and
-- `ir-to-trace` emits none of them (`Once.CCC.Codegen.FrameFreeTrace`), so both
-- anchors are FIXED for the whole run. Under a moving frame this predicate
-- would be destroyed by every call.
--
-- THE PRESERVATION PROOF (`sp-abstract` / `flat-stack-ptr`) covers every
-- frame-free instruction EXCEPT `instr-case-on-tag`: one flat step there runs
-- whole NESTED branch traces, whose `lea-slot`s need pair bounds the emitter
-- states only for the MAIN trace (`SlotBudget` — `slot-of` is `nothing` on the
-- carrying instruction). That fragment is behind the `events-running-case`
-- model defect anyway; since item 6 (2026-08-01) `case` DOES compile to flat
-- control and `instr-case-on-tag` is in the unemittable set — its clauses
-- below are absurd on `FrameFreeI`. (`lea-indexed` needed a cursor
-- discipline here until 2026-08-01, when it turned out to be UNEMITTABLE —
-- the cata codegen walks heap-linked stacks — and joined `FrameFreeI`'s ⊥
-- set, taking the `lea-indexed-wf` residual with it.)
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatStackPtr (FS : FrameSemantics) where

open import Once.CCC.Label using (LabelId)

open import Data.Nat using (ℕ; zero; suc; _<_; _≟_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Once.Memory.HeapAddress using (HeapLocation; _≟HL_)
import Once.Allocator.AbstractInstance as AI
open import Once.SigOp.Info using (SigOpInfo; effect; EffectShape; Pure; Emits; Halts)
open import Once.Type using (Type; FitsInReg; fits-in-reg?)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.Machine.SMCore
open FrameSemantics FS using (Frame; _≟F_)
open MemOps {FS}
open ExecFinal {FS}
open AbstractExec {FS}
open import Once.CCC.Machine.FrameFree using (FrameFreeI; EmittableI)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}

------------------------------------------------------------------------
-- The per-value predicate. A CATCHALL for the non-stack-pointer shapes, which
-- still reduces on a concrete constructor — and reduces to the CONJUNCTION on
-- `SV-Ptr (AtStack f k)`, so a use site that has the register equation gets
-- both halves with no clash boilerplate.
------------------------------------------------------------------------
-- Plan 0.63 step 2b: THE PAYLOAD IS NOW TRIVIAL — *there is no stack
-- pointer at all*. The old payload ("addresses a live pair of the CURRENT
-- frame") could not survive a frame move, and the closure markers move the
-- frame; but a frame move cannot invalidate pointers that do not exist.
-- This is TRUE of emitted code because `exec-abstract (lea-slot slot)` is
-- the only producer of `SV-Ptr (AtStack …)` in the machine (`lea-indexed`
-- only moves an existing one, and it is retired), and all four `lea-slot`
-- sites in `ir-to-trace'` are Stack-mode clauses — so a HEAP-MODED trace
-- emits none (`Once.CCC.Codegen.NoLeaSlot`). The `lea-slot` clause below is
-- correspondingly unprovable, and its route is made absurd one level up in
-- `ConcFlatSim.stack-ptr-step`, where `RunAt` supplies `run-heap`.
StackPtrOK : StoredValue FS → Set
StackPtrOK (SV-Ptr (AtStack f k)) = ⊥
{-# CATCHALL #-}
StackPtrOK _                      = ⊤

-- …lifted to a memory cell (an unwritten cell holds no pointer at all)
StackPtrOK? : Maybe (StoredValue FS) → Set
StackPtrOK? (just v) = StackPtrOK v
StackPtrOK? nothing  = ⊤

------------------------------------------------------------------------
-- The state invariant: registers, heap cells and stack cells alike. All three
-- are needed — a load moves a value from memory into a register, so an
-- invariant about registers alone is not preserved.
--
-- Stated over the LocState alone (`SPInv`) — Plan 0.63 step 2b dropped the
-- frame anchor and the slot bound, which the trivial payload no longer
-- mentions. That is what lets the closure markers preserve it: a frame move
-- changes only the AllocState, which the invariant no longer reads.
-- `StackPtrWF` is its FlatState instance.
------------------------------------------------------------------------
record SPInv (ls : LocState FS) : Set where
  constructor mkStackPtrWF
  field
    sp-regs  : ∀ (r : AbstractReg)
             → StackPtrOK (readReg (regs ls) r)
    sp-heap  : ∀ (hl : HeapLocation)
             → StackPtrOK? (heapMem ls hl)
    sp-stack : ∀ (f : Frame) (k : Slot)
             → StackPtrOK? (stackMem ls f k)
open SPInv public

StackPtrWF : FlatState → Set
StackPtrWF fs = SPInv (floc fs)

------------------------------------------------------------------------
-- THE USE-SITE FORMS. `StackPtrOK … (SV-Ptr (AtStack f k))` now REDUCES TO
-- `⊥`, so a route that knows a register holds a stack pointer is refuted
-- outright: these keep their old signatures (nothing downstream changes)
-- but are now `⊥-elim`. That is the point — under heap mode the situation
-- they described cannot arise.
------------------------------------------------------------------------
stack-ptr-frame : ∀ (fs : FlatState) (r : AbstractReg) (f : Frame) (k : Slot)
                → StackPtrWF fs
                → readReg (regs (floc fs)) r ≡ SV-Ptr (AtStack f k)
                → f ≡ current-frame (falloc fs)
stack-ptr-frame fs r f k wf eq =
  ⊥-elim (subst (StackPtrOK) eq (sp-regs wf r))

-- the PAIR bound: the cell after it is live too
stack-ptr-suc-live : ∀ (fs : FlatState) (r : AbstractReg) (f : Frame) (k : Slot)
                   → StackPtrWF fs
                   → readReg (regs (floc fs)) r ≡ SV-Ptr (AtStack f k)
                   → ⊥
stack-ptr-suc-live fs r f k wf eq =
  ⊥-elim (subst (StackPtrOK) eq (sp-regs wf r))

-- …hence the cell itself is
stack-ptr-live : ∀ (fs : FlatState) (r : AbstractReg) (f : Frame) (k : Slot)
               → StackPtrWF fs
               → readReg (regs (floc fs)) r ≡ SV-Ptr (AtStack f k)
               → ⊥
stack-ptr-live fs r f k wf eq = stack-ptr-suc-live fs r f k wf eq

------------------------------------------------------------------------
-- BRICKS FOR THE PRESERVATION PROOF.
--
-- The step lemma is a per-instruction induction, but every case has the same
-- two moves: the ANCHORS (`current-frame`, `frame-slots`) do not move — a
-- frame-free instruction cannot touch either — and the VALUE written is one the
-- invariant already covers (read out of a register or a cell) or a freshly
-- built non-stack-pointer. These bricks are those two moves, stated once.
------------------------------------------------------------------------

-- Reading back a register after a write: either you get the written value, or
-- the write missed you. Enumerated, because `writeReg` dispatches on the
-- register, so each entry holds DEFINITIONALLY.
readReg-write : ∀ (rf : Registers FS) (x r : AbstractReg) (v : StoredValue FS)
              → (readReg (writeReg rf x v) r ≡ v) ⊎ (readReg (writeReg rf x v) r ≡ readReg rf r)
readReg-write rf Input1  Input1  v = inj₁ refl
readReg-write rf Input1  Input2  v = inj₂ refl
readReg-write rf Input1  Output  v = inj₂ refl
readReg-write rf Input1  Scratch v = inj₂ refl
readReg-write rf Input1  Count   v = inj₂ refl
readReg-write rf Input2  Input1  v = inj₂ refl
readReg-write rf Input2  Input2  v = inj₁ refl
readReg-write rf Input2  Output  v = inj₂ refl
readReg-write rf Input2  Scratch v = inj₂ refl
readReg-write rf Input2  Count   v = inj₂ refl
readReg-write rf Output  Input1  v = inj₂ refl
readReg-write rf Output  Input2  v = inj₂ refl
readReg-write rf Output  Output  v = inj₁ refl
readReg-write rf Output  Scratch v = inj₂ refl
readReg-write rf Output  Count   v = inj₂ refl
readReg-write rf Scratch Input1  v = inj₂ refl
readReg-write rf Scratch Input2  v = inj₂ refl
readReg-write rf Scratch Output  v = inj₂ refl
readReg-write rf Scratch Scratch v = inj₁ refl
readReg-write rf Scratch Count   v = inj₂ refl
readReg-write rf Count   Input1  v = inj₂ refl
readReg-write rf Count   Input2  v = inj₂ refl
readReg-write rf Count   Output  v = inj₂ refl
readReg-write rf Count   Scratch v = inj₂ refl
readReg-write rf Count   Count   v = inj₁ refl

-- Flipping the halt flag touches no field the invariant reads.
sp-halt : ∀ (cf : Frame) (ls : LocState FS) (b : Bool)
        → SPInv ls → SPInv (record ls { halted = b })
sp-halt cf ls b wf = record
  { sp-regs = sp-regs wf ; sp-heap = sp-heap wf ; sp-stack = sp-stack wf }

-- A register write of an OK value preserves the invariant. Since Plan 0.63
-- the predicate has no anchors at all — no frame, no slot count — so the
-- memory halves transport by `refl` and only the written register needs a
-- case.
sp-write-reg : ∀ (cf : Frame) (ls : LocState FS) (x : AbstractReg) (v : StoredValue FS)
             → StackPtrOK v
             → SPInv ls
             → SPInv (record ls { regs = writeReg (regs ls) x v })
sp-write-reg cf ls x v ok wf = record
  { sp-regs  = λ r → go r (readReg-write (regs ls) x r v)
  ; sp-heap  = λ hl → sp-heap wf hl
  ; sp-stack = λ f k → sp-stack wf f k }
  where
    go : ∀ (r : AbstractReg)
       → (readReg (writeReg (regs ls) x v) r ≡ v)
       ⊎ (readReg (writeReg (regs ls) x v) r ≡ readReg (regs ls) r)
       → StackPtrOK
                    (readReg (writeReg (regs ls) x v) r)
    go r (inj₁ eq) rewrite eq = ok
    go r (inj₂ eq) rewrite eq = sp-regs wf r

-- …and the SigOp shape: the same write with the halt flag set in the same
-- record update.
sp-write-reg-halt : ∀ (cf : Frame) (ls : LocState FS) (x : AbstractReg)
                      (v : StoredValue FS) (b : Bool)
                  → StackPtrOK v
                  → SPInv ls
                  → SPInv (record ls { regs = writeReg (regs ls) x v ; halted = b })
sp-write-reg-halt cf ls x v b ok wf =
  sp-halt cf (record ls { regs = writeReg (regs ls) x v }) b
          (sp-write-reg cf ls x v ok wf)

------------------------------------------------------------------------
-- MEMORY WRITES. `writeStackMem` / `writeHeapMem` are aux-style on the
-- equality decision, so the read-back is a case split on the SAME `Dec` the
-- write routed on — either the cell got the (OK) written value, or it kept its
-- old (OK) contents.
------------------------------------------------------------------------
sp-wsm-aux : ∀ {f f' : Frame} {k k' : Slot}
             (df : Dec (f ≡ f')) (dk : Dec (k ≡ k'))
             (old : Maybe (StoredValue FS)) (v : StoredValue FS)
           → StackPtrOK? old → StackPtrOK v
           → StackPtrOK? (writeStackMem-aux df dk old v)
sp-wsm-aux (no _)  _       old v po pv = po
sp-wsm-aux (yes _) (yes _) old v po pv = pv
sp-wsm-aux (yes _) (no _)  old v po pv = po

sp-whm-aux : ∀ {hl hl' : HeapLocation}
             (d : Dec (hl ≡ hl'))
             (old : Maybe (StoredValue FS)) (v : StoredValue FS)
           → StackPtrOK? old → StackPtrOK v
           → StackPtrOK? (writeHeapMem-aux d old v)
sp-whm-aux (yes _) old v po pv = pv
sp-whm-aux (no _)  old v po pv = po

sp-write-stack : ∀ (cf : Frame) (ls : LocState FS) (f : Frame) (k : Slot) (v : StoredValue FS)
               → StackPtrOK v
               → SPInv ls
               → SPInv (writeLocToStack ls f k v)
sp-write-stack cf ls f k v ok wf = record
  { sp-regs  = sp-regs wf
  ; sp-heap  = sp-heap wf
  ; sp-stack = λ f' k' → sp-wsm-aux (f ≟F f') (k ≟ k') (stackMem ls f' k') v
                                    (sp-stack wf f' k') ok }

sp-write-heap : ∀ (cf : Frame) (ls : LocState FS) (hl : HeapLocation) (v : StoredValue FS)
              → StackPtrOK v
              → SPInv ls
              → SPInv (writeLocToHeap ls hl v)
sp-write-heap cf ls hl v ok wf = record
  { sp-regs  = sp-regs wf
  ; sp-heap  = λ hl' → sp-whm-aux (hl ≟HL hl') (heapMem ls hl') v
                                  (sp-heap wf hl') ok
  ; sp-stack = sp-stack wf }

-- `writeLoc`'s `AtDynamic` clauses are ENUMERATED on the value (the store
-- guard); fold them back into the one heap write they all are now.
writeLoc-dyn : ∀ (ls : LocState FS) (hl : HeapLocation) (v : StoredValue FS)
             → writeLoc ls (AtDynamic hl) v ≡ writeLocToHeap ls hl v
writeLoc-dyn ls hl (SV-Ptr (AtStack f k))   = refl
writeLoc-dyn ls hl (SV-Ptr (AtDynamic hl')) = refl
writeLoc-dyn ls hl (SV-Tag t)               = refl
writeLoc-dyn ls hl (SV-Lit p x)             = refl
writeLoc-dyn ls hl (SV-Code c)              = refl

sp-write-mem : ∀ (cf : Frame) (ls : LocState FS) (loc : ValueLocation FS) (v : StoredValue FS)
             → StackPtrOK v
             → SPInv ls
             → SPInv (writeLoc ls loc v)
sp-write-mem cf ls (AtStack f k)  v ok wf = sp-write-stack cf ls f k v ok wf
sp-write-mem cf ls (AtDynamic hl) v ok wf =
  subst SPInv (sym (writeLoc-dyn ls hl v)) (sp-write-heap cf ls hl v ok wf)

-- What comes OUT of memory is covered by the invariant's memory halves.
sp-read-loc : ∀ (cf : Frame) (ls : LocState FS) → SPInv ls
            → ∀ (loc : ValueLocation FS)
            → StackPtrOK? (readLoc ls loc)
sp-read-loc cf ls wf (AtStack f k)  = sp-stack wf f k
sp-read-loc cf ls wf (AtDynamic hl) = sp-heap wf hl

------------------------------------------------------------------------
-- The aux-style helpers `exec-abstract` routes through, each enumerated on
-- its `Maybe` argument (the halt route is a record update on `halted`).
------------------------------------------------------------------------
sp-load-value : ∀ (cf : Frame) (ls : LocState FS) (dst : AbstractReg)
                  (mv : Maybe (StoredValue FS))
              → StackPtrOK? mv
              → SPInv ls
              → SPInv (exec-load-with-value dst mv ls)
sp-load-value cf ls dst (just v) ok wf = sp-write-reg cf ls dst v ok wf
sp-load-value cf ls dst nothing  ok wf = sp-halt cf ls true wf

sp-load-resolved : ∀ (cf : Frame) (ls : LocState FS) (dst : AbstractReg)
                     (ml : Maybe (ValueLocation FS))
                 → SPInv ls
                 → SPInv (exec-load-via-resolved dst ml ls)
sp-load-resolved cf ls dst nothing    wf = sp-halt cf ls true wf
sp-load-resolved cf ls dst (just loc) wf =
  sp-load-value cf ls dst (readLoc ls loc) (sp-read-loc cf ls wf loc) wf

sp-load-suc-resolved : ∀ (cf : Frame) (ls : LocState FS) (dst : AbstractReg)
                         (ml : Maybe (ValueLocation FS))
                     → SPInv ls
                     → SPInv (exec-load-suc-via-resolved dst ml ls)
sp-load-suc-resolved cf ls dst nothing    wf = sp-halt cf ls true wf
sp-load-suc-resolved cf ls dst (just loc) wf =
  sp-load-value cf ls dst (readLoc ls (sucLoc loc))
                (sp-read-loc cf ls wf (sucLoc loc)) wf

sp-store-resolved : ∀ (cf : Frame) (ls : LocState FS)
                      (ml : Maybe (ValueLocation FS)) (v : StoredValue FS)
                  → StackPtrOK v
                  → SPInv ls
                  → SPInv (exec-store-via-resolved ml v ls)
sp-store-resolved cf ls nothing    v ok wf = sp-halt cf ls true wf
sp-store-resolved cf ls (just loc) v ok wf = sp-write-mem cf ls loc v ok wf

sp-store-suc-resolved : ∀ (cf : Frame) (ls : LocState FS)
                          (ml : Maybe (ValueLocation FS)) (v : StoredValue FS)
                      → StackPtrOK v
                      → SPInv ls
                      → SPInv (exec-store-suc-via-resolved ml v ls)
sp-store-suc-resolved cf ls nothing    v ok wf = sp-halt cf ls true wf
sp-store-suc-resolved cf ls (just loc) v ok wf = sp-write-mem cf ls (sucLoc loc) v ok wf

-- the two slot reads (`load-from-slot` / `worklist-pop`, and `restore-input`):
-- a register write on a hit, a halt on an empty cell. Stated with the anchor
-- `current-frame alloc` and the FULL pair, so the conclusion matches
-- `exec-abstract`'s clause even while the read value is still a variable.
sp-from-slot : ∀ (ls : LocState FS) (alloc : AllocState {FS}) (mv : Maybe (StoredValue FS))
             → StackPtrOK? mv
             → SPInv ls
             → SPInv (proj₁ (exec-load-from-slot-with-value mv ls alloc))
sp-from-slot ls alloc (just v) ok wf = sp-write-reg (current-frame alloc) ls Output v ok wf
sp-from-slot ls alloc nothing  ok wf = sp-halt (current-frame alloc) ls true wf

sp-restore : ∀ (ls : LocState FS) (alloc : AllocState {FS}) (mv : Maybe (StoredValue FS))
           → StackPtrOK? mv
           → SPInv ls
           → SPInv (proj₁ (exec-restore-input-with-value mv ls alloc))
sp-restore ls alloc (just v) ok wf = sp-write-reg (current-frame alloc) ls Input1 v ok wf
sp-restore ls alloc nothing  ok wf = sp-halt (current-frame alloc) ls true wf

-- `sv-pred` / `sv-succ` produce a TAG on every input shape.
sp-pred : ∀ (v : StoredValue FS) → StackPtrOK (sv-pred v)
sp-pred (SV-Tag zero)    = tt
sp-pred (SV-Tag (suc m)) = tt
sp-pred (SV-Ptr l)       = tt
sp-pred (SV-Lit p x)     = tt
sp-pred (SV-Code c)      = tt

sp-succ : ∀ (v : StoredValue FS) → StackPtrOK (sv-succ v)
sp-succ (SV-Tag m)   = tt
sp-succ (SV-Ptr l)   = tt
sp-succ (SV-Lit p x) = tt
sp-succ (SV-Code c)  = tt

sp-reg-op : ∀ (cf : Frame) (ls : LocState FS) (op : RegOp)
          → SPInv ls → SPInv (exec-reg-op op ls)
sp-reg-op cf ls scratch-one        wf = sp-write-reg cf ls Scratch (SV-Tag 1) tt wf
sp-reg-op cf ls scratch-zero       wf = sp-write-reg cf ls Scratch (SV-Tag 0) tt wf
sp-reg-op cf ls scratch-dec        wf =
  sp-write-reg cf ls Scratch (sv-pred (readReg (regs ls) Scratch))
               (sp-pred (readReg (regs ls) Scratch)) wf
sp-reg-op cf ls scratch-load-count wf =
  sp-write-reg cf ls Scratch (readReg (regs ls) Count) (sp-regs wf Count) wf
sp-reg-op cf ls count-zero         wf = sp-write-reg cf ls Count (SV-Tag 0) tt wf
sp-reg-op cf ls count-inc          wf =
  sp-write-reg cf ls Count (sv-succ (readReg (regs ls) Count))
               (sp-succ (readReg (regs ls) Count)) wf

-- (`lea-indexed` needs no cursor case at all: it joined the unemittable set
-- 2026-08-01 — the cata codegen walks heap-LINKED stacks, never an indexed
-- cursor — so its route below is `⊥`-elim on `FrameFreeI`.)

------------------------------------------------------------------------
-- THE SIGOP OUTPUT. `Emits`/`Halts` produce `unit-storedvalue`; a `Pure`
-- SigOp's output is a literal (`SV-Lit`) except for the postulated
-- non-register-fittable case, which gets the companion axiom below — the same
-- trusted base as `structured-pure-sigop-output` itself (D061), and the same
-- shape as `FlatStoreWF.structured-pure-sigop-below`.
------------------------------------------------------------------------
postulate
  structured-pure-sigop-no-stack :
    ∀ {A B} (si : SigOpInfo A B) (ls : LocState FS)
    → StackPtrOK (structured-pure-sigop-output si ls)

sigop-output-ok : ∀ {A B} (si : SigOpInfo A B) (ls : LocState FS)
                → StackPtrOK (exec-sigop-output si ls)
sigop-output-ok {A} {B} si ls = go (effect si)
  where
    pov : ∀ (fitB : FitsInReg B) (ma : Maybe ⟦ A ⟧)
        → StackPtrOK (pure-sigop-out-val si fitB ma)
    pov fitB (just a) = tt
    pov fitB nothing  = tt
    aux : ∀ (mf : Maybe (FitsInReg B)) (ml : Maybe (ValueLocation FS))
        → StackPtrOK (pure-sigop-out-aux si ls mf ml)
    aux (just fitB) (just in-loc) = pov fitB (readTyped A in-loc ls)
    aux (just fitB) nothing       = pov fitB (readReg-typed A (readReg (regs ls) Input1))
    aux nothing     _             = structured-pure-sigop-no-stack si ls
    go : ∀ (e : EffectShape B) → StackPtrOK (exec-sigop-output-of e si ls)
    go Pure      = aux (fits-in-reg? B) (sv-as-loc (readReg (regs ls) Input1))
    go (Emits _) = tt
    go (Halts _) = tt

------------------------------------------------------------------------
-- THE PER-INSTRUCTION PRESERVATION over the structured semantics. No mutual
-- block: with `instr-case-on-tag` excluded and `instr-loop` unemittable, every
-- covered instruction is straight-line.
--
-- The conclusion's anchor is the POST alloc's frame — definitionally the same
-- frame in every covered clause (a frame-free instruction never writes
-- `current-frame`), which is what lets the flat lift consume it directly.
------------------------------------------------------------------------
sp-abstract : ∀ (i : AbstractInstr) (ls : LocState FS) (alloc : AllocState {FS})
            → EmittableI i
            → SPInv ls
            → SPInv (proj₁ (exec-abstract i ls alloc))
sp-abstract mov-to-output ls alloc ff wf =
  sp-write-reg (current-frame alloc) ls Output (readReg (regs ls) Input1) (sp-regs wf Input1) wf
sp-abstract mov-to-input ls alloc ff wf =
  sp-write-reg (current-frame alloc) ls Input1 (readReg (regs ls) Output) (sp-regs wf Output) wf
sp-abstract mov-output-to-input2 ls alloc ff wf =
  sp-write-reg (current-frame alloc) ls Input2 (readReg (regs ls) Output) (sp-regs wf Output) wf
sp-abstract mov-input2-to-output ls alloc ff wf =
  sp-write-reg (current-frame alloc) ls Output (readReg (regs ls) Input2) (sp-regs wf Input2) wf
sp-abstract load-indirect ls alloc ff wf =
  sp-load-resolved (current-frame alloc) ls Output (sv-as-loc (readReg (regs ls) Input1)) wf
sp-abstract load-indirect-suc ls alloc ff wf =
  sp-load-suc-resolved (current-frame alloc) ls Output (sv-as-loc (readReg (regs ls) Input1)) wf
sp-abstract (load-from-slot slot) ls alloc ff wf =
  sp-from-slot ls alloc (readLoc ls (AtStack (current-frame alloc) slot))
               (sp-read-loc (current-frame alloc) ls wf (AtStack (current-frame alloc) slot)) wf
sp-abstract (store-at-slot slot) ls alloc ff wf =
  sp-write-mem (current-frame alloc) ls (AtStack (current-frame alloc) slot)
               (readReg (regs ls) Output) (sp-regs wf Output) wf
sp-abstract store-indirect ls alloc ff wf =
  sp-store-resolved (current-frame alloc) ls (sv-as-loc (readReg (regs ls) Input1))
                    (readReg (regs ls) Output) (sp-regs wf Output) wf
sp-abstract store-indirect-suc ls alloc ff wf =
  sp-store-suc-resolved (current-frame alloc) ls (sv-as-loc (readReg (regs ls) Input1))
                        (readReg (regs ls) Output) (sp-regs wf Output) wf
-- THE ONE PRODUCER OF A STACK POINTER — and `⊥` in `FrameFreeI` since step
-- 2b, because it is emitted only by the four STACK-mode clauses of
-- `ir-to-trace'` and the correspondence runs over heap-moded code.
sp-abstract (lea-slot slot) ls alloc () wf
sp-abstract (restore-input slot) ls alloc ff wf =
  sp-restore ls alloc (readLoc ls (AtStack (current-frame alloc) slot))
             (sp-read-loc (current-frame alloc) ls wf (AtStack (current-frame alloc) slot)) wf
-- `lea-indexed` is unemittable (2026-08-01) — `⊥` in `FrameFreeI`
sp-abstract (lea-indexed slot) ls alloc () wf
-- the frame ops and the loop are unemittable — `⊥` in `FrameFreeI`
sp-abstract (instr-alloc-stack n)   ls alloc () wf
sp-abstract (instr-dealloc-stack n) ls alloc () wf
sp-abstract (instr-push-frame cap)  ls alloc () wf
sp-abstract instr-pop-frame         ls alloc () wf
sp-abstract (instr-loop body)       ls alloc () wf
-- the case is unemittable since item 6 (`case` compiles to flat control)
sp-abstract (instr-case-on-tag f g) ls alloc () wf
sp-abstract (instr-reclaim-to n)  ls alloc ff wf = wf
sp-abstract instr-call-closure    ls alloc ff wf = wf
sp-abstract (worklist-init slot)  ls alloc ff wf = wf
sp-abstract (worklist-push slot)  ls alloc ff wf =
  sp-write-mem (current-frame alloc) ls (AtStack (current-frame alloc) slot)
               (readReg (regs ls) Output) (sp-regs wf Output) wf
sp-abstract (worklist-pop slot)   ls alloc ff wf =
  sp-from-slot ls alloc (readLoc ls (AtStack (current-frame alloc) slot))
               (sp-read-loc (current-frame alloc) ls wf (AtStack (current-frame alloc) slot)) wf
sp-abstract (worklist-check slot) ls alloc ff wf = wf
sp-abstract (instr-sigop si) ls alloc ff wf =
  sp-write-reg-halt (current-frame alloc) ls Output (exec-sigop-output si ls) (exec-sigop-halts si ls)
                    (sigop-output-ok si ls) wf
sp-abstract (instr-load-const p v)   ls alloc ff wf =
  sp-write-reg (current-frame alloc) ls Output (SV-Lit p v) tt wf
sp-abstract (instr-load-code-addr n) ls alloc ff wf =
  sp-write-reg (current-frame alloc) ls Output (SV-Code n) tt wf
sp-abstract instr-save-closure-reg   ls alloc ff wf = wf
sp-abstract (instr-load-tag-lit n)   ls alloc ff wf =
  sp-write-reg (current-frame alloc) ls Output (SV-Tag n) tt wf
sp-abstract (instr-alloc-heap n)     ls alloc ff wf =
  sp-write-reg (current-frame alloc) ls Output
    (SV-Ptr (AtDynamic (proj₁ (AI.alloc-impl n (next-heap-ref alloc))))) tt wf
sp-abstract (instr-reg-op op)        ls alloc ff wf =
  sp-reg-op (current-frame alloc) ls op wf
sp-abstract (instr-ctrl c)           ls alloc ff wf = wf

------------------------------------------------------------------------
-- Lifted to the FLAT machine. The control cases move `fpc`/`halted` only; the
-- straight-line cases are `sp-abstract`; the frame-moving instructions, the
-- loop and the case are `⊥`-elim. Enumerated — a catch-all here would not
-- reduce `flat-exec-instr`'s own catch-all in the case tree.
------------------------------------------------------------------------
sp-jump : ∀ (mpc : Maybe ℕ) (fs : FlatState)
        → StackPtrWF fs → StackPtrWF (do-jump mpc fs)
sp-jump (just pc') fs wf = wf
sp-jump nothing    fs wf = sp-halt (current-frame (falloc fs)) (floc fs) true wf

sp-branch : ∀ (b : Bool) (m : LabelId) (prog : AbstractTrace) (fs : FlatState)
          → StackPtrWF fs → StackPtrWF (do-branch b m prog fs)
sp-branch true  m prog fs wf = sp-jump (find-label prog m) fs wf
sp-branch false m prog fs wf = wf

-- Plan 0.63: a return releases the body's frame (invisible to the invariant)
-- and pops the return stack, or halts on an empty one.
sp-ret : ∀ (r : List ℕ) (fs : FlatState)
       → StackPtrWF fs → StackPtrWF (do-ret r fs)
sp-ret []           fs wf = sp-halt (current-frame (falloc fs)) (floc fs) true wf
sp-ret (pc' ∷ rest) fs wf = wf

-- Plan 0.54 rung D: a body ENTRY grows the frame (invisible to the invariant,
-- which no longer reads the AllocState) and CLEARS it (visible: `stackMem`
-- moves). Registers and the heap come straight over; the cleared slots are
-- `nothing`, which `StackPtrOK?` accepts outright, and the untouched ones are
-- the pre-state's.
sp-thunk : ∀ (b : ℕ) (fs : FlatState)
         → StackPtrWF fs → StackPtrWF (do-thunk b fs)
sp-thunk b fs wf = mkStackPtrWF (sp-regs wf) (sp-heap wf) cleared
  where
    cleared : ∀ (f : Frame) (k : Slot)
            → StackPtrOK? (stackMem (floc (do-thunk b fs)) f k)
    cleared f k with (FrameSemantics.shift-frame FS (current-frame (falloc fs)) b) ≟F f
                   | Data.Nat.Properties._<?_ k b
    ... | yes _ | yes _ = tt
    ... | yes _ | no  _ = sp-stack wf f k
    ... | no  _ | _     = sp-stack wf f k

-- D092: THE CALL. Like the return, and for the same reason: `SPInv` reads only
-- the `LocState`, and a call touches only the AllocState, the return stack and
-- the pc. Halting rows go through the halt transport.
sp-call : ∀ (prog : AbstractTrace) (fs : FlatState)
        → StackPtrWF fs → StackPtrWF (do-call prog fs)
sp-call prog fs wf = go (callView prog fs)
  where go : CallPost prog fs → StackPtrWF (do-call prog fs)
        go (cp-halt    e) rewrite e = sp-halt (current-frame (falloc fs)) (floc fs) true wf
        go (cp-enter ℓ j fq e) rewrite e = wf

flat-stack-ptr : ∀ (i : AbstractInstr) (prog : AbstractTrace) (fs : FlatState)
               → EmittableI i
               → StackPtrWF fs → StackPtrWF (flat-exec-instr i prog fs)
flat-stack-ptr (instr-ctrl (c-label m))               prog fs ff wf = wf
-- Plan 0.63 step 2b: THE CLOSURE MARKERS MOVE THE FRAME, AND IT NO LONGER
-- MATTERS. With the payload trivial, `SPInv` reads only the LocState — and
-- `enter-frame`/`leave-frame` touch only the AllocState. So a body entry is
-- `wf` outright, and a return is `wf` or its halt transport, exactly like a
-- jump. This is what the old current-frame anchor could never have given.
--
-- Plan 0.54 rung D: a body entry is no longer `wf` OUTRIGHT, because
-- `do-thunk` now also CLEARS the entered frame — the `LocState` differs, so
-- the record must be REBUILT. Only `sp-stack` sees the clear, and it survives
-- it trivially: a cleared cell is `nothing`, and `StackPtrOK? nothing = ⊤`.
flat-stack-ptr (instr-ctrl (c-thunk m b))             prog fs ff wf =
  sp-thunk b fs wf
flat-stack-ptr (instr-ctrl (c-ret b))                 prog fs ff wf =
  sp-ret (fret fs) fs wf
flat-stack-ptr (instr-ctrl (c-jmp m))                 prog fs ff wf =
  sp-jump (find-label prog m) fs wf
flat-stack-ptr (instr-ctrl (c-branch-scratch-zero m)) prog fs ff wf =
  sp-branch (sv-is-zero (readReg (regs (floc fs)) Scratch)) m prog fs wf
flat-stack-ptr (instr-ctrl (c-branch-tag-zero m))     prog fs ff wf =
  sp-branch (tag-zf (flat-read-tag (floc fs))) m prog fs wf
flat-stack-ptr (instr-alloc-stack n)   prog fs () wf
flat-stack-ptr (instr-dealloc-stack n) prog fs () wf
flat-stack-ptr (instr-push-frame cap)  prog fs () wf
flat-stack-ptr instr-pop-frame         prog fs () wf
flat-stack-ptr (instr-loop body)       prog fs () wf
flat-stack-ptr (instr-case-on-tag f g) prog fs () wf
flat-stack-ptr mov-to-output            prog fs ff wf =
  sp-abstract mov-to-output (floc fs) (falloc fs) ff wf
flat-stack-ptr mov-to-input             prog fs ff wf =
  sp-abstract mov-to-input (floc fs) (falloc fs) ff wf
flat-stack-ptr mov-output-to-input2     prog fs ff wf =
  sp-abstract mov-output-to-input2 (floc fs) (falloc fs) ff wf
flat-stack-ptr mov-input2-to-output     prog fs ff wf =
  sp-abstract mov-input2-to-output (floc fs) (falloc fs) ff wf
flat-stack-ptr load-indirect            prog fs ff wf =
  sp-abstract load-indirect (floc fs) (falloc fs) ff wf
flat-stack-ptr load-indirect-suc        prog fs ff wf =
  sp-abstract load-indirect-suc (floc fs) (falloc fs) ff wf
flat-stack-ptr (load-from-slot k)       prog fs ff wf =
  sp-abstract (load-from-slot k) (floc fs) (falloc fs) ff wf
flat-stack-ptr (store-at-slot k)        prog fs ff wf =
  sp-abstract (store-at-slot k) (floc fs) (falloc fs) ff wf
flat-stack-ptr store-indirect           prog fs ff wf =
  sp-abstract store-indirect (floc fs) (falloc fs) ff wf
flat-stack-ptr store-indirect-suc       prog fs ff wf =
  sp-abstract store-indirect-suc (floc fs) (falloc fs) ff wf
flat-stack-ptr (lea-slot k) prog fs () wf
flat-stack-ptr (restore-input k)        prog fs ff wf =
  sp-abstract (restore-input k) (floc fs) (falloc fs) ff wf
flat-stack-ptr (lea-indexed k)          prog fs () wf
flat-stack-ptr (instr-reclaim-to k)     prog fs ff wf =
  sp-abstract (instr-reclaim-to k) (floc fs) (falloc fs) ff wf
flat-stack-ptr instr-call-closure       prog fs ff wf = sp-call prog fs wf
flat-stack-ptr (worklist-init k)        prog fs ff wf =
  sp-abstract (worklist-init k) (floc fs) (falloc fs) ff wf
flat-stack-ptr (worklist-push k)        prog fs ff wf =
  sp-abstract (worklist-push k) (floc fs) (falloc fs) ff wf
flat-stack-ptr (worklist-pop k)         prog fs ff wf =
  sp-abstract (worklist-pop k) (floc fs) (falloc fs) ff wf
flat-stack-ptr (worklist-check k)       prog fs ff wf =
  sp-abstract (worklist-check k) (floc fs) (falloc fs) ff wf
flat-stack-ptr (instr-sigop si)         prog fs ff wf =
  sp-abstract (instr-sigop si) (floc fs) (falloc fs) ff wf
flat-stack-ptr (instr-load-const p v)   prog fs ff wf =
  sp-abstract (instr-load-const p v) (floc fs) (falloc fs) ff wf
flat-stack-ptr (instr-load-code-addr k) prog fs ff wf =
  sp-abstract (instr-load-code-addr k) (floc fs) (falloc fs) ff wf
flat-stack-ptr instr-save-closure-reg   prog fs ff wf =
  sp-abstract instr-save-closure-reg (floc fs) (falloc fs) ff wf
flat-stack-ptr (instr-load-tag-lit k)   prog fs ff wf =
  sp-abstract (instr-load-tag-lit k) (floc fs) (falloc fs) ff wf
flat-stack-ptr (instr-alloc-heap k)     prog fs ff wf =
  sp-abstract (instr-alloc-heap k) (floc fs) (falloc fs) ff wf
flat-stack-ptr (instr-reg-op op)        prog fs ff wf =
  sp-abstract (instr-reg-op op) (floc fs) (falloc fs) ff wf
