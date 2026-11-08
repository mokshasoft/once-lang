-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Machine
--
-- D200: the MACHINE LEMMAS the clauses share — what a store or a load does to
-- memory, which locations a step leaves alone, and the two straight-line
-- setup skeletons (`TenStepPres` for the two-cell builds, `ApplySetupPres`
-- for `apply`'s sixteen rows before the call).
--
-- Nothing here mentions `IRObsCorrectF`; it is all about `exec-abstract`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Machine (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Interface o tbl public
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot)
open import Once.CCC.Machine.Locations using (AtStack; ValueLocation; AtDynamic)
open import Once.CCC.Machine.SMCore using (AllocState; AbstractTrace; store-at-slot; readReg; Output; LocState; sv-as-loc; Input1; store-indirect; StoredValue; sucLoc; load-indirect-suc; load-indirect; load-from-slot; writeReg-preserves; SV-Ptr; SV-Tag; SV-Lit; SV-Code; store-indirect-suc; writeReg-same; AbstractInstr; instr-alloc-heap; mov-to-input; mov-to-output; module LocState; module AllocState)
open AllocState using (current-frame; saved-frames; next-slot; next-heap-ref)
open LocState using (regs; halted)
open import Once.Memory.HeapAddress using (_≟HL_; HeapLocation; sucHL; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM

module Mach {FS : FrameSemantics} where

  open Core {FS}

  flat-store-floc : ∀ (slot : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → floc (flat-exec-instr (store-at-slot slot) prog fs)
      ≡ SMCore.MemOps.writeLoc (floc fs) (AtStack (current-frame (falloc fs)) slot)
                 (readReg (regs (floc fs)) Output)
  flat-store-floc slot prog fs = refl

  flat-store-falloc : ∀ (slot : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → falloc (flat-exec-instr (store-at-slot slot) prog fs) ≡ falloc fs
  flat-store-falloc slot prog fs = refl

  flat-store-fpc : ∀ (slot : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → fpc (flat-exec-instr (store-at-slot slot) prog fs) ≡ suc (fpc fs)
  flat-store-fpc slot prog fs = refl

  -- D174: INPUT1 SURVIVES THE MEMORY INSTRUCTIONS.
  --
  -- `SMPrimitives` already has this for `store-at-slot` and the two
  -- `load-indirect`s; `store-indirect` and `load-from-slot` had no such lemma
  -- because nothing had yet run a chain that dereferences a pointer it must
  -- still hold afterwards. `inl` does: one allocation feeds TWO indirect
  -- stores, so the pointer has to survive the first store and an intervening
  -- slot load. Both instructions case-split on a `with`, so neither is `refl`
  -- — the caller's own `InstrWF` witness is what collapses the split.
  store-ind-preserves-input : ∀ (s : LocState FS) (alloc : AllocState {FS})
      (loc : ValueLocation FS)
    → sv-as-loc (readReg (regs s) Input1) ≡ just loc
    → readReg (regs (proj₁ (exec-abstract store-indirect s alloc))) Input1
      ≡ readReg (regs s) Input1
  store-ind-preserves-input s alloc loc eq
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just loc) | refl =
    cong (λ r → readReg r Input1) (SMCore.MemOps.writeLoc-regs s loc (readReg (regs s) Output))

  -- D184: …and the same for the two INDIRECT loads, which `apply` runs before
  -- it has stashed anything. Both resolve `Input1` through a `Maybe` and then
  -- write `Output`, so the caller's own `InstrWF` collapses the resolution and
  -- what is left is a register write to a DIFFERENT register.
  load-ind-suc-preserves-input : ∀ (s : LocState FS) (alloc : AllocState {FS})
      (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs s) Input1) ≡ just loc
    → SMCore.MemOps.readLoc s (sucLoc loc) ≡ just v
    → readReg (regs (proj₁ (exec-abstract load-indirect-suc s alloc))) Input1
      ≡ readReg (regs s) Input1
  load-ind-suc-preserves-input s alloc loc v eq cell
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just loc) | refl with SMCore.MemOps.readLoc s (sucLoc loc) | cell
  ...   | .(just v) | refl = refl

  load-ind-preserves-input : ∀ (s : LocState FS) (alloc : AllocState {FS})
      (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs s) Input1) ≡ just loc
    → SMCore.MemOps.readLoc s loc ≡ just v
    → readReg (regs (proj₁ (exec-abstract load-indirect s alloc))) Input1
      ≡ readReg (regs s) Input1
  load-ind-preserves-input s alloc loc v eq cell
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just loc) | refl with SMCore.MemOps.readLoc s loc | cell
  ...   | .(just v) | refl = refl

  load-slot-preserves-input : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
      (v : StoredValue FS)
    → readLoc s (AtStack (current-frame alloc) slot) ≡ just v
    → readReg (regs (proj₁ (exec-abstract (load-from-slot slot) s alloc))) Input1
      ≡ readReg (regs s) Input1
  load-slot-preserves-input slot s alloc v eq
    with readLoc s (AtStack (current-frame alloc) slot) | eq
  ... | .(just v) | refl = writeReg-preserves (regs s) Output Input1 v (λ ())

  -- …and the same for a STACK cell. `store-indirect` is not
  -- `InstrNoHeapWrite` (it writes through a pointer that may be heap), so
  -- `exec-abstract-preserves-stack-slot` does not cover it — but a heap write
  -- never disturbs a stack cell, and `writeLoc-preserves-other` is `refl` on
  -- exactly that pairing. The caller's pointer witness collapses the `with`.
  store-ind-preserves-slot : ∀ (s : LocState FS) (alloc : AllocState {FS})
      (hl : HeapLocation) {f : Once.CCC.FrameSemantics.FrameSemantics.Frame FS} (slot : ℕ)
    → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
    → SMCore.MemOps.readLoc (proj₁ (exec-abstract store-indirect s alloc)) (AtStack f slot)
      ≡ SMCore.MemOps.readLoc s (AtStack f slot)
  store-ind-preserves-slot s alloc hl {f} slot eq
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just (AtDynamic hl)) | refl =
    SMCore.MemOps.writeLoc-preserves-other s (AtDynamic hl) (AtStack f slot)
      (readReg (regs s) Output) (λ ())

  -- D174: THE HEAP'S READ-AFTER-WRITE. `SMCore` deliberately ships none —
  -- "callers just case-split on ≟HL", because `writeHeapMem` routes through an
  -- explicit `Dec` rather than an internal `with`. `inl` is the first caller
  -- that needs it, so here it is, in the two pieces that split demands:
  -- `writeLoc` pattern-matches on the VALUE's constructor, so reaching
  -- `writeLocToHeap` is a five-way split, and the read-back itself is the
  -- `≟HL` decision.
  writeLoc-heap-eq : ∀ (s : LocState FS) (hl : HeapLocation) (v : StoredValue FS)
    → SMCore.MemOps.writeLoc s (AtDynamic hl) v ≡ SMCore.MemOps.writeLocToHeap s hl v
  writeLoc-heap-eq s hl (SV-Ptr (AtStack _ _))  = refl
  writeLoc-heap-eq s hl (SV-Ptr (AtDynamic _))  = refl
  writeLoc-heap-eq s hl (SV-Tag _)              = refl
  writeLoc-heap-eq s hl (SV-Lit _ _)            = refl
  writeLoc-heap-eq s hl (SV-Code _)             = refl

  heap-read-toheap : ∀ (s : LocState FS) (hl : HeapLocation) (v : StoredValue FS)
    → SMCore.MemOps.readLoc (SMCore.MemOps.writeLocToHeap s hl v) (AtDynamic hl) ≡ just v
  heap-read-toheap s hl v with hl ≟HL hl
  ... | yes _  = refl
  ... | no ne  = ⊥-elim (ne refl)

  heap-read-same : ∀ (s : LocState FS) (hl : HeapLocation) (v : StoredValue FS)
    → SMCore.MemOps.readLoc (SMCore.MemOps.writeLoc s (AtDynamic hl) v) (AtDynamic hl) ≡ just v
  heap-read-same s hl v =
    trans (cong (λ t → SMCore.MemOps.readLoc t (AtDynamic hl)) (writeLoc-heap-eq s hl v))
          (heap-read-toheap s hl v)

  -- The indirect stores, with the `with` collapsed by the caller's pointer
  -- witness — the heap analogue of `store-ind-preserves-slot`.
  store-ind-result : ∀ (s : LocState FS) (alloc : AllocState {FS}) (hl : HeapLocation)
    → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
    → SMCore.MemOps.readLoc (proj₁ (exec-abstract store-indirect s alloc)) (AtDynamic hl)
      ≡ just (readReg (regs s) Output)
  store-ind-result s alloc hl eq with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just (AtDynamic hl)) | refl = heap-read-same s hl (readReg (regs s) Output)

  -- `sucLoc (AtDynamic hl)` IS `AtDynamic (sucHL hl)` definitionally, so the
  -- successor cell is just another heap cell and the same read-back serves.
  store-ind-suc-result : ∀ (s : LocState FS) (alloc : AllocState {FS}) (hl : HeapLocation)
    → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
    → SMCore.MemOps.readLoc (proj₁ (exec-abstract store-indirect-suc s alloc)) (AtDynamic (sucHL hl))
      ≡ just (readReg (regs s) Output)
  store-ind-suc-result s alloc hl eq with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just (AtDynamic hl)) | refl = heap-read-same s (sucHL hl) (readReg (regs s) Output)

  load-slot-result : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
      (v : StoredValue FS)
    → SMCore.MemOps.readLoc s (AtStack (current-frame alloc) slot) ≡ just v
    → readReg (regs (proj₁ (exec-abstract (load-from-slot slot) s alloc))) Output ≡ v
  load-slot-result slot s alloc v eq
    with SMCore.MemOps.readLoc s (AtStack (current-frame alloc) slot) | eq
  ... | .(just v) | refl = writeReg-same (regs s) Output v

  -- A heap cell and its successor are distinct: same ref, offsets `o` and
  -- `suc o`. Needed because `inl` writes BOTH cells of one block and each
  -- read-back must survive the other's write.
  sucHL-≢ : ∀ (hl : HeapLocation) → AtDynamic {FS} (sucHL hl) ≢ AtDynamic hl
  sucHL-≢ (heap-loc r o) ()

  -- Heap cells are preserved by any instruction that writes no heap.
  heap-untouched : ∀ (i : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS})
      (hl : HeapLocation) → InstrNoHeapWrite i
    → SMCore.MemOps.readLoc (proj₁ (exec-abstract i s alloc)) (AtDynamic hl)
      ≡ SMCore.MemOps.readLoc s (AtDynamic hl)
  heap-untouched i s alloc hl nhw =
    cong (λ m → m hl) (exec-abstract-preserves-heapMem i s alloc nhw)

  store-ind-suc-preserves-heap : ∀ (s : LocState FS) (alloc : AllocState {FS})
      (hl hl' : HeapLocation)
    → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
    → AtDynamic {FS} (sucHL hl) ≢ AtDynamic hl'
    → SMCore.MemOps.readLoc (proj₁ (exec-abstract store-indirect-suc s alloc)) (AtDynamic hl')
      ≡ SMCore.MemOps.readLoc s (AtDynamic hl')
  store-ind-suc-preserves-heap s alloc hl hl' eq ne
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just (AtDynamic hl)) | refl =
    SMCore.MemOps.writeLoc-preserves-other s (AtDynamic (sucHL hl)) (AtDynamic hl')
      (readReg (regs s) Output) ne

  store-ind-suc-preserves-slot : ∀ (s : LocState FS) (alloc : AllocState {FS})
      (hl : HeapLocation) {f : Once.CCC.FrameSemantics.FrameSemantics.Frame FS} (slot : ℕ)
    → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
    → SMCore.MemOps.readLoc (proj₁ (exec-abstract store-indirect-suc s alloc)) (AtStack f slot)
      ≡ SMCore.MemOps.readLoc s (AtStack f slot)
  store-ind-suc-preserves-slot s alloc hl {f} slot eq
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just (AtDynamic hl)) | refl =
    SMCore.MemOps.writeLoc-preserves-other s (sucLoc (AtDynamic hl)) (AtStack f slot)
      (readReg (regs s) Output) (λ ())

  ------------------------------------------------------------------------
  -- D182: the `*-mem-pres` vocabulary, stated at an ARBITRARY `BeforeFrontier`
  -- location instead of at a named cell. `inl`, `inr` and `curry` each
  -- postulated the same invariant about the same ten-instruction heap build;
  -- these three lemmas are what turns it into a ten-step `trans` chain.
  --
  -- The reason it could not be `derive-mem-preserved` (ClosureWellFormed) is
  -- that that one bans heap writes outright (`TraceNoHeapWrites`), and this run
  -- writes the heap twice. What makes those writes invisible is not their
  -- ABSENCE but their FRESHNESS — they land in a block allocated during the
  -- run, whose ref-id is at or above the frontier the caller's locations are
  -- bounded by. Freshness is a runtime fact about `Input1`, which is why no
  -- static trace predicate expresses it and why it enters as a premise here.
  ------------------------------------------------------------------------

  -- (1) An instruction that writes NO memory preserves every location.
  mem-untouched : ∀ (i : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS})
      (loc : ValueLocation FS)
    → InstrNoHeapWrite i → instr-writes-slot i ≡ nothing
    → SMCore.MemOps.readLoc (proj₁ (exec-abstract i s alloc)) loc ≡ SMCore.MemOps.readLoc s loc
  mem-untouched i s alloc (AtStack f slot) nhw nws =
    exec-abstract-preserves-stack-slot i s alloc f slot nhw nws
  mem-untouched i s alloc (AtDynamic hl)   nhw nws = heap-untouched i s alloc hl nhw

  -- (2) A stack write AT OR ABOVE the frontier misses everything the caller can
  -- name. `next-slot alloc ≤ k` is exactly the emitter's own premise (D155).
  -- The step's `alloc'` is separate from the caller's `alloc`: the frame does
  -- not move during the run, and the equation says so.
  store-slot-preserves-before : ∀ (k : ℕ) (st : LocState FS)
      (alloc alloc' : AllocState {FS}) (loc : ValueLocation FS)
    → current-frame alloc' ≡ current-frame alloc
    → next-slot alloc ≤ k
    → BeforeFrontier alloc loc
    → SMCore.MemOps.readLoc (proj₁ (exec-abstract (store-at-slot k) st alloc')) loc
      ≡ SMCore.MemOps.readLoc st loc
  store-slot-preserves-before k st alloc alloc' .(AtStack _ _) cf-eq ns≤k
    (BeforeFrontier.stack-before {f} {j} f≡cf j<ns) =
    subst (λ f' → SMCore.MemOps.readLoc (proj₁ (exec-abstract (store-at-slot k) st alloc')) (AtStack f' j)
                  ≡ SMCore.MemOps.readLoc st (AtStack f' j))
          (trans cf-eq (sym f≡cf))
          (store-at-slot-preserves-below j k st alloc' (<-≤-trans j<ns ns≤k))
  store-slot-preserves-before k st alloc alloc' .(AtStack _ _) cf-eq ns≤k
    (BeforeFrontier.stack-ancestor {f} {j} cf≺f _) =
    store-at-slot-preserves-ancestor k st alloc' f j
      (subst (λ c → Once.CCC.FrameSemantics.FrameSemantics._≺_ FS c f) (sym cf-eq) cf≺f)
  store-slot-preserves-before k st alloc alloc' .(AtDynamic _) cf-eq ns≤k
    (BeforeFrontier.heap-before {hl} _) =
    SMCore.MemOps.writeLoc-preserves-other st (AtStack (current-frame alloc') k) (AtDynamic hl)
      (readReg (regs st) Output) (λ ())

  -- (3) A heap write into a FRESH block misses everything the caller can name:
  -- a stack cell is a different KIND of location, and a heap cell the caller
  -- can name has `ref-id < next-heap-ref alloc ≤ ref-id` of the block written.
  -- `sucHL` keeps the REF (`heap-loc r o ↦ heap-loc r (suc o)`), so a bound on
  -- the block's ref-id serves both its cells.
  sucHL-ref : ∀ (hl : HeapLocation) → ref-id (heap-ref (sucHL hl)) ≡ ref-id (heap-ref hl)
  sucHL-ref (heap-loc r o) = refl

  fresh-heap-≢ : ∀ (alloc : AllocState {FS}) (hl h : HeapLocation)
               → next-heap-ref alloc ≤ ref-id (heap-ref hl)
               → ref-id (heap-ref h) < next-heap-ref alloc
               → AtDynamic {FS} hl ≢ AtDynamic h
  fresh-heap-≢ alloc hl h fresh h<f refl = <-irrefl refl (≤-<-trans fresh h<f)

  store-ind-preserves-before : ∀ (st : LocState FS) (alloc alloc' : AllocState {FS})
      (hl : HeapLocation) (loc : ValueLocation FS)
    → sv-as-loc (readReg (regs st) Input1) ≡ just (AtDynamic hl)
    → next-heap-ref alloc ≤ ref-id (heap-ref hl)
    → BeforeFrontier alloc loc
    → SMCore.MemOps.readLoc (proj₁ (exec-abstract store-indirect st alloc')) loc
      ≡ SMCore.MemOps.readLoc st loc
  store-ind-preserves-before st alloc alloc' hl .(AtStack _ _) rdi fresh
    (BeforeFrontier.stack-before {f} {j} _ _) = store-ind-preserves-slot st alloc' hl j rdi
  store-ind-preserves-before st alloc alloc' hl .(AtStack _ _) rdi fresh
    (BeforeFrontier.stack-ancestor {f} {j} _ _) = store-ind-preserves-slot st alloc' hl j rdi
  store-ind-preserves-before st alloc alloc' hl .(AtDynamic _) rdi fresh
    (BeforeFrontier.heap-before {h} h<f)
    with sv-as-loc (readReg (regs st) Input1) | rdi
  ... | .(just (AtDynamic hl)) | refl =
    SMCore.MemOps.writeLoc-preserves-other st (AtDynamic hl) (AtDynamic h)
      (readReg (regs st) Output) (fresh-heap-≢ alloc hl h fresh h<f)

  store-ind-suc-preserves-before : ∀ (st : LocState FS) (alloc alloc' : AllocState {FS})
      (hl : HeapLocation) (loc : ValueLocation FS)
    → sv-as-loc (readReg (regs st) Input1) ≡ just (AtDynamic hl)
    → next-heap-ref alloc ≤ ref-id (heap-ref hl)
    → BeforeFrontier alloc loc
    → SMCore.MemOps.readLoc (proj₁ (exec-abstract store-indirect-suc st alloc')) loc
      ≡ SMCore.MemOps.readLoc st loc
  store-ind-suc-preserves-before st alloc alloc' hl .(AtStack _ _) rdi fresh
    (BeforeFrontier.stack-before {f} {j} _ _) = store-ind-suc-preserves-slot st alloc' hl j rdi
  store-ind-suc-preserves-before st alloc alloc' hl .(AtStack _ _) rdi fresh
    (BeforeFrontier.stack-ancestor {f} {j} _ _) = store-ind-suc-preserves-slot st alloc' hl j rdi
  store-ind-suc-preserves-before st alloc alloc' hl .(AtDynamic _) rdi fresh
    (BeforeFrontier.heap-before {h} h<f) =
    -- `sucHL` keeps the REF, so the successor cell is fresh by the same bound.
    store-ind-suc-preserves-heap st alloc' hl h rdi
      (fresh-heap-≢ alloc (sucHL hl) h (subst (λ r → next-heap-ref alloc ≤ r) (sym (sucHL-ref hl)) fresh) h<f)

  ------------------------------------------------------------------------
  -- D182: THE TEN-STEP INVARIANT, ONCE. `inl`, `inr` and `curry` emit the SAME
  -- heap build and differed only in rows 6 and 8 — a tag literal vs an env
  -- load, a payload load vs a code address — none of which touches memory. So
  -- the invariant is one lemma over that shape, and the three clauses are its
  -- instances.
  --
  -- Every state is `flat-step-straight`: all ten instructions are non-`ctrl`,
  -- so `flat-exec-instr i prog` reduces to it for each concrete instruction and
  -- the clauses' own nests ARE these states, definitionally. (Writing them with
  -- `flat-exec-instr` and a variable `i6` would not reduce — its catch-all is
  -- stuck on a variable, which is exactly what `StraightStep` exists to work
  -- around.)
  ------------------------------------------------------------------------
  ------------------------------------------------------------------------
  -- D209: THE NINE-INSTRUCTION HEAP BUILD, over an ARBITRARY start state.
  --
  -- `inl`, `inr`, `curry`, `Ana` and `⟨ f , g ⟩` all end with the same nine
  -- instructions — stash, allocate two cells, stash the pointer, then write
  -- the two cells and hand the pointer back:
  --
  --   store-at-slot n ∷ instr-alloc-heap 2 ∷ store-at-slot (suc n) ∷
  --   mov-to-input ∷ i6 ∷ store-indirect ∷ i8 ∷ store-indirect-suc ∷
  --   load-from-slot (suc n) ∷ []
  --
  -- The first four begin it at the entry state, one `mov-to-output` in;
  -- `pair` begins it wherever `g`'s run settled. So the module takes the
  -- START STATE as a parameter, with the two facts relating its allocator to
  -- the one the caller's data is measured against. `TenStepPres` below is the
  -- entry-state instance — a wrapper, not a copy.
  ------------------------------------------------------------------------
  -- THE NINE STATES, on their own, parameterized by exactly what they depend
  -- on. Every consumer names them THROUGH this module (profile 2026-09-29): two
  -- families written out separately are definitionally equal, but deciding it
  -- unfolds both nine-step chains into their normal forms, and that exhausted
  -- the heap in `PairAssemble.dispatch-g`, where `Pair`'s chain states meet
  -- `NineStepPres`'s. Named here, both sides are `NineSteps.uₖ` at the same
  -- arguments and compare in one step.
  module NineSteps (n : ℕ) (i6 i8 : AbstractInstr) (u1 : FlatState) where
    u2 u3 u4 u5 u6 u7 u8 u9 u10 : FlatState
    u2  = flat-step-straight (store-at-slot n)        u1
    u3  = flat-step-straight (instr-alloc-heap 2)     u2
    u4  = flat-step-straight (store-at-slot (suc n))  u3
    u5  = flat-step-straight mov-to-input             u4
    u6  = flat-step-straight i6                       u5
    u7  = flat-step-straight store-indirect           u6
    u8  = flat-step-straight i8                       u7
    u9  = flat-step-straight store-indirect-suc       u8
    u10 = flat-step-straight (load-from-slot (suc n)) u9

    -- THE END STATE BEHIND A NAME AGDA WILL NOT UNFOLD (plan 0.144; the
    -- `context-form-mismatch-opaque` pattern). Two families that build the
    -- nine rows separately (`Pair.Chain`'s run, `Pair.Place`, `Pair.Pres`)
    -- reach `u10` at syntactically different forms, and deciding them equal
    -- evaluated all nine rows (~100 s each, profile 2026-11-06). Two copies of
    -- `u10ᵒ` compare by their arguments alone; `u10ᵒ-def` crosses back.
    opaque
      u10ᵒ : FlatState
      u10ᵒ = u10

    opaque
      unfolding u10ᵒ
      u10ᵒ-def : u10ᵒ ≡ u10
      u10ᵒ-def = refl

  module NineStepPres
    (n : ℕ) (i6 i8 : AbstractInstr)
    (u1 : FlatState) (s : LocState FS) (alloc : AllocState {FS})
    -- the start state's allocator, related to the frontier the CALLER's live
    -- data is measured against
    (heapref-u1 : next-heap-ref (falloc u1) ≡ next-heap-ref alloc)
    (cf-u1      : current-frame (falloc u1) ≡ current-frame alloc)
    where

    open NineSteps n i6 i8 u1 public

    hl : HeapLocation
    hl = heap-loc (mkHeapRef (next-heap-ref (falloc u2))) 0

    -- The stash does not allocate, so the ref handed out at `u3` is the one
    -- the start state was carrying — which is the caller's.
    heapref-u2 : next-heap-ref (falloc u2) ≡ next-heap-ref alloc
    heapref-u2 =
      trans (exec-abstract-preserves-heap-ref (store-at-slot n) (floc u1) (falloc u1) tt)
            heapref-u1

    fresh : next-heap-ref alloc ≤ ref-id (heap-ref hl)
    fresh = ≤-reflexive (sym heapref-u2)

    cf-u3 : current-frame (falloc u3) ≡ current-frame alloc
    cf-u3 =
      trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc u2) (falloc u2))
     (trans (exec-abstract-preserves-frame (store-at-slot n) (floc u1) (falloc u1))
            cf-u1)

    -- What the nine leave alone, RELATIVE TO THE START STATE. The caller
    -- composes this with whatever it knows about how the start state was
    -- reached — for the entry-state instance that is one `mov-to-output`, for
    -- `pair` it is the two sub-IR runs.
    mem-pres-from :
        InstrNoHeapWrite i6 → instr-writes-slot i6 ≡ nothing
      → InstrNoHeapWrite i8 → instr-writes-slot i8 ≡ nothing
      → next-slot alloc ≤ n
      → sv-as-loc (readReg (regs (floc u6)) Input1) ≡ just (AtDynamic hl)
      → sv-as-loc (readReg (regs (floc u8)) Input1) ≡ just (AtDynamic hl)
      → (loc : ValueLocation FS)
      → BeforeFrontier (record alloc { next-slot = n }) loc
      → SMCore.MemOps.readLoc (floc u10) loc ≡ SMCore.MemOps.readLoc (floc u1) loc
    mem-pres-from nhw6 nws6 nhw8 nws8 ns≤n rdi6 rdi8 loc bf =
      trans (mem-untouched (load-from-slot (suc n)) (floc u9) (falloc u9) loc
               nhw-load-from-slot refl)
     (trans (store-ind-suc-preserves-before (floc u8) (record alloc { next-slot = n })
               (falloc u8) hl loc rdi8 fresh bf)
     (trans (mem-untouched i8 (floc u7) (falloc u7) loc nhw8 nws8)
     (trans (store-ind-preserves-before (floc u6) (record alloc { next-slot = n })
               (falloc u6) hl loc rdi6 fresh bf)
     (trans (mem-untouched i6 (floc u5) (falloc u5) loc nhw6 nws6)
     (trans (mem-untouched mov-to-input (floc u4) (falloc u4) loc nhw-mov-to-input refl)
     (trans (store-slot-preserves-before (suc n) (floc u3) (record alloc { next-slot = n })
               (falloc u3) loc cf-u3 (n≤1+n n) bf)
     (trans (mem-untouched (instr-alloc-heap 2) (floc u2) (falloc u2) loc
               nhw-instr-alloc-heap refl)
            (store-slot-preserves-before n (floc u1) (record alloc { next-slot = n })
               (falloc u1) loc cf-u1 ≤-refl bf))))))))

  -- The ENTRY-STATE instance: one REGISTER-ONLY step, then the nine. Plan
  -- 0.108 made the first step a parameter — `inl`/`inr` copy the payload
  -- (`mov-to-output`), a comparison computes its tag (`out-nz`); the nine are
  -- the same build either way. What the first step owes is exactly what the nine
  -- need of their start: the frontier, the frame, and every memory cell alone.
  module TenStepPresAt
    (i0 : AbstractInstr) (n : ℕ) (i6 i8 : AbstractInstr) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (heapref-t1 : next-heap-ref (falloc (flat-step-straight i0 (entry-flat base s alloc cl rs)))
                  ≡ next-heap-ref alloc)
    (cf-t1      : current-frame (falloc (flat-step-straight i0 (entry-flat base s alloc cl rs)))
                  ≡ current-frame alloc)
    (mem-t1     : ∀ (loc : ValueLocation FS)
                → SMCore.MemOps.readLoc (floc (flat-step-straight i0 (entry-flat base s alloc cl rs))) loc
                  ≡ SMCore.MemOps.readLoc s loc)
    where

    t0 t1 : FlatState
    t0  = entry-flat base s alloc cl rs
    t1  = flat-step-straight i0 t0

    module NSP = NineStepPres n i6 i8 t1 s alloc heapref-t1 cf-t1

    t2 t3 t4 t5 t6 t7 t8 t9 t10 : FlatState
    t2  = NSP.u2 ; t3 = NSP.u3 ; t4 = NSP.u4 ; t5 = NSP.u5 ; t6 = NSP.u6
    t7  = NSP.u7 ; t8 = NSP.u8 ; t9 = NSP.u9 ; t10 = NSP.u10

    hl : HeapLocation
    hl = NSP.hl

    heapref-t2 : next-heap-ref (falloc t2) ≡ next-heap-ref alloc
    heapref-t2 = NSP.heapref-u2

    fresh : next-heap-ref alloc ≤ ref-id (heap-ref hl)
    fresh = NSP.fresh

    cf-t3 : current-frame (falloc t3) ≡ current-frame alloc
    cf-t3 = NSP.cf-u3

    -- …and the entry-state form: the nine, then the leading step, which
    -- writes a register and so touches no memory.
    mem-pres :
        InstrNoHeapWrite i6 → instr-writes-slot i6 ≡ nothing
      → InstrNoHeapWrite i8 → instr-writes-slot i8 ≡ nothing
      → next-slot alloc ≤ n
      → sv-as-loc (readReg (regs (floc t6)) Input1) ≡ just (AtDynamic hl)
      → sv-as-loc (readReg (regs (floc t8)) Input1) ≡ just (AtDynamic hl)
      → (loc : ValueLocation FS)
      → BeforeFrontier (record alloc { next-slot = n }) loc
      → SMCore.MemOps.readLoc (floc t10) loc ≡ SMCore.MemOps.readLoc s loc
    mem-pres nhw6 nws6 nhw8 nws8 ns≤n rdi6 rdi8 loc bf =
      trans (NSP.mem-pres-from nhw6 nws6 nhw8 nws8 ns≤n rdi6 rdi8 loc bf) (mem-t1 loc)

  -- …the `inl`/`inr` instance: the leading step copies the payload.
  module TenStepPres
    (n : ℕ) (i6 i8 : AbstractInstr) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    = TenStepPresAt mov-to-output n i6 i8 prog base s alloc cl rs
        (exec-abstract-preserves-heap-ref mov-to-output s alloc tt)
        (exec-abstract-preserves-frame mov-to-output s alloc)
        (λ loc → mem-untouched mov-to-output s alloc loc nhw-mov-to-output refl)

  -- D170 / Phase E2 probe: the DENOTATION half of `obs-correct-curry`.
  -- `curry` builds a value; it invokes no SigOp, so its trace is empty at every
  -- depth. Named here because it is one of the two halves the discharge needs,
  -- and because it is `refl` — which is the evidence that the clause is
  -- Class-B shaped rather than label-bearing.

