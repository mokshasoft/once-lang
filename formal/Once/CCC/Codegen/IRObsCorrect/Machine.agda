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

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Machine (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Interface o public

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module Mach {FS : FrameSemantics} where

  open Core {FS}

  flat-store-floc : ∀ (slot : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → floc (flat-exec-instr (store-at-slot slot) prog fs)
      ≡ MemOps.writeLoc (floc fs) (AtStack (current-frame (falloc fs)) slot)
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
    cong (λ r → readReg r Input1) (MemOps.writeLoc-regs s loc (readReg (regs s) Output))

  -- D184: …and the same for the two INDIRECT loads, which `apply` runs before
  -- it has stashed anything. Both resolve `Input1` through a `Maybe` and then
  -- write `Output`, so the caller's own `InstrWF` collapses the resolution and
  -- what is left is a register write to a DIFFERENT register.
  load-ind-suc-preserves-input : ∀ (s : LocState FS) (alloc : AllocState {FS})
      (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs s) Input1) ≡ just loc
    → MemOps.readLoc s (sucLoc loc) ≡ just v
    → readReg (regs (proj₁ (exec-abstract load-indirect-suc s alloc))) Input1
      ≡ readReg (regs s) Input1
  load-ind-suc-preserves-input s alloc loc v eq cell
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just loc) | refl with MemOps.readLoc s (sucLoc loc) | cell
  ...   | .(just v) | refl = refl

  load-ind-preserves-input : ∀ (s : LocState FS) (alloc : AllocState {FS})
      (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs s) Input1) ≡ just loc
    → MemOps.readLoc s loc ≡ just v
    → readReg (regs (proj₁ (exec-abstract load-indirect s alloc))) Input1
      ≡ readReg (regs s) Input1
  load-ind-preserves-input s alloc loc v eq cell
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just loc) | refl with MemOps.readLoc s loc | cell
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
      (hl : HeapLocation) {f : Once.CCC.FrameSemantics.Frame FS} (slot : ℕ)
    → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
    → MemOps.readLoc (proj₁ (exec-abstract store-indirect s alloc)) (AtStack f slot)
      ≡ MemOps.readLoc s (AtStack f slot)
  store-ind-preserves-slot s alloc hl {f} slot eq
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just (AtDynamic hl)) | refl =
    MemOps.writeLoc-preserves-other s (AtDynamic hl) (AtStack f slot)
      (readReg (regs s) Output) (λ ())

  -- D174: THE HEAP'S READ-AFTER-WRITE. `SMCore` deliberately ships none —
  -- "callers just case-split on ≟HL", because `writeHeapMem` routes through an
  -- explicit `Dec` rather than an internal `with`. `inl` is the first caller
  -- that needs it, so here it is, in the two pieces that split demands:
  -- `writeLoc` pattern-matches on the VALUE's constructor, so reaching
  -- `writeLocToHeap` is a five-way split, and the read-back itself is the
  -- `≟HL` decision.
  writeLoc-heap-eq : ∀ (s : LocState FS) (hl : HeapLocation) (v : StoredValue FS)
    → MemOps.writeLoc s (AtDynamic hl) v ≡ MemOps.writeLocToHeap s hl v
  writeLoc-heap-eq s hl (SV-Ptr (AtStack _ _))  = refl
  writeLoc-heap-eq s hl (SV-Ptr (AtDynamic _))  = refl
  writeLoc-heap-eq s hl (SV-Tag _)              = refl
  writeLoc-heap-eq s hl (SV-Lit _ _)            = refl
  writeLoc-heap-eq s hl (SV-Code _)             = refl

  heap-read-toheap : ∀ (s : LocState FS) (hl : HeapLocation) (v : StoredValue FS)
    → MemOps.readLoc (MemOps.writeLocToHeap s hl v) (AtDynamic hl) ≡ just v
  heap-read-toheap s hl v with hl ≟HL hl
  ... | yes _  = refl
  ... | no ne  = ⊥-elim (ne refl)

  heap-read-same : ∀ (s : LocState FS) (hl : HeapLocation) (v : StoredValue FS)
    → MemOps.readLoc (MemOps.writeLoc s (AtDynamic hl) v) (AtDynamic hl) ≡ just v
  heap-read-same s hl v =
    trans (cong (λ t → MemOps.readLoc t (AtDynamic hl)) (writeLoc-heap-eq s hl v))
          (heap-read-toheap s hl v)

  -- The indirect stores, with the `with` collapsed by the caller's pointer
  -- witness — the heap analogue of `store-ind-preserves-slot`.
  store-ind-result : ∀ (s : LocState FS) (alloc : AllocState {FS}) (hl : HeapLocation)
    → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
    → MemOps.readLoc (proj₁ (exec-abstract store-indirect s alloc)) (AtDynamic hl)
      ≡ just (readReg (regs s) Output)
  store-ind-result s alloc hl eq with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just (AtDynamic hl)) | refl = heap-read-same s hl (readReg (regs s) Output)

  -- `sucLoc (AtDynamic hl)` IS `AtDynamic (sucHL hl)` definitionally, so the
  -- successor cell is just another heap cell and the same read-back serves.
  store-ind-suc-result : ∀ (s : LocState FS) (alloc : AllocState {FS}) (hl : HeapLocation)
    → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
    → MemOps.readLoc (proj₁ (exec-abstract store-indirect-suc s alloc)) (AtDynamic (sucHL hl))
      ≡ just (readReg (regs s) Output)
  store-ind-suc-result s alloc hl eq with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just (AtDynamic hl)) | refl = heap-read-same s (sucHL hl) (readReg (regs s) Output)

  load-slot-result : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
      (v : StoredValue FS)
    → MemOps.readLoc s (AtStack (current-frame alloc) slot) ≡ just v
    → readReg (regs (proj₁ (exec-abstract (load-from-slot slot) s alloc))) Output ≡ v
  load-slot-result slot s alloc v eq
    with MemOps.readLoc s (AtStack (current-frame alloc) slot) | eq
  ... | .(just v) | refl = writeReg-same (regs s) Output v

  -- A heap cell and its successor are distinct: same ref, offsets `o` and
  -- `suc o`. Needed because `inl` writes BOTH cells of one block and each
  -- read-back must survive the other's write.
  sucHL-≢ : ∀ (hl : HeapLocation) → AtDynamic {FS} (sucHL hl) ≢ AtDynamic hl
  sucHL-≢ (heap-loc r o) ()

  -- Heap cells are preserved by any instruction that writes no heap.
  heap-untouched : ∀ (i : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS})
      (hl : HeapLocation) → InstrNoHeapWrite i
    → MemOps.readLoc (proj₁ (exec-abstract i s alloc)) (AtDynamic hl)
      ≡ MemOps.readLoc s (AtDynamic hl)
  heap-untouched i s alloc hl nhw =
    cong (λ m → m hl) (exec-abstract-preserves-heapMem i s alloc nhw)

  store-ind-suc-preserves-heap : ∀ (s : LocState FS) (alloc : AllocState {FS})
      (hl hl' : HeapLocation)
    → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
    → AtDynamic {FS} (sucHL hl) ≢ AtDynamic hl'
    → MemOps.readLoc (proj₁ (exec-abstract store-indirect-suc s alloc)) (AtDynamic hl')
      ≡ MemOps.readLoc s (AtDynamic hl')
  store-ind-suc-preserves-heap s alloc hl hl' eq ne
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just (AtDynamic hl)) | refl =
    MemOps.writeLoc-preserves-other s (AtDynamic (sucHL hl)) (AtDynamic hl')
      (readReg (regs s) Output) ne

  store-ind-suc-preserves-slot : ∀ (s : LocState FS) (alloc : AllocState {FS})
      (hl : HeapLocation) {f : Once.CCC.FrameSemantics.Frame FS} (slot : ℕ)
    → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
    → MemOps.readLoc (proj₁ (exec-abstract store-indirect-suc s alloc)) (AtStack f slot)
      ≡ MemOps.readLoc s (AtStack f slot)
  store-ind-suc-preserves-slot s alloc hl {f} slot eq
    with sv-as-loc (readReg (regs s) Input1) | eq
  ... | .(just (AtDynamic hl)) | refl =
    MemOps.writeLoc-preserves-other s (sucLoc (AtDynamic hl)) (AtStack f slot)
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
    → MemOps.readLoc (proj₁ (exec-abstract i s alloc)) loc ≡ MemOps.readLoc s loc
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
    → MemOps.readLoc (proj₁ (exec-abstract (store-at-slot k) st alloc')) loc
      ≡ MemOps.readLoc st loc
  store-slot-preserves-before k st alloc alloc' .(AtStack _ _) cf-eq ns≤k
    (BeforeFrontier.stack-before {f} {j} f≡cf j<ns) =
    subst (λ f' → MemOps.readLoc (proj₁ (exec-abstract (store-at-slot k) st alloc')) (AtStack f' j)
                  ≡ MemOps.readLoc st (AtStack f' j))
          (trans cf-eq (sym f≡cf))
          (store-at-slot-preserves-below j k st alloc' (<-≤-trans j<ns ns≤k))
  store-slot-preserves-before k st alloc alloc' .(AtStack _ _) cf-eq ns≤k
    (BeforeFrontier.stack-ancestor {f} {j} cf≺f _) =
    store-at-slot-preserves-ancestor k st alloc' f j
      (subst (λ c → Once.CCC.FrameSemantics.FrameSemantics._≺_ FS c f) (sym cf-eq) cf≺f)
  store-slot-preserves-before k st alloc alloc' .(AtDynamic _) cf-eq ns≤k
    (BeforeFrontier.heap-before {hl} _) =
    MemOps.writeLoc-preserves-other st (AtStack (current-frame alloc') k) (AtDynamic hl)
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
    → MemOps.readLoc (proj₁ (exec-abstract store-indirect st alloc')) loc
      ≡ MemOps.readLoc st loc
  store-ind-preserves-before st alloc alloc' hl .(AtStack _ _) rdi fresh
    (BeforeFrontier.stack-before {f} {j} _ _) = store-ind-preserves-slot st alloc' hl j rdi
  store-ind-preserves-before st alloc alloc' hl .(AtStack _ _) rdi fresh
    (BeforeFrontier.stack-ancestor {f} {j} _ _) = store-ind-preserves-slot st alloc' hl j rdi
  store-ind-preserves-before st alloc alloc' hl .(AtDynamic _) rdi fresh
    (BeforeFrontier.heap-before {h} h<f)
    with sv-as-loc (readReg (regs st) Input1) | rdi
  ... | .(just (AtDynamic hl)) | refl =
    MemOps.writeLoc-preserves-other st (AtDynamic hl) (AtDynamic h)
      (readReg (regs st) Output) (fresh-heap-≢ alloc hl h fresh h<f)

  store-ind-suc-preserves-before : ∀ (st : LocState FS) (alloc alloc' : AllocState {FS})
      (hl : HeapLocation) (loc : ValueLocation FS)
    → sv-as-loc (readReg (regs st) Input1) ≡ just (AtDynamic hl)
    → next-heap-ref alloc ≤ ref-id (heap-ref hl)
    → BeforeFrontier alloc loc
    → MemOps.readLoc (proj₁ (exec-abstract store-indirect-suc st alloc')) loc
      ≡ MemOps.readLoc st loc
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
  module NineStepPres
    (n : ℕ) (i6 i8 : AbstractInstr)
    (u1 : FlatState) (s : LocState FS) (alloc : AllocState {FS})
    -- the start state's allocator, related to the frontier the CALLER's live
    -- data is measured against
    (heapref-u1 : next-heap-ref (falloc u1) ≡ next-heap-ref alloc)
    (cf-u1      : current-frame (falloc u1) ≡ current-frame alloc)
    where

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
      → MemOps.readLoc (floc u10) loc ≡ MemOps.readLoc (floc u1) loc
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

  -- The ENTRY-STATE instance: one `mov-to-output`, then the nine. Every field
  -- is `NineStepPres`'s, re-exported at the names the four existing clauses
  -- already use.
  module TenStepPres
    (n : ℕ) (i6 i8 : AbstractInstr) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    where

    t0 t1 : FlatState
    t0  = entry-flat base s alloc cl
    t1  = flat-step-straight mov-to-output t0

    heapref-t1 : next-heap-ref (falloc t1) ≡ next-heap-ref alloc
    heapref-t1 = exec-abstract-preserves-heap-ref mov-to-output (floc t0) (falloc t0) tt

    cf-t1 : current-frame (falloc t1) ≡ current-frame alloc
    cf-t1 = exec-abstract-preserves-frame mov-to-output (floc t0) (falloc t0)

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

    -- …and the entry-state form: the nine, then the leading `mov-to-output`,
    -- which writes a register and so touches no memory.
    mem-pres :
        InstrNoHeapWrite i6 → instr-writes-slot i6 ≡ nothing
      → InstrNoHeapWrite i8 → instr-writes-slot i8 ≡ nothing
      → next-slot alloc ≤ n
      → sv-as-loc (readReg (regs (floc t6)) Input1) ≡ just (AtDynamic hl)
      → sv-as-loc (readReg (regs (floc t8)) Input1) ≡ just (AtDynamic hl)
      → (loc : ValueLocation FS)
      → BeforeFrontier (record alloc { next-slot = n }) loc
      → MemOps.readLoc (floc t10) loc ≡ MemOps.readLoc s loc
    mem-pres nhw6 nws6 nhw8 nws8 ns≤n rdi6 rdi8 loc bf =
      trans (NSP.mem-pres-from nhw6 nws6 nhw8 nws8 ns≤n rdi6 rdi8 loc bf)
            (mem-untouched mov-to-output (floc t0) (falloc t0) loc
               nhw-mov-to-output refl)

  module ApplySetupPres
    (n : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    where

    arg-stash env-stash pair-stash : ℕ
    arg-stash  = n
    env-stash  = suc n
    pair-stash = suc (suc n)

    a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : FlatState
    a0  = entry-flat base s alloc cl
    a1  = flat-step-straight load-indirect-suc            a0
    a2  = flat-step-straight (store-at-slot arg-stash)    a1
    a3  = flat-step-straight load-indirect                a2
    a4  = flat-step-straight mov-to-input                 a3
    a5  = do-save-closure                                 a4
    a6  = flat-step-straight load-indirect                a5
    a7  = flat-step-straight (store-at-slot env-stash)    a6
    a8  = flat-step-straight (instr-alloc-heap 2)         a7
    a9  = flat-step-straight (store-at-slot pair-stash)   a8
    a10 = flat-step-straight mov-to-input                 a9
    a11 = flat-step-straight (load-from-slot env-stash)   a10
    a12 = flat-step-straight store-indirect               a11
    a13 = flat-step-straight (load-from-slot arg-stash)   a12
    a14 = flat-step-straight store-indirect-suc           a13
    a15 = flat-step-straight (load-from-slot pair-stash)  a14
    a16 = flat-step-straight mov-to-input                 a15

    -- The callee's (env , arg) pair, as the allocator hands it out at a8.
    ahl : HeapLocation
    ahl = heap-loc (mkHeapRef (next-heap-ref (falloc a7))) 0

    heapref-a7 : next-heap-ref (falloc a7) ≡ next-heap-ref alloc
    heapref-a7 =
      trans (exec-abstract-preserves-heap-ref (store-at-slot env-stash) (floc a6) (falloc a6) tt)
     (trans (exec-abstract-preserves-heap-ref load-indirect (floc a5) (falloc a5) tt)
     (trans (exec-abstract-preserves-heap-ref mov-to-input (floc a3) (falloc a3) tt)
     (trans (exec-abstract-preserves-heap-ref load-indirect (floc a2) (falloc a2) tt)
     (trans (exec-abstract-preserves-heap-ref (store-at-slot arg-stash) (floc a1) (falloc a1) tt)
            (exec-abstract-preserves-heap-ref load-indirect-suc (floc a0) (falloc a0) tt)))))

    fresh-a : next-heap-ref alloc ≤ ref-id (heap-ref ahl)
    fresh-a = ≤-reflexive (sym heapref-a7)

    -- The frame does not move: none of the sixteen is a frame op. (Row 5 is
    -- `do-save-closure`, which does not touch `falloc` at all.)
    cf-a1 : current-frame (falloc a1) ≡ current-frame alloc
    cf-a1 = exec-abstract-preserves-frame load-indirect-suc (floc a0) (falloc a0)

    cf-a6 : current-frame (falloc a6) ≡ current-frame alloc
    cf-a6 =
      trans (exec-abstract-preserves-frame load-indirect (floc a5) (falloc a5))
     (trans (exec-abstract-preserves-frame mov-to-input (floc a3) (falloc a3))
     (trans (exec-abstract-preserves-frame load-indirect (floc a2) (falloc a2))
     (trans (exec-abstract-preserves-frame (store-at-slot arg-stash) (floc a1) (falloc a1))
            cf-a1)))

    cf-a8 : current-frame (falloc a8) ≡ current-frame alloc
    cf-a8 =
      trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc a7) (falloc a7))
     (trans (exec-abstract-preserves-frame (store-at-slot env-stash) (floc a6) (falloc a6))
            cf-a6)

    cf-a10 : current-frame (falloc a10) ≡ current-frame alloc
    cf-a10 =
      trans (exec-abstract-preserves-frame mov-to-input (floc a9) (falloc a9))
     (trans (exec-abstract-preserves-frame (store-at-slot pair-stash) (floc a8) (falloc a8))
            cf-a8)

    cf-a12 : current-frame (falloc a12) ≡ current-frame alloc
    cf-a12 =
      trans (exec-abstract-preserves-frame store-indirect (floc a11) (falloc a11))
     (trans (exec-abstract-preserves-frame (load-from-slot env-stash) (floc a10) (falloc a10))
            cf-a10)

    cf-a14 : current-frame (falloc a14) ≡ current-frame alloc
    cf-a14 =
      trans (exec-abstract-preserves-frame store-indirect-suc (floc a13) (falloc a13))
     (trans (exec-abstract-preserves-frame (load-from-slot arg-stash) (floc a12) (falloc a12))
            cf-a12)

    -- THE SETUP PRESERVES EVERYTHING THE CALLER CAN NAME. The three stashes sit
    -- at `n`, `n+1`, `n+2`, all at or above the frontier; the two heap writes
    -- land in the block allocated at row 8.
    setup-mem-pres :
        next-slot alloc ≤ n
      → sv-as-loc (readReg (regs (floc a11)) Input1) ≡ just (AtDynamic ahl)
      → sv-as-loc (readReg (regs (floc a13)) Input1) ≡ just (AtDynamic ahl)
      -- D206: at `apply`'s OWN frontier `n`; its three stashes are `n`,
      -- `suc n`, `suc (suc n)`, all at or above it.
      → (loc : ValueLocation FS)
      → BeforeFrontier (record alloc { next-slot = n }) loc
      → MemOps.readLoc (floc a16) loc ≡ MemOps.readLoc s loc
    setup-mem-pres ns≤n rdi12 rdi14 loc bf =
      trans (mem-untouched mov-to-input (floc a15) (falloc a15) loc nhw-mov-to-input refl)
     (trans (mem-untouched (load-from-slot pair-stash) (floc a14) (falloc a14) loc
               nhw-load-from-slot refl)
     (trans (store-ind-suc-preserves-before (floc a13) (record alloc { next-slot = n })
               (falloc a13) ahl loc rdi14 fresh-a bf)
     (trans (mem-untouched (load-from-slot arg-stash) (floc a12) (falloc a12) loc
               nhw-load-from-slot refl)
     (trans (store-ind-preserves-before (floc a11) (record alloc { next-slot = n })
               (falloc a11) ahl loc rdi12 fresh-a bf)
     (trans (mem-untouched (load-from-slot env-stash) (floc a10) (falloc a10) loc
               nhw-load-from-slot refl)
     (trans (mem-untouched mov-to-input (floc a9) (falloc a9) loc nhw-mov-to-input refl)
     (trans (store-slot-preserves-before pair-stash (floc a8) (record alloc { next-slot = n })
               (falloc a8) loc cf-a8 (≤-trans (n≤1+n n) (n≤1+n (suc n))) bf)
     (trans (mem-untouched (instr-alloc-heap 2) (floc a7) (falloc a7) loc
               nhw-instr-alloc-heap refl)
     (trans (store-slot-preserves-before env-stash (floc a6) (record alloc { next-slot = n })
               (falloc a6) loc cf-a6 (n≤1+n n) bf)
     (trans (mem-untouched load-indirect (floc a5) (falloc a5) loc nhw-load-indirect refl)
     (trans (mem-untouched mov-to-input (floc a3) (falloc a3) loc nhw-mov-to-input refl)
     (trans (mem-untouched load-indirect (floc a2) (falloc a2) loc nhw-load-indirect refl)
     (trans (store-slot-preserves-before arg-stash (floc a1) (record alloc { next-slot = n })
               (falloc a1) loc cf-a1 ≤-refl bf)
            (mem-untouched load-indirect-suc (floc a0) (falloc a0) loc
               nhw-load-indirect-suc refl))))))))))))))

    ------------------------------------------------------------------------
    -- D184: THE CALL LOOKS UP THE CLOSURE'S OWN LABEL — the last thing the
    -- machine side can say before the program's block table has to speak.
    --
    -- `callView` reads two things: the closure REGISTER (saved at row 5 from
    -- `Input1`, which row 4 loaded out of the input pair's first cell) and the
    -- code cell it points at. This says both are exactly what the closure
    -- witness promises: the register holds the closure's own heap pointer, and
    -- the cell holds the label the witness names. What remains after it — and
    -- ALL that remains — is `find-thunk prog ℓ`, i.e. whether the program's
    -- block table implements that label. That is D183's premise.
    ------------------------------------------------------------------------
    -- Row 1 (`load-indirect-suc`) resolves `Input1` and writes `Output`; row 2
    -- writes memory. Neither disturbs `Input1` — but row 1's resolution is a
    -- `Maybe` split, so it is the caller's own witness that collapses it.
    input1-a2 : ∀ (pair-loc : ValueLocation FS) (arg-sv : StoredValue FS)
              → readReg (regs s) Input1 ≡ SV-Ptr pair-loc
              → MemOps.readLoc s (sucLoc pair-loc) ≡ just arg-sv
              → readReg (regs (floc a2)) Input1 ≡ SV-Ptr pair-loc
    input1-a2 pair-loc arg-sv eq cell =
      trans (cong (λ r → readReg r Input1)
                  (MemOps.writeLoc-regs (floc a1)
                     (AtStack (current-frame (falloc a1)) arg-stash)
                     (readReg (regs (floc a1)) Output)))
     (trans (load-ind-suc-preserves-input (floc a0) (falloc a0) pair-loc arg-sv
               (cong sv-as-loc eq) cell)
            eq)

    pair-cell-a2 : ∀ (pair-loc : ValueLocation FS)
                 → next-slot alloc ≤ n → BeforeFrontier alloc pair-loc
                 → MemOps.readLoc (floc a2) pair-loc ≡ MemOps.readLoc s pair-loc
    pair-cell-a2 pair-loc ns≤n bf =
      trans (store-slot-preserves-before arg-stash (floc a1) alloc (falloc a1) pair-loc
               cf-a1 ns≤n bf)
            (mem-untouched load-indirect-suc (floc a0) (falloc a0) pair-loc
               nhw-load-indirect-suc refl)

    ------------------------------------------------------------------------
    -- D185: THE SETUP'S SEVENTEEN OBLIGATIONS. Everything the run needs, in
    -- dependency order — each row's `InstrWF` and its `halted ≡ false`. The
    -- premises are exactly what the input's `ValidAtWF` provides once it is
    -- decomposed: the pair's two cells, the closure's two cells, and the
    -- `BeforeFrontier` of each.
    --
    -- The environment cell is taken as a STORED VALUE (`env-sv`) rather than a
    -- pointer, because D181 made it either — a pointer for a boxed env, the
    -- value itself for a register literal or `Unit`. `load-indirect` at row 6
    -- reads the cell either way, so nothing here needs to know which.
    ------------------------------------------------------------------------
    -- D188: the ARGUMENT is taken as a STORED VALUE too. D187 made a pair cell
    -- either a pointer or the component itself, and row 1 only needs SOMETHING
    -- to be there.
    module Obligations
      (pair-loc fst-loc : ValueLocation FS)
      (arg-sv env-sv : StoredValue FS)
      (rdi      : readReg (regs s) Input1 ≡ SV-Ptr pair-loc)
      (fst-cell : MemOps.readLoc s pair-loc ≡ just (SV-Ptr fst-loc))
      (snd-cell : MemOps.readLoc s (sucLoc pair-loc) ≡ just arg-sv)
      (env-cell : MemOps.readLoc s fst-loc ≡ just env-sv)
      (bf-pair  : BeforeFrontier alloc pair-loc)
      (bf-fst   : BeforeFrontier alloc fst-loc)
      (ns≤n     : next-slot alloc ≤ n)
      (nh       : halted s ≡ false)
      where

      -- ROW 1: the argument pointer, out of the input pair's second cell.
      wf1 : InstrWF (floc a0) (falloc a0) load-indirect-suc
      wf1 = pair-loc , cong sv-as-loc rdi , arg-sv , snd-cell

      -- ROW 3: the closure pointer, out of its first cell.
      wf3 : InstrWF (floc a2) (falloc a2) load-indirect
      wf3 = pair-loc , cong sv-as-loc (input1-a2 pair-loc arg-sv rdi snd-cell)
          , SV-Ptr fst-loc , trans (pair-cell-a2 pair-loc ns≤n bf-pair) fst-cell

      -- ROW 6: the environment, out of the closure's first cell. `Input1` was
      -- pointed at the closure by row 4.
      input1-a5 : readReg (regs (floc a5)) Input1 ≡ SV-Ptr fst-loc
      input1-a5 =
        trans (writeReg-same (regs (floc a3)) Input1 (readReg (regs (floc a3)) Output))
              (exec-abstract-load-indirect-output (floc a2) (falloc a2) pair-loc
                 (SV-Ptr fst-loc) (input1-a2 pair-loc arg-sv rdi snd-cell)
                 (trans (pair-cell-a2 pair-loc ns≤n bf-pair) fst-cell))

      env-cell-a5 : MemOps.readLoc (floc a5) fst-loc ≡ just env-sv
      env-cell-a5 =
        trans (mem-untouched mov-to-input (floc a3) (falloc a3) fst-loc nhw-mov-to-input refl)
       (trans (mem-untouched load-indirect (floc a2) (falloc a2) fst-loc nhw-load-indirect refl)
       (trans (store-slot-preserves-before arg-stash (floc a1) alloc (falloc a1) fst-loc
                 cf-a1 ns≤n bf-fst)
       (trans (mem-untouched load-indirect-suc (floc a0) (falloc a0) fst-loc
                 nhw-load-indirect-suc refl)
              env-cell)))

      wf6 : InstrWF (floc a5) (falloc a5) load-indirect
      wf6 = fst-loc , cong sv-as-loc input1-a5 , env-sv , env-cell-a5

      -- The three `halted` witnesses the conditional rows need, and the
      -- unconditional ones between them.
      nh0 : halted (floc a0) ≡ false
      nh0 = nh
      nh1 : halted (floc a1) ≡ false
      nh1 = exec-abstract-preserves-halted-WF load-indirect-suc (floc a0) (falloc a0) nh0 wf1
      nh2 : halted (floc a2) ≡ false
      nh2 = exec-abstract-preserves-halted-WF (store-at-slot arg-stash) (floc a1) (falloc a1) nh1 tt
      nh3 : halted (floc a3) ≡ false
      nh3 = exec-abstract-preserves-halted-WF load-indirect (floc a2) (falloc a2) nh2 wf3
      nh4 : halted (floc a4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF mov-to-input (floc a3) (falloc a3) nh3 tt
      nh5 : halted (floc a5) ≡ false
      nh5 = nh4
      nh6 : halted (floc a6) ≡ false
      nh6 = exec-abstract-preserves-halted-WF load-indirect (floc a5) (falloc a5) nh5 wf6
      nh7 : halted (floc a7) ≡ false
      nh7 = exec-abstract-preserves-halted-WF (store-at-slot env-stash) (floc a6) (falloc a6) nh6 tt
      nh8 : halted (floc a8) ≡ false
      nh8 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc a7) (falloc a7) nh7 tt
      nh9 : halted (floc a9) ≡ false
      nh9 = exec-abstract-preserves-halted-WF (store-at-slot pair-stash) (floc a8) (falloc a8) nh8 tt
      nh10 : halted (floc a10) ≡ false
      nh10 = exec-abstract-preserves-halted-WF mov-to-input (floc a9) (falloc a9) nh9 tt

      ------------------------------------------------------------------------
      -- THE THREE STASHES, read back. Each survives the rows between its write
      -- and its read: the other stack writes target HIGHER slots, the heap
      -- writes are a different kind of location, and the rest touch no memory.
      --
      -- Ordered by dependency, not by row: the fresh pair's pointer is what the
      -- two indirect stores aim at, so `rdi12'` has to be established before
      -- any read that has to travel across them.
      ------------------------------------------------------------------------

      -- (ii) the ENVIRONMENT, stashed at row 7 and reloaded at row 11.
      env-sv' : StoredValue FS
      env-sv' = readReg (regs (floc a6)) Output

      env-a7 : MemOps.readLoc (floc a7) (AtStack (current-frame (falloc a6)) env-stash)
               ≡ just env-sv'
      env-a7 = MemOps.writeLoc-read-same-stack (floc a6) (current-frame (falloc a6)) env-stash env-sv'

      env-a10 : MemOps.readLoc (floc a10) (AtStack (current-frame (falloc a6)) env-stash)
                ≡ just env-sv'
      env-a10 =
        trans (exec-abstract-preserves-stack-slot mov-to-input (floc a9) (falloc a9)
                 (current-frame (falloc a6)) env-stash nhw-mov-to-input refl)
       (trans (store-at-slot-preserves-below env-stash pair-stash (floc a8) (falloc a8) (n<1+n (suc n)))
       (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc a7) (falloc a7)
                 (current-frame (falloc a6)) env-stash nhw-instr-alloc-heap refl)
              env-a7))

      ------------------------------------------------------------------------
      -- `Input1` AT THE TWO INDIRECT STORES: the fresh pair, put there by row
      -- 10 and surviving the slot loads (which write `Output`) and the first
      -- store (which writes memory).
      ------------------------------------------------------------------------
      alloc-out : readReg (regs (floc a8)) Output ≡ SV-Ptr (AtDynamic ahl)
      alloc-out = writeReg-same (regs (floc a7)) Output (SV-Ptr (AtDynamic ahl))

      input1-a10 : readReg (regs (floc a10)) Input1 ≡ SV-Ptr (AtDynamic ahl)
      input1-a10 =
        trans (writeReg-same (regs (floc a9)) Input1 (readReg (regs (floc a9)) Output))
        (trans (cong (λ r → readReg r Output)
                  (MemOps.writeLoc-regs (floc a8)
                     (AtStack (current-frame (falloc a8)) pair-stash)
                     (readReg (regs (floc a8)) Output)))
               alloc-out)

      wf11 : InstrWF (floc a10) (falloc a10) (load-from-slot env-stash)
      wf11 = env-sv'
           , subst (λ f → MemOps.readLoc (floc a10) (AtStack f env-stash) ≡ just env-sv')
                   (trans cf-a6 (sym cf-a10)) env-a10

      rdi12' : sv-as-loc (readReg (regs (floc a11)) Input1) ≡ just (AtDynamic ahl)
      rdi12' =
        cong sv-as-loc
          (trans (load-slot-preserves-input env-stash (floc a10) (falloc a10) env-sv'
                    (proj₂ wf11))
                 input1-a10)

      -- (i) the ARGUMENT, stashed at row 2 and reloaded at row 13.
      arg-stashed : StoredValue FS
      arg-stashed = readReg (regs (floc a1)) Output

      arg-a2 : MemOps.readLoc (floc a2) (AtStack (current-frame (falloc a1)) arg-stash)
               ≡ just arg-stashed
      arg-a2 = MemOps.writeLoc-read-same-stack (floc a1) (current-frame (falloc a1)) arg-stash arg-stashed

      arg-a12 : MemOps.readLoc (floc a12) (AtStack (current-frame (falloc a1)) arg-stash)
                ≡ just arg-stashed
      arg-a12 =
        trans (store-ind-preserves-slot (floc a11) (falloc a11) ahl arg-stash rdi12')
       (trans (exec-abstract-preserves-stack-slot (load-from-slot env-stash) (floc a10) (falloc a10)
                 (current-frame (falloc a1)) arg-stash nhw-load-from-slot refl)
       (trans (exec-abstract-preserves-stack-slot mov-to-input (floc a9) (falloc a9)
                 (current-frame (falloc a1)) arg-stash nhw-mov-to-input refl)
       (trans (store-at-slot-preserves-below arg-stash pair-stash (floc a8) (falloc a8)
                 (<-trans (n<1+n n) (n<1+n (suc n))))
       (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc a7) (falloc a7)
                 (current-frame (falloc a1)) arg-stash nhw-instr-alloc-heap refl)
       (trans (store-at-slot-preserves-below arg-stash env-stash (floc a6) (falloc a6) (n<1+n n))
       (trans (exec-abstract-preserves-stack-slot load-indirect (floc a5) (falloc a5)
                 (current-frame (falloc a1)) arg-stash nhw-load-indirect refl)
       (trans (exec-abstract-preserves-stack-slot mov-to-input (floc a3) (falloc a3)
                 (current-frame (falloc a1)) arg-stash nhw-mov-to-input refl)
       (trans (exec-abstract-preserves-stack-slot load-indirect (floc a2) (falloc a2)
                 (current-frame (falloc a1)) arg-stash nhw-load-indirect refl)
              arg-a2))))))))

      wf13 : InstrWF (floc a12) (falloc a12) (load-from-slot arg-stash)
      wf13 = arg-stashed
           , subst (λ f → MemOps.readLoc (floc a12) (AtStack f arg-stash) ≡ just arg-stashed)
                   (trans cf-a1 (sym cf-a12)) arg-a12

      rdi14' : sv-as-loc (readReg (regs (floc a13)) Input1) ≡ just (AtDynamic ahl)
      rdi14' =
        cong sv-as-loc
          (trans (load-slot-preserves-input arg-stash (floc a12) (falloc a12) arg-stashed (proj₂ wf13))
          (trans (store-ind-preserves-input (floc a11) (falloc a11) (AtDynamic ahl) rdi12')
                 (trans (load-slot-preserves-input env-stash (floc a10) (falloc a10) env-sv'
                           (proj₂ wf11))
                        input1-a10)))

      -- (iii) the NEW PAIR's pointer, stashed at row 9 and reloaded at row 15.
      newpair-sv : StoredValue FS
      newpair-sv = readReg (regs (floc a8)) Output

      newpair-a9 : MemOps.readLoc (floc a9) (AtStack (current-frame (falloc a8)) pair-stash)
                   ≡ just newpair-sv
      newpair-a9 =
        MemOps.writeLoc-read-same-stack (floc a8) (current-frame (falloc a8)) pair-stash newpair-sv

      newpair-a14 : MemOps.readLoc (floc a14) (AtStack (current-frame (falloc a8)) pair-stash)
                    ≡ just newpair-sv
      newpair-a14 =
        trans (store-ind-suc-preserves-slot (floc a13) (falloc a13) ahl pair-stash rdi14')
       (trans (exec-abstract-preserves-stack-slot (load-from-slot arg-stash) (floc a12) (falloc a12)
                 (current-frame (falloc a8)) pair-stash nhw-load-from-slot refl)
       (trans (store-ind-preserves-slot (floc a11) (falloc a11) ahl pair-stash rdi12')
       (trans (exec-abstract-preserves-stack-slot (load-from-slot env-stash) (floc a10) (falloc a10)
                 (current-frame (falloc a8)) pair-stash nhw-load-from-slot refl)
              newpair-a9)))

      wf15 : InstrWF (floc a14) (falloc a14) (load-from-slot pair-stash)
      wf15 = newpair-sv
           , subst (λ f → MemOps.readLoc (floc a14) (AtStack f pair-stash) ≡ just newpair-sv)
                   (trans cf-a8 (sym cf-a14)) newpair-a14

      -- …and the rest of the `halted` chain, now that every conditional row's
      -- witness is in hand. Row 17 (`instr-call-closure`) is the flat machine's
      -- own step, not an `exec-abstract` one, so it is not here.
      nh11 : halted (floc a11) ≡ false
      nh11 = exec-abstract-preserves-halted-WF (load-from-slot env-stash) (floc a10) (falloc a10) nh10 wf11
      nh12 : halted (floc a12) ≡ false
      nh12 = exec-abstract-preserves-halted-WF store-indirect (floc a11) (falloc a11) nh11
               (AtDynamic ahl , rdi12')
      nh13 : halted (floc a13) ≡ false
      nh13 = exec-abstract-preserves-halted-WF (load-from-slot arg-stash) (floc a12) (falloc a12) nh12 wf13
      nh14 : halted (floc a14) ≡ false
      nh14 = exec-abstract-preserves-halted-WF store-indirect-suc (floc a13) (falloc a13) nh13
               (AtDynamic ahl , rdi14')
      nh15 : halted (floc a15) ≡ false
      nh15 = exec-abstract-preserves-halted-WF (load-from-slot pair-stash) (floc a14) (falloc a14) nh14 wf15
      nh16 : halted (floc a16) ≡ false
      nh16 = exec-abstract-preserves-halted-WF mov-to-input (floc a15) (falloc a15) nh15 tt

      ------------------------------------------------------------------------
      -- D188: THE CALLEE'S PAIR, as the call leaves it. `Input1` points at it,
      -- its first cell holds what the CLOSURE's first cell held and its second
      -- what the caller's pair held — whatever those were (D187).
      ------------------------------------------------------------------------
      input1-a16 : readReg (regs (floc a16)) Input1 ≡ SV-Ptr (AtDynamic ahl)
      input1-a16 =
        trans (writeReg-same (regs (floc a15)) Input1 (readReg (regs (floc a15)) Output))
        (trans (load-slot-result pair-stash (floc a14) (falloc a14) newpair-sv (proj₂ wf15))
               alloc-out)

      env-sv'≡ : env-sv' ≡ env-sv
      env-sv'≡ =
        exec-abstract-load-indirect-output (floc a5) (falloc a5) fst-loc env-sv
          input1-a5 env-cell-a5

      arg-stashed≡ : arg-stashed ≡ arg-sv
      arg-stashed≡ =
        exec-abstract-load-indirect-suc-output (floc a0) (falloc a0) pair-loc arg-sv
          rdi snd-cell

      envout-a11 : readReg (regs (floc a11)) Output ≡ env-sv'
      envout-a11 = load-slot-result env-stash (floc a10) (falloc a10) env-sv' (proj₂ wf11)

      argout-a13 : readReg (regs (floc a13)) Output ≡ arg-stashed
      argout-a13 = load-slot-result arg-stash (floc a12) (falloc a12) arg-stashed (proj₂ wf13)

      pair-fst-a16 : MemOps.readLoc (floc a16) (AtDynamic ahl) ≡ just env-sv
      pair-fst-a16 =
        trans (mem-untouched mov-to-input (floc a15) (falloc a15) (AtDynamic ahl)
                 nhw-mov-to-input refl)
       (trans (mem-untouched (load-from-slot pair-stash) (floc a14) (falloc a14)
                 (AtDynamic ahl) nhw-load-from-slot refl)
       (trans (store-ind-suc-preserves-heap (floc a13) (falloc a13) ahl ahl rdi14'
                 (sucHL-≢ ahl))
       (trans (mem-untouched (load-from-slot arg-stash) (floc a12) (falloc a12)
                 (AtDynamic ahl) nhw-load-from-slot refl)
       (trans (store-ind-result (floc a11) (falloc a11) ahl rdi12')
              (cong just (trans envout-a11 env-sv'≡))))))

      pair-snd-a16 : MemOps.readLoc (floc a16) (sucLoc (AtDynamic ahl)) ≡ just arg-sv
      pair-snd-a16 =
        trans (mem-untouched mov-to-input (floc a15) (falloc a15) (AtDynamic (sucHL ahl))
                 nhw-mov-to-input refl)
       (trans (mem-untouched (load-from-slot pair-stash) (floc a14) (falloc a14)
                 (AtDynamic (sucHL ahl)) nhw-load-from-slot refl)
       (trans (store-ind-suc-result (floc a13) (falloc a13) ahl rdi14')
              (cong just (trans argout-a13 arg-stashed≡))))

      ------------------------------------------------------------------------
      -- The frontier the call hands on, and the transport it licenses.
      ------------------------------------------------------------------------
      heapref-a16 : next-heap-ref (falloc a16) ≡ suc (next-heap-ref (falloc a7))
      heapref-a16 =
        trans (exec-abstract-preserves-heap-ref mov-to-input (floc a15) (falloc a15) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot pair-stash) (floc a14) (falloc a14) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc a13) (falloc a13) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot arg-stash) (floc a12) (falloc a12) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect (floc a11) (falloc a11) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot env-stash) (floc a10) (falloc a10) tt)
       (trans (exec-abstract-preserves-heap-ref mov-to-input (floc a9) (falloc a9) tt)
              (exec-abstract-preserves-heap-ref (store-at-slot pair-stash) (floc a8) (falloc a8) tt)))))))

      before-ahl : BeforeFrontier (falloc a16) (AtDynamic ahl)
      before-ahl = BeforeFrontier.heap-before
                     (subst (λ m → next-heap-ref (falloc a7) < m) (sym heapref-a16) (n<1+n _))

      before-ahl-suc : BeforeFrontier (falloc a16) (sucLoc (AtDynamic ahl))
      before-ahl-suc = BeforeFrontier.heap-before
                         (subst (λ m → next-heap-ref (falloc a7) < m) (sym heapref-a16) (n<1+n _))

      cf-a16 : current-frame (falloc a16) ≡ current-frame alloc
      cf-a16 =
        trans (exec-abstract-preserves-frame mov-to-input (floc a15) (falloc a15))
       (trans (exec-abstract-preserves-frame (load-from-slot pair-stash) (floc a14) (falloc a14))
              cf-a14)

      nextslot-a16 : next-slot (falloc a16) ≡ next-slot alloc
      nextslot-a16 =
        trans (exec-abstract-preserves-next-slot mov-to-input (floc a15) (falloc a15) tt)
       (trans (exec-abstract-preserves-next-slot (load-from-slot pair-stash) (floc a14) (falloc a14) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect-suc (floc a13) (falloc a13) tt)
       (trans (exec-abstract-preserves-next-slot (load-from-slot arg-stash) (floc a12) (falloc a12) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect (floc a11) (falloc a11) tt)
       (trans (exec-abstract-preserves-next-slot (load-from-slot env-stash) (floc a10) (falloc a10) tt)
       (trans (exec-abstract-preserves-next-slot mov-to-input (floc a9) (falloc a9) tt)
       (trans (exec-abstract-preserves-next-slot (store-at-slot pair-stash) (floc a8) (falloc a8) tt)
       (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc a7) (falloc a7) tt)
       (trans (exec-abstract-preserves-next-slot (store-at-slot env-stash) (floc a6) (falloc a6) tt)
       (trans (exec-abstract-preserves-next-slot load-indirect (floc a5) (falloc a5) tt)
       (trans (exec-abstract-preserves-next-slot mov-to-input (floc a3) (falloc a3) tt)
       (trans (exec-abstract-preserves-next-slot load-indirect (floc a2) (falloc a2) tt)
       (trans (exec-abstract-preserves-next-slot (store-at-slot arg-stash) (floc a1) (falloc a1) tt)
              (exec-abstract-preserves-next-slot load-indirect-suc (floc a0) (falloc a0) tt))))))))))))))

      nextslot-a16-≤ : next-slot alloc ≤ next-slot (falloc a16)
      nextslot-a16-≤ = ≤-reflexive (sym nextslot-a16)

      heapref-a16-≤ : next-heap-ref alloc ≤ next-heap-ref (falloc a16)
      heapref-a16-≤ =
        subst (λ m → next-heap-ref alloc ≤ m) (sym heapref-a16)
              (subst (λ m → next-heap-ref alloc ≤ suc m) (sym heapref-a7) (n≤1+n _))

      bf-advance : ∀ {lc : ValueLocation FS} → BeforeFrontier alloc lc
                 → BeforeFrontier (falloc a16) lc
      bf-advance (BeforeFrontier.stack-before f≡cf j<ns) =
        BeforeFrontier.stack-before (trans f≡cf (sym cf-a16)) (<-≤-trans j<ns nextslot-a16-≤)
      bf-advance (BeforeFrontier.stack-ancestor cf≺f src) =
        BeforeFrontier.stack-ancestor
          (subst (λ c → Once.CCC.FrameSemantics.FrameSemantics._≺_ FS c _)
                 (sym cf-a16) cf≺f) src
      bf-advance (BeforeFrontier.heap-before r<h) =
        BeforeFrontier.heap-before (<-≤-trans r<h heapref-a16-≤)

      -- A component that was valid for the caller is valid for the callee: the
      -- setup writes only fresh cells and the frontier only advances.
      carry : ∀ {mC C} (c : ⟦ C ⟧) (lc : ValueLocation FS)
            → BeforeFrontier alloc lc → ValidAtWF mC alloc {C} c lc s
            → ValidAtWF mC (falloc a16) {C} c lc (floc a16)
      carry c lc cb v =
        validityWF-frontier-advance c lc (floc a16) cf-a16 nextslot-a16-≤ heapref-a16-≤
          (validityWF-mem-preserved c lc s (floc a16) cb
             -- D206: `setup-mem-pres` is stated at apply's own frontier `n`;
             -- the caller's data lies below `next-slot alloc ≤ n`, so the
             -- hypothesis weakens upward.
             (λ loc' bf' → setup-mem-pres ns≤n rdi12' rdi14' loc'
                             (frontier-monotone alloc (record alloc { next-slot = n })
                                refl ns≤n ≤-refl loc' bf'))
             v)

      -- The two premises `setup-mem-pres` and `code-cell` ask for, discharged
      -- here rather than at the call site: they are facts about THIS run.
      mem-pres : (loc : ValueLocation FS)
               → BeforeFrontier (record alloc { next-slot = n }) loc
               → MemOps.readLoc (floc a16) loc ≡ MemOps.readLoc s loc
      mem-pres = setup-mem-pres ns≤n rdi12' rdi14'

    -- The closure register, at the call.
    closure-reg : ∀ (pair-loc fst-loc : ValueLocation FS) (arg-stashed : StoredValue FS)
                → next-slot alloc ≤ n → BeforeFrontier alloc pair-loc
                → readReg (regs s) Input1 ≡ SV-Ptr pair-loc
                → MemOps.readLoc s (sucLoc pair-loc) ≡ just arg-stashed
                → MemOps.readLoc s pair-loc ≡ just (SV-Ptr fst-loc)
                → fclosure a16 ≡ SV-Ptr fst-loc
    closure-reg pair-loc fst-loc arg-stashed ns≤n bf rdi snd-cell cell =
      trans (writeReg-same (regs (floc a3)) Input1 (readReg (regs (floc a3)) Output))
            (exec-abstract-load-indirect-output (floc a2) (falloc a2) pair-loc
               (SV-Ptr fst-loc) (input1-a2 pair-loc arg-stashed rdi snd-cell)
               (trans (pair-cell-a2 pair-loc ns≤n bf) cell))

    -- …and the code cell it points at, carried across the setup.
    code-cell : ∀ (fst-loc : ValueLocation FS) (ℓ : LabelId)
              → next-slot alloc ≤ n
              → sv-as-loc (readReg (regs (floc a11)) Input1) ≡ just (AtDynamic ahl)
              → sv-as-loc (readReg (regs (floc a13)) Input1) ≡ just (AtDynamic ahl)
              → BeforeFrontier alloc (sucLoc fst-loc)
              → MemOps.readLoc s (sucLoc fst-loc) ≡ just (SV-Code ℓ)
              → MemOps.readLoc (floc a16) (sucLoc fst-loc) ≡ just (SV-Code ℓ)
    code-cell fst-loc ℓ ns≤n rdi12 rdi14 bf-suc cell =
      trans (setup-mem-pres ns≤n rdi12 rdi14 (sucLoc fst-loc)
               (frontier-monotone alloc (record alloc { next-slot = n })
                  refl ns≤n ≤-refl (sucLoc fst-loc) bf-suc))
            cell

  -- D170 / Phase E2 probe: the DENOTATION half of `obs-correct-curry`.
  -- `curry` builds a value; it invokes no SigOp, so its trace is empty at every
  -- depth. Named here because it is one of the two halves the discharge needs,
  -- and because it is `refl` — which is the evidence that the clause is
  -- Class-B shaped rather than label-bearing.

