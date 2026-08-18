-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-32.FlatSimulation
--
-- Plan 0.32 Phase D, Stage 2: the abstract↔x86 plus-simulation over the
-- flat machine. `CompiledCorr hv prog fs s` relates a FlatState `fs` (flat
-- pc/fuel machine, typed StoredValues) to an x86 `State s` running the
-- compiled program `compile-trace prog`, where:
--   * the DATA agrees (registers under enc-sv, heap under enc-hl, flags,
--     halt) — exactly the FlatCorrespondence.FlatCorr data fields, and
--   * the CONTROL agrees up to the block offset: x86.pc = blk-off prog
--     (fpc fs)  (one flat instruction ↦ a contiguous x86 BLOCK; NOT 1-to-1
--     lockstep — see [[feedback-injectivity-not-lockstep]]).
--
-- The jump correspondence rides `FlatComposition.find-label-corr`. The
-- per-instruction DATA effects ride the FlatCorrespondence `sim-*` lemmas.
-- This module composes them under fuel.
--
-- ROADMAP (this file, in progress):
--   [x] CompiledCorr relation (data ⊕ block-offset pc)
--   [ ] block-step: one flat step ↔ `exec (blk-len i)` of its x86 block,
--       preserving CompiledCorr (uses sim-* for data, find-label-corr for
--       jumps, blk-off for the pc advance). Needs the per-x86-instr
--       "execInstr reduces to the sim-* post-state" facts (the deferred
--       (B) obligations).
--   [ ] fuel induction: exec-flat fuel prog fs ↔ exec (bound) (compile-
--       trace prog) s, lifting block-step; fuel bound = Σ blk-len.
--   [ ] wire into Correct.agda (retires compile-ir).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; shift-frame; frame-word; frame-base; shift-base; slot-addr; slot-addr-linear)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-ref; ref-id)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Once.CCC.Target.X86-32.Syntax using (slot-size)
open import Once.Type using (fits-int)
open import Once.Word using (Carrier)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≡ᵇ_; _<_; _≤_; s≤s; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.CanonicalName using (CanonicalName)

module Once.Adequacy.ArchCorrectness.X86-32.FlatSimulation
  -- D089's definition identity, threaded only so `CompiledCorrespondence` can
  -- state `bs-lea-slot`'s `RunAt` premise (2026-08-16).
  (o : CanonicalName)
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open import Once.CCC.Machine.FlatStoreWF FS using (sv-below; svm-below; StoreWF; FlatWF; flat-wf-step; wf-regs; wf-heap; wf-stack; wf-fresh)
import Once.CCC.Target.X86-32.Semantics as X
open X using (mkstate; execInstr; mkflags; _<ᵇ_; writeMem; updateFlags)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-32.Syntax
  using (eax; edx; ecx; esp; ebp; edi; esi; Reg; Operand; Program; reg; imm; mem; mov; add; sub; cmp; label; jmp-l; je; push; pop; lea; ebx; base; base+disp; slots; slot-size; ret; call; mov-code)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (true; false)
open import Data.List using (_∷_; []; _++_; drop; length)
open import Relation.Binary.PropositionalEquality using (refl)

import Once.Adequacy.ArchCorrectness.X86-32.FlatCorrespondence as FC
module C = FC FS word-eq   -- HeapView / enc-sv / FlatCorr data fields
open C using (HeapView; haddr; HDom; hfront)
open import Once.CCC.Label using (once; thunk; LabelId)
-- Plan 0.65 G1c step 2: the register-poke sims take any post-state `SetsRole`
-- describes; `C.sets-role-x86` is x86-32 exhibiting the one it builds.
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (role-sp; role-clos; role-heap; role-out; role-in1; role-scratch; role-count)
open import Once.Adequacy.ArchCorrectness.X86-32.FlatComposition FS
  using (blk-off; blk-len; blk-off-suc; fetch-block-head; find-label-corr; find-thunk-corr; fetch-block-2nd; fetch-block-3rd; fetch-block-4th; fetch-block-5th; fetch-block-6th)
open import Once.Adequacy.ArchCorrectness.X86-32.StepLemmas using (exec-1; step-mov-rr; step-mov-ri; step-label; step-jmp-l; step-mov-rm; step-mov-mr; step-add-ri; step-add-rr; step-sub-ri; step-cmp-ri; step-cmp-mi; step-je-taken; step-je-not; step-push; step-pop; step-lea; step-mov-code; step-ret; step-call)
open import Once.CCC.Target.X86-32.AbstractToX86-32 using (compile-trace; compile-abstract; slot-to-disp)
open import Data.Empty using (⊥)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-comm; ∸-+-assoc; *-suc; *-identityʳ; *-assoc
                                      ; +-monoʳ-<; *-monoˡ-<
                                      ; <⇒≢; <-transˡ; ≤-trans; m∸n≤m; m≤m+n; m∸n+n≡m
                                      ; m<m+n; ≤-refl; ≤-<-trans; m≤n+m; +-monoʳ-≤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst; subst₂)
open MemOps {FS} using (writeLoc; writeLocToHeap; readLoc)
open import Once.Float.Dyadic using (Dyadic; encode; binary32; binary64)
open import Once.Type using (fits-float)
open import Data.Float using () renaming (Float to AgdaFloat)

------------------------------------------------------------------------
-- The compiled correspondence = the DATA correspondence (FlatCorr, now
-- pc-free) ⊕ the block-offset pc relation. block-step gets the data from
-- the sim-* lemmas (which produce FlatCorr) and the pc from blk-off-suc /
-- find-label-corr — cleanly separated. (Plan 0.34: no zf-eq.)
------------------------------------------------------------------------
-- THE COMPILED CORRESPONDENCE — NOW THE CORE'S (plan 0.65 G2, item 4's first
-- slice). x86-32's record and riscv64's were structurally identical, differing
-- only in the state type, so it moved to `FlatCore.CompiledCorrespondence` and
-- both arches instantiate it. The field comments (why `pc-off`/`ret-eq`/
-- `code-eq` live here rather than in `FlatCorr` — D093, D096) moved with it.
open import Once.Adequacy.ArchCorrectness.X86-32.RegRoles using (x86-32-roles)
xrreg : X.State → Reg → ℕ
xrreg s r = X.readReg (X.State.regs s) r

-- WHERE AN UNSPILLED RETURN LIVES ON x86-32: exactly where a spilled one does.
-- `call` PUSHES the return address, so the head row of `RetAddrs` in the
-- call/marker window is the same memory claim as every other row — which is
-- what makes this arch's three structural proofs a two-clause adapter rather
-- than an argument. RISC-V is where the two rows differ.
x86-32-link-claim : X.State → ℕ → ℕ → Set
x86-32-link-claim s a v = X.State.memory s a ≡ just v

open import Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
       o FS slot-size word-eq (encode binary32) Reg x86-32-roles X.State xrreg X.State.memory X.State.halted
       x86-32-link-claim
       X.State.pc Program compile-trace X.find-label blk-off blk-len X.exec
       X.W.modulus
  public

------------------------------------------------------------------------
-- (B) execInstr-reduces facts. For each x86 instruction the codegen
-- emits, `execInstr` reduces to the exact post-state the FlatCorrespondence
-- `sim-*` lemmas assume. The PURE ones (register/imm/arith/cmp) are stated
-- standalone here; the memory ones (loads/stores) depend on the heap
-- correspondence and are discharged inside block-step.
------------------------------------------------------------------------
-- mov (reg dst) (reg src): eax↔ecx register shuffles (mov-to-output, …).
b-mov-reg-reg : ∀ (prog : Program) (s : X.State) (dst src : Reg)
  → execInstr prog s (mov (reg dst) (reg src))
    ≡ just (mkstate (xwriteReg (xregs s) dst (xreadReg (xregs s) src))
                    (memory s) (flags s) (pc s + 1) (xhalted s))
b-mov-reg-reg prog s dst src = refl

-- mov (reg dst) (imm n): tag/reg-op immediate loads (load-tag-lit, …).
-- PLAN 0.70 PHASE D: the machine NORMS an immediate (an immediate field holds a
-- machine word), so this readout says so. Consumers convert with `W.norm-id` /
-- `W.norm-0` where they know the immediate fits.
b-mov-reg-imm : ∀ (prog : Program) (s : X.State) (dst : Reg) (n : ℕ)
  → execInstr prog s (mov (reg dst) (imm n))
    ≡ just (mkstate (xwriteReg (xregs s) dst (X.W.norm n))
                    (memory s) (flags s) (pc s + 1) (xhalted s))
b-mov-reg-imm prog s dst n = refl

-- cmp (reg dst) (imm n): the control test (c-test-scratch). Like the flat
-- test, it SETS zf (= the dst≟n result) — so it preserves zf-eq, unlike
-- the arithmetic ops below.
b-cmp-reg-imm : ∀ (prog : Program) (s : X.State) (dst : Reg) (n : ℕ)
  → execInstr prog s (cmp (reg dst) (imm n))
    ≡ just (mkstate (xregs s) (memory s)
                    (mkflags (xreadReg (xregs s) dst ≡ᵇ X.W.norm n) (xreadReg (xregs s) dst <ᵇ X.W.norm n) false)
                    (pc s + 1) (xhalted s))
b-cmp-reg-imm prog s dst n = refl

------------------------------------------------------------------------
-- block-step (Plan 0.32 Stage 2): one flat step ↔ X.exec (blk-len i) of
-- its compiled block, preserving CompiledCorr. Result type abbreviation:
------------------------------------------------------------------------
-- A step may EXTEND the heap view (only `instr-alloc-heap` does); `BlockStep`
-- is the same-view case, `BlockStepAt hv hv'` the general one.
-- (`BlockStepAt`/`BlockStep` moved to FlatCore.CompiledCorrespondence:
--  identical on both arches but for the state type and which `exec`.)

-- THE RETURN PICTURE IS UNTOUCHED (D093). The generic helpers below are
-- polymorphic in the instruction, so `falloc (flat-exec-instr i prog fs)` does
-- not reduce and they cannot see that a straight-line step moves neither the
-- frame stack nor the ghost return stack. Stated once as a pair of equations
-- the caller discharges with `refl refl` (`i` is concrete there) — the same
-- shape as the `fpc-eq` premise beside it, and the same reason.
-- (Third component added 2026-08-16: `RetAddrs` now selects its head row by
-- `flink`, so "the return picture is untouched" includes the link marker. Every
-- straight-line instruction discharges it `refl` — `flinkView` says so, and
-- these call sites are where that pays out.)
RetSame : AbstractTrace → FlatState → AbstractInstr → Set
RetSame prog fs i =
  (C.frames-of (falloc (flat-exec-instr i prog fs)) ≡ C.frames-of (falloc fs))
  × (fret (flat-exec-instr i prog fs) ≡ fret fs)
  × (flink (flat-exec-instr i prog fs) ≡ flink fs)

-- …and its use: carry the pre-state's component across such a step. `mem` is
-- explicit because the helpers that WRITE memory (the stores) need it at their
-- own post-memory, with a separation argument rather than this.
ret-same : ∀ (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr)
             (mem : X.Memory) {LK : ℕ → ℕ → Set} (rs : RetSame prog fs i)
         → C.RetAddrs (blk-off prog) mem LK (flink fs) (C.frames-of (falloc fs)) (fret fs)
         → C.RetAddrs (blk-off prog) mem LK (flink (flat-exec-instr i prog fs))
                      (C.frames-of (falloc (flat-exec-instr i prog fs)))
                      (fret (flat-exec-instr i prog fs))
ret-same prog fs i _ (fr-eq , rt-eq , fl-eq) r
  rewrite fr-eq | rt-eq | fl-eq = r

-- A HEAP STORE MISSES THEM TOO, and more easily: a live heap cell is below the
-- frontier (`dom-below`), the frontier is below the high-water mark
-- (`front-lo`), and every live frame's base is at or above that mark — so the
-- whole heap is under every return cell. This is the layout separation the
-- correspondence already carries, read at a new address.
ret-heap-store : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : X.State)
                   (a : ℕ) (v : X.Word)
               → CompiledCorr hv prog fs s
               → a < C.lo hv
               → C.RetAddrs (blk-off prog) (writeMem (X.State.memory s) a v)
                            (λ ad w → writeMem (X.State.memory s) a v ad ≡ just w)
                            (flink fs) (C.frames-of (falloc fs)) (fret fs)
ret-heap-store {hv} prog fs s a v cc a<lo =
  C.ret-agree-above (blk-off prog) (X.State.memory s) (writeMem (X.State.memory s) a v)
    (x86-32-link-claim s) (λ ad w → writeMem (X.State.memory s) a v ad ≡ just w)
    (flink fs)
    (stackMem (floc fs)) (C.lo hv) (C.frames-of (falloc fs)) (fret fs)
    (λ c le → C.read-write-miss (X.State.memory s) a v c (λ eq → <⇒≢ (<-transˡ a<lo le) (sym eq)))
    -- THE HEAD ROW TRAVELS BY THE SAME MISS, because on x86-32 it IS the memory
    -- claim (`call` pushed the return address). This is the two-line adapter the
    -- plan promised, and it is why the ~21 call sites did not move.
    (λ c w le p → trans (C.read-write-miss (X.State.memory s) a v c
                           (λ eq → <⇒≢ (<-transˡ a<lo le) (sym eq))) p)
    (C.stack-eq (dataCorr cc)) (ret-eq cc)

-- A STACK STORE MISSES EVERY PENDING RETURN (D093). The write is inside this
-- frame's window (`slot < frame-slots`, the emitted-code discipline), and the
-- head's return cell is the window END — one slot above the last slot it can
-- reach. Everything older is above that end by the floor thread. This is the
-- D086 gap doing its job.
ret-slot-store : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : X.State)
                   (slot : Slot) (v : X.Word)
               → CompiledCorr hv prog fs s
               → slot < frame-slots (falloc fs)
               → C.RetAddrs (blk-off prog)
                   (writeMem (X.State.memory s) (X.readReg (xregs s) esp + slot-to-disp slot) v)
                   (λ ad w → writeMem (X.State.memory s)
                               (X.readReg (xregs s) esp + slot-to-disp slot) v ad ≡ just w)
                   (flink fs) (C.frames-of (falloc fs)) (fret fs)
ret-slot-store {hv} prog fs s slot v cc slot<b =
  C.ret-write-in-frame (blk-off prog) (X.State.memory s)
    (x86-32-link-claim s)
    (λ ad w → writeMem (X.State.memory s)
                (X.readReg (xregs s) esp + slot-to-disp slot) v ad ≡ just w)
    (flink fs) (stackMem (floc fs))
    (X.readReg (xregs s) esp + slot-to-disp slot) v (C.lo hv)
    (current-frame (falloc fs)) (frame-slots (falloc fs))
    (saved-frames (falloc fs)) (fret fs)
    w<end
    -- the same adapter as `ret-heap-store`'s, at this write's own miss
    (λ c w lt p → trans (C.read-write-miss (X.State.memory s)
                           (X.readReg (xregs s) esp + slot-to-disp slot) v c
                           (λ eq → <⇒≢ lt (sym eq))) p)
    (C.stack-eq (dataCorr cc)) (ret-eq cc)
  where
    w<end : X.readReg (xregs s) esp + slot-to-disp slot
          < frame-base FS (current-frame (falloc fs)) + slots (frame-slots (falloc fs))
    w<end rewrite C.sp-eq (dataCorr cc) =
      +-monoʳ-< (frame-base FS (current-frame (falloc fs))) (*-monoˡ-< slot-size slot<b)

-- The two `Maybe`-dispatched loads keep the INPUT allocator in both branches,
-- so the frame picture is unchanged — but only once the `Maybe` is split,
-- which is why these exist (`FlatStackSlot.ss-mv` is the same fact for
-- `frame-slots` alone; `RetAddrs` needs the whole frame list).
elfs-frames : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
            → C.frames-of (proj₂ (AbstractExec.exec-load-from-slot-with-value {FS} mv ls alloc))
              ≡ C.frames-of alloc
elfs-frames (just v) ls alloc = refl
elfs-frames nothing  ls alloc = refl

eris-frames : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
            → C.frames-of (proj₂ (AbstractExec.exec-restore-input-with-value {FS} mv ls alloc))
              ≡ C.frames-of alloc
eris-frames (just v) ls alloc = refl
eris-frames nothing  ls alloc = refl

-- Generic single-`mov reg,reg` block-step: any straight-line instruction
-- whose x86 block is one `mov (reg dst) (reg src)`. The caller supplies the
-- compile-abstract shape (refl) + the DATA correspondence (a sim-* lemma).
-- Assembly: fetch-block-head + step-mov-rr + exec-1 (x86), then pc via
-- pc-off + blk-off-suc. No flags (Plan 0.34).
block-step-mov-rr : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : X.State)
    (i : AbstractInstr) (dst src : Reg)
  → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just i
  → compile-abstract i ≡ mov (reg dst) (reg src) ∷ []
  → fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)         -- i is straight-line
  → RetSame prog fs i                                      -- …and moves no frame
  → C.FlatCorr hv (flat-exec-instr i prog fs)
               (record s { regs = xwriteReg (xregs s) dst (xreadReg (xregs s) src) ; pc = pc s + 1 })
  → BlockStep hv prog fs s i
block-step-mov-rr {hv} prog fs s i dst src cc h-flat ft ca fpc-eq rsame dataPost =
  post , exec-eq-len , record { dataCorr = dataPost ; pc-off = pco'
                             ; ret-eq = ret-same prog fs i (memory s) rsame (ret-eq cc)
                             ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h-flat
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg dst) (reg src))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (trans (fetch-block-head prog (fpc fs) i ft)
                             (cong (λ b → X.fetch (b ++ compile-trace (drop (suc (fpc fs)) prog)) 0) ca))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) dst (xreadReg (xregs s) src) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rr {compile-trace prog} {s} {dst} {src} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    exec-eq-len : X.exec (blk-len i) (compile-trace prog) s ≡ just post
    exec-eq-len = trans (cong (λ m → X.exec m (compile-trace prog) s) (cong length ca)) exec-eq
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr i prog fs))
    pco' rewrite fpc-eq =
      trans (cong (_+ 1) po)
            (trans (sym (cong (blk-off prog (fpc fs) +_) (cong length ca)))
                   (sym (blk-off-suc prog (fpc fs) i ft)))

-- The four register shuffles (mov-to-output ↔ eax/ecx, …) — one-liners.
block-step-mov-to-output : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-to-output → BlockStep hv prog fs s mov-to-output
block-step-mov-to-output {hv} prog fs s cc h ft =
  block-step-mov-rr prog fs s mov-to-output eax ecx cc h ft refl refl (refl , refl , refl) (C.sim-mov-to-output fs s _ (dataCorr cc) (C.sets-role-x86 s role-out _ _ _))

block-step-mov-to-input : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-to-input → BlockStep hv prog fs s mov-to-input
block-step-mov-to-input {hv} prog fs s cc h ft =
  block-step-mov-rr prog fs s mov-to-input ecx eax cc h ft refl refl (refl , refl , refl) (C.sim-mov-to-input fs s _ (dataCorr cc) (C.sets-role-x86 s role-in1 _ _ _))



-- Generic single-`mov reg,imm` block-step (load-tag-lit, reg-op imm loads).
block-step-mov-ri : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : X.State)
    (i : AbstractInstr) (dst : Reg) (n : ℕ)
  → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just i
  → compile-abstract i ≡ mov (reg dst) (imm n) ∷ []
  -- PLAN 0.70 PHASE D — THE IMMEDIATE FITS IN A MACHINE WORD. The machine norms
  -- an immediate (an immediate field IS a word), so reading the post-state back
  -- as a bare `n` needs `n` in range. This is the `lit-word : Carrier → Word`
  -- seam made visible: the model used to admit a register holding a value no
  -- register can hold. Callers with a literal immediate discharge it by
  -- computation; `instr-load-const` is where it becomes a real obligation.
  → n < X.W.modulus
  → fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)
  → RetSame prog fs i                                      -- …and moves no frame
  → C.FlatCorr hv (flat-exec-instr i prog fs)
               (record s { regs = xwriteReg (xregs s) dst n ; pc = pc s + 1 })
  → BlockStep hv prog fs s i
block-step-mov-ri {hv} prog fs s i dst n cc h-flat ft ca fits fpc-eq rsame dataPost =
  post , exec-eq-len , record { dataCorr = dataPost ; pc-off = pco'
                             ; ret-eq = ret-same prog fs i (memory s) rsame (ret-eq cc)
                             ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h-flat
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg dst) (imm n))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (trans (fetch-block-head prog (fpc fs) i ft)
                             (cong (λ b → X.fetch (b ++ compile-trace (drop (suc (fpc fs)) prog)) 0) ca))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) dst n ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → X.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = xwriteReg (xregs s) dst w ; pc = pc s + 1 }))
                (X.W.norm-id fits)
                (step-mov-ri {compile-trace prog} {s} {dst} {n} fetch-x86)
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    exec-eq-len : X.exec (blk-len i) (compile-trace prog) s ≡ just post
    exec-eq-len = trans (cong (λ m → X.exec m (compile-trace prog) s) (cong length ca)) exec-eq
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr i prog fs))
    pco' rewrite fpc-eq =
      trans (cong (_+ 1) po)
            (trans (sym (cong (blk-off prog (fpc fs) +_) (cong length ca)))
                   (sym (blk-off-suc prog (fpc fs) i ft)))

-- PLAN 0.70 PHASE D: the tag literal must FIT IN A MACHINE WORD. Propagated
-- rather than discharged here, because `n` is this lemma's own parameter — the
-- caller is where a concrete tag is known.
block-step-load-tag-lit : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-tag-lit n) → n < X.W.modulus
  → BlockStep hv prog fs s (instr-load-tag-lit n)
block-step-load-tag-lit {hv} prog fs s n cc h ft fits =
  block-step-mov-ri prog fs s (instr-load-tag-lit n) eax n cc h ft refl fits refl (refl , refl , refl) (C.sim-load-tag-lit n fs s _ (dataCorr cc) (C.sets-role-x86 s role-out _ _ _))

block-step-scratch-one : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-one) → BlockStep hv prog fs s (instr-reg-op scratch-one)
block-step-scratch-one {hv} prog fs s cc h ft =
  block-step-mov-ri prog fs s (instr-reg-op scratch-one) edx 1 cc h ft refl (X.W.1<modulus (s≤s z≤n)) refl (refl , refl , refl) (C.sim-reg-scratch-one fs s _ (dataCorr cc) (C.sets-role-x86 s role-scratch _ _ _))

block-step-scratch-zero : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-zero) → BlockStep hv prog fs s (instr-reg-op scratch-zero)
block-step-scratch-zero {hv} prog fs s cc h ft =
  block-step-mov-ri prog fs s (instr-reg-op scratch-zero) edx 0 cc h ft refl X.W.0<modulus refl (refl , refl , refl) (C.sim-reg-scratch-zero fs s _ (dataCorr cc) (C.sets-role-x86 s role-scratch _ _ _))

block-step-count-zero : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op count-zero) → BlockStep hv prog fs s (instr-reg-op count-zero)
block-step-count-zero {hv} prog fs s cc h ft =
  block-step-mov-ri prog fs s (instr-reg-op count-zero) edi 0 cc h ft refl X.W.0<modulus refl (refl , refl , refl) (C.sim-reg-count-zero fs s _ (dataCorr cc) (C.sets-role-x86 s role-count _ _ _))

block-step-scratch-load-count : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-load-count) → BlockStep hv prog fs s (instr-reg-op scratch-load-count)
block-step-scratch-load-count {hv} prog fs s cc h ft =
  block-step-mov-rr prog fs s (instr-reg-op scratch-load-count) edx edi cc h ft refl refl (refl , refl , refl) (C.sim-reg-scratch-load-count fs s _ (dataCorr cc) (C.sets-role-x86 s role-scratch _ _ _))

-- c-label: pc passes through (x86 `label` is a 1-instr no-op). The flat
-- step only bumps fpc, so the DATA correspondence transports unchanged
-- (no sim-* needed — floc/regs are untouched on both sides).
block-step-c-label : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-label n)) → BlockStep hv prog fs s (instr-ctrl (c-label n))
block-step-c-label {hv} prog fs s n cc h ft = post , exec-eq , record
  { dataCorr = record { in1-eq = C.in1-eq (dataCorr cc)
                      ; out-eq = C.out-eq (dataCorr cc) ; scratch-eq = C.scratch-eq (dataCorr cc) ; count-eq = C.count-eq (dataCorr cc)
                      ; clos-eq = C.clos-eq (dataCorr cc) ; halt-eq = C.halt-eq (dataCorr cc) ; heap-eq = C.heap-eq (dataCorr cc)
                      ; sp-eq = C.sp-eq (dataCorr cc)
                      ; sp-eq = C.sp-eq (dataCorr cc) ; frontier-eq = C.frontier-eq (dataCorr cc) ; dom-fresh = C.dom-fresh (dataCorr cc) ; dom-written = C.dom-written (dataCorr cc) ; dom-sized = C.dom-sized (dataCorr cc)
                      ; lo-le = C.lo-le (dataCorr cc) ; untouched = C.untouched (dataCorr cc) ; stack-eq = C.stack-eq (dataCorr cc) }
  ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (label (once n))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-label n)) ft)
    post : X.State
    post = record s { pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-label {compile-trace prog} {s} {once n} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-ctrl (c-label n)) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-label n)) ft))

-- Plan 0.63 step 2a: `c-thunk` NO LONGER HAS A BLOCK-STEP HERE. Step 1's
-- `block-step-c-thunk` was a copy of `block-step-c-label` — sound while the
-- marker lowered to a bare `label`. It now lowers to `label ; subq $b*8,%esp`
-- and RESERVES THE BODY'S FRAME, so its correspondence is
-- `block-step-alloc-stack`'s: the descending high-water view plus freshness
-- of the callee frame (`fresh-abs`) and the honest `stack-room`.
-- Those premises cannot be supplied until the bodies are emitted and the
-- per-frame story exists (plan 0.63 steps 2b/2c), so until then the marker
-- has no producer and `events-running-fetch` routes it absurdly — the same
-- fence as `c-ret` and the frame ops. The brick to compose when 2c lands is
-- `block-step-alloc-stack` below, preceded by a `step-label` fetch.

-- worklist-init / worklist-check: pure cata bookkeeping — compile to [] (blk-len 0),
-- flat step is identity (exec-abstract = s,alloc) mod fpc, x86 does nothing. FlatCorr
-- copied (floc/falloc unchanged); pc-off shifts by blk-len 0 (+-identityʳ). The
-- cleanest possible block-step: `X.exec 0 = just s` is refl.
block-step-worklist-init : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-init n) → BlockStep hv prog fs s (worklist-init n)
block-step-worklist-init {hv} prog fs s n cc h ft = s , refl , record
  { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                      ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
  ; pc-off = trans (pc-off cc)
             (sym (trans (blk-off-suc prog (fpc fs) (worklist-init n) ft) (+-identityʳ _)))
             ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where dc = dataCorr cc

block-step-worklist-check : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-check n) → BlockStep hv prog fs s (worklist-check n)
block-step-worklist-check {hv} prog fs s n cc h ft = s , refl , record
  { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                      ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
  ; pc-off = trans (pc-off cc)
             (sym (trans (blk-off-suc prog (fpc fs) (worklist-check n) ft) (+-identityʳ _)))
             ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where dc = dataCorr cc

-- instr-reclaim-to: allocation bookkeeping — compile to [] (blk-len 0), flat step
-- lowers `next-slot` (floc + heapMem unchanged). The heap correspondence is carried
-- by the VIEW (not indexed by the abstract alloc state), so it copies through
-- unchanged — this is what retired the old `LiveIn-reclaim` allocator postulate.
block-step-reclaim-to : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reclaim-to n) → BlockStep hv prog fs s (instr-reclaim-to n)
block-step-reclaim-to {hv} prog fs s n cc h ft = s , refl , record
  { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                      ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                      ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }   -- reclaim-to changes next-slot, not frame-slots ⇒ bound stable
  ; pc-off = trans (pc-off cc)
             (sym (trans (blk-off-suc prog (fpc fs) (instr-reclaim-to n) ft) (+-identityʳ _)))
             ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where dc = dataCorr cc

-- c-jmp: unconditional jump. find-label-corr maps the flat label index to
-- the x86 block-offset, so the x86 `jmp` lands at the same place. Data
-- unchanged (jmp touches only the pc). Hypothesis: the target exists.
block-step-c-jmp : ∀ {hv : HeapView} prog fs s n j → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp n))
  → find-label prog n ≡ just j
  → BlockStep hv prog fs s (instr-ctrl (c-jmp n))
block-step-c-jmp {hv} prog fs s n j cc h ft fl-eq = block-step
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (jmp-l (once n))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-jmp n)) ft)
    fl-x86 : X.find-label (compile-trace prog) (once n) ≡ just (blk-off prog j)
    fl-x86 = find-label-corr prog n 0 j fl-eq
    post : X.State
    post = record s { pc = blk-off prog j }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-jmp-l {compile-trace prog} {s} {once n} {blk-off prog j} fetch-x86 fl-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    block-step : BlockStep hv prog fs s (instr-ctrl (c-jmp n))
    block-step rewrite fl-eq = post , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc
                          ; out-eq = C.out-eq dc ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc
                          ; clos-eq = C.clos-eq dc ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc ; heap-eq = C.heap-eq dc
                          ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = refl ; ret-eq = ret-eq cc ; code-eq = code-eq cc }

-- load-indirect: Output := *Input1 ↔ `mov eax, [ecx]`. The read VALUE comes
-- from heap-eq (memory s at haddr hv hl = enc-sv w), the ADDRESS from in1-eq
-- (ecx = haddr hv hl since Input1 = SV-Ptr (AtDynamic hl)).
block-step-load-indirect : ∀ {hv : HeapView} prog fs s hl w → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl        -- the loaded pointer is live (store-WF)
  → heapMem (floc fs) hl ≡ just w
  → BlockStep hv prog fs s load-indirect
block-step-load-indirect {hv} prog fs s hl w cc h ft i-eq live-hl h-eq =
  post , exec-eq , record { dataCorr = C.sim-load-indirect hl w fs s _ dc i-eq h-eq (C.sets-role-x86 s role-out _ _ _) ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg eax) (mem (base ecx)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect ft)
    rdi-val : xreadReg (xregs s) ecx ≡ haddr hv hl
    rdi-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    rd : X.readMem (memory s) (X.effectiveAddr s (base ecx)) ≡ just (C.enc-sv hv w)
    rd = trans (cong (X.readMem (memory s)) rdi-val) (trans (C.heap-eq dc hl live-hl) (cong (C.enc-maybe hv) h-eq))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) eax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {eax} {base ecx} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr load-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) load-indirect ft))

-- load-indirect-suc: Output := *(sucLoc Input1) ↔ `mov eax, [ecx + slot]`.
-- The address law C.haddr-suc hv bridges the x86 effective address (haddr hv hl +
-- slot-size) to the heap cell at sucHL hl (haddr hv (sucHL hl)).
block-step-load-indirect-suc : ∀ {hv : HeapView} prog fs s hl w → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)     -- the loaded second cell is live (store-WF)
  → heapMem (floc fs) (sucHL hl) ≡ just w
  → BlockStep hv prog fs s load-indirect-suc
block-step-load-indirect-suc {hv} prog fs s hl w cc h ft i-eq live-shl h-eq =
  post , exec-eq , record { dataCorr = C.sim-load-indirect-suc hl w fs s _ dc i-eq h-eq (C.sets-role-x86 s role-out _ _ _) ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg eax) (mem (base+disp ecx slot-size)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect-suc ft)
    rdi-val : xreadReg (xregs s) ecx ≡ haddr hv hl
    rdi-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-eq : X.effectiveAddr s (base+disp ecx slot-size) ≡ haddr hv (sucHL hl)
    addr-eq = trans (cong (_+ slot-size) rdi-val) (sym (C.haddr-suc hv hl))
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp ecx slot-size)) ≡ just (C.enc-sv hv w)
    rd = trans (cong (X.readMem (memory s)) addr-eq) (trans (C.heap-eq dc (sucHL hl) live-shl) (cong (C.enc-maybe hv) h-eq))
    post : X.State
    post = record s { regs = xwriteReg (xregs s) eax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {eax} {base+disp ecx slot-size} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr load-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) load-indirect-suc ft))

-- load-from-slot: Output := stack[current-frame, slot] ↔ `mov eax, [esp + disp]`.
-- The read VALUE comes from the NEW stack-eq field (memory s at esp+disp = enc-maybe
-- of the slot's abstract value); with the slot holding `just w`, that pins the x86
-- read to `just (enc-sv w)` — feeding step-mov-rm exactly as load-indirect uses heap-eq.
-- FIRST consumer of stack-eq: deleting the field breaks `rd`.
block-step-load-from-slot : ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (load-from-slot slot)
  → slot < frame-slots (falloc fs)   -- the read slot is within the runtime frame (WF)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep hv prog fs s (load-from-slot slot)
block-step-load-from-slot {hv} prog fs s slot w cc h ft slot<ns st-eq =
  post , exec-eq , record { dataCorr = C.sim-load-from-slot slot w fs s _ dc st-eq (C.sets-role-x86 s role-out _ _ _) ; pc-off = pco'
                       ; ret-eq = ret-same prog fs (load-from-slot slot) (memory s)
                                     (elfs-frames (stackMem (floc fs) (current-frame (falloc fs)) slot) (floc fs) (falloc fs) , refl , refl) (ret-eq cc)
                       ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg eax) (mem (base+disp esp (slot-to-disp slot))))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (load-from-slot slot) ft)
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp esp (slot-to-disp slot))) ≡ just (C.enc-sv hv w)
    rd = C.stack-eq-cur dc slot slot<ns _ st-eq
    post : X.State
    post = record s { regs = xwriteReg (xregs s) eax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {eax} {base+disp esp (slot-to-disp slot)} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (load-from-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (load-from-slot slot) ft))

-- restore-input: Input1 := stack[current-frame, slot] ↔ `mov ecx, [esp+disp]`.
-- Identical to load-from-slot but the destination register is ecx (Input1).
block-step-restore-input : ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (restore-input slot)
  → slot < frame-slots (falloc fs)   -- the read slot is within the runtime frame (WF)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep hv prog fs s (restore-input slot)
block-step-restore-input {hv} prog fs s slot w cc h ft slot<ns st-eq =
  post , exec-eq , record { dataCorr = C.sim-restore-input slot w fs s _ dc st-eq (C.sets-role-x86 s role-in1 _ _ _) ; pc-off = pco'
                       ; ret-eq = ret-same prog fs (restore-input slot) (memory s)
                                     (eris-frames (stackMem (floc fs) (current-frame (falloc fs)) slot) (floc fs) (falloc fs) , refl , refl) (ret-eq cc)
                       ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg ecx) (mem (base+disp esp (slot-to-disp slot))))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (restore-input slot) ft)
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp esp (slot-to-disp slot))) ≡ just (C.enc-sv hv w)
    rd = C.stack-eq-cur dc slot slot<ns _ st-eq
    post : X.State
    post = record s { regs = xwriteReg (xregs s) ecx (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {ecx} {base+disp esp (slot-to-disp slot)} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (restore-input slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (restore-input slot) ft))

-- alloc-stack: reserve n slots ↔ `sub esp, n*8`. Uses step-sub-ri; the flag
-- clobber is invisible (FlatCorr flag-free). The 3 fresh-frame facts (entry,
-- fresh-abs) are threaded to sim-alloc-stack; heap liveness now rides
-- the carried view, so the old `liveinv` premise is gone.
block-step-alloc-stack : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-alloc-stack n)
  -- Plan 0.61: the reservation MOVES into the callee frame, so the freshness is
  -- about the SHIFTED frame (a weaker premise than the caller-frame one).
  → (∀ k → k < n → stackMem (floc fs) (shift-frame FS (current-frame (falloc fs)) n) k ≡ nothing)
  -- `fresh-x86` GONE (Plan 0.54 rung D): with `C.Window` one-directional the
  -- callee's window follows from `fresh-abs` alone. It was the FALSE premise —
  -- on frame re-entry the concrete cells below `%esp` hold the previous
  -- incarnation's data — and it is what blocked `block-step-c-thunk`.
  -- THE DESCENT (plan 0.54 rung D step 3): %esp drops, so the view's high-water
  -- mark drops with it and the step lands at the DESCENDED view. The ROOM premise
  -- (stack overflow) is what the dispatcher spends on `front-lo'`.
  → (lo' : ℕ) (lo'≤lo : lo' ≤ C.lo hv) (front-lo' : C.hfront hv ≤ lo')
  → lo' ≤ X.readReg (xregs s) esp ∸ slots n
  -- THE FRAME FITS (Plan 0.63, D085) — see `C.sim-alloc-stack`.
  → slots n ≤ X.readReg (xregs s) esp
  -- THE RETURN PICTURE (D093). This step PUSHES a frame, so the pending
  -- returns re-anchor and the pre-state's component does not carry. It is a
  -- premise rather than a proof because the instruction is UNEMITTABLE — its
  -- dispatch route is `⊥`-elim (`frame-op-absurd`) and this lemma has no
  -- caller; only a matched prologue/epilogue producer could discharge it, and
  -- `ir-to-trace` emits none.
  → C.RetAddrs (blk-off prog) (X.State.memory s) (x86-32-link-claim s)
               (flink (flat-exec-instr (instr-alloc-stack n) prog fs))
               (C.frames-of (falloc (flat-exec-instr (instr-alloc-stack n) prog fs)))
               (fret (flat-exec-instr (instr-alloc-stack n) prog fs))
  -- THE MACHINE IS FINITE (plan 0.70 phase C): `%esp` holds a value below the
  -- modulus. Same class as `StackRoom`/`HeapRoom` (D087) — a fact about the
  -- running program that the loader establishes — so it arrives as a premise
  -- rather than being assumed inside.
  → xreadReg (xregs s) esp < X.W.modulus
  → BlockStepAt hv (C.descend-view hv lo' lo'≤lo front-lo') prog fs s (instr-alloc-stack n)
block-step-alloc-stack {hv} prog fs s n cc h ft fresh-abs lo' lo'≤lo front-lo' lo'≤esp fits retPost esp<mod =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' ; ret-eq = retPost ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (sub (reg esp) (imm (slots n)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-alloc-stack n) ft)
    -- PLAN 0.70 PHASE C: the machine subtracts MODULARLY. `fits` — which has
    -- sat here since D085 purely to tame truncated `∸` — is exactly the
    -- no-borrow side condition under which `⊖` and `∸` agree, so the bridge is
    -- `⊖≡∸` applied to a premise that was already present. The remaining
    -- ingredient is the upper bound, which is genuinely new: a register holds
    -- a value below the modulus because the machine is finite.
    -- PLAN 0.70 PHASE D: peel the immediate's `norm` FIRST. `⊖` is
    -- `norm (x + (modulus ∸ y))`, so an out-of-range `y` would collapse it to
    -- `norm x` — norming the operand is what keeps `⊖` on its domain. The
    -- range fact is not new: `fits` and `esp<mod` already give it.
    in-range : slots n < X.W.modulus
    in-range = ≤-<-trans fits esp<mod
    borrow-free : xreadReg (xregs s) esp X.W.⊖ X.W.norm (slots n) ≡ xreadReg (xregs s) esp ∸ slots n
    borrow-free = trans (X.W.⊖-normʳ (xreadReg (xregs s) esp) (slots n) in-range)
                        (X.W.⊖≡∸ (xreadReg (xregs s) esp) (slots n) fits esp<mod)
    newFlags : X.Flags
    newFlags = updateFlags (xreadReg (xregs s) esp ∸ slots n)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) esp (xreadReg (xregs s) esp ∸ slots n)
                    ; flags = newFlags ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → X.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = xwriteReg (xregs s) esp w
                                        ; flags = updateFlags w
                                        ; pc = pc s + 1 }))
                borrow-free
                (step-sub-ri {compile-trace prog} {s} {esp} {slots n} fetch-x86)
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr (C.descend-view hv lo' lo'≤lo front-lo')
                          (flat-exec-instr (instr-alloc-stack n) prog fs) post
    dataPost = C.sim-alloc-stack n fs s _ dc fresh-abs
                                 lo' lo'≤lo front-lo' lo'≤esp fits
                                 (C.sets-role-x86 s role-sp _ _ _)
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-alloc-stack n) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-alloc-stack n) ft))

------------------------------------------------------------------------
-- THE CLOSURE BODY ENTRY: `c-thunk n b` ↔ `label (thunk n) ; sub esp, 8b`.
--
-- TWO x86 instructions, one abstract step. The label is a pc-only no-op; the
-- `sub` is the body's reservation, which `C.sim-thunk` matches with
-- `grow-frame` (D086: the body GROWS the frame the call already entered — it
-- does not push one, because the concrete `call` already spent a slot on the
-- return address and that slot is not abstractly addressable).
--
-- THIS IS THE ONE THE HANDOFF SAID NOT TO BUILD, and it was right at the time:
-- against the old bidirectional `C.Window` its premise was FALSE, because the
-- callee window demanded unmapped concrete cells and a closure applied twice at
-- one depth re-enters over its predecessor's live data. With `Window`
-- one-directional the head window is vacuous from `fresh-abs` alone, so the
-- block-step is a plain two-step composition.
------------------------------------------------------------------------
-- (`r` and the live-link premise are the FIELD's, added 2026-08-16 for riscv64,
-- whose marker SPILLS onto the head return cell. x86-32's marker writes no
-- memory, so it ignores both and its `ret-unlink` stays `λ _ _ p → p`.)
block-step-c-thunk : ∀ {hv : HeapView} prog fs s n b r rpc rest → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk n b))
  -- NO freshness premise: `do-thunk` CLEARS the entered frame, so the callee
  -- window holds by computation. Neither the abstract nor the concrete
  -- freshness claim survives frame re-entry, and this is why neither is needed.
  → (lo' : ℕ) (lo'≤lo : lo' ≤ C.lo hv) (front-lo' : C.hfront hv ≤ lo')
  → lo' ≤ X.readReg (xregs s) esp ∸ slots b
  → slots b ≤ X.readReg (xregs s) esp
  -- THE FRAME IT DEEPENS RESERVES NOTHING (D093). A body entry is reached by a
  -- CALL, and `enter-call` reserves 0 (D086) — so the window end this marker
  -- moves the frame away from is the frame's own base, and it lands back on it
  -- (`ret-head`). Without this the pending return's cell would move by the
  -- pre-state's reservation and the component would be lost. Supplied at the
  -- dispatch site from the run invariant, where the emitter's layout lives.
  → frame-slots (falloc fs) ≡ 0
  -- THE MACHINE IS FINITE (plan 0.70 phase C), as at `block-step-alloc-stack`.
  → xreadReg (xregs s) esp < X.W.modulus
  → flink fs ≡ just r
  → fret fs ≡ rpc ∷ rest
  → BlockStepAt hv (C.descend-view hv lo' lo'≤lo front-lo') prog fs s (instr-ctrl (c-thunk n b))
block-step-c-thunk {hv} prog fs s n b r rpc rest cc h ft lo' lo'≤lo front-lo' lo'≤esp fits empty-frame esp<mod no-link pend =
  post-sub , exec-eq , record { dataCorr = dataPost ; pc-off = pco' ; ret-eq = retPost ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    -- step 1: the body-entry label (pc only)
    fetch-lab : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (label (thunk n))
    fetch-lab = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-thunk n b)) ft)
    post-lab : X.State
    post-lab = record s { pc = pc s + 1 }
    step-lab : X.step-not-halted (compile-trace prog) s ≡ just post-lab
    step-lab = step-label {compile-trace prog} {s} {thunk n} fetch-lab
    -- step 2: the reservation
    fetch-sub : X.fetch (compile-trace prog) (X.State.pc post-lab) ≡ just (sub (reg esp) (imm (slots b)))
    fetch-sub = trans (cong (λ q → X.fetch (compile-trace prog) (q + 1)) po)
                      (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-thunk n b)) ft)
    newFlags : X.Flags
    newFlags = updateFlags (xreadReg (xregs s) esp ∸ slots b)
    post-sub : X.State
    post-sub = record s { regs = xwriteReg (xregs s) esp (xreadReg (xregs s) esp ∸ slots b)
                        ; flags = newFlags ; pc = pc s + 1 + 1 }
    -- plan 0.70 phase C: `fits` is the no-borrow condition (see
    -- `block-step-alloc-stack`); `post-lab` has the same `%esp` as `s`.
    -- PLAN 0.70 PHASE D: peel the immediate's `norm` FIRST. `⊖` is
    -- `norm (x + (modulus ∸ y))`, so an out-of-range `y` would collapse it to
    -- `norm x` — norming the operand is what keeps `⊖` on its domain. The
    -- range fact is not new: `fits` and `esp<mod` already give it.
    in-range : slots b < X.W.modulus
    in-range = ≤-<-trans fits esp<mod
    borrow-free : xreadReg (xregs s) esp X.W.⊖ X.W.norm (slots b) ≡ xreadReg (xregs s) esp ∸ slots b
    borrow-free = trans (X.W.⊖-normʳ (xreadReg (xregs s) esp) (slots b) in-range)
                        (X.W.⊖≡∸ (xreadReg (xregs s) esp) (slots b) fits esp<mod)
    step-sub : X.step-not-halted (compile-trace prog) post-lab ≡ just post-sub
    step-sub = subst (λ w → X.step-not-halted (compile-trace prog) post-lab
                            ≡ just (record s { regs = xwriteReg (xregs s) esp w
                                             ; flags = updateFlags w
                                             ; pc = pc s + 1 + 1 }))
                     borrow-free
                     (step-sub-ri {compile-trace prog} {post-lab} {esp} {slots b} fetch-sub)
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-sub
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-lab} halt-s step-lab halt-s)
                    (exec-1 {compile-trace prog} {0} {post-lab} {post-sub} halt-s step-sub halt-s)
    dataPost : C.FlatCorr (C.descend-view hv lo' lo'≤lo front-lo')
                          (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs) post-sub
    dataPost = C.sim-thunk b fs s _ dc
                           lo' lo'≤lo front-lo' lo'≤esp fits
                           (C.sets-role-x86 s role-sp _ _ _)
    pco' : X.State.pc post-sub
         ≡ blk-off prog (fpc (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs))
    pco' = trans (+-assoc (pc s) 1 1)
                 (trans (cong (_+ 2) po)
                        (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-thunk n b)) ft)))
    -- THE PENDING RETURN'S CELL DOES NOT MOVE (D093). The marker shifts the
    -- frame down by its reservation and sets the reservation to it, so the
    -- window END returns to the frame's own base — which is where it already
    -- was, because the frame a CALL entered reserves nothing (`empty-frame`).
    -- `slots b ≤ frame-base` is `fits` read through `sp-eq`.
    fits-base : slots b ≤ frame-base FS (current-frame (falloc fs))
    fits-base = subst (slots b ≤_) (C.sp-eq dc) fits
    addr-eq : frame-base FS (shift-frame FS (current-frame (falloc fs)) b) + slots b
            ≡ frame-base FS (current-frame (falloc fs)) + slots (frame-slots (falloc fs))
    addr-eq =
      trans (cong (_+ slots b)
                  (trans (shift-base FS (current-frame (falloc fs)) b)
                         (cong (frame-base FS (current-frame (falloc fs)) ∸_)
                               (cong (b *_) word-eq))))
      (trans (m∸n+n≡m fits-base)
             (trans (sym (+-identityʳ (frame-base FS (current-frame (falloc fs)))))
                    (cong (frame-base FS (current-frame (falloc fs)) +_)
                          (sym (cong slots empty-frame)))))
    -- THE SPILL (plan 0.65 G2). The body marker converts the head row from the
    -- link claim to the stack cell, and on x86-32 that conversion is the
    -- IDENTITY: `call` wrote the cell, so the claim it left behind IS the cell's.
    -- riscv64's `sd ra` is where this becomes an instruction.
    retPost : C.RetAddrs (blk-off prog) (X.State.memory post-sub) (x86-32-link-claim post-sub)
                         (flink (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs))
                         (C.frames-of (falloc (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs)))
                         (fret (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs))
    retPost = C.ret-head (blk-off prog) (X.State.memory s) (x86-32-link-claim s) nothing
                         (current-frame (falloc fs))
                         (shift-frame FS (current-frame (falloc fs)) b)
                         (frame-slots (falloc fs)) b
                         (saved-frames (falloc fs)) (fret fs)
                         addr-eq
                         (C.ret-unlink (blk-off prog) (X.State.memory s) (x86-32-link-claim s)
                            (flink fs) (current-frame (falloc fs)) (frame-slots (falloc fs))
                            (saved-frames (falloc fs)) (fret fs)
                            (λ v p → p) (ret-eq cc))

------------------------------------------------------------------------
-- THE CALL (D098): `instr-call-closure` ↔ `call *0x8(%ebx)`.
--
-- The last correspondence step, and it consumes every piece the previous four
-- decisions put in place:
--
--   `%ebx` mirrors `fclosure`            (D097) — so the target is reachable;
--   a code address is an ADDRESS         (D096) — so the value found there is
--                                                 the body's index, not a label
--                                                 number;
--   `RetAddrs` + `GapNext`               (D093/D095) — so the pushed cell is
--                                                 described, and the frame it
--                                                 enters sits one slot under;
--   the machine performs the transfer    (D092) — so there is something to
--                                                 correspond to at all.
--
-- The two scans agree by `find-thunk-corr`; the pushed return address is
-- `blk-off prog (suc (fpc fs))` on both sides by `blk-off-suc`, since the
-- call's block is one instruction.
------------------------------------------------------------------------
block-step-call : ∀ {hv : HeapView} prog fs s hl ℓ j → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just instr-call-closure
  → fclosure fs ≡ SV-Ptr (AtDynamic hl)
  → heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ)
  → HDom hv (sucHL hl)                       -- the code cell is live
  → find-thunk prog ℓ ≡ just j               -- …and names a body
  → (lo' : ℕ) (lo'≤lo : lo' ≤ C.lo hv) (front-lo' : C.hfront hv ≤ lo')
  → lo' ≤ X.readReg (xregs s) esp ∸ slot-size
  → slot-size ≤ X.readReg (xregs s) esp      -- room for the return address
  -- (the range premise is riscv64's — `call` reserves the slot in hardware here)
  → xreadReg (xregs s) esp < X.W.modulus
  -- …and NO UNSPILLED RETURN ALREADY PENDING (plan 0.65 G2). The call PUSHES a
  -- head, so the one it pushes onto must be the stack-cell row this step
  -- carries across. The engine derives it from `run-link-at-thunk`.
  → flink fs ≡ nothing
  → BlockStepAt hv (C.descend-view hv lo' lo'≤lo front-lo') prog fs s instr-call-closure
block-step-call {hv} prog fs s hl ℓ j cc h ft ceq heq live fteq lo' lo'≤lo front-lo' lo'≤esp fits esp<mod no-link =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' ; ret-eq = retPost
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (call (mem (base+disp ebx slot-size)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) instr-call-closure ft)
    -- THE TARGET: `%ebx` is the closure pointer, its second cell is the code
    -- address, and that address is the body's index.
    r12-val : X.readReg (xregs s) ebx ≡ haddr hv hl
    r12-val = trans (C.clos-eq dc) (cong (C.enc-sv hv) ceq)
    cell-addr : X.readReg (xregs s) ebx + slot-size ≡ haddr hv (sucHL hl)
    cell-addr = trans (cong (_+ slot-size) r12-val) (sym (C.haddr-suc hv hl))
    conc-res : X.find-label (compile-trace prog) (thunk ℓ) ≡ just (blk-off prog j)
    conc-res = find-thunk-corr prog ℓ 0 j fteq
    rd : X.readMem (X.State.memory s) (X.effectiveAddr s (base+disp ebx slot-size))
       ≡ just (blk-off prog j)
    rd = trans (cong (X.readMem (X.State.memory s)) cell-addr)
        (trans (C.heap-eq dc (sucHL hl) live)
        (trans (cong (C.enc-maybe hv) heq)
               (cong just (code-eq cc ℓ (blk-off prog j) conc-res))))
    retAddr : ℕ
    retAddr = X.State.pc s + 1
    post : X.State
    post = record s { regs   = xwriteReg (xregs s) esp (X.readReg (xregs s) esp ∸ slot-size)
                    ; memory = writeMem (memory s) (X.readReg (xregs s) esp ∸ slot-size) retAddr
                    ; pc     = blk-off prog j }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-call {compile-trace prog} {s} {base+disp ebx slot-size} {blk-off prog j} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    -- the abstract post-state, in the shape `callView` hands back
    absPost : FlatState
    -- …and the LINK (plan 0.65 G2): x86-32's `call` writes the return address
    -- to memory AND leaves it as the link in the same instruction, so this is
    -- the degenerate case of the abstract link register — the spill has already
    -- happened by the time the callee's prologue runs.
    absPost = record fs { falloc = enter-call (falloc fs)
                        ; fret   = suc (fpc fs) ∷ fret fs
                        ; flink  = just (suc (fpc fs))
                        ; fpc    = j }
    step-eq : flat-exec-instr instr-call-closure prog fs ≡ absPost
    step-eq = trans (cong (λ z → do-call-sv prog z fs) ceq)
             (trans (cong (λ z → do-call-code prog z fs) heq)
                    (cong (λ z → do-call-at z fs) fteq))
    -- THE PUSHED CELL, described: the entered frame reserves nothing, so its
    -- window END is its own base — the very cell the call wrote.
    newbase : X.readReg (xregs s) esp ∸ slot-size
            ≡ frame-base FS (shift-frame FS (current-frame (falloc fs)) 1)
    newbase = trans (cong (_∸ slot-size) (C.sp-eq dc))
                    (trans (cong (λ w → frame-base FS (current-frame (falloc fs)) ∸ 1 * w)
                                 (sym word-eq))
                           (sym (shift-base FS (current-frame (falloc fs)) 1)))
    -- THE STATE THE CALL DOES NOT PASS THROUGH (plan 0.65 G2): `%esp` moved,
    -- memory not. `call` does both in one instruction, but they are separate
    -- FACTS and only the first is shared with RISC-V — so the core proves the
    -- frame descent (`sim-call-frame`) and x86-32 composes its own push on top.
    -- The pushed cell IS the post-state's gap cell, so the store lemma is the
    -- one the body marker uses.
    mid : X.State
    mid = record s { regs = xwriteReg (xregs s) esp (X.readReg (xregs s) esp ∸ slot-size) }
    dataMid : C.FlatCorr (C.descend-view hv lo' lo'≤lo front-lo') absPost mid
    dataMid = C.sim-call-frame j fs s mid dc lo' lo'≤lo front-lo' lo'≤esp fits
                (C.sets-role-x86 s role-sp _ _ _)
    gap-post : C.GapNext (frame-base FS (shift-frame FS (current-frame (falloc fs)) 1) + slots 0)
                         (C.frames-of (falloc fs))
    gap-post = trans (cong (_+ slot-size) (trans (+-identityʳ _) (sym newbase)))
                     (trans (m∸n+n≡m fits) (C.sp-eq dc))
    mem-post : X.State.memory post
             ≡ writeMem (X.State.memory mid)
                 (frame-base FS (shift-frame FS (current-frame (falloc fs)) 1) + slots 0)
                 retAddr
    mem-post = cong (λ a → writeMem (memory s) a retAddr)
                    (trans (sym (+-identityʳ (X.readReg (xregs s) esp ∸ slot-size)))
                           (cong (_+ 0) newbase))
    dataPost : C.FlatCorr (C.descend-view hv lo' lo'≤lo front-lo')
                          (flat-exec-instr instr-call-closure prog fs) post
    dataPost = subst (λ z → C.FlatCorr (C.descend-view hv lo' lo'≤lo front-lo') z post)
                     (sym step-eq)
                     (C.corr-store-gap absPost mid post retAddr dataMid
                        (λ r → refl) refl mem-post gap-post)
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr instr-call-closure prog fs))
    pco' = cong (λ z → blk-off prog (fpc z)) (sym step-eq)
    ret-val : retAddr ≡ blk-off prog (suc (fpc fs))
    ret-val = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) instr-call-closure ft))
    w<base : X.readReg (xregs s) esp ∸ slot-size < frame-base FS (current-frame (falloc fs))
    w<base = subst (X.readReg (xregs s) esp ∸ slot-size <_) (C.sp-eq dc)
                   (subst (suc (X.readReg (xregs s) esp ∸ slot-size) ≤_) (m∸n+n≡m fits)
                          (m<m+n (X.readReg (xregs s) esp ∸ slot-size) (s≤s z≤n)))
    retPost : C.RetAddrs (blk-off prog) (X.State.memory post) (x86-32-link-claim post)
                         (flink (flat-exec-instr instr-call-closure prog fs))
                         (C.frames-of (falloc (flat-exec-instr instr-call-closure prog fs)))
                         (fret (flat-exec-instr instr-call-closure prog fs))
    retPost = subst (λ z → C.RetAddrs (blk-off prog) (X.State.memory post)
                             (x86-32-link-claim post) (flink z)
                             (C.frames-of (falloc z)) (fret z))
                    (sym step-eq)
                    ( head-cell , gap , tail )
      where
        waddr = X.readReg (xregs s) esp ∸ slot-size
        head-cell : X.readMem (X.State.memory post)
                      (frame-base FS (shift-frame FS (current-frame (falloc fs)) 1) + slots 0)
                    ≡ just (blk-off prog (suc (fpc fs)))
        head-cell = trans (cong (λ a → X.readMem (X.State.memory post) a)
                               (trans (+-identityʳ _) (sym newbase)))
                          (trans (C.read-write-hit (memory s) waddr retAddr) (cong just ret-val))
        gap : C.GapNext (frame-base FS (shift-frame FS (current-frame (falloc fs)) 1) + slots 0)
                        (C.frames-of (falloc fs))
        gap = trans (cong (_+ slot-size) (trans (+-identityʳ _) (sym newbase)))
                    (trans (m∸n+n≡m fits) (C.sp-eq dc))
        tail : C.RetAddrs (blk-off prog) (X.State.memory post) (x86-32-link-claim post)
                          nothing (C.frames-of (falloc fs)) (fret fs)
        tail = C.ret-agree-above (blk-off prog) (memory s) (X.State.memory post)
                 (x86-32-link-claim s) (x86-32-link-claim post) nothing
                 (stackMem (floc fs)) (frame-base FS (current-frame (falloc fs)))
                 (C.frames-of (falloc fs)) (fret fs)
                 (λ a le → C.read-write-miss (memory s) waddr retAddr a
                             (λ eq → <⇒≢ (<-transˡ w<base le) (sym eq)))
                 (λ a v le p → trans (C.read-write-miss (memory s) waddr retAddr a
                                        (λ eq → <⇒≢ (<-transˡ w<base le) (sym eq))) p)
                 (C.windows-reanchor (C.lo hv) (frame-base FS (current-frame (falloc fs)))
                    (current-frame (falloc fs)) (frame-slots (falloc fs))
                    (saved-frames (falloc fs)) ≤-refl (C.stack-eq dc))
                 (subst (λ z → C.RetAddrs (blk-off prog) (memory s) (x86-32-link-claim s) z
                                 (C.frames-of (falloc fs)) (fret fs))
                        no-link (ret-eq cc))

------------------------------------------------------------------------
-- THE RETURN (D095): `c-ret b` ↔ `add esp, 8b ; ret`.
--
-- Two x86 instructions, one abstract step, and the FIRST step of the
-- correspondence that reads the pending-return component: the `ret` pops
-- exactly the cell `RetAddrs` describes, at exactly the address the `add`
-- leaves `%esp` on. Everything the proof needs comes from the component:
--
--   the ADDRESS  — `sp-eq` puts `%esp` at the frame's base, the bracket
--                  premise `b ≡ frame-slots` makes `add esp,8b` land on the
--                  window END, which is where the call put the address;
--   the VALUE    — `RetAddrs`' head says that cell holds `blk-off prog rpc`,
--                  so the concrete pc lands where the abstract `fpc` does;
--   the NEW %esp — `GapNext` says the caller's base is one slot above that
--                  cell, which is exactly where `ret` leaves `%esp` (sp-eq
--                  for the post-state);
--   the TAIL     — the post-state's component IS the pre-state's tail, since
--                  `frames-of (leave-frame alloc)` is `saved-frames alloc`.
------------------------------------------------------------------------
block-step-c-ret : ∀ {hv : HeapView} prog fs s b rpc rest f₀ b₀ frs
  → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
  → fret fs ≡ rpc ∷ rest
  -- THE BRACKET (D095): the budget a return releases IS the reservation in
  -- force — `ir-to-trace'` emits `c-thunk ℓ bb … c-ret bb`.
  → b ≡ frame-slots (falloc fs)
  -- …and the frame it returns INTO, from the same `RetMatch` pairing
  → saved-frames (falloc fs) ≡ (f₀ , b₀) ∷ frs
  -- THE ADDRESS SPACE DOES NOT WRAP (plan 0.70 phase C): the released `%esp`
  -- is representable. `add` computes `W.⊕` unconditionally — D054 forbids a
  -- no-overflow precondition ON THE INSTRUCTION — so the consumer that wants
  -- plain `+` pays here. A LAYOUT fact, not a claim about user arithmetic:
  -- `addr-eq`/`gap` below show this sum IS the caller's frame base less one
  -- slot. Threaded as `AddrNoWrap.ret-no-wrap` (D087).
  → xreadReg (xregs s) esp + slots (suc b) < X.W.modulus
  -- …and NO UNSPILLED RETURN (plan 0.65 G2). The `ret` READS the head cell, so
  -- the head row must be the stack claim and not the arch's link claim. The
  -- engine derives it from `run-link-at-thunk`: this branch fetched a `c-ret`.
  → flink fs ≡ nothing
  → BlockStep hv prog fs s (instr-ctrl (c-ret b))
block-step-c-ret {hv} prog fs s b rpc rest f₀ b₀ frs cc h ft req beq feq no-wrap-suc no-link =
  post-ret , exec-eq , record { dataCorr = dataPost ; pc-off = pco' ; ret-eq = retPost ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    -- x86-32 only ADDS `8b` here — the extra slot rides in the `ret`'s own pop —
    -- so it takes the weaker half of the caller's-base bound.
    no-wrap : xreadReg (xregs s) esp + slots b < X.W.modulus
    no-wrap = ≤-<-trans (+-monoʳ-≤ (xreadReg (xregs s) esp)
                           (m≤n+m (slots b) slot-size))
                        no-wrap-suc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    -- step 1: the frame release
    fetch-add : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (add (reg esp) (imm (slots b)))
    fetch-add = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-ret b)) ft)
    newFlags : X.Flags
    newFlags = updateFlags (xreadReg (xregs s) esp + slots b)
    post-add : X.State
    post-add = record s { regs = xwriteReg (xregs s) esp (xreadReg (xregs s) esp + slots b)
                        ; flags = newFlags ; pc = pc s + 1 }
    wrap-free : xreadReg (xregs s) esp X.W.⊕ X.W.norm (slots b) ≡ xreadReg (xregs s) esp + slots b
    -- PHASE D: peel the immediate's `norm` first — UNCONDITIONAL for `⊕`,
    -- which norms its sum anyway, so a pre-normed argument is unobservable.
    wrap-free = trans (X.W.⊕-normʳ (xreadReg (xregs s) esp) (slots b))
                      (X.W.⊕≡+ (xreadReg (xregs s) esp) (slots b) no-wrap)
    step-add : X.step-not-halted (compile-trace prog) s ≡ just post-add
    step-add = subst (λ w → X.step-not-halted (compile-trace prog) s
                            ≡ just (record s { regs = xwriteReg (xregs s) esp w
                                             ; flags = updateFlags w
                                             ; pc = pc s + 1 }))
                     wrap-free
                     (step-add-ri {compile-trace prog} {s} {esp} {slots b} fetch-add)
    -- THE COMPONENT, projected at the cons shape of `fret`
    comp : C.RetAddrs (blk-off prog) (X.State.memory s) (x86-32-link-claim s) nothing
                      ((current-frame (falloc fs) , frame-slots (falloc fs)) ∷ saved-frames (falloc fs))
                      (rpc ∷ rest)
    comp = subst₂ (λ lk rl → C.RetAddrs (blk-off prog) (X.State.memory s)
                               (x86-32-link-claim s) lk (C.frames-of (falloc fs)) rl)
                  no-link req (ret-eq cc)
    -- …and the address it speaks about IS where the `add` left `%esp`
    addr-eq : X.readReg (X.State.regs post-add) esp
            ≡ frame-base FS (current-frame (falloc fs)) + slots (frame-slots (falloc fs))
    addr-eq = trans (cong (_+ slots b) (C.sp-eq dc)) (cong (λ z → frame-base FS (current-frame (falloc fs)) + slots z) beq)
    rd : X.readMem (X.State.memory post-add) (X.readReg (X.State.regs post-add) esp)
       ≡ just (blk-off prog rpc)
    rd = trans (cong (X.readMem (X.State.memory s)) addr-eq) (proj₁ comp)
    -- step 2: the pop-and-jump
    fetch-ret : X.fetch (compile-trace prog) (X.State.pc post-add) ≡ just ret
    fetch-ret = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                      (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-ret b)) ft)
    post-ret : X.State
    post-ret = record post-add { regs = xwriteReg (X.State.regs post-add) esp
                                          (X.readReg (X.State.regs post-add) esp + slot-size)
                               ; pc = blk-off prog rpc }
    step-r : X.step-not-halted (compile-trace prog) post-add ≡ just post-ret
    step-r = step-ret {compile-trace prog} {post-add} {blk-off prog rpc} fetch-ret rd
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-ret
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-add} halt-s step-add halt-s)
                    (exec-1 {compile-trace prog} {0} {post-add} {post-ret} halt-s step-r halt-s)
    -- THE CALLER'S BASE is one slot above that cell — `GapNext`, read through
    -- the frame list's shape.
    gap : frame-base FS (current-frame (falloc fs)) + slots (frame-slots (falloc fs)) + slot-size
        ≡ frame-base FS f₀
    gap = subst (λ fr → C.GapNext (frame-base FS (current-frame (falloc fs))
                                   + slots (frame-slots (falloc fs))) fr)
                feq (proj₁ (proj₂ comp))
    base-leave : saved-frames (falloc fs) ≡ (f₀ , b₀) ∷ frs
               → frame-base FS (current-frame (leave-frame (falloc fs))) ≡ frame-base FS f₀
    base-leave e rewrite e = refl
    restores : X.readReg (xregs s) esp + slots b + slot-size
             ≡ frame-base FS (current-frame (leave-frame (falloc fs)))
    restores = trans (cong (_+ slot-size) addr-eq) (trans gap (sym (base-leave feq)))
    dataPost : C.FlatCorr hv (flat-exec-instr (instr-ctrl (c-ret b)) prog fs) post-ret
    dataPost = C.sim-ret b rpc rest fs s _ dc req restores (C.sets-role-x86 s role-sp _ _ _)
    pco' : X.State.pc post-ret ≡ blk-off prog (fpc (flat-exec-instr (instr-ctrl (c-ret b)) prog fs))
    pco' = cong (blk-off prog) (sym (do-ret-pc-∷ fs rpc rest req))
    retPost : C.RetAddrs (blk-off prog) (X.State.memory post-ret) (x86-32-link-claim post-ret)
                         (flink (flat-exec-instr (instr-ctrl (c-ret b)) prog fs))
                         (C.frames-of (falloc (flat-exec-instr (instr-ctrl (c-ret b)) prog fs)))
                         (fret (flat-exec-instr (instr-ctrl (c-ret b)) prog fs))
    retPost = subst (λ lk → C.RetAddrs (blk-off prog) (X.State.memory s) (x86-32-link-claim s) lk
                              (C.frames-of (falloc (flat-exec-instr (instr-ctrl (c-ret b)) prog fs)))
                              (fret (flat-exec-instr (instr-ctrl (c-ret b)) prog fs)))
                    (sym lk-post)
                    (subst₂ (C.RetAddrs (blk-off prog) (X.State.memory s) (x86-32-link-claim s) nothing)
                            (sym (trans (cong C.frames-of (do-ret-alloc fs)) (frames-leave feq)))
                            (sym (do-ret-fret-∷ fs rpc rest req))
                            (proj₂ (proj₂ comp)))
      where frames-leave : saved-frames (falloc fs) ≡ (f₀ , b₀) ∷ frs
                         → C.frames-of (leave-frame (falloc fs)) ≡ saved-frames (falloc fs)
            frames-leave e rewrite e = refl
            -- a RETURN threads the link (`flinkView`), and it was `nothing`
            lk-post : flink (flat-exec-instr (instr-ctrl (c-ret b)) prog fs) ≡ nothing
            lk-post = trans (flink-do-ret (fret fs) fs) no-link

-- dealloc-stack: free n slots ↔ `add esp, n*8`. At a full-frame exit
-- (frame-slots ≡ n), sim-dealloc-stack's post bound is vacuous. Uses step-add-ri.
block-step-dealloc-stack : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-dealloc-stack n)
  -- matched pairing: the restored (caller) frame's base is where %esp lands
  → X.readReg (xregs s) esp + slots n
      ≡ frame-base FS (current-frame (leave-frame (falloc fs)))
  -- (Plan 0.63, D085: the restored CALLER's window used to be a premise here —
  -- it is now the TAIL of the pre-state's `stack-eq`, `C.windows-leave`.)
  -- …and the return picture, a premise for the same reason as
  -- `block-step-alloc-stack`'s: this POPS a frame, and the instruction is
  -- unemittable, so no caller exists to discharge it.
  → C.RetAddrs (blk-off prog) (X.State.memory s) (x86-32-link-claim s)
               (flink (flat-exec-instr (instr-dealloc-stack n) prog fs))
               (C.frames-of (falloc (flat-exec-instr (instr-dealloc-stack n) prog fs)))
               (fret (flat-exec-instr (instr-dealloc-stack n) prog fs))
  -- THE ADDRESS SPACE DOES NOT WRAP (plan 0.70 phase C), as in
  -- `block-step-c-ret`. `restores` just above already says this sum IS the
  -- restored frame's base, so what is added is only that the base is
  -- representable — a layout fact.
  → xreadReg (xregs s) esp + slots n < X.W.modulus
  → BlockStep hv prog fs s (instr-dealloc-stack n)
block-step-dealloc-stack {hv} prog fs s n cc h ft restores retPost no-wrap =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' ; ret-eq = retPost ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (add (reg esp) (imm (slots n)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-dealloc-stack n) ft)
    newFlags : X.Flags
    newFlags = updateFlags (xreadReg (xregs s) esp + slots n)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) esp (xreadReg (xregs s) esp + slots n)
                    ; flags = newFlags ; pc = pc s + 1 }
    wrap-free : xreadReg (xregs s) esp X.W.⊕ X.W.norm (slots n) ≡ xreadReg (xregs s) esp + slots n
    -- PHASE D: peel the immediate's `norm` first — UNCONDITIONAL for `⊕`,
    -- which norms its sum anyway, so a pre-normed argument is unobservable.
    wrap-free = trans (X.W.⊕-normʳ (xreadReg (xregs s) esp) (slots n))
                      (X.W.⊕≡+ (xreadReg (xregs s) esp) (slots n) no-wrap)
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → X.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = xwriteReg (xregs s) esp w
                                        ; flags = updateFlags w
                                        ; pc = pc s + 1 }))
                wrap-free
                (step-add-ri {compile-trace prog} {s} {esp} {slots n} fetch-x86)
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr (instr-dealloc-stack n) prog fs) post
    dataPost = C.sim-dealloc-stack n fs s _ dc restores (C.sets-role-x86 s role-sp _ _ _)
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-dealloc-stack n) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-dealloc-stack n) ft))

-- push-frame / pop-frame: THE `%ebp` FRAME MODEL IS A FOSSIL. Their
-- `block-step-*` pair was deleted 2026-08-04 — flagged deletable on
-- 2026-07-31 ("now DEAD, nothing references them") and confirmed again here.
-- The live model is frameless and `%esp`-relative, and Plan 0.63's closure
-- frames ride on `alloc-stack`/`dealloc-stack`, whose block-steps are kept
-- above precisely because `c-thunk`/`c-ret` compose from them.

-- load-const (int): Output := SV-Lit fits-int v ↔ `mov eax, imm v` (1 step).
-- With the enc-sv fix the immediate matches exactly (sim-load-const's out-eq = refl).
--
-- PLAN 0.70 PHASE D — THIS IS THE `lit-word` SEAM, AND IT IS NOW A PREMISE.
-- `lit-word : Carrier → Word` is the identity, which is only FAITHFUL for a
-- literal that fits in a machine word: the immediate field of a `mov` holds a
-- word, and the machine norms it. Before phase D this lemma silently concluded
-- that the register held `v` for ANY `v` — a register holding a value no
-- register can hold. Now the obligation is visible, and it is the honest one:
-- D054 makes `Int` a modular `Word`, so an elaborated literal is in range by
-- construction; the day that is threaded from the frontend, this premise is
-- discharged rather than assumed.
block-step-load-const : ∀ {hv : HeapView} prog fs s (v : Carrier) → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-const fits-int v)
  → v < X.W.modulus
  → BlockStep hv prog fs s (instr-load-const fits-int v)
block-step-load-const {hv} prog fs s v cc h ft fits =
  post , exec-eq , record { dataCorr = C.sim-load-const v fs s _ dc (C.sets-role-x86 s role-out _ _ _) ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg eax) (imm v))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-load-const fits-int v) ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) eax v ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → X.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = xwriteReg (xregs s) eax w ; pc = pc s + 1 }))
                (X.W.norm-id fits)
                (step-mov-ri {compile-trace prog} {s} {eax} {v} fetch-x86)
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-load-const fits-int v) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-load-const fits-int v) ft))
------------------------------------------------------------------------
-- …and the FLOAT constant. This is the block-step that COULD NOT EXIST while a
-- `Float` was 64 bits everywhere (D109): x86-32 lowered the instruction to
-- `ud2`, so the abstract machine loaded a value and the concrete one trapped.
--
-- With the encoding arch-relative — `float-bits-single` (as it was) here, `float-bits` (as it was) on
-- the 64-bit targets, both passed to the core as `fenc` — the two sides load
-- the SAME number and this is the int case verbatim, `norm-id` and all. Note
-- what the premise says: `fenc v < modulus`, i.e. the encoded literal fits a
-- word of THIS machine. At 64 bits it is a fact about `float-bits` (as it was); here it is
-- a fact about `float-bits-single` (as it was), and it is true by the encoder's
-- construction rather than by luck.
------------------------------------------------------------------------
block-step-load-const-float : ∀ {hv : HeapView} prog fs s (v : Dyadic) → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-const fits-float v)
  → (encode binary32) v < X.W.modulus
  → BlockStep hv prog fs s (instr-load-const fits-float v)
block-step-load-const-float {hv} prog fs s v cc h ft fits =
  post , exec-eq , record { dataCorr = C.sim-load-const-float v fs s _ dc (C.sets-role-x86 s role-out _ _ _) ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg eax) (imm (encode binary32 v)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-load-const fits-float v) ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) eax (encode binary32 v) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → X.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = xwriteReg (xregs s) eax w ; pc = pc s + 1 }))
                (X.W.norm-id fits)
                (step-mov-ri {compile-trace prog} {s} {eax} {(encode binary32) v} fetch-x86)
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-load-const fits-float v) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-load-const fits-float v) ft))

block-step-load-code-addr : ∀ {hv : HeapView} prog fs s n j → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-code-addr n)
  → X.find-label (compile-trace prog) (thunk n) ≡ just j
  → BlockStep hv prog fs s (instr-load-code-addr n)
block-step-load-code-addr {hv} prog fs s n j cc h ft fl =
  post , exec-eq , record { dataCorr = C.sim-load-code-addr n j fs s _ dc (code-eq cc n j fl) (C.sets-role-x86 s role-out _ _ _)
                          ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov-code eax n)
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-load-code-addr n) ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) eax j ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-code {compile-trace prog} {s} {eax} {n} {j} fetch-x86 fl
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-load-code-addr n) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-load-code-addr n) ft))

-- save-closure-reg: abstract identity ↔ `mov ebx, ecx`. ebx is untracked, so the
-- whole FlatCorr copies through (sim-save-closure-reg).
block-step-save-closure-reg : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just instr-save-closure-reg
  → BlockStep hv prog fs s instr-save-closure-reg
block-step-save-closure-reg {hv} prog fs s cc h ft =
  post , exec-eq , record { dataCorr = C.sim-save-closure-reg fs s _ dc (C.sets-role-x86 s role-clos _ _ _) ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg ebx) (reg ecx))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) instr-save-closure-reg ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) ebx (xreadReg (xregs s) ecx) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rr {compile-trace prog} {s} {ebx} {ecx} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr instr-save-closure-reg prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) instr-save-closure-reg ft))

-- worklist-push / worklist-pop: their abstract semantics + x86 lowering are
-- IDENTICAL to store-at-slot / load-from-slot respectively (SMCore/AbstractToX86),
-- so flat-exec-instr reduces the same way and the sim-* lemmas are reused verbatim.
block-step-worklist-push : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-push slot)
  → slot < frame-slots (falloc fs)   -- the written slot is inside this frame (D085)
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) esp + slot-to-disp slot ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s (worklist-push slot)
block-step-worklist-push {hv} prog fs s slot cc h ft slot<ns disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = ret-slot-store prog fs s slot _ cc slot<ns
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (mem (base+disp esp (slot-to-disp slot))) (reg eax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (worklist-push slot) ft)
    post : X.State
    post = record s { memory = writeMem (memory s) (X.effectiveAddr s (base+disp esp (slot-to-disp slot)))
                                        (xreadReg (xregs s) eax)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-mr {compile-trace prog} {s} {base+disp esp (slot-to-disp slot)} {eax} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    post-eq : post ≡ mkstate (xregs s)
                             (writeMem (memory s) (X.readReg (xregs s) esp + slot-to-disp slot)
                                       (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ v → mkstate (xregs s)
                            (writeMem (memory s) (X.readReg (xregs s) esp + slot-to-disp slot) v)
                            (flags s) (pc s + 1) (xhalted s))
                   (C.out-eq dc)
    dataPost : C.FlatCorr hv (flat-exec-instr (worklist-push slot) prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr (worklist-push slot) prog fs)) (sym post-eq)
                     (C.sim-store-at-slot slot fs s _ dc slot<ns disj (C.sets-mem-x86 s _ _ _ _))
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (worklist-push slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (worklist-push slot) ft))

block-step-worklist-pop : ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-pop slot)
  → slot < frame-slots (falloc fs)   -- the read slot is within the runtime frame (WF)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep hv prog fs s (worklist-pop slot)
block-step-worklist-pop {hv} prog fs s slot w cc h ft slot<ns st-eq =
  post , exec-eq , record { dataCorr = C.sim-load-from-slot slot w fs s _ dc st-eq (C.sets-role-x86 s role-out _ _ _) ; pc-off = pco'
                       ; ret-eq = ret-same prog fs (load-from-slot slot) (memory s)
                                     (elfs-frames (stackMem (floc fs) (current-frame (falloc fs)) slot) (floc fs) (falloc fs) , refl , refl) (ret-eq cc)
                       ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg eax) (mem (base+disp esp (slot-to-disp slot))))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (worklist-pop slot) ft)
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp esp (slot-to-disp slot))) ≡ just (C.enc-sv hv w)
    rd = C.stack-eq-cur dc slot slot<ns _ st-eq
    post : X.State
    post = record s { regs = xwriteReg (xregs s) eax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {eax} {base+disp esp (slot-to-disp slot)} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (worklist-pop slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (worklist-pop slot) ft))

-- store-indirect: *Input1 := Output ↔ `mov [ecx], eax`. step-mov-mr writes
-- the RAW register values (readReg ecx / readReg eax); sim-store-indirect's
-- post has the ENCODED values (haddr hv hl / enc-sv Output) — bridge the two
-- post-states via in1-eq + out-eq, then transport the data correspondence.
block-step-store-indirect : ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl        -- the store target is live (store-WF)
  → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
  -- (heap/stack disjointness is no longer a premise — D085 derives it, for
  -- every live frame, from the frame list's floor)
  → BlockStep hv prog fs s store-indirect
block-step-store-indirect {hv} prog fs s hl cc h ft i-eq live-hl guard =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = subst (λ m → C.RetAddrs (blk-off prog) m
                                                    (λ ad w → m ad ≡ just w) (flink fs)
                                                    (C.frames-of (falloc fs)) (fret fs))
                                           (cong₂ (writeMem (memory s)) (sym rdi-val) refl)
                                           (ret-heap-store prog fs s (haddr hv hl) _ cc
                                              (≤-trans (C.dom-below hv live-hl) (C.front-lo hv)))
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (mem (base ecx)) (reg eax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) store-indirect ft)
    rdi-val : xreadReg (xregs s) ecx ≡ haddr hv hl
    rdi-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    post : X.State
    post = record s { memory = writeMem (memory s) (X.effectiveAddr s (base ecx)) (xreadReg (xregs s) eax)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-mr {compile-trace prog} {s} {base ecx} {eax} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    -- bridge post (raw) ≡ sim-post (encoded)
    post-eq : post ≡ mkstate (xregs s) (writeMem (memory s) (haddr hv hl) (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ m → mkstate (xregs s) m (flags s) (pc s + 1) (xhalted s))
                   (cong₂ (writeMem (memory s)) rdi-val (C.out-eq dc))
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr store-indirect prog fs)) (sym post-eq)
                     (C.sim-store-indirect hl fs s _ dc i-eq live-hl guard (C.sets-mem-x86 s _ _ _ _))
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr store-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) store-indirect ft))

-- store-indirect-suc: *(sucLoc Input1) := Output ↔ `mov [ecx+slot], eax`.
-- Like store-indirect + the address law C.haddr-suc hv for the +slot offset.
block-step-store-indirect-suc : ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)     -- the store target (second cell) is live (store-WF)
  → writeLoc (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) (sucHL hl) (readReg (regs (floc fs)) Output)
  → BlockStep hv prog fs s store-indirect-suc
block-step-store-indirect-suc {hv} prog fs s hl cc h ft i-eq live-shl guard =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = subst (λ m → C.RetAddrs (blk-off prog) m
                                                    (λ ad w → m ad ≡ just w) (flink fs)
                                                    (C.frames-of (falloc fs)) (fret fs))
                                           (cong₂ (writeMem (memory s)) (sym addr-val) refl)
                                           (ret-heap-store prog fs s (haddr hv (sucHL hl)) _ cc
                                              (≤-trans (C.dom-below hv live-shl) (C.front-lo hv)))
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (mem (base+disp ecx slot-size)) (reg eax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) store-indirect-suc ft)
    rdi-val : xreadReg (xregs s) ecx ≡ haddr hv hl
    rdi-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-val : xreadReg (xregs s) ecx + slot-size ≡ haddr hv (sucHL hl)
    addr-val = trans (cong (_+ slot-size) rdi-val) (sym (C.haddr-suc hv hl))
    post : X.State
    post = record s { memory = writeMem (memory s) (X.effectiveAddr s (base+disp ecx slot-size)) (xreadReg (xregs s) eax)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-mr {compile-trace prog} {s} {base+disp ecx slot-size} {eax} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    post-eq : post ≡ mkstate (xregs s) (writeMem (memory s) (haddr hv (sucHL hl)) (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ m → mkstate (xregs s) m (flags s) (pc s + 1) (xhalted s))
                   (cong₂ (writeMem (memory s)) addr-val (C.out-eq dc))
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect-suc prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr store-indirect-suc prog fs)) (sym post-eq)
                     (C.sim-store-indirect-suc hl fs s _ dc i-eq live-shl guard (C.sets-mem-x86 s _ _ _ _))
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr store-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) store-indirect-suc ft))

-- store-at-slot: stack[current-frame, slot] := Output ↔ `mov [esp+disp], eax`.
-- step-mov-mr writes the RAW eax; sim-store-at-slot's post has enc-sv Output —
-- bridge via out-eq (the address is esp+disp, definitional, no register bridge).
-- The stack/heap disjointness (`disj`) is threaded to sim-store-at-slot.
block-step-store-at-slot : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (store-at-slot slot)
  → slot < frame-slots (falloc fs)   -- the written slot is inside this frame (D085)
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) esp + slot-to-disp slot ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s (store-at-slot slot)
block-step-store-at-slot {hv} prog fs s slot cc h ft slot<ns disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = ret-slot-store prog fs s slot _ cc slot<ns
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (mem (base+disp esp (slot-to-disp slot))) (reg eax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (store-at-slot slot) ft)
    post : X.State
    post = record s { memory = writeMem (memory s) (X.effectiveAddr s (base+disp esp (slot-to-disp slot)))
                                        (xreadReg (xregs s) eax)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-mr {compile-trace prog} {s} {base+disp esp (slot-to-disp slot)} {eax} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    post-eq : post ≡ mkstate (xregs s)
                             (writeMem (memory s) (X.readReg (xregs s) esp + slot-to-disp slot)
                                       (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                             (flags s) (pc s + 1) (xhalted s)
    post-eq = cong (λ v → mkstate (xregs s)
                            (writeMem (memory s) (X.readReg (xregs s) esp + slot-to-disp slot) v)
                            (flags s) (pc s + 1) (xhalted s))
                   (C.out-eq dc)
    dataPost : C.FlatCorr hv (flat-exec-instr (store-at-slot slot) prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr (store-at-slot slot) prog fs)) (sym post-eq)
                     (C.sim-store-at-slot slot fs s _ dc slot<ns disj (C.sets-mem-x86 s _ _ _ _))
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (store-at-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (store-at-slot slot) ft))

-- Arithmetic reg-ops: count-inc (add edi,1) / scratch-dec (sub edx,1).
-- x86 add/sub set flags as a side effect, but CompiledCorr/FlatCorr are
-- flag-free (Plan 0.34), so the flag clobber is invisible — the sim-* lemma
-- is parametric over the post flags (instantiated with updateFlags here).
block-step-count-inc : ∀ {hv : HeapView} prog fs s k → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op count-inc)
  → readReg (regs (floc fs)) Count ≡ SV-Tag k
  -- THE COUNTER DOES NOT WRAP (plan 0.70 phase C). The one `add` site that is
  -- not an address: `%edi` is the OBSERVABLE counter. `add` computes `W.⊕`
  -- unconditionally (D054), so the consumer supplies the range — here the
  -- resource bound "this run does not emit 2⁶⁴ observations", which is of the
  -- same D087 family as `HeapRoom`, and just as discharge-able by a linker
  -- argument about the program's own size.
  → xreadReg (xregs s) edi + 1 < X.W.modulus
  → BlockStep hv prog fs s (instr-reg-op count-inc)
block-step-count-inc {hv} prog fs s k cc h ft c-eq no-wrap =
  post , exec-eq , record
    { dataCorr = C.sim-reg-count-inc k fs s _ dc c-eq (C.sets-role-x86 s role-count _ _ _)
    ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (add (reg edi) (imm 1))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-reg-op count-inc) ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) edi (xreadReg (xregs s) edi + 1)
                    ; flags = updateFlags (xreadReg (xregs s) edi + 1) ; pc = pc s + 1 }
    wrap-free : xreadReg (xregs s) edi X.W.⊕ X.W.norm 1 ≡ xreadReg (xregs s) edi + 1
    -- PHASE D: peel the immediate's `norm` first — UNCONDITIONAL for `⊕`,
    -- which norms its sum anyway, so a pre-normed argument is unobservable.
    wrap-free = trans (X.W.⊕-normʳ (xreadReg (xregs s) edi) 1)
                      (X.W.⊕≡+ (xreadReg (xregs s) edi) 1 no-wrap)
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → X.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = xwriteReg (xregs s) edi w
                                        ; flags = updateFlags w
                                        ; pc = pc s + 1 }))
                wrap-free
                (step-add-ri {compile-trace prog} {s} {edi} {1} fetch-x86)
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-reg-op count-inc) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-reg-op count-inc) ft))

-- PLAN 0.70 PHASE C — THE ONE SUBTRACTION THAT HAD NO GUARD.
--
-- The other three `sub` sites (`alloc-stack`, `c-thunk`, `call`) carry a
-- `fits` premise that has always existed to tame truncated `∸`, and it turns
-- out to be exactly the no-borrow condition modular subtraction needs. This
-- one carried none: it decremented unconditionally, and BOTH sides clamped at
-- zero (`∸` on the machine, `sv-pred (SV-Tag 0) = SV-Tag 0` abstractly), so
-- the correspondence was true while both diverged from hardware together.
--
-- The guard is not new — it is in the EMITTED CODE. `cata-nat-I₂`/`I₃` emit
--
--     L4: c-branch-scratch-zero → L5 ; <body> ; scratch-dec ; c-jmp L4 ; L5:
--
-- so the decrement is reached only when the branch was NOT taken. `1 ≤ scratch`
-- was true of every reachable state all along and simply was not written down.
-- Now it is, and the dispatch discharges it from the branch it just took.
block-step-scratch-dec : ∀ {hv : HeapView} prog fs s k → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-dec)
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → 1 ≤ xreadReg (xregs s) edx                    -- the branch guard, recorded
  → xreadReg (xregs s) edx < X.W.modulus          -- the machine is finite
  → BlockStep hv prog fs s (instr-reg-op scratch-dec)
block-step-scratch-dec {hv} prog fs s k cc h ft sc-eq no-borrow edx<mod =
  post , exec-eq , record
    { dataCorr = C.sim-reg-scratch-dec k fs s _ dc sc-eq (C.sets-role-x86 s role-scratch _ _ _)
    ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (sub (reg edx) (imm 1))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-reg-op scratch-dec) ft)
    -- PLAN 0.70 PHASE D: peel the immediate's `norm` FIRST. `⊖` is
    -- `norm (x + (modulus ∸ y))`, so an out-of-range `y` would collapse it to
    -- `norm x` — norming the operand is what keeps `⊖` on its domain. The
    -- range fact is not new: `no-borrow` and `edx<mod` already give it.
    in-range : 1 < X.W.modulus
    in-range = ≤-<-trans no-borrow edx<mod
    borrow-free : xreadReg (xregs s) edx X.W.⊖ X.W.norm 1 ≡ xreadReg (xregs s) edx ∸ 1
    borrow-free = trans (X.W.⊖-normʳ (xreadReg (xregs s) edx) 1 in-range)
                        (X.W.⊖≡∸ (xreadReg (xregs s) edx) 1 no-borrow edx<mod)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) edx (xreadReg (xregs s) edx ∸ 1)
                    ; flags = updateFlags (xreadReg (xregs s) edx ∸ 1) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → X.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = xwriteReg (xregs s) edx w
                                        ; flags = updateFlags w
                                        ; pc = pc s + 1 }))
                borrow-free
                (step-sub-ri {compile-trace prog} {s} {edx} {1} fetch-x86)
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-reg-op scratch-dec) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-reg-op scratch-dec) ft))

-- c-branch-scratch-zero: cmp edx,0 ; je n. Two x86 steps; the je branch
-- depends on whether Scratch ≟ 0. With Scratch = SV-Tag k, the flat
-- condition sv-is-zero and the x86 zf (edx≡ᵇ0, edx = k) agree by case on k.
-- Data unchanged (control only).
block-step-c-branch-scratch-zero : ∀ {hv : HeapView} prog fs s n k j → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero n))
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → find-label prog n ≡ just j
  → BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
block-step-c-branch-scratch-zero {hv} prog fs s n zero j cc h ft sc-eq fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (reg edx) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (xreadReg (xregs s) edx ≡ᵇ 0) (xreadReg (xregs s) edx <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    step-cmp = step-cmp-ri {compile-trace prog} {s} {edx} {0} fetch-cmp
    rbx-val : xreadReg (xregs s) edx ≡ 0
    rbx-val = trans (C.scratch-eq dc) (cong (C.enc-sv hv) sc-eq)
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    zf-true : X.Flags.zf (flags post-cmp) ≡ true
    zf-true = cong (_≡ᵇ 0) rbx-val
    fl-x86 : X.find-label (compile-trace prog) (once n) ≡ just (blk-off prog j)
    fl-x86 = find-label-corr prog n 0 j fl-eq
    post-je : X.State
    post-je = record post-cmp { pc = blk-off prog j }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-taken {compile-trace prog} {post-cmp} {once n} {blk-off prog j} fetch-je zf-true fl-x86
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq | fl-eq = post-je , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = refl ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
block-step-c-branch-scratch-zero {hv} prog fs s n (suc m) j cc h ft sc-eq fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (reg edx) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (xreadReg (xregs s) edx ≡ᵇ 0) (xreadReg (xregs s) edx <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    step-cmp = step-cmp-ri {compile-trace prog} {s} {edx} {0} fetch-cmp
    rbx-val : xreadReg (xregs s) edx ≡ suc m
    rbx-val = trans (C.scratch-eq dc) (cong (C.enc-sv hv) sc-eq)
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    zf-false : X.Flags.zf (flags post-cmp) ≡ false
    zf-false = cong (_≡ᵇ 0) rbx-val
    post-je : X.State
    post-je = record post-cmp { pc = X.State.pc post-cmp + 1 }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-not {compile-trace prog} {post-cmp} {once n} fetch-je zf-false
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    pco' : X.State.pc post-je ≡ blk-off prog (suc (fpc fs))
    pco' = trans (+-assoc (pc s) 1 1) (trans (cong (_+ 2) po) (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)))
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq = post-je , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }

-- c-branch-tag-zero: cmp [ecx],0 ; je n. Like scratch-zero but the condition
-- is the heap tag at *Input1 (cond-eq reduces it to sv-is-zero (SV-Tag k)
-- like sim-test-tag); the x86 cmp reads the same value via heap-eq. The
-- THE `+ 0` IS THE CORE'S, NOT THIS ARCH'S. `CompiledCorrespondence`'s field
-- says `memory s (rreg s in1-reg + 0)`, which is the shape x86-64's
-- `[rdi+0]` and riscv64's `ld t1, 0(t0)` both produce. x86-32 emits
-- `cmp [ecx], 0` — no displacement — so its read is at `rreg s in1-reg` and
-- the premise is converted here, next to the addressing mode it belongs to,
-- with `+-identityʳ`. (The core would read better saying what it MEANS — the
-- tag cell at the Input1 pointer — and letting each arch add its own
-- displacement; noted for a follow-up, since two arches match it as written.)
-- RESIDENCE-GENERIC (2026-08-02 vacuity fix): the branch never cared where
-- the tag cell lives — only the ABSTRACT read (`readLoc`, both residences)
-- and the CONCRETE read (`rd`, supplied by the routing site per residence:
-- heap via `heap-eq`/`dom-written`, stack via `stack-eq` + the live-pair
-- witness). Stack-mode sums (`inl/inr Stack`) DO write their tag — into a
-- stack slot — so the old `AtDynamic`-only form was REFUTABLE (probe).
block-step-c-branch-tag-zero : ∀ {hv : HeapView} prog fs s n loc k j → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero n))
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
  → readLoc (floc fs) loc ≡ just (SV-Tag k)
  → X.readMem (memory s) (xreadReg (xregs s) ecx + 0) ≡ just k
  → find-label prog n ≡ just j
  → BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
block-step-c-branch-tag-zero {hv} prog fs s n loc zero j cc h ft i-eq r-eq rd fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (mem (base ecx)) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (0 ≡ᵇ 0) (0 <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    rd' : X.readMem (memory s) (X.effectiveAddr s (base ecx)) ≡ just 0
    rd' = subst (λ a → X.readMem (memory s) a ≡ just 0) (+-identityʳ (xreadReg (xregs s) ecx)) rd
    step-cmp = step-cmp-mi {compile-trace prog} {s} {base ecx} {0} {0} fetch-cmp rd'
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    fl-x86 : X.find-label (compile-trace prog) (once n) ≡ just (blk-off prog j)
    fl-x86 = find-label-corr prog n 0 j fl-eq
    post-je : X.State
    post-je = record post-cmp { pc = blk-off prog j }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-taken {compile-trace prog} {post-cmp} {once n} {blk-off prog j} fetch-je refl fl-x86
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    cond-eq : tag-zf (flat-read-tag (floc fs)) ≡ sv-is-zero (SV-Tag {FS} zero)
    cond-eq = cong tag-zf (trans (cong (flat-read-at (floc fs)) (cong sv-as-loc i-eq)) r-eq)
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
    result rewrite cond-eq | fl-eq = post-je , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = refl ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
block-step-c-branch-tag-zero {hv} prog fs s n loc (suc m) j cc h ft i-eq r-eq rd fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (mem (base ecx)) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (suc m ≡ᵇ 0) (suc m <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    rd' : X.readMem (memory s) (X.effectiveAddr s (base ecx)) ≡ just (suc m)
    rd' = subst (λ a → X.readMem (memory s) a ≡ just (suc m)) (+-identityʳ (xreadReg (xregs s) ecx)) rd
    step-cmp = step-cmp-mi {compile-trace prog} {s} {base ecx} {0} {suc m} fetch-cmp rd'
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post-je : X.State
    post-je = record post-cmp { pc = X.State.pc post-cmp + 1 }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-not {compile-trace prog} {post-cmp} {once n} fetch-je refl
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    cond-eq : tag-zf (flat-read-tag (floc fs)) ≡ sv-is-zero (SV-Tag {FS} (suc m))
    cond-eq = cong tag-zf (trans (cong (flat-read-at (floc fs)) (cong sv-as-loc i-eq)) r-eq)
    pco' : X.State.pc post-je ≡ blk-off prog (suc (fpc fs))
    pco' = trans (+-assoc (pc s) 1 1) (trans (cong (_+ 2) po) (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)))
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
    result rewrite cond-eq = post-je , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }

------------------------------------------------------------------------
-- THE EMPTY-CELL STUCK FACTS (D073): a load through a pointer whose target
-- cell is UNWRITTEN reads unmapped memory — `execInstr` fails, ending the
-- concrete trace exactly where the abstract machine halts. One per addressing
-- form (heap/stack × first/second cell); ConcFlatSim assembles each with
-- `run-events-stuck` + `flat-events-halted`. The heap forms take `HDom` (fed
-- from `dom-sized` + the load-site in-bounds discipline); the stack forms take
-- the live-pair witnesses `stack-ptr-current{,-suc}` provide.
------------------------------------------------------------------------
load-indirect-heap-empty-stuck : ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s
  → fetch prog (fpc fs) ≡ just load-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl
  → heapMem (floc fs) hl ≡ nothing
  → (X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg eax) (mem (base ecx))))
    × (X.execInstr (compile-trace prog) s (mov (reg eax) (mem (base ecx))) ≡ nothing)
load-indirect-heap-empty-stuck {hv} prog fs s hl cc ft i-eq dom h-eq = fetch-x86 , stuck
  where
    dc = dataCorr cc ; po = pc-off cc
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg eax) (mem (base ecx)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect ft)
    rdi-val : xreadReg (xregs s) ecx ≡ haddr hv hl
    rdi-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    rd : X.readMem (memory s) (X.effectiveAddr s (base ecx)) ≡ nothing
    rd = trans (cong (X.readMem (memory s)) rdi-val)
               (trans (C.heap-eq dc hl dom) (cong (C.enc-maybe hv) h-eq))
    stuck : X.execInstr (compile-trace prog) s (mov (reg eax) (mem (base ecx))) ≡ nothing
    stuck rewrite rd = refl

-- `load-indirect-stack-empty-stuck` / `load-indirect-suc-stack-empty-stuck`
-- DELETED (Plan 0.54 rung D). Each proved "the abstract slot is empty ⇒ the
-- concrete machine is stuck", which needed the OLD bidirectional `C.Window` to
-- assert the concrete cell was unmapped wherever the abstract one was. That
-- assertion was FALSE on frame re-entry (the cells hold the previous
-- incarnation's data) and is gone with the one-directional `Window`.
--
-- Their routes are UNREACHABLE anyway, which is the honest reason to delete
-- rather than re-prove: under heap mode `StackPtrWF` says there is NO stack
-- pointer, so `Input1` holding one is `⊥` (`stack-ptr-live` /
-- `stack-ptr-suc-live`). `ConcFlatSim`'s `go-stack … nothing` branches now
-- discharge by `⊥-elim` on exactly that.


load-indirect-suc-heap-empty-stuck : ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s
  → fetch prog (fpc fs) ≡ just load-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)
  → heapMem (floc fs) (sucHL hl) ≡ nothing
  → (X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg eax) (mem (base+disp ecx slot-size))))
    × (X.execInstr (compile-trace prog) s (mov (reg eax) (mem (base+disp ecx slot-size))) ≡ nothing)
load-indirect-suc-heap-empty-stuck {hv} prog fs s hl cc ft i-eq dom h-eq = fetch-x86 , stuck
  where
    dc = dataCorr cc ; po = pc-off cc
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg eax) (mem (base+disp ecx slot-size)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect-suc ft)
    rdi-val : xreadReg (xregs s) ecx ≡ haddr hv hl
    rdi-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-eq : X.effectiveAddr s (base+disp ecx slot-size) ≡ haddr hv (sucHL hl)
    addr-eq = trans (cong (_+ slot-size) rdi-val) (sym (C.haddr-suc hv hl))
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp ecx slot-size)) ≡ nothing
    rd = trans (cong (X.readMem (memory s)) addr-eq)
               (trans (C.heap-eq dc (sucHL hl) dom) (cong (C.enc-maybe hv) h-eq))
    stuck : X.execInstr (compile-trace prog) s (mov (reg eax) (mem (base+disp ecx slot-size))) ≡ nothing
    stuck rewrite rd = refl

-- c-branch-tag-zero NOT TAKEN, label-free: a nonzero tag never consults the
-- label, so the fall-through needs no `find-label` premise at all — this is
-- what discharges the not-taken route of `branch-tag-label-miss` (the missing
-- label is irrelevant when the branch is not taken). Body identical to the
-- `suc` clause above minus the unused label witness.
block-step-c-branch-tag-nz : ∀ {hv : HeapView} prog fs s n loc m → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero n))
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
  → readLoc (floc fs) loc ≡ just (SV-Tag (suc m))
  → X.readMem (memory s) (xreadReg (xregs s) ecx + 0) ≡ just (suc m)
  → BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
block-step-c-branch-tag-nz {hv} prog fs s n loc m cc h ft i-eq r-eq rd = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (mem (base ecx)) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (suc m ≡ᵇ 0) (suc m <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    rd' : X.readMem (memory s) (X.effectiveAddr s (base ecx)) ≡ just (suc m)
    rd' = subst (λ a → X.readMem (memory s) a ≡ just (suc m)) (+-identityʳ (xreadReg (xregs s) ecx)) rd
    step-cmp = step-cmp-mi {compile-trace prog} {s} {base ecx} {0} {suc m} fetch-cmp rd'
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post-je : X.State
    post-je = record post-cmp { pc = X.State.pc post-cmp + 1 }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-not {compile-trace prog} {post-cmp} {once n} fetch-je refl
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    cond-eq : tag-zf (flat-read-tag (floc fs)) ≡ sv-is-zero (SV-Tag {FS} (suc m))
    cond-eq = cong tag-zf (trans (cong (flat-read-at (floc fs)) (cong sv-as-loc i-eq)) r-eq)
    pco' : X.State.pc post-je ≡ blk-off prog (suc (fpc fs))
    pco' = trans (+-assoc (pc s) 1 1) (trans (cong (_+ 2) po) (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)))
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
    result rewrite cond-eq = post-je , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }

-- alloc-heap: `mov eax, esi ; add esi, n*8` (2 steps) ↔ the abstract fresh block.
-- THE view-EXTENDING step: the post-state correspondence holds at
-- `C.extend-view hv (next-heap-ref …) n (dom-fresh …)`, where the fresh block sits
-- exactly at the old `%esi`. The store-WF premises (nothing references the not-yet-
-- allocated ref) and the fresh-cell premises are the routing site's obligations.
block-step-alloc-heap : ∀ {hv : HeapView} prog fs s n → (cc : CompiledCorr hv prog fs s)
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-alloc-heap n)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Input1)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Scratch)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Count)
  → sv-below (next-heap-ref (falloc fs)) (fclosure fs)   -- D097: the closure register
  → (∀ hl → HDom hv hl → svm-below (next-heap-ref (falloc fs)) (heapMem (floc fs) hl))
  -- over EVERY frame (D085) — the form `FlatWF.wf-stack` already has
  → (∀ (f : FrameSemantics.Frame FS) (k : Slot) → svm-below (next-heap-ref (falloc fs)) (stackMem (floc fs) f k))
  → (∀ hl → ref-id (heap-ref hl) ≡ next-heap-ref (falloc fs) → heapMem (floc fs) hl ≡ nothing)
  -- ROOM: the bump stays below the stack's HIGH-WATER MARK (heap exhaustion). Plan
  -- 0.54 rung D step 3: measured against `lo`, not `%esp`, because a region the
  -- stack has already visited keeps its contents — and that is exactly what makes
  -- the fresh block's cells provably unwritten (the old `fresh-x86` premise, and
  -- with it the postulate `alloc-heap-fresh-x86`, is GONE).
  → (room : C.hfront hv + slots n ≤ C.lo hv)
  -- THE LAYOUT FITS IN THE ADDRESS SPACE (plan 0.70 phase C). `add` computes
  -- `W.⊕` unconditionally (D054), so the bump's no-wrap is the consumer's to
  -- pay — but here `room` above already bounds the bumped frontier by the
  -- stack's high-water mark, so the ONLY thing missing is that the mark itself
  -- is representable. That is the layout bound in its most basic form, and it
  -- is strictly weaker than a per-site no-wrap premise.
  → C.lo hv < X.W.modulus
  → BlockStep (C.extend-view hv (next-heap-ref (falloc fs)) n (C.dom-fresh (dataCorr cc)) room)
              prog fs s (instr-alloc-heap n)
block-step-alloc-heap {hv} prog fs s n cc h ft wf1 wfs wfc wfcl wf-heap wf-stack fresh-abs room lo-fits =
  post-add , exec-eq , record { dataCorr = dataPost ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-mov : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg eax) (reg esi))
    fetch-mov = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-alloc-heap n) ft)
    post-mov : X.State
    post-mov = record s { regs = xwriteReg (xregs s) eax (xreadReg (xregs s) esi) ; pc = pc s + 1 }
    step1 : X.step-not-halted (compile-trace prog) s ≡ just post-mov
    step1 = step-mov-rr {compile-trace prog} {s} {eax} {esi} fetch-mov
    fetch-add : X.fetch (compile-trace prog) (X.State.pc post-mov) ≡ just (add (reg esi) (imm (slots n)))
    fetch-add = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                      (fetch-block-2nd prog (fpc fs) (instr-alloc-heap n) ft)
    post-add : X.State
    post-add = record post-mov { regs = xwriteReg (xregs post-mov) esi (xreadReg (xregs post-mov) esi + slots n)
                               ; flags = updateFlags (xreadReg (xregs post-mov) esi + slots n)
                               ; pc = pc post-mov + 1 }
    -- `%esi` IS the frontier (`frontier-eq`), so `room` bounds the bump by
    -- `lo`, and `lo-fits` carries it under the modulus.
    no-wrap : xreadReg (xregs post-mov) esi + slots n < X.W.modulus
    no-wrap = ≤-<-trans (subst (λ z → z + slots n ≤ C.lo hv)
                               (sym (C.frontier-eq dc)) room)
                        lo-fits
    wrap-free : xreadReg (xregs post-mov) esi X.W.⊕ X.W.norm (slots n)
              ≡ xreadReg (xregs post-mov) esi + slots n
    -- PHASE D: peel the immediate's `norm` first — UNCONDITIONAL for `⊕`,
    -- which norms its sum anyway, so a pre-normed argument is unobservable.
    wrap-free = trans (X.W.⊕-normʳ (xreadReg (xregs post-mov) esi) (slots n))
                      (X.W.⊕≡+ (xreadReg (xregs post-mov) esi) (slots n) no-wrap)
    step2 : X.step-not-halted (compile-trace prog) post-mov ≡ just post-add
    step2 = subst (λ w → X.step-not-halted (compile-trace prog) post-mov
                         ≡ just (record post-mov { regs = xwriteReg (xregs post-mov) esi w
                                                 ; flags = updateFlags w
                                                 ; pc = pc post-mov + 1 }))
                  wrap-free
                  (step-add-ri {compile-trace prog} {post-mov} {esi} {slots n} fetch-add)
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-add
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-mov} halt-s step1 halt-s)
                    (exec-1 {compile-trace prog} {0} {post-mov} {post-add} halt-s step2 halt-s)
    dataPost : C.FlatCorr (C.extend-view hv (next-heap-ref (falloc fs)) n (C.dom-fresh dc) room)
                          (flat-exec-instr (instr-alloc-heap n) prog fs) post-add
    dataPost = C.sim-alloc-heap n fs s _ dc
                 wf1 wfs wfc wfcl wf-heap wf-stack fresh-abs room
                 (C.sets-2roles-x86 s role-out role-heap _ _ _ _ (λ ()))
    pco' : X.State.pc post-add ≡ blk-off prog (fpc (flat-exec-instr (instr-alloc-heap n) prog fs))
    pco' = trans (trans (cong (λ p → (p + 1) + 1) po) (+-assoc (blk-off prog (fpc fs)) 1 1))
                 (sym (blk-off-suc prog (fpc fs) (instr-alloc-heap n) ft))

-- lea-slot: Output := &stack[frame, slot] ↔ `lea eax, [esp + slot-to-disp slot]`.
-- Plan 0.61's payoff: `X.effectiveAddr s (base+disp esp d) = readReg esp + d`, and
-- `sp-eq` anchors %esp to the current frame's base, so the computed address IS
-- the abstract slot's address (`sim-lea-slot`).
block-step-lea-slot : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (lea-slot slot)
  → BlockStep hv prog fs s (lea-slot slot)
block-step-lea-slot {hv} prog fs s slot cc h ft =
  post , exec-eq , record { dataCorr = C.sim-lea-slot slot fs s _ dc (C.sets-role-x86 s role-out _ _ _) ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (lea eax (base+disp esp (slot-to-disp slot)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (lea-slot slot) ft)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) eax
                               (X.effectiveAddr s (base+disp esp (slot-to-disp slot)))
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-lea {compile-trace prog} {s} {eax} {base+disp esp (slot-to-disp slot)} fetch-x86
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (lea-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (lea-slot slot) ft))


-- c-branch NOT TAKEN (`Scratch ≡ SV-Tag (suc m)`): the `je` falls through, so the
-- jump target is never consulted — no label premise, which is what lets the
-- MISSING-label case of a not-taken branch be an ordinary step rather than a
-- residual. (The taken case still needs `find-label ≡ just j`.)
block-step-c-branch-nz : ∀ {hv : HeapView} prog fs s n m → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero n))
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag (suc m)
  → BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
block-step-c-branch-nz {hv} prog fs s n m cc h ft sc-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (reg edx) (imm 0))
    fetch-cmp = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    post-cmp : X.State
    post-cmp = record s { flags = mkflags (xreadReg (xregs s) edx ≡ᵇ 0) (xreadReg (xregs s) edx <ᵇ 0) false ; pc = pc s + 1 }
    step-cmp : X.step-not-halted (compile-trace prog) s ≡ just post-cmp
    step-cmp = step-cmp-ri {compile-trace prog} {s} {edx} {0} fetch-cmp
    rbx-val : xreadReg (xregs s) edx ≡ suc m
    rbx-val = trans (C.scratch-eq dc) (cong (C.enc-sv hv) sc-eq)
    fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once n))
    fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) po)
                     (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    zf-false : X.Flags.zf (flags post-cmp) ≡ false
    zf-false = cong (_≡ᵇ 0) rbx-val
    post-je : X.State
    post-je = record post-cmp { pc = X.State.pc post-cmp + 1 }
    step-je : X.step-not-halted (compile-trace prog) post-cmp ≡ just post-je
    step-je = step-je-not {compile-trace prog} {post-cmp} {once n} fetch-je zf-false
    exec-eq : X.exec 2 (compile-trace prog) s ≡ just post-je
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-cmp} halt-s step-cmp halt-s)
                    (exec-1 {compile-trace prog} {0} {post-cmp} {post-je} halt-s step-je halt-s)
    pco' : X.State.pc post-je ≡ blk-off prog (suc (fpc fs))
    pco' = trans (+-assoc (pc s) 1 1) (trans (cong (_+ 2) po) (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)))
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq = post-je , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }


-- load-indirect through a STACK pointer ↔ `mov eax, [ecx]`. `in1-eq` gives
-- ecx ≡ slot-addr f k; for the CURRENT frame `sp-eq` + `slot-addr-linear` turn
-- that into `esp + slot-to-disp k`, which is exactly the address `stack-eq`
-- speaks about — so the loaded value is the slot's. Unprovable before plan 0.61,
-- when a stack pointer encoded to the placeholder `0`.
block-step-load-indirect-stack : ∀ {hv : HeapView} prog fs s f k w → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → f ≡ current-frame (falloc fs)
  → k < frame-slots (falloc fs)
  → stackMem (floc fs) (current-frame (falloc fs)) k ≡ just w
  → BlockStep hv prog fs s load-indirect
block-step-load-indirect-stack {hv} prog fs s f k w cc h ft i-eq f-eq k<ss st-eq =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (reg eax) (mem (base ecx)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect ft)
    -- ecx is the slot's ADDRESS, and for the current frame that is esp-relative
    rdi-val : xreadReg (xregs s) ecx ≡ xreadReg (xregs s) esp + slot-to-disp k
    rdi-val = trans (C.in1-eq dc)
              (trans (cong (C.enc-sv hv) i-eq)
              (trans (cong (λ fr → slot-addr FS fr k) f-eq)
              (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                     (cong₂ (λ b w' → b + k * w') (sym (C.sp-eq dc)) word-eq))))
    rd : X.readMem (memory s) (X.effectiveAddr s (base ecx)) ≡ just (C.enc-sv hv w)
    rd = trans (cong (X.readMem (memory s)) rdi-val)
               (C.stack-eq-cur dc k k<ss _ st-eq)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) eax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {eax} {base ecx} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr load-indirect prog fs) post
    dataPost = C.sim-load-indirect-stack f k w fs s _ dc i-eq
                 (trans (cong (λ fr → stackMem (floc fs) fr k) f-eq) st-eq)
                 (C.sets-role-x86 s role-out _ _ _)
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr load-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) load-indirect ft))

-- load-indirect-suc through a stack pointer ↔ `mov eax, [ecx + 8]`. The x86
-- address is `slot-addr f k + 8`, which for the current frame is
-- `esp + slot-to-disp (suc k)` — the cell `stack-eq` relates to slot `suc k`.
block-step-load-indirect-suc-stack : ∀ {hv : HeapView} prog fs s f k w → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → f ≡ current-frame (falloc fs)
  → suc k < frame-slots (falloc fs)
  → stackMem (floc fs) (current-frame (falloc fs)) (suc k) ≡ just w
  → BlockStep hv prog fs s load-indirect-suc
block-step-load-indirect-suc-stack {hv} prog fs s f k w cc h ft i-eq f-eq sk<ss st-eq =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (reg eax) (mem (base+disp ecx slot-size)))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) load-indirect-suc ft)
    -- ecx + 8 = (esp + 8·k) + 8 = esp + 8·(suc k)
    addr-eq : xreadReg (xregs s) ecx + slot-size
            ≡ xreadReg (xregs s) esp + slot-to-disp (suc k)
    addr-eq = trans (cong (_+ slot-size)
                      (trans (C.in1-eq dc)
                      (trans (cong (C.enc-sv hv) i-eq)
                      (trans (cong (λ fr → slot-addr FS fr k) f-eq)
                      (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                             (cong₂ (λ b w' → b + k * w') (sym (C.sp-eq dc)) word-eq))))))
                    (trans (+-assoc (xreadReg (xregs s) esp) (k * slot-size) slot-size)
                           (cong (xreadReg (xregs s) esp +_)
                                 (+-comm (k * slot-size) slot-size)))
    rd : X.readMem (memory s) (X.effectiveAddr s (base+disp ecx slot-size)) ≡ just (C.enc-sv hv w)
    rd = trans (cong (X.readMem (memory s)) addr-eq)
               (C.stack-eq-cur dc (suc k) sk<ss _ st-eq)
    post : X.State
    post = record s { regs = xwriteReg (xregs s) eax (C.enc-sv hv w) ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mov-rm {compile-trace prog} {s} {eax} {base+disp ecx slot-size} {C.enc-sv hv w} fetch-x86 rd
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr load-indirect-suc prog fs) post
    dataPost = C.sim-load-indirect-suc-stack f k w fs s _ dc i-eq
                 (trans (cong (λ fr → stackMem (floc fs) fr (suc k)) f-eq) st-eq)
                 (C.sets-role-x86 s role-out _ _ _)
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr load-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) load-indirect-suc ft))

-- store-indirect through a stack pointer ↔ `mov [ecx], eax`, where ecx is the
-- slot's address. Same shape as `block-step-store-at-slot`, with the address
-- coming from Input1 (`in1-eq` + `slot-addr-linear` + `sp-eq`).
block-step-store-indirect-stack : ∀ {hv : HeapView} prog fs s f k → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → f ≡ current-frame (falloc fs)
  -- D085: the write must be inside THIS frame's reservation — otherwise it
  -- lands in the caller's window (`stack-ptr-current` supplies it).
  → k < frame-slots (falloc fs)
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) esp + slot-to-disp k ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s store-indirect
block-step-store-indirect-stack {hv} prog fs s f k cc h ft i-eq f-eq k<ns disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = ret-slot-store prog fs s k _ cc k<ns
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    Out = readReg (regs (floc fs)) Output
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (mov (mem (base ecx)) (reg eax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) store-indirect ft)
    rdi-val : xreadReg (xregs s) ecx ≡ xreadReg (xregs s) esp + slot-to-disp k
    rdi-val = trans (C.in1-eq dc)
              (trans (cong (C.enc-sv hv) i-eq)
              (trans (cong (λ fr → slot-addr FS fr k) f-eq)
              (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                     (cong₂ (λ b w' → b + k * w') (sym (C.sp-eq dc)) word-eq))))
    i-eq' : readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
    i-eq' = trans i-eq (cong (λ fr → SV-Ptr (AtStack fr k)) f-eq)
    post : X.State
    post = record s { memory = writeMem (memory s) (xreadReg (xregs s) esp + slot-to-disp k)
                                        (C.enc-sv hv Out)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = trans (step-mov-mr {compile-trace prog} {s} {base ecx} {eax} fetch-x86)
                (cong just (cong₂ (λ a v → record s { memory = writeMem (memory s) a v ; pc = pc s + 1 })
                                  rdi-val (C.out-eq dc)))
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect prog fs) post
    dataPost = C.sim-store-indirect-stack k fs s _ dc i-eq' k<ns disj (C.sets-mem-x86 s _ _ _ _)
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr store-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) store-indirect ft))

-- …and the SECOND cell: `mov [ecx+8], eax`, whose target is esp+8·(suc k) —
-- exactly what `sucLoc (AtStack f k)` names abstractly. The address arithmetic is
-- `block-step-load-indirect-suc-stack`'s (ecx+8 = (esp+8k)+8 = esp+8·(suc k));
-- the read-back/disjointness is the non-suc store's, at slot `suc k`.
block-step-store-indirect-suc-stack : ∀ {hv : HeapView} prog fs s f k → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → f ≡ current-frame (falloc fs)
  → suc k < frame-slots (falloc fs)   -- the PAIR's second slot (D085)
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) esp + slot-to-disp (suc k) ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s store-indirect-suc
block-step-store-indirect-suc-stack {hv} prog fs s f k cc h ft i-eq f-eq sk<ns disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = ret-slot-store prog fs s (suc k) _ cc sk<ns
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    Out = readReg (regs (floc fs)) Output
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s)
              ≡ just (mov (mem (base+disp ecx slot-size)) (reg eax))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) store-indirect-suc ft)
    -- ecx + 8 = (esp + 8·k) + 8 = esp + 8·(suc k)
    addr-eq : xreadReg (xregs s) ecx + slot-size
            ≡ xreadReg (xregs s) esp + slot-to-disp (suc k)
    addr-eq = trans (cong (_+ slot-size)
                      (trans (C.in1-eq dc)
                      (trans (cong (C.enc-sv hv) i-eq)
                      (trans (cong (λ fr → slot-addr FS fr k) f-eq)
                      (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                             (cong₂ (λ b w' → b + k * w') (sym (C.sp-eq dc)) word-eq))))))
                    (trans (+-assoc (xreadReg (xregs s) esp) (k * slot-size) slot-size)
                           (cong (xreadReg (xregs s) esp +_)
                                 (+-comm (k * slot-size) slot-size)))
    i-eq' : readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
    i-eq' = trans i-eq (cong (λ fr → SV-Ptr (AtStack fr k)) f-eq)
    post : X.State
    post = record s { memory = writeMem (memory s) (xreadReg (xregs s) esp + slot-to-disp (suc k))
                                        (C.enc-sv hv Out)
                    ; pc = pc s + 1 }
    snh : X.step-not-halted (compile-trace prog) s ≡ just post
    snh = trans (step-mov-mr {compile-trace prog} {s} {base+disp ecx slot-size} {eax} fetch-x86)
                (cong just (cong₂ (λ a v → record s { memory = writeMem (memory s) a v ; pc = pc s + 1 })
                                  addr-eq (C.out-eq dc)))
    exec-eq : X.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect-suc prog fs) post
    dataPost = C.sim-store-indirect-suc-stack k fs s _ dc i-eq' sk<ns disj (C.sets-mem-x86 s _ _ _ _)
    pco' : X.State.pc post ≡ blk-off prog (fpc (flat-exec-instr store-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) store-indirect-suc ft))

------------------------------------------------------------------------
-- THE SUPPLY RECORD (plan 0.65 G2 item 4, slice 2 — the deliverable).
--
-- x86-32 filling the core's `BlockSteps`: one field per block-step the
-- ENGINE dispatches to, and the thing slice 3's generic event layer will take
-- as its per-arch argument.
--
-- IT IS ALSO THE GATE. A `BlockSteps` field that is under-constrained relative
-- to what an arch needs typechecks perfectly on its own — the record is just a
-- type — and the engine would simply never demand the missing premise. That
-- failure mode was invisible until this value existed, because a record VALUE
-- takes its field types from the record and so cannot drift from them. From
-- here on, weakening a field breaks this line.
--
-- The five block-steps above with NO field here are not omissions: the engine
-- refutes `alloc-stack` / `dealloc-stack` / `push-frame` / `pop-frame` /
-- `lea-indexed` outright (`frame-op-absurd` — `ir-to-trace` emits none of
-- them), so nothing can ever call them.
------------------------------------------------------------------------
x86-32-block-steps : BlockSteps
x86-32-block-steps = record
  { bs-mov-to-output        = block-step-mov-to-output
  ; bs-mov-to-input         = block-step-mov-to-input
  ; bs-scratch-one          = block-step-scratch-one
  ; bs-scratch-zero         = block-step-scratch-zero
  ; bs-count-zero           = block-step-count-zero
  ; bs-scratch-load-count   = block-step-scratch-load-count
  ; bs-c-label              = block-step-c-label
  ; bs-reclaim-to           = block-step-reclaim-to
  ; bs-worklist-init        = block-step-worklist-init
  ; bs-worklist-check       = block-step-worklist-check
  -- the `RunAt` is DROPPED: x86-32 computes a slot address with `lea`, which
  -- carries no range obligation. The premise exists for riscv64's `addi`
  -- (2026-08-16 — see the field), and this arch paying nothing for it is the
  -- interface working as intended.
  ; bs-lea-slot             = λ prog fs s slot cc h ft _ →
                                block-step-lea-slot prog fs s slot cc h ft
  ; bs-save-closure-reg     = block-step-save-closure-reg
  ; bs-load-tag-lit         = block-step-load-tag-lit
  ; bs-load-indirect            = block-step-load-indirect
  ; bs-load-indirect-stack      = block-step-load-indirect-stack
  ; bs-load-indirect-suc        = block-step-load-indirect-suc
  ; bs-load-indirect-suc-stack  = block-step-load-indirect-suc-stack
  ; bs-load-from-slot           = block-step-load-from-slot
  ; bs-restore-input            = block-step-restore-input
  ; bs-worklist-pop             = block-step-worklist-pop
  ; bs-store-at-slot            = block-step-store-at-slot
  ; bs-worklist-push            = block-step-worklist-push
  ; bs-store-indirect           = block-step-store-indirect
  ; bs-store-indirect-stack     = block-step-store-indirect-stack
  ; bs-store-indirect-suc       = block-step-store-indirect-suc
  ; bs-store-indirect-suc-stack = block-step-store-indirect-suc-stack
  ; bs-c-jmp                    = block-step-c-jmp
  ; bs-c-branch-scratch-zero    = block-step-c-branch-scratch-zero
  ; bs-c-branch-nz              = block-step-c-branch-nz
  ; bs-c-branch-tag-zero        = block-step-c-branch-tag-zero
  ; bs-c-branch-tag-nz          = block-step-c-branch-tag-nz
  ; bs-scratch-dec              = block-step-scratch-dec
  ; bs-count-inc                = block-step-count-inc
  ; bs-c-thunk                  = block-step-c-thunk
  ; bs-c-ret                    = block-step-c-ret
  ; bs-load-const               = block-step-load-const
  ; bs-load-const-float         = block-step-load-const-float
  ; bs-load-code-addr           = block-step-load-code-addr
  ; bs-call                     = block-step-call
  ; bs-alloc-heap               = block-step-alloc-heap
  }
