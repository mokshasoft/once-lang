-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation
--
-- riscv64's compiled correspondence — the DATA correspondence (`FlatCorr`,
-- pc-free) ⊕ the block-offset pc relation, ⊕ the pending returns and the code
-- map. Mirror of x86-64's, and the same four fields for the same reasons:
-- `pc-off`, `ret-eq` and `code-eq` live HERE rather than in `FlatCorr` because
-- each needs `prog` to translate an abstract index or label.
--
-- SCOPE: `CompiledCorr`, the two generic single-instruction helpers, and the
-- straight-line register family. The instructions with real control or memory
-- content — the branches, the call/return, the frame movers — are still ahead;
-- `beq` in particular belongs to G1d step 3's branch-block law.
--
-- It exists now for two reasons, both structural rather than opportunistic:
--
--   * `RiscV64/FlatComposition.agda` was an ISLAND — typechecked by the
--     `ccc-riscv64` target and imported by nothing. This is its first real
--     consumer (`blk-off`), so the second instance of the G1b core is now
--     wired rather than merely gated.
--   * `HeapRoom`/`StackRoom`/`CallRoom` are CONDITIONED on `CompiledCorr` —
--     unconditioned they are refutable (the 2026-07-30 vacuity lesson). So
--     riscv64 could not state its resource bounds, and therefore could not
--     thread them from the apex, until this record existed. That thread is
--     what stops G2's block-steps from inventing their own premises.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.CCC.Target.RiscV64.Syntax using (slot-size)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

module Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Nat using (ℕ; suc; _+_; zero; _∸_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; drop; length)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS} using (FlatState; fpc; fret; falloc; floc; halted; flat-exec-instr; fetch)
open import Once.CCC.Label using (once; thunk; LabelId)

import Once.CCC.Target.RiscV64.Semantics as R
import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence as FC
module C = FC FS word-eq
open C using (HeapView; haddr; HDom; hfront)
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition FS
  using (blk-off; blk-len; blk-off-suc; fetch-block-head)
open import Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas
  using (exec-1; step-mv; step-li; step-label; step-ld; step-sd; step-addi)
open import Once.CCC.Target.RiscV64.Syntax using (Reg; mv; li; label; ld; sd; addi; a0; a1; t0; s3; s4; sp; slots)
import Data.Integer as ℤ
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (role-sp; role-clos; role-heap; role-out; role-in1; role-in2; role-scratch; role-count)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-trace; compile-abstract; slot-to-disp)
open import Data.Nat.Properties using (+-monoʳ-<; *-monoˡ-<)
open import Data.Empty using (⊥)
open import Once.CCC.FrameSemantics using (frame-base)

------------------------------------------------------------------------
-- The compiled correspondence.
------------------------------------------------------------------------
record CompiledCorr (hv : HeapView) (prog : AbstractTrace) (fs : FlatState) (s : R.State) : Set where
  field
    dataCorr : C.FlatCorr hv fs s
    -- CONTROL: the machine pc sits at the block offset of the flat pc.
    pc-off   : R.State.pc s ≡ blk-off prog (fpc fs)
    -- THE PENDING RETURNS (D093): every ghost `fret` entry is really in the
    -- machine's memory, at its frame's window end, under the same block-offset
    -- translation the pc uses.
    ret-eq   : C.RetAddrs (blk-off prog) (R.State.memory s)
                          (C.frames-of (falloc fs)) (fret fs)
    -- THE CODE MAP IS THE PROGRAM'S OWN RESOLUTION (D096): a `SV-Code ℓ`
    -- encodes to `caddr hv ℓ`, and that is the index the compiled program's
    -- own label scan finds.
    code-eq  : ∀ (ℓ : LabelId) (j : ℕ)
             → R.find-label (compile-trace prog) (thunk ℓ) ≡ just j
             → C.caddr hv ℓ ≡ j
open CompiledCorr public

------------------------------------------------------------------------
-- THE RETURN PICTURE IS UNTOUCHED (D093), same statement as x86-64's: the
-- generic helpers below are polymorphic in the instruction, so
-- `falloc (flat-exec-instr i prog fs)` does not reduce and they cannot see
-- that a straight-line step moves neither the frame stack nor the ghost return
-- stack. A pair of equations the caller discharges with `refl , refl`.
------------------------------------------------------------------------
RetSame : AbstractTrace → FlatState → AbstractInstr → Set
RetSame prog fs i =
  (C.frames-of (falloc (flat-exec-instr i prog fs)) ≡ C.frames-of (falloc fs))
  × (fret (flat-exec-instr i prog fs) ≡ fret fs)

ret-same : ∀ (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr)
             (mem : C.Memory) (rs : RetSame prog fs i)
         → C.RetAddrs (blk-off prog) mem (C.frames-of (falloc fs)) (fret fs)
         → C.RetAddrs (blk-off prog) mem
                      (C.frames-of (falloc (flat-exec-instr i prog fs)))
                      (fret (flat-exec-instr i prog fs))
ret-same prog fs i _ (fr-eq , rt-eq) r rewrite fr-eq | rt-eq = r

------------------------------------------------------------------------
-- ONE ABSTRACT STEP ↔ ITS COMPILED BLOCK.
------------------------------------------------------------------------
BlockStepAt : HeapView → HeapView → AbstractTrace → FlatState → R.State → AbstractInstr → Set
BlockStepAt hv hv' prog fs s i =
  Σ R.State (λ s' → (R.exec (blk-len i) (compile-trace prog) s ≡ just s')
                  × CompiledCorr hv' prog (flat-exec-instr i prog fs) s')

BlockStep : HeapView → AbstractTrace → FlatState → R.State → AbstractInstr → Set
BlockStep hv = BlockStepAt hv hv

------------------------------------------------------------------------
-- Generic single-`mv rd, rs` block-step. Assembly: fetch-block-head +
-- step-mv + exec-1, then the pc via pc-off + blk-off-suc. x86-64's
-- `block-step-mov-rr`, with `mv` where it writes `mov (reg _) (reg _)`.
------------------------------------------------------------------------
block-step-mv : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : R.State)
    (i : AbstractInstr) (dst src : Reg)
  → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just i
  → compile-abstract i ≡ mv dst src ∷ []
  → fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)
  → RetSame prog fs i
  → C.FlatCorr hv (flat-exec-instr i prog fs)
               (record s { regs = R.writeReg (R.State.regs s) dst (R.readReg (R.State.regs s) src)
                         ; pc = R.State.pc s + 1 })
  → BlockStep hv prog fs s i
block-step-mv {hv} prog fs s i dst src cc h-flat ft ca fpc-eq rsame dataPost =
  post , exec-eq-len , record { dataCorr = dataPost ; pc-off = pco'
                              ; ret-eq = ret-same prog fs i (R.State.memory s) rsame (ret-eq cc)
                              ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h-flat
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (mv dst src)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (trans (fetch-block-head prog (fpc fs) i ft)
                            (cong (λ b → R.fetch (b ++ compile-trace (drop (suc (fpc fs)) prog)) 0) ca))
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) dst (R.readReg (R.State.regs s) src)
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-mv {compile-trace prog} {s} {dst} {src} fetch-rv
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    exec-eq-len : R.exec (blk-len i) (compile-trace prog) s ≡ just post
    exec-eq-len = trans (cong (λ m → R.exec m (compile-trace prog) s) (cong length ca)) exec-eq
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr i prog fs))
    pco' rewrite fpc-eq =
      trans (cong (_+ 1) po)
            (trans (sym (cong (blk-off prog (fpc fs) +_) (cong length ca)))
                   (sym (blk-off-suc prog (fpc fs) i ft)))

-- The four register shuffles. riscv64 spells them `mv`, so each is the same
-- one-liner as x86-64's with its own pair of role registers.
block-step-mov-to-output : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-to-output → BlockStep hv prog fs s mov-to-output
block-step-mov-to-output {hv} prog fs s cc h ft =
  block-step-mv prog fs s mov-to-output a0 t0 cc h ft refl refl (refl , refl)
    (C.sim-mov-to-output fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-out _ _))

block-step-mov-to-input : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-to-input → BlockStep hv prog fs s mov-to-input
block-step-mov-to-input {hv} prog fs s cc h ft =
  block-step-mv prog fs s mov-to-input t0 a0 cc h ft refl refl (refl , refl)
    (C.sim-mov-to-input fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-in1 _ _))

block-step-mov-input2-to-output : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-input2-to-output → BlockStep hv prog fs s mov-input2-to-output
block-step-mov-input2-to-output {hv} prog fs s cc h ft =
  block-step-mv prog fs s mov-input2-to-output a0 a1 cc h ft refl refl (refl , refl)
    (C.sim-mov-input2-to-output fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-out _ _))

block-step-mov-output-to-input2 : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-output-to-input2 → BlockStep hv prog fs s mov-output-to-input2
block-step-mov-output-to-input2 {hv} prog fs s cc h ft =
  block-step-mv prog fs s mov-output-to-input2 a1 a0 cc h ft refl refl (refl , refl)
    (C.sim-mov-output-to-input2 fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-in2 _ _))

-- …and `scratch-load-count`, the fifth `mv`.
block-step-scratch-load-count : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-load-count)
  → BlockStep hv prog fs s (instr-reg-op scratch-load-count)
block-step-scratch-load-count {hv} prog fs s cc h ft =
  block-step-mv prog fs s (instr-reg-op scratch-load-count) s3 s4 cc h ft refl refl (refl , refl)
    (C.sim-reg-scratch-load-count fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-scratch _ _))

------------------------------------------------------------------------
-- Generic single-`li rd, +n` block-step — x86-64's `block-step-mov-ri`.
--
-- The immediate is `+ n` because that is what the emitter produces, and it is
-- `step-li` now covers BOTH signs (phase D): the old restriction existed only
-- because `execInstr` wrote `0` for a negative immediate, which was a defect
-- rather than a case. The emitter still only produces non-negative ones here.
------------------------------------------------------------------------
block-step-li : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : R.State)
    (i : AbstractInstr) (dst : Reg) (n : ℕ)
  → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just i
  → compile-abstract i ≡ li dst (ℤ.+ n) ∷ []
  -- PLAN 0.70 PHASE D — THE IMMEDIATE FITS IN A MACHINE WORD, exactly as on
  -- x86-64. `li` reads its immediate with `W.fromℤ`, which NORMS, so reading
  -- the post-state back as a bare `n` needs `n` in range.
  → n < R.W.modulus
  → fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)
  → RetSame prog fs i
  → C.FlatCorr hv (flat-exec-instr i prog fs)
               (record s { regs = R.writeReg (R.State.regs s) dst (R.offsetToℕ (ℤ.+ n))
                         ; pc = R.State.pc s + 1 })
  → BlockStep hv prog fs s i
block-step-li {hv} prog fs s i dst n cc h-flat ft ca fits fpc-eq rsame dataPost =
  post , exec-eq-len , record { dataCorr = dataPost ; pc-off = pco'
                              ; ret-eq = ret-same prog fs i (R.State.memory s) rsame (ret-eq cc)
                              ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h-flat
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (li dst (ℤ.+ n))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (trans (fetch-block-head prog (fpc fs) i ft)
                            (cong (λ b → R.fetch (b ++ compile-trace (drop (suc (fpc fs)) prog)) 0) ca))
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) dst (R.offsetToℕ (ℤ.+ n))
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → R.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = R.writeReg (R.State.regs s) dst w
                                        ; pc = R.State.pc s + 1 }))
                (R.W.norm-id fits)
                (step-li {compile-trace prog} {s} {dst} {ℤ.+ n} fetch-rv)
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    exec-eq-len : R.exec (blk-len i) (compile-trace prog) s ≡ just post
    exec-eq-len = trans (cong (λ m → R.exec m (compile-trace prog) s) (cong length ca)) exec-eq
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr i prog fs))
    pco' rewrite fpc-eq =
      trans (cong (_+ 1) po)
            (trans (sym (cong ((blk-off prog (fpc fs)) +_) (cong length ca)))
                   (sym (blk-off-suc prog (fpc fs) i ft)))

-- PHASE D: the tag literal must fit in a machine word; propagated, since `n` is
-- this lemma's own parameter (x86-64's `block-step-load-tag-lit` does the same).
block-step-load-tag-lit : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-tag-lit n) → n < R.W.modulus
  → BlockStep hv prog fs s (instr-load-tag-lit n)
block-step-load-tag-lit {hv} prog fs s n cc h ft fits =
  block-step-li prog fs s (instr-load-tag-lit n) a0 n cc h ft refl fits refl (refl , refl)
    (C.sim-load-tag-lit n fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-out _ _))

block-step-scratch-one : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-one)
  → BlockStep hv prog fs s (instr-reg-op scratch-one)
block-step-scratch-one {hv} prog fs s cc h ft =
  block-step-li prog fs s (instr-reg-op scratch-one) s3 1 cc h ft refl (R.W.1<modulus (s≤s z≤n)) refl (refl , refl)
    (C.sim-reg-scratch-one fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-scratch _ _))

block-step-scratch-zero : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-zero)
  → BlockStep hv prog fs s (instr-reg-op scratch-zero)
block-step-scratch-zero {hv} prog fs s cc h ft =
  block-step-li prog fs s (instr-reg-op scratch-zero) s3 0 cc h ft refl R.W.0<modulus refl (refl , refl)
    (C.sim-reg-scratch-zero fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-scratch _ _))

block-step-count-zero : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op count-zero)
  → BlockStep hv prog fs s (instr-reg-op count-zero)
block-step-count-zero {hv} prog fs s cc h ft =
  block-step-li prog fs s (instr-reg-op count-zero) s4 0 cc h ft refl R.W.0<modulus refl (refl , refl)
    (C.sim-reg-count-zero fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-count _ _))

------------------------------------------------------------------------
-- `c-label`: the pc passes through and nothing else moves. riscv64's `label`
-- is a no-op at runtime exactly as x86-64's is, so the whole content is
-- copying `FlatCorr` across and shifting the pc by one block.
--
-- The data correspondence is rebuilt field by field rather than reused
-- wholesale because the flat step changes `fpc`, so the two `FlatCorr`s are at
-- different flat states even though every field's PROOF is the same one.
------------------------------------------------------------------------
block-step-c-label : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-label n)) → BlockStep hv prog fs s (instr-ctrl (c-label n))
block-step-c-label {hv} prog fs s n cc h ft = post , exec-eq , record
  { dataCorr = record { in1-eq = C.in1-eq (dataCorr cc) ; in2-eq = C.in2-eq (dataCorr cc)
                      ; out-eq = C.out-eq (dataCorr cc) ; scratch-eq = C.scratch-eq (dataCorr cc)
                      ; count-eq = C.count-eq (dataCorr cc) ; clos-eq = C.clos-eq (dataCorr cc)
                      ; halt-eq = C.halt-eq (dataCorr cc) ; heap-eq = C.heap-eq (dataCorr cc)
                      ; sp-eq = C.sp-eq (dataCorr cc) ; frontier-eq = C.frontier-eq (dataCorr cc)
                      ; dom-fresh = C.dom-fresh (dataCorr cc) ; dom-written = C.dom-written (dataCorr cc)
                      ; dom-sized = C.dom-sized (dataCorr cc) ; lo-le = C.lo-le (dataCorr cc)
                      ; untouched = C.untouched (dataCorr cc) ; stack-eq = C.stack-eq (dataCorr cc) }
  ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (label (once n))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-ctrl (c-label n)) ft)
    post : R.State
    post = record s { pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-label {compile-trace prog} {s} {once n} fetch-rv
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-ctrl (c-label n)) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-label n)) ft))

------------------------------------------------------------------------
-- THE SLOT ACCESSES — riscv64's first MEMORY-touching block-steps (0.65 G2).
--
-- Mirrors x86-64's three exactly, which is the point: `stack-eq-cur` already
-- states the read address as `rreg s sp-reg + slot-to-disp k`, and riscv64's
-- `effectiveAddr rf base off` IS `readReg rf base + off`, so the generic
-- correspondence lands on `ld`/`sd` with no adapter. The two helpers below are
-- copied from x86-64 for the same reason (`elfs-frames` is abstract-side only
-- and is a candidate for the core; `ret-slot-store` differs only by the state
-- type).
------------------------------------------------------------------------

elfs-frames : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
            → C.frames-of (proj₂ (AbstractExec.exec-load-from-slot-with-value {FS} mv ls alloc))
              ≡ C.frames-of alloc
elfs-frames (just v) ls alloc = refl
elfs-frames nothing  ls alloc = refl

-- A STACK STORE MISSES EVERY PENDING RETURN (D093) — x86-64's `ret-slot-store`,
-- at riscv64's state type.
ret-slot-store : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : R.State)
                   (slot : Slot) (v : R.Word)
               → CompiledCorr hv prog fs s
               → slot < frame-slots (falloc fs)
               → C.RetAddrs (blk-off prog)
                   (R.writeMem (R.State.memory s)
                      (R.readReg (R.State.regs s) sp + slot-to-disp slot) v)
                   (C.frames-of (falloc fs)) (fret fs)
ret-slot-store {hv} prog fs s slot v cc slot<b =
  C.ret-write-in-frame (blk-off prog) (R.State.memory s) (stackMem (floc fs))
    (R.readReg (R.State.regs s) sp + slot-to-disp slot) v (C.lo hv)
    (current-frame (falloc fs)) (frame-slots (falloc fs))
    (saved-frames (falloc fs)) (fret fs)
    w<end (C.stack-eq (dataCorr cc)) (ret-eq cc)
  where
    w<end : R.readReg (R.State.regs s) sp + slot-to-disp slot
          < frame-base FS (current-frame (falloc fs)) + slots (frame-slots (falloc fs))
    w<end rewrite C.sp-eq (dataCorr cc) =
      +-monoʳ-< (frame-base FS (current-frame (falloc fs))) (*-monoˡ-< slot-size slot<b)

-- load-from-slot: Output := stack[slot] ↔ `ld a0, slot*8(sp)`.
block-step-load-from-slot : ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (load-from-slot slot)
  → slot < frame-slots (falloc fs)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep hv prog fs s (load-from-slot slot)
block-step-load-from-slot {hv} prog fs s slot w cc h ft slot<ns st-eq =
  post , exec-eq , record { dataCorr = C.sim-load-from-slot slot w fs s _ dc st-eq (C.sets-role-riscv64 s role-out _ _) ; pc-off = pco'
                          ; ret-eq = ret-same prog fs (load-from-slot slot) (R.State.memory s)
                                       (elfs-frames (stackMem (floc fs) (current-frame (falloc fs)) slot) (floc fs) (falloc fs) , refl) (ret-eq cc)
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s)
             ≡ just (ld a0 sp (slot-to-disp slot))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (load-from-slot slot) ft)
    rd : R.readMem (R.State.memory s)
           (R.effectiveAddr (R.State.regs s) sp (slot-to-disp slot))
       ≡ just (C.enc-sv hv w)
    rd = C.stack-eq-cur dc slot slot<ns _ st-eq
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) a0 (C.enc-sv hv w)
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-ld {compile-trace prog} {s} {a0} {sp} {slot-to-disp slot} {C.enc-sv hv w} fetch-rv rd
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (load-from-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (load-from-slot slot) ft))

-- store-at-slot: stack[slot] := Output ↔ `sd a0, slot*8(sp)`.
block-step-store-at-slot : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (store-at-slot slot)
  → slot < frame-slots (falloc fs)
  → (∀ hl' → HDom hv hl' → (R.readReg (R.State.regs s) sp + slot-to-disp slot ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s (store-at-slot slot)
block-step-store-at-slot {hv} prog fs s slot cc h ft slot<ns disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = ret-slot-store prog fs s slot _ cc slot<ns
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s)
             ≡ just (sd a0 sp (slot-to-disp slot))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (store-at-slot slot) ft)
    post : R.State
    post = record s { memory = R.writeMem (R.State.memory s)
                                 (R.effectiveAddr (R.State.regs s) sp (slot-to-disp slot))
                                 (R.readReg (R.State.regs s) a0)
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-sd {compile-trace prog} {s} {a0} {sp} {slot-to-disp slot} fetch-rv
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    post-eq : post ≡ R.mkstate (R.State.regs s)
                        (R.writeMem (R.State.memory s)
                           (R.readReg (R.State.regs s) sp + slot-to-disp slot)
                           (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                        (R.State.pc s + 1) (R.State.halted s)
    post-eq = cong (λ v → R.mkstate (R.State.regs s)
                            (R.writeMem (R.State.memory s)
                               (R.readReg (R.State.regs s) sp + slot-to-disp slot) v)
                            (R.State.pc s + 1) (R.State.halted s))
                   (C.out-eq dc)
    dataPost : C.FlatCorr hv (flat-exec-instr (store-at-slot slot) prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr (store-at-slot slot) prog fs)) (sym post-eq)
                     (C.sim-store-at-slot slot fs s _ dc slot<ns disj (C.sets-mem-riscv64 s _ _ _))
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (store-at-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (store-at-slot slot) ft))

-- lea-slot: Output := &stack[slot] ↔ `addi a0, sp, slot*8`.
--
-- THE ONE PLACE riscv64 DIFFERS FROM x86-64 HERE, and it is plan 0.70's doing
-- rather than the ISA's: x86-64 computes this address with `lea`, which is not
-- an arithmetic instruction and so was never made modular. riscv64 has no `lea`
-- — it computes the address with `addi`, a real add — so the block-step needs
-- the ADDRESS NO-WRAP fact that x86-64's `lea` route never had to state. Same
-- class as `AddrNoWrap` (D087); a premise here until riscv64 has a
-- `ConcFlatSim` to supply it.
block-step-lea-slot : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (lea-slot slot)
  → R.readReg (R.State.regs s) sp + slot-to-disp slot < R.W.modulus
  → BlockStep hv prog fs s (lea-slot slot)
block-step-lea-slot {hv} prog fs s slot cc h ft no-wrap =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s)
             ≡ just (addi a0 sp (ℤ.+ (slot-to-disp slot)))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (lea-slot slot) ft)
    -- `addi` computes `⊕` on a NORMED immediate; peel the norm (unconditional
    -- for `⊕`) and then the modularity (the no-wrap premise).
    addr-eq : R.readReg (R.State.regs s) sp R.W.⊕ R.W.fromℤ (ℤ.+ (slot-to-disp slot))
            ≡ R.readReg (R.State.regs s) sp + slot-to-disp slot
    addr-eq = trans (R.W.⊕-normʳ (R.readReg (R.State.regs s) sp) (slot-to-disp slot))
                    (R.W.⊕≡+ (R.readReg (R.State.regs s) sp) (slot-to-disp slot) no-wrap)
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) a0
                               (R.readReg (R.State.regs s) sp + slot-to-disp slot)
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → R.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = R.writeReg (R.State.regs s) a0 w
                                        ; pc = R.State.pc s + 1 }))
                addr-eq
                (step-addi {compile-trace prog} {s} {a0} {sp} {ℤ.+ (slot-to-disp slot)} fetch-rv)
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr (lea-slot slot) prog fs) post
    dataPost = C.sim-lea-slot slot fs s _ dc (C.sets-role-riscv64 s role-out _ _)
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (lea-slot slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (lea-slot slot) ft))
