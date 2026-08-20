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
open import Once.CanonicalName using (CanonicalName)

-- `fmt-eq`'s type names a format, so this import must precede the header.
open import Once.Float.Dyadic using (Dyadic; encode; binary32; binary64)

module Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation
  -- D089's definition identity, threaded only so `CompiledCorrespondence` can
  -- state `bs-lea-slot`'s `RunAt` premise (2026-08-16).
  (o : CanonicalName)
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  -- …and the same kind of pinning for the FLOAT FORMAT (plan 0.73, D113).
  -- The emitter writes `encode binary64` into the immediate; the abstract machine
  -- materialises a float literal at `float-format FS`. For those to be the
  -- same number, THIS `FS` has to be this arch's — and with `FS` abstract
  -- here, that is not derivable, it is a premise. Discharged by `refl` at
  -- instantiation, exactly as `word-eq` is.
  (fmt-eq : FrameSemantics.float-format FS ≡ binary64)
  where

open import Data.Nat using (ℕ; suc; _+_; zero; _∸_; _<_; s≤s; z≤n; _≤_; _≡ᵇ_; _*_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; drop; length)
open import Data.Bool using (false; true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.CCC.Machine.SMCore
open MemOps {FS} using (writeLoc; writeLocToHeap; readLoc)
open import Once.CCC.Machine.Flat
open FlatMachine {FS} using (FlatState; fpc; fret; flink; falloc; floc; fclosure; halted; flat-exec-instr; fetch; find-label; tag-zf; flat-read-tag; flat-read-at; sv-is-zero; sv-as-loc; flink-do-ret; leave-frame; do-ret-pc-∷; do-ret-fret-∷; do-ret-alloc; enter-call; do-call-sv; do-call-code; do-call-at; find-thunk)
open import Once.CCC.Label using (once; thunk; LabelId)

import Once.CCC.Target.RiscV64.Semantics as R
import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence as FC
module C = FC FS word-eq
open C using (HeapView; haddr; HDom; hfront)
open import Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition FS
  using (blk-off; blk-len; blk-off-suc; fetch-block-head; fetch-block-2nd; fetch-block-3rd; find-label-corr; find-thunk-corr)
open import Once.Adequacy.ArchCorrectness.RiscV64.StepLemmas
  using (exec-1; step-mv; step-li; step-label; step-ld; step-sd; step-addi; step-lla; step-j-found; step-beq-taken; step-beq-not; step-ret; step-jalr)
open import Once.CCC.Target.RiscV64.Syntax using (Reg; mv; li; label; ld; sd; addi; lla; beq; j; ret; jalr; a0; a1; t0; t1; s1; s2; s3; s4; sp; ra; zero; slots)
import Data.Integer as ℤ
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (role-sp; role-clos; role-heap; role-out; role-in1; role-scratch; role-count)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-trace; compile-abstract; slot-to-disp)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Data.Nat.Properties using (+-monoʳ-<; *-monoˡ-<; ≤-<-trans; ≤-trans; <-transˡ; <⇒≢
                                      ; m∸n+n≡m)
open import Data.Empty using (⊥)
open import Once.CCC.FrameSemantics using (frame-base; slot-addr; slot-addr-linear; shift-frame; shift-base)
-- …and what `block-step-alloc-heap`'s premise list needs: the store-WF
-- predicates and the heap-reference identity (plan 0.65 G2).
open import Once.CCC.Machine.FlatStoreWF FS using (sv-below; svm-below)
open import Once.Memory.HeapAddress using (heap-ref; ref-id)
open import Once.Word using (Carrier)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Once.Type using (fits-int; fits-float)

------------------------------------------------------------------------
-- The compiled correspondence — NOW THE CORE'S (plan 0.65 G2, item 4's first
-- slice). riscv64's copy and x86-64's were structurally identical, differing
-- only in the state type, so the record moved to
-- `FlatCore.CompiledCorrespondence` and both arches instantiate it. What was a
-- duplicated four-field record is now one statement.
------------------------------------------------------------------------
open import Once.Adequacy.ArchCorrectness.RiscV64.RegRoles using (riscv64-roles)
open import Once.CCC.Target.RiscV64.Syntax using (Reg; Program) renaming (slot-size to rv-slot-size)
open R.State using () renaming (halted to rhalted)

rreg' : R.State → Reg → ℕ
rreg' s r = R.readReg (R.State.regs s) r

-- WHERE AN UNSPILLED RETURN LIVES ON riscv64: IN A REGISTER (plan 0.65 G2).
-- `jalr` writes `ra` and touches neither the stack pointer nor memory, so
-- between a call and the callee's `sd ra` the head pending return has no cell
-- at all. The ADDRESS argument is therefore ignored — that asymmetry with
-- x86-64 (whose claim reads the very cell the address names) is the ABI
-- difference this whole parameter exists to carry.
riscv64-link-claim : R.State → ℕ → ℕ → Set
riscv64-link-claim s _ v = rreg' s ra ≡ v

open import Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
       o FS rv-slot-size word-eq Reg riscv64-roles R.State rreg' R.State.memory rhalted
       riscv64-link-claim
       R.State.pc Program compile-trace R.find-label blk-off blk-len R.exec
       R.W.modulus
  public

-- …and its price: a register claim must be RE-STATED at every post-state, where
-- x86-64's memory claim rides along for free on a register write. One line per
-- site, `refl` whenever the written register is concrete (the register file is
-- a record, so `readReg (writeReg rf dst v) ra` computes).
-- Stated as an IMPLICATION BETWEEN CLAIMS rather than between states: `LK`/`LK'`
-- are then plain metas that the expected type solves outright, where
-- `riscv64-link-claim ?s` would need the unifier to unfold a definition.
ret-ra : ∀ {xoff : ℕ → ℕ} {mem : C.Memory} {LK LK' : ℕ → ℕ → Set} {lk : Maybe ℕ}
           {fr : List (FrameSemantics.Frame FS × ℕ)} {rs : List ℕ}
       → (∀ (a v : ℕ) → LK a v → LK' a v)
       → C.RetAddrs xoff mem LK lk fr rs
       → C.RetAddrs xoff mem LK' lk fr rs
ret-ra {xoff} {mem} {LK} {LK'} {lk} {fr} {rs} tr =
  C.ret-relk xoff mem LK LK' lk fr rs tr

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
  × (flink (flat-exec-instr i prog fs) ≡ flink fs)

ret-same : ∀ (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr)
             (mem : C.Memory) {LK : ℕ → ℕ → Set} (rs : RetSame prog fs i)
         → C.RetAddrs (blk-off prog) mem LK (flink fs) (C.frames-of (falloc fs)) (fret fs)
         → C.RetAddrs (blk-off prog) mem LK (flink (flat-exec-instr i prog fs))
                      (C.frames-of (falloc (flat-exec-instr i prog fs)))
                      (fret (flat-exec-instr i prog fs))
ret-same prog fs i _ (fr-eq , rt-eq , fl-eq) r rewrite fr-eq | rt-eq | fl-eq = r

------------------------------------------------------------------------
-- ONE ABSTRACT STEP ↔ ITS COMPILED BLOCK.
------------------------------------------------------------------------
-- (`BlockStepAt`/`BlockStep` moved to FlatCore.CompiledCorrespondence:
--  identical on both arches but for the state type and which `exec`.)

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
  -- …AND THE LINK REGISTER IS NOT `dst` (plan 0.65 G2). riscv64's head-row
  -- claim reads `ra`, so a register write has to say it missed it. `refl` at
  -- every caller — `dst` is concrete there and the register file is a record.
  → R.readReg (R.writeReg (R.State.regs s) dst (R.readReg (R.State.regs s) src)) ra
    ≡ R.readReg (R.State.regs s) ra
  → C.FlatCorr hv (flat-exec-instr i prog fs)
               (record s { regs = R.writeReg (R.State.regs s) dst (R.readReg (R.State.regs s) src)
                         ; pc = R.State.pc s + 1 })
  → BlockStep hv prog fs s i
block-step-mv {hv} prog fs s i dst src cc h-flat ft ca fpc-eq rsame ra-keep dataPost =
  post , exec-eq-len , record { dataCorr = dataPost ; pc-off = pco'
                              ; ret-eq = ret-ra (λ a v p → trans ra-keep p) (ret-same prog fs i (R.State.memory s) rsame (ret-eq cc))
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
  block-step-mv prog fs s mov-to-output a0 t0 cc h ft refl refl (refl , refl , refl) refl
    (C.sim-mov-to-output fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-out _ _))

block-step-mov-to-input : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just mov-to-input → BlockStep hv prog fs s mov-to-input
block-step-mov-to-input {hv} prog fs s cc h ft =
  block-step-mv prog fs s mov-to-input t0 a0 cc h ft refl refl (refl , refl , refl) refl
    (C.sim-mov-to-input fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-in1 _ _))



-- …and `scratch-load-count`, the fifth `mv`.
block-step-scratch-load-count : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-load-count)
  → BlockStep hv prog fs s (instr-reg-op scratch-load-count)
block-step-scratch-load-count {hv} prog fs s cc h ft =
  block-step-mv prog fs s (instr-reg-op scratch-load-count) s3 s4 cc h ft refl refl (refl , refl , refl) refl
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
  -- …and the link register is not `dst`, as at `block-step-mv`.
  → R.readReg (R.writeReg (R.State.regs s) dst (R.offsetToℕ (ℤ.+ n))) ra
    ≡ R.readReg (R.State.regs s) ra
  → C.FlatCorr hv (flat-exec-instr i prog fs)
               (record s { regs = R.writeReg (R.State.regs s) dst (R.offsetToℕ (ℤ.+ n))
                         ; pc = R.State.pc s + 1 })
  → BlockStep hv prog fs s i
block-step-li {hv} prog fs s i dst n cc h-flat ft ca fits fpc-eq rsame ra-keep dataPost =
  post , exec-eq-len , record { dataCorr = dataPost ; pc-off = pco'
                              ; ret-eq = ret-ra (λ a v p → trans ra-keep p) (ret-same prog fs i (R.State.memory s) rsame (ret-eq cc))
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
  block-step-li prog fs s (instr-load-tag-lit n) a0 n cc h ft refl fits refl (refl , refl , refl) refl
    (C.sim-load-tag-lit n fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-out _ _))

block-step-scratch-one : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-one)
  → BlockStep hv prog fs s (instr-reg-op scratch-one)
block-step-scratch-one {hv} prog fs s cc h ft =
  block-step-li prog fs s (instr-reg-op scratch-one) s3 1 cc h ft refl (R.W.1<modulus (s≤s z≤n)) refl (refl , refl , refl) refl
    (C.sim-reg-scratch-one fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-scratch _ _))

block-step-scratch-zero : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-zero)
  → BlockStep hv prog fs s (instr-reg-op scratch-zero)
block-step-scratch-zero {hv} prog fs s cc h ft =
  block-step-li prog fs s (instr-reg-op scratch-zero) s3 0 cc h ft refl R.W.0<modulus refl (refl , refl , refl) refl
    (C.sim-reg-scratch-zero fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-scratch _ _))

block-step-count-zero : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op count-zero)
  → BlockStep hv prog fs s (instr-reg-op count-zero)
block-step-count-zero {hv} prog fs s cc h ft =
  block-step-li prog fs s (instr-reg-op count-zero) s4 0 cc h ft refl R.W.0<modulus refl (refl , refl , refl) refl
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
  { dataCorr = record { in1-eq = C.in1-eq (dataCorr cc)
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
                   (riscv64-link-claim s) (flink fs)
                   (C.frames-of (falloc fs)) (fret fs)
ret-slot-store {hv} prog fs s slot v cc slot<b =
  C.ret-write-in-frame (blk-off prog) (R.State.memory s)
    (riscv64-link-claim s) (riscv64-link-claim s) (flink fs) (stackMem (floc fs))
    (R.readReg (R.State.regs s) sp + slot-to-disp slot) v (C.lo hv)
    (current-frame (falloc fs)) (frame-slots (falloc fs))
    (saved-frames (falloc fs)) (fret fs)
    w<end
    -- the head row is a REGISTER claim: a memory write cannot touch it
    (λ c w lt p → p)
    (C.stack-eq (dataCorr cc)) (ret-eq cc)
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
                          ; ret-eq = (ret-same prog fs (load-from-slot slot) (R.State.memory s)
                                       (elfs-frames (stackMem (floc fs) (current-frame (falloc fs)) slot) (floc fs) (falloc fs) , refl , refl) (ret-eq cc))
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
                          ; ret-eq = (ret-slot-store prog fs s slot _ cc slot<ns)
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

------------------------------------------------------------------------
-- THE CONSTANT AND COUNTER OPS (0.65 G2).
--
-- WHERE riscv64 DIVERGES FROM x86-64 HERE, and it is the ISA this time:
-- RISC-V has NO `sub` with an immediate. It decrements with `addi rd, rs, -1`,
-- a genuinely NEGATIVE immediate — the case `execInstr` used to get WRONG
-- (D103's second instance, fixed in plan 0.70 phase D, where `li`/`addi` moved
-- to `W.fromℤ`). So `scratch-dec` reaches `⊖` through `⊕-neg-suc` rather than
-- directly, and that route only exists because the defect was fixed.
--
-- FLOATS ARE NO LONGER ABSENT HERE. `instr-load-const fits-float` used to emit
-- `unimp` — a TRAP — so there was no correspondence to state and riscv64 sat
-- below x86-64 on this route. That is D079's exact situation one arch over
-- (x86-64's clause was `ud2` until 2026-08-03), and it is fixed the same way:
-- a float constant is a 64-bit PATTERN, so it loads as an ordinary immediate.
------------------------------------------------------------------------

-- load-const (int): Output := SV-Lit fits-int v ↔ `li a0, v`. Shares
-- `block-step-li` with the tag/reg-op loads, so the phase-D range obligation
-- arrives the same way.
block-step-load-const : ∀ {hv : HeapView} prog fs s (v : Carrier) → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-const fits-int v)
  → v < R.W.modulus
  → BlockStep hv prog fs s (instr-load-const fits-int v)
block-step-load-const {hv} prog fs s v cc h ft fits =
  block-step-li prog fs s (instr-load-const fits-int v) a0 v cc h ft refl fits refl (refl , refl , refl) refl
    (C.sim-load-const v fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-out _ _))

-- load-code-addr: Output := SV-Code n ↔ `lla a0, .L_thunk_n`. D103's FIRST
-- instance was here: `lla` used to write 0, so this block-step could not have
-- been stated truthfully before plan 0.70.
-- (`jix`, not `j`: `j` is RISC-V's unconditional-jump CONSTRUCTOR, and a bound
-- variable of that name shadows it into a pattern-match error.)
block-step-load-code-addr : ∀ {hv : HeapView} prog fs s n jix → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-code-addr n)
  → R.find-label (compile-trace prog) (thunk n) ≡ just jix
  → BlockStep hv prog fs s (instr-load-code-addr n)
block-step-load-code-addr {hv} prog fs s n jix cc h ft fl =
  post , exec-eq , record { dataCorr = C.sim-load-code-addr n jix fs s _ dc (code-eq cc n jix fl) (C.sets-role-riscv64 s role-out _ _)
                          ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (lla a0 n)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-load-code-addr n) ft)
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) a0 jix ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-lla {compile-trace prog} {s} {a0} {n} {jix} fetch-rv fl
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-load-code-addr n) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-load-code-addr n) ft))

-- count-inc ↔ `addi s4, s4, 1`. The observable counter; same no-wrap bound as
-- x86-64's `add r14, 1` (plan 0.70 phase C).
block-step-count-inc : ∀ {hv : HeapView} prog fs s k → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op count-inc)
  → readReg (regs (floc fs)) Count ≡ SV-Tag k
  → R.readReg (R.State.regs s) s4 + 1 < R.W.modulus
  → BlockStep hv prog fs s (instr-reg-op count-inc)
block-step-count-inc {hv} prog fs s k cc h ft c-eq no-wrap =
  post , exec-eq , record
    { dataCorr = C.sim-reg-count-inc k fs s _ dc c-eq (C.sets-role-riscv64 s role-count _ _)
    ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (addi s4 s4 (ℤ.+ 1))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-reg-op count-inc) ft)
    wrap-free : R.readReg (R.State.regs s) s4 R.W.⊕ R.W.fromℤ (ℤ.+ 1)
              ≡ R.readReg (R.State.regs s) s4 + 1
    wrap-free = trans (R.W.⊕-normʳ (R.readReg (R.State.regs s) s4) 1)
                      (R.W.⊕≡+ (R.readReg (R.State.regs s) s4) 1 no-wrap)
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) s4 (R.readReg (R.State.regs s) s4 + 1)
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → R.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = R.writeReg (R.State.regs s) s4 w
                                        ; pc = R.State.pc s + 1 }))
                wrap-free
                (step-addi {compile-trace prog} {s} {s4} {s4} {ℤ.+ 1} fetch-rv)
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-reg-op count-inc) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-reg-op count-inc) ft))

-- scratch-dec ↔ `addi s3, s3, -1` — THE NEGATIVE IMMEDIATE. `⊕-neg-suc` is what
-- turns adding a two's complement into `⊖`; from there it is x86-64's route
-- exactly (`⊖≡∸` under the branch guard).
block-step-scratch-dec : ∀ {hv : HeapView} prog fs s k → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-dec)
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → 1 ≤ R.readReg (R.State.regs s) s3          -- the branch guard, recorded
  → R.readReg (R.State.regs s) s3 < R.W.modulus
  → BlockStep hv prog fs s (instr-reg-op scratch-dec)
block-step-scratch-dec {hv} prog fs s k cc h ft sc-eq no-borrow s3<mod =
  post , exec-eq , record
    { dataCorr = C.sim-reg-scratch-dec k fs s _ dc sc-eq (C.sets-role-riscv64 s role-scratch _ _)
    ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s)
             ≡ just (addi s3 s3 (ℤ.-[1+ 0 ]))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-reg-op scratch-dec) ft)
    in-range : 1 < R.W.modulus
    in-range = ≤-<-trans no-borrow s3<mod
    borrow-free : R.readReg (R.State.regs s) s3 R.W.⊕ R.W.fromℤ (ℤ.-[1+ 0 ])
                ≡ R.readReg (R.State.regs s) s3 ∸ 1
    borrow-free = trans (R.W.⊕-neg-suc (R.readReg (R.State.regs s) s3) 0 in-range)
                        (R.W.⊖≡∸ (R.readReg (R.State.regs s) s3) 1 no-borrow s3<mod)
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) s3 (R.readReg (R.State.regs s) s3 ∸ 1)
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = subst (λ w → R.step-not-halted (compile-trace prog) s
                       ≡ just (record s { regs = R.writeReg (R.State.regs s) s3 w
                                        ; pc = R.State.pc s + 1 }))
                borrow-free
                (step-addi {compile-trace prog} {s} {s3} {s3} {ℤ.-[1+ 0 ]} fetch-rv)
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (instr-reg-op scratch-dec) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (instr-reg-op scratch-dec) ft))

-- load-const (float): Output := SV-Lit fits-float v ↔ `li a0, <bits>`.
-- D079 applied to riscv64 (0.65 G2). Shares `block-step-li` with the int case,
-- so the phase-D range obligation arrives identically — and here it is TRUE BY
-- CONSTRUCTION (`float-bits` (as it was) is `primWord64ToNat` of a `Word64`), assumed only
-- because `Data.Word.Properties` states no such bound.
block-step-load-const-float : ∀ {hv : HeapView} prog fs s (v : Dyadic) → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-load-const fits-float v)
  -- Stated in the INTERFACE's language (`lit-value`, the machine's own
  -- materialisation) rather than the emitter's, so `BlockSteps` needs no
  -- adapter. `fmt-eq` converts, once, below.
  → AbstractExec.lit-value {FS} fits-float v < R.W.modulus
  → BlockStep hv prog fs s (instr-load-const fits-float v)
block-step-load-const-float {hv} prog fs s v cc h ft fits =
  block-step-li prog fs s (instr-load-const fits-float v) a0 (encode binary64 v) cc h ft refl fits64 refl (refl , refl , refl) refl
    (C.sim-load-const-float v fs s _ (dataCorr cc) sr)
  where
    -- The premise speaks of `float-format FS`; `block-step-li` needs the
    -- emitter's concrete format. One `subst` each way, and `fmt-eq` is spent.
    -- (`subst`, not `rewrite`: `rewrite` would generalise `float-format FS`
    -- over the whole type and the abstraction fails.)
    fits64 : (encode binary64) v < R.W.modulus
    fits64 = subst (λ F → encode F v < R.W.modulus) fmt-eq fits
    sr : C.SetsRole s _ role-out (C.lit-word (AbstractExec.lit-value {FS} fits-float v))
    sr = subst (λ F → C.SetsRole s _ role-out (C.lit-word (encode F v)))
               (sym fmt-eq)
               (C.sets-role-riscv64 s role-out _ _)

------------------------------------------------------------------------
-- THE HEAP-INDIRECT ACCESSES (0.65 G2).
--
-- riscv64's `ld a0, 0(t0)` against x86-64's `mov rax, [rdi]`: the ONE textual
-- difference is that riscv64's addressing always carries a displacement, so the
-- base case reads `readReg t0 + 0` where x86-64's `base` mode reads `readReg
-- rdi` outright. `+-identityʳ` is the whole adapter.
------------------------------------------------------------------------

-- A HEAP STORE MISSES EVERY PENDING RETURN — x86-64's `ret-heap-store` at
-- riscv64's state type. Every return cell is at or above `lo`; the heap is
-- strictly below it.
ret-heap-store : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : R.State)
                   (a : ℕ) (v : R.Word)
               → CompiledCorr hv prog fs s
               → a < C.lo hv
               → C.RetAddrs (blk-off prog) (R.writeMem (R.State.memory s) a v)
                            (riscv64-link-claim s) (flink fs)
                            (C.frames-of (falloc fs)) (fret fs)
ret-heap-store {hv} prog fs s a v cc a<lo =
  C.ret-agree-above (blk-off prog) (R.State.memory s) (R.writeMem (R.State.memory s) a v)
    (riscv64-link-claim s) (riscv64-link-claim s) (flink fs)
    (stackMem (floc fs)) (C.lo hv) (C.frames-of (falloc fs)) (fret fs)
    (λ c le → C.read-write-miss (R.State.memory s) a v c (λ eq → <⇒≢ (<-transˡ a<lo le) (sym eq)))
    (λ c w le p → p)
    (C.stack-eq (dataCorr cc)) (ret-eq cc)

-- load-indirect: Output := *Input1 ↔ `ld a0, 0(t0)`.
block-step-load-indirect : ∀ {hv : HeapView} prog fs s hl w → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl
  → heapMem (floc fs) hl ≡ just w
  → BlockStep hv prog fs s load-indirect
block-step-load-indirect {hv} prog fs s hl w cc h ft i-eq live-hl h-eq =
  post , exec-eq , record { dataCorr = C.sim-load-indirect hl w fs s _ dc i-eq h-eq (C.sets-role-riscv64 s role-out _ _)
                          ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld a0 t0 0)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) load-indirect ft)
    t0-val : R.readReg (R.State.regs s) t0 ≡ haddr hv hl
    t0-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-eq : R.effectiveAddr (R.State.regs s) t0 0 ≡ haddr hv hl
    addr-eq = trans (+-identityʳ (R.readReg (R.State.regs s) t0)) t0-val
    rd : R.readMem (R.State.memory s) (R.effectiveAddr (R.State.regs s) t0 0)
       ≡ just (C.enc-sv hv w)
    rd = trans (cong (R.readMem (R.State.memory s)) addr-eq)
               (trans (C.heap-eq dc hl live-hl) (cong (C.enc-maybe hv) h-eq))
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) a0 (C.enc-sv hv w) ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-ld {compile-trace prog} {s} {a0} {t0} {0} {C.enc-sv hv w} fetch-rv rd
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr load-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) load-indirect ft))

-- load-indirect-suc: Output := *(sucLoc Input1) ↔ `ld a0, 8(t0)`.
block-step-load-indirect-suc : ∀ {hv : HeapView} prog fs s hl w → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)
  → heapMem (floc fs) (sucHL hl) ≡ just w
  → BlockStep hv prog fs s load-indirect-suc
block-step-load-indirect-suc {hv} prog fs s hl w cc h ft i-eq live-shl h-eq =
  post , exec-eq , record { dataCorr = C.sim-load-indirect-suc hl w fs s _ dc i-eq h-eq (C.sets-role-riscv64 s role-out _ _)
                          ; pc-off = pco' ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld a0 t0 slot-size)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) load-indirect-suc ft)
    t0-val : R.readReg (R.State.regs s) t0 ≡ haddr hv hl
    t0-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-eq : R.effectiveAddr (R.State.regs s) t0 slot-size ≡ haddr hv (sucHL hl)
    addr-eq = trans (cong (_+ slot-size) t0-val) (sym (C.haddr-suc hv hl))
    rd : R.readMem (R.State.memory s) (R.effectiveAddr (R.State.regs s) t0 slot-size)
       ≡ just (C.enc-sv hv w)
    rd = trans (cong (R.readMem (R.State.memory s)) addr-eq)
               (trans (C.heap-eq dc (sucHL hl) live-shl) (cong (C.enc-maybe hv) h-eq))
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) a0 (C.enc-sv hv w) ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-ld {compile-trace prog} {s} {a0} {t0} {slot-size} {C.enc-sv hv w} fetch-rv rd
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr load-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) load-indirect-suc ft))

-- store-indirect: *Input1 := Output ↔ `sd a0, 0(t0)`.
block-step-store-indirect : ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl
  → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
  → BlockStep hv prog fs s store-indirect
block-step-store-indirect {hv} prog fs s hl cc h ft i-eq live-hl guard =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = subst (λ m → C.RetAddrs (blk-off prog) m
                                                    (riscv64-link-claim s) (flink fs)
                                                    (C.frames-of (falloc fs)) (fret fs))
                                           (cong₂ (R.writeMem (R.State.memory s)) (sym addr-eq) refl)
                                           (ret-heap-store prog fs s (haddr hv hl) _ cc
                                              (≤-trans (C.dom-below hv live-hl) (C.front-lo hv)))
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (sd a0 t0 0)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) store-indirect ft)
    t0-val : R.readReg (R.State.regs s) t0 ≡ haddr hv hl
    t0-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-eq : R.effectiveAddr (R.State.regs s) t0 0 ≡ haddr hv hl
    addr-eq = trans (+-identityʳ (R.readReg (R.State.regs s) t0)) t0-val
    post : R.State
    post = record s { memory = R.writeMem (R.State.memory s)
                                 (R.effectiveAddr (R.State.regs s) t0 0)
                                 (R.readReg (R.State.regs s) a0)
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-sd {compile-trace prog} {s} {a0} {t0} {0} fetch-rv
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    post-eq : post ≡ R.mkstate (R.State.regs s)
                        (R.writeMem (R.State.memory s) (haddr hv hl)
                           (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                        (R.State.pc s + 1) (R.State.halted s)
    post-eq = cong (λ m → R.mkstate (R.State.regs s) m (R.State.pc s + 1) (R.State.halted s))
                   (cong₂ (R.writeMem (R.State.memory s)) addr-eq (C.out-eq dc))
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr store-indirect prog fs)) (sym post-eq)
                     (C.sim-store-indirect hl fs s _ dc i-eq live-hl guard (C.sets-mem-riscv64 s _ _ _))
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr store-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) store-indirect ft))

-- store-indirect-suc: *(sucLoc Input1) := Output ↔ `sd a0, 8(t0)`.
block-step-store-indirect-suc : ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)
  → writeLoc (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) (sucHL hl) (readReg (regs (floc fs)) Output)
  → BlockStep hv prog fs s store-indirect-suc
block-step-store-indirect-suc {hv} prog fs s hl cc h ft i-eq live-shl guard =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = subst (λ m → C.RetAddrs (blk-off prog) m
                                                    (riscv64-link-claim s) (flink fs)
                                                    (C.frames-of (falloc fs)) (fret fs))
                                           (cong₂ (R.writeMem (R.State.memory s)) (sym addr-eq) refl)
                                           (ret-heap-store prog fs s (haddr hv (sucHL hl)) _ cc
                                              (≤-trans (C.dom-below hv live-shl) (C.front-lo hv)))
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (sd a0 t0 slot-size)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) store-indirect-suc ft)
    t0-val : R.readReg (R.State.regs s) t0 ≡ haddr hv hl
    t0-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-eq : R.effectiveAddr (R.State.regs s) t0 slot-size ≡ haddr hv (sucHL hl)
    addr-eq = trans (cong (_+ slot-size) t0-val) (sym (C.haddr-suc hv hl))
    post : R.State
    post = record s { memory = R.writeMem (R.State.memory s)
                                 (R.effectiveAddr (R.State.regs s) t0 slot-size)
                                 (R.readReg (R.State.regs s) a0)
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-sd {compile-trace prog} {s} {a0} {t0} {slot-size} fetch-rv
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    post-eq : post ≡ R.mkstate (R.State.regs s)
                        (R.writeMem (R.State.memory s) (haddr hv (sucHL hl))
                           (C.enc-sv hv (readReg (regs (floc fs)) Output)))
                        (R.State.pc s + 1) (R.State.halted s)
    post-eq = cong (λ m → R.mkstate (R.State.regs s) m (R.State.pc s + 1) (R.State.halted s))
                   (cong₂ (R.writeMem (R.State.memory s)) addr-eq (C.out-eq dc))
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect-suc prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr store-indirect-suc prog fs)) (sym post-eq)
                     (C.sim-store-indirect-suc hl fs s _ dc i-eq live-shl guard (C.sets-mem-riscv64 s _ _ _))
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr store-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) store-indirect-suc ft))

------------------------------------------------------------------------
-- THE FRAME MOVERS (0.65 G2) — the three that touch no stack pointer.
------------------------------------------------------------------------

-- Companion to `elfs-frames`, for the OTHER `Maybe`-dispatched load.
eris-frames : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
            → C.frames-of (proj₂ (AbstractExec.exec-restore-input-with-value {FS} mv ls alloc))
              ≡ C.frames-of alloc
eris-frames (just v) ls alloc = refl
eris-frames nothing  ls alloc = refl

-- restore-input: Input1 := stack[slot] ↔ `ld t0, slot*8(sp)`.
block-step-restore-input : ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (restore-input slot)
  → slot < frame-slots (falloc fs)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep hv prog fs s (restore-input slot)
block-step-restore-input {hv} prog fs s slot w cc h ft slot<ns st-eq =
  post , exec-eq , record { dataCorr = C.sim-restore-input slot w fs s _ dc st-eq (C.sets-role-riscv64 s role-in1 _ _) ; pc-off = pco'
                          ; ret-eq = (ret-same prog fs (restore-input slot) (R.State.memory s)
                                       (eris-frames (stackMem (floc fs) (current-frame (falloc fs)) slot) (floc fs) (falloc fs) , refl , refl) (ret-eq cc))
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s)
             ≡ just (ld t0 sp (slot-to-disp slot))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (restore-input slot) ft)
    rd : R.readMem (R.State.memory s)
           (R.effectiveAddr (R.State.regs s) sp (slot-to-disp slot))
       ≡ just (C.enc-sv hv w)
    rd = C.stack-eq-cur dc slot slot<ns _ st-eq
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) t0 (C.enc-sv hv w) ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-ld {compile-trace prog} {s} {t0} {sp} {slot-to-disp slot} {C.enc-sv hv w} fetch-rv rd
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (restore-input slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (restore-input slot) ft))

-- save-closure-reg: Closure := Input1 ↔ `mv s1, t0`.
block-step-save-closure-reg : ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just instr-save-closure-reg
  → BlockStep hv prog fs s instr-save-closure-reg
block-step-save-closure-reg {hv} prog fs s cc h ft =
  block-step-mv prog fs s instr-save-closure-reg s1 t0 cc h ft refl refl (refl , refl , refl) refl
    (C.sim-save-closure-reg fs s _ (dataCorr cc) (C.sets-role-riscv64 s role-clos _ _))

-- reclaim-to: EMITS NOTHING on either arch — it changes `next-slot`, not
-- `frame-slots`, so the machine does not move and every field is carried
-- across unchanged.
block-step-reclaim-to : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-reclaim-to n)
  → BlockStep hv prog fs s (instr-reclaim-to n)
block-step-reclaim-to {hv} prog fs s n cc h ft = s , refl , record
  { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                      ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc
                      ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc
                      ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                      ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
  ; pc-off = trans (pc-off cc)
             (sym (trans (blk-off-suc prog (fpc fs) (instr-reclaim-to n) ft) (+-identityʳ _)))
  ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where dc = dataCorr cc

------------------------------------------------------------------------
-- THE WORKLIST OPS (0.65 G2). `init`/`check` EMIT NOTHING on both arches (the
-- simplified model: the proofs use Star-based reasoning, not loop mechanics);
-- `push`/`pop` are `store-at-slot`/`load-from-slot` under another name, and
-- reuse those sims exactly as x86-64 does.
------------------------------------------------------------------------

block-step-worklist-init : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-init n)
  → BlockStep hv prog fs s (worklist-init n)
block-step-worklist-init {hv} prog fs s n cc h ft = s , refl , record
  { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                      ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc
                      ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc
                      ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                      ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
  ; pc-off = trans (pc-off cc)
             (sym (trans (blk-off-suc prog (fpc fs) (worklist-init n) ft) (+-identityʳ _)))
  ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where dc = dataCorr cc

block-step-worklist-check : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-check n)
  → BlockStep hv prog fs s (worklist-check n)
block-step-worklist-check {hv} prog fs s n cc h ft = s , refl , record
  { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                      ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc
                      ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc
                      ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                      ; heap-eq = C.heap-eq dc
                      ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
  ; pc-off = trans (pc-off cc)
             (sym (trans (blk-off-suc prog (fpc fs) (worklist-check n) ft) (+-identityʳ _)))
  ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where dc = dataCorr cc

-- worklist-push ↔ `sd a0, slot*8(sp)` — `store-at-slot` under another name.
block-step-worklist-push : ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-push slot)
  → slot < frame-slots (falloc fs)
  → (∀ hl' → HDom hv hl' → (R.readReg (R.State.regs s) sp + slot-to-disp slot ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s (worklist-push slot)
block-step-worklist-push {hv} prog fs s slot cc h ft slot<ns disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = (ret-slot-store prog fs s slot _ cc slot<ns)
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s)
             ≡ just (sd a0 sp (slot-to-disp slot))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (worklist-push slot) ft)
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
    dataPost : C.FlatCorr hv (flat-exec-instr (worklist-push slot) prog fs) post
    dataPost = subst (C.FlatCorr hv (flat-exec-instr (worklist-push slot) prog fs)) (sym post-eq)
                     (C.sim-store-at-slot slot fs s _ dc slot<ns disj (C.sets-mem-riscv64 s _ _ _))
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (worklist-push slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (worklist-push slot) ft))

-- worklist-pop ↔ `ld a0, slot*8(sp)` — `load-from-slot` under another name.
block-step-worklist-pop : ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (worklist-pop slot)
  → slot < frame-slots (falloc fs)
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → BlockStep hv prog fs s (worklist-pop slot)
block-step-worklist-pop {hv} prog fs s slot w cc h ft slot<ns st-eq =
  post , exec-eq , record { dataCorr = C.sim-load-from-slot slot w fs s _ dc st-eq (C.sets-role-riscv64 s role-out _ _) ; pc-off = pco'
                          ; ret-eq = (ret-same prog fs (load-from-slot slot) (R.State.memory s)
                                       (elfs-frames (stackMem (floc fs) (current-frame (falloc fs)) slot) (floc fs) (falloc fs) , refl , refl) (ret-eq cc))
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s)
             ≡ just (ld a0 sp (slot-to-disp slot))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (worklist-pop slot) ft)
    rd : R.readMem (R.State.memory s)
           (R.effectiveAddr (R.State.regs s) sp (slot-to-disp slot))
       ≡ just (C.enc-sv hv w)
    rd = C.stack-eq-cur dc slot slot<ns _ st-eq
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) a0 (C.enc-sv hv w) ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-ld {compile-trace prog} {s} {a0} {sp} {slot-to-disp slot} {C.enc-sv hv w} fetch-rv rd
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr (worklist-pop slot) prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) (worklist-pop slot) ft))

------------------------------------------------------------------------
-- CONTROL FLOW (0.65 G2 / G1d step 3) — THE BRANCH-BLOCK LAW.
--
-- This is riscv64's real structural difference from x86-64, and it shows up as
-- a BLOCK LENGTH: `c-branch-scratch-zero` is ONE instruction here
-- (`beq s3, zero, L`) against x86-64's `cmp rbx, 0 ; je L` pair, so the
-- not-taken outcome is `exec 1` rather than `exec 2` and no flags register
-- exists in between. `c-branch-tag-zero` is two on BOTH arches, but for
-- different reasons: x86-64 compares memory directly (`cmp [rdi], 0`), while
-- RISC-V must load first (`ld t1, 0(t0)`) because its compare takes registers.
--
-- That the generic `BlockStep` type absorbs a per-arch block length without
-- adaptation is exactly what plan 0.65's structural-difference #2 predicted.
------------------------------------------------------------------------

-- c-jmp ↔ `j L`.
block-step-c-jmp : ∀ {hv : HeapView} prog fs s n j₀ → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp n))
  -- (the CONCRETE scan is no longer a premise: `find-label-corr` derives it
  -- from the abstract one, which is what the engine passes. Plan 0.65 G2.)
  → find-label prog n ≡ just j₀
  → BlockStep hv prog fs s (instr-ctrl (c-jmp n))
block-step-c-jmp {hv} prog fs s n j₀ cc h ft fl-eq = block-step
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (j (once n))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-ctrl (c-jmp n)) ft)
    post : R.State
    post = record s { pc = blk-off prog j₀ }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    -- the CONCRETE scan agrees with the abstract one: a THEOREM
    -- (`FlatComposition.find-label-corr`), not a premise.
    fl-rv : R.find-label (compile-trace prog) (once n) ≡ just (blk-off prog j₀)
    fl-rv = find-label-corr prog n 0 j₀ fl-eq
    snh = step-j-found {compile-trace prog} {s} {once n} {blk-off prog j₀} fetch-rv fl-rv
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    block-step : BlockStep hv prog fs s (instr-ctrl (c-jmp n))
    block-step rewrite fl-eq = post , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc
                          ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc
                          ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                          ; heap-eq = C.heap-eq dc
                          ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = refl ; ret-eq = ret-eq cc ; code-eq = code-eq cc }

-- c-branch-scratch-zero ↔ `beq s3, zero, L` — ONE instruction, both outcomes.
-- x86-64 needs `cmp ; je` for the same law; this is the block-length difference
-- plan 0.65 called structural, and the generic `BlockStep` absorbs it.
block-step-c-branch-scratch-zero : ∀ {hv : HeapView} prog fs s n k j₀ → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero n))
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  -- (the CONCRETE scan is no longer a premise: `find-label-corr` derives it
  -- from the abstract one, which is what the engine passes. Plan 0.65 G2.)
  → find-label prog n ≡ just j₀
  → BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
block-step-c-branch-scratch-zero {hv} prog fs s n zero j₀ cc h ft sc-eq fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (beq s3 zero (once n))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    s3-val : R.readReg (R.State.regs s) s3 ≡ 0
    s3-val = trans (C.scratch-eq dc) (cong (C.enc-sv hv) sc-eq)
    taken : (R.readReg (R.State.regs s) s3 ≡ᵇ R.readReg (R.State.regs s) zero) ≡ true
    taken = cong (_≡ᵇ 0) s3-val
    post : R.State
    post = record s { pc = blk-off prog j₀ }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    -- the CONCRETE scan agrees with the abstract one: a THEOREM
    -- (`FlatComposition.find-label-corr`), not a premise.
    fl-rv : R.find-label (compile-trace prog) (once n) ≡ just (blk-off prog j₀)
    fl-rv = find-label-corr prog n 0 j₀ fl-eq
    snh = step-beq-taken {compile-trace prog} {s} {s3} {zero} {once n} {blk-off prog j₀} fetch-rv taken fl-rv
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq | fl-eq = post , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc
                          ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc
                          ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                          ; heap-eq = C.heap-eq dc
                          ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = refl ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
block-step-c-branch-scratch-zero {hv} prog fs s n (suc m) j₀ cc h ft sc-eq fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (beq s3 zero (once n))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    s3-val : R.readReg (R.State.regs s) s3 ≡ suc m
    s3-val = trans (C.scratch-eq dc) (cong (C.enc-sv hv) sc-eq)
    not-taken : (R.readReg (R.State.regs s) s3 ≡ᵇ R.readReg (R.State.regs s) zero) ≡ false
    not-taken = cong (_≡ᵇ 0) s3-val
    post : R.State
    post = record s { pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-beq-not {compile-trace prog} {s} {s3} {zero} {once n} fetch-rv not-taken
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq = post , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc
                          ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc
                          ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                          ; heap-eq = C.heap-eq dc
                          ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = trans (cong (_+ 1) po)
                       (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft))
      ; ret-eq = ret-eq cc ; code-eq = code-eq cc }

-- c-branch-tag-zero ↔ `ld t1, 0(t0) ; beq t1, zero, L` — TWO instructions, as
-- on x86-64, but for a different reason: x86-64 compares memory in place
-- (`cmp [rdi], 0`); RISC-V's compare takes registers, so the tag is loaded
-- first.
block-step-c-branch-tag-zero : ∀ {hv : HeapView} prog fs s n loc k j₀ → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero n))
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
  → readLoc (floc fs) loc ≡ just (SV-Tag k)
  → R.readMem (R.State.memory s) (R.effectiveAddr (R.State.regs s) t0 0) ≡ just k
  -- (the CONCRETE scan is no longer a premise: `find-label-corr` derives it
  -- from the abstract one, which is what the engine passes. Plan 0.65 G2.)
  → find-label prog n ≡ just j₀
  → BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
block-step-c-branch-tag-zero {hv} prog fs s n loc zero j₀ cc h ft i-eq r-eq rd fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-ld : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld t1 t0 0)
    fetch-ld = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post-ld : R.State
    post-ld = record s { regs = R.writeReg (R.State.regs s) t1 0 ; pc = R.State.pc s + 1 }
    step-ld' : R.step-not-halted (compile-trace prog) s ≡ just post-ld
    step-ld' = step-ld {compile-trace prog} {s} {t1} {t0} {0} {0} fetch-ld rd
    fetch-beq : R.fetch (compile-trace prog) (R.State.pc post-ld) ≡ just (beq t1 zero (once n))
    fetch-beq = trans (cong (λ p → R.fetch (compile-trace prog) (p + 1)) po)
                      (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post : R.State
    post = record post-ld { pc = blk-off prog j₀ }
    step-b : R.step-not-halted (compile-trace prog) post-ld ≡ just post
    -- the CONCRETE scan agrees with the abstract one: a THEOREM
    -- (`FlatComposition.find-label-corr`), not a premise.
    fl-rv : R.find-label (compile-trace prog) (once n) ≡ just (blk-off prog j₀)
    fl-rv = find-label-corr prog n 0 j₀ fl-eq
    step-b = step-beq-taken {compile-trace prog} {post-ld} {t1} {zero} {once n} {blk-off prog j₀} fetch-beq refl fl-rv
    exec-eq : R.exec 2 (compile-trace prog) s ≡ just post
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-ld} halt-s step-ld' halt-s)
                    (exec-1 {compile-trace prog} {0} {post-ld} {post} halt-s step-b halt-s)
    cond-eq : tag-zf (flat-read-tag (floc fs)) ≡ sv-is-zero (SV-Tag {FS} zero)
    cond-eq = cong tag-zf (trans (cong (flat-read-at (floc fs)) (cong sv-as-loc i-eq)) r-eq)
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
    result rewrite cond-eq | fl-eq = post , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc
                          ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc
                          ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                          ; heap-eq = C.heap-eq dc
                          ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = refl ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
block-step-c-branch-tag-zero {hv} prog fs s n loc (suc m) j₀ cc h ft i-eq r-eq rd fl-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-ld : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld t1 t0 0)
    fetch-ld = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post-ld : R.State
    post-ld = record s { regs = R.writeReg (R.State.regs s) t1 (suc m) ; pc = R.State.pc s + 1 }
    step-ld' : R.step-not-halted (compile-trace prog) s ≡ just post-ld
    step-ld' = step-ld {compile-trace prog} {s} {t1} {t0} {0} {suc m} fetch-ld rd
    fetch-beq : R.fetch (compile-trace prog) (R.State.pc post-ld) ≡ just (beq t1 zero (once n))
    fetch-beq = trans (cong (λ p → R.fetch (compile-trace prog) (p + 1)) po)
                      (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post : R.State
    post = record post-ld { pc = R.State.pc post-ld + 1 }
    step-b : R.step-not-halted (compile-trace prog) post-ld ≡ just post
    step-b = step-beq-not {compile-trace prog} {post-ld} {t1} {zero} {once n} fetch-beq refl
    exec-eq : R.exec 2 (compile-trace prog) s ≡ just post
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-ld} halt-s step-ld' halt-s)
                    (exec-1 {compile-trace prog} {0} {post-ld} {post} halt-s step-b halt-s)
    cond-eq : tag-zf (flat-read-tag (floc fs)) ≡ sv-is-zero (SV-Tag {FS} (suc m))
    cond-eq = cong tag-zf (trans (cong (flat-read-at (floc fs)) (cong sv-as-loc i-eq)) r-eq)
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
    result rewrite cond-eq = post , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc
                          ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc
                          ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                          ; heap-eq = C.heap-eq dc
                          ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = trans (+-assoc (R.State.pc s) 1 1)
                       (trans (cong (_+ 2) po)
                              (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)))
      ; ret-eq = ret-eq cc ; code-eq = code-eq cc }

------------------------------------------------------------------------
-- THE STACK-POINTER VARIANTS (0.65 G2). Same INSTRUCTIONS as the heap-indirect
-- four — the abstract `Input1` points at a stack slot rather than a heap cell,
-- so the address arrives through `slot-addr-linear` and `sp-eq` instead of
-- through `haddr`. riscv64's extra `+ 0` on the base case is again the only
-- textual difference.
------------------------------------------------------------------------

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
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld a0 t0 0)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) load-indirect ft)
    t0-val : R.readReg (R.State.regs s) t0
           ≡ R.readReg (R.State.regs s) sp + slot-to-disp k
    t0-val = trans (C.in1-eq dc)
             (trans (cong (C.enc-sv hv) i-eq)
             (trans (cong (λ fr → slot-addr FS fr k) f-eq)
             (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                    (cong₂ (λ b w' → b + k * w') (sym (C.sp-eq dc)) word-eq))))
    addr-eq : R.effectiveAddr (R.State.regs s) t0 0
            ≡ R.readReg (R.State.regs s) sp + slot-to-disp k
    addr-eq = trans (+-identityʳ (R.readReg (R.State.regs s) t0)) t0-val
    rd : R.readMem (R.State.memory s) (R.effectiveAddr (R.State.regs s) t0 0)
       ≡ just (C.enc-sv hv w)
    rd = trans (cong (R.readMem (R.State.memory s)) addr-eq)
               (C.stack-eq-cur dc k k<ss _ st-eq)
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) a0 (C.enc-sv hv w) ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-ld {compile-trace prog} {s} {a0} {t0} {0} {C.enc-sv hv w} fetch-rv rd
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr load-indirect prog fs) post
    dataPost = C.sim-load-indirect-stack f k w fs s _ dc i-eq
                 (trans (cong (λ fr → stackMem (floc fs) fr k) f-eq) st-eq)
                 (C.sets-role-riscv64 s role-out _ _)
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr load-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) load-indirect ft))

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
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld a0 t0 slot-size)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) load-indirect-suc ft)
    addr-eq : R.effectiveAddr (R.State.regs s) t0 slot-size
            ≡ R.readReg (R.State.regs s) sp + slot-to-disp (suc k)
    addr-eq = trans (cong (_+ slot-size)
                      (trans (C.in1-eq dc)
                      (trans (cong (C.enc-sv hv) i-eq)
                      (trans (cong (λ fr → slot-addr FS fr k) f-eq)
                      (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                             (cong₂ (λ b w' → b + k * w') (sym (C.sp-eq dc)) word-eq))))))
                    (trans (+-assoc (R.readReg (R.State.regs s) sp) (k * slot-size) slot-size)
                           (cong (R.readReg (R.State.regs s) sp +_)
                                 (+-comm (k * slot-size) slot-size)))
    rd : R.readMem (R.State.memory s) (R.effectiveAddr (R.State.regs s) t0 slot-size)
       ≡ just (C.enc-sv hv w)
    rd = trans (cong (R.readMem (R.State.memory s)) addr-eq)
               (C.stack-eq-cur dc (suc k) sk<ss _ st-eq)
    post : R.State
    post = record s { regs = R.writeReg (R.State.regs s) a0 (C.enc-sv hv w) ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-ld {compile-trace prog} {s} {a0} {t0} {slot-size} {C.enc-sv hv w} fetch-rv rd
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr load-indirect-suc prog fs) post
    dataPost = C.sim-load-indirect-suc-stack f k w fs s _ dc i-eq
                 (trans (cong (λ fr → stackMem (floc fs) fr (suc k)) f-eq) st-eq)
                 (C.sets-role-riscv64 s role-out _ _)
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr load-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) load-indirect-suc ft))

block-step-store-indirect-stack : ∀ {hv : HeapView} prog fs s f k → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → f ≡ current-frame (falloc fs)
  → k < frame-slots (falloc fs)
  → (∀ hl' → HDom hv hl' → (R.readReg (R.State.regs s) sp + slot-to-disp k ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s store-indirect
block-step-store-indirect-stack {hv} prog fs s f k cc h ft i-eq f-eq k<ns disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = (ret-slot-store prog fs s k _ cc k<ns)
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (sd a0 t0 0)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) store-indirect ft)
    t0-val : R.readReg (R.State.regs s) t0
           ≡ R.readReg (R.State.regs s) sp + slot-to-disp k
    t0-val = trans (C.in1-eq dc)
             (trans (cong (C.enc-sv hv) i-eq)
             (trans (cong (λ fr → slot-addr FS fr k) f-eq)
             (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                    (cong₂ (λ b w' → b + k * w') (sym (C.sp-eq dc)) word-eq))))
    addr-eq : R.effectiveAddr (R.State.regs s) t0 0
            ≡ R.readReg (R.State.regs s) sp + slot-to-disp k
    addr-eq = trans (+-identityʳ (R.readReg (R.State.regs s) t0)) t0-val
    i-eq' : readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
    i-eq' = trans i-eq (cong (λ fr → SV-Ptr (AtStack fr k)) f-eq)
    post : R.State
    post = record s { memory = R.writeMem (R.State.memory s)
                                 (R.readReg (R.State.regs s) sp + slot-to-disp k)
                                 (C.enc-sv hv (readReg (regs (floc fs)) Output))
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = trans (step-sd {compile-trace prog} {s} {a0} {t0} {0} fetch-rv)
                (cong just (cong₂ (λ a v → record s { memory = R.writeMem (R.State.memory s) a v
                                                    ; pc = R.State.pc s + 1 })
                                  addr-eq (C.out-eq dc)))
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect prog fs) post
    dataPost = C.sim-store-indirect-stack k fs s _ dc i-eq' k<ns disj (C.sets-mem-riscv64 s _ _ _)
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr store-indirect prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) store-indirect ft))

block-step-store-indirect-suc-stack : ∀ {hv : HeapView} prog fs s f k → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just store-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → f ≡ current-frame (falloc fs)
  → suc k < frame-slots (falloc fs)
  → (∀ hl' → HDom hv hl' → (R.readReg (R.State.regs s) sp + slot-to-disp (suc k) ≡ haddr hv hl') → ⊥)
  → BlockStep hv prog fs s store-indirect-suc
block-step-store-indirect-suc-stack {hv} prog fs s f k cc h ft i-eq f-eq sk<ns disj =
  post , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                          ; ret-eq = (ret-slot-store prog fs s (suc k) _ cc sk<ns)
                          ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (sd a0 t0 slot-size)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) store-indirect-suc ft)
    addr-eq : R.effectiveAddr (R.State.regs s) t0 slot-size
            ≡ R.readReg (R.State.regs s) sp + slot-to-disp (suc k)
    addr-eq = trans (cong (_+ slot-size)
                      (trans (C.in1-eq dc)
                      (trans (cong (C.enc-sv hv) i-eq)
                      (trans (cong (λ fr → slot-addr FS fr k) f-eq)
                      (trans (slot-addr-linear FS (current-frame (falloc fs)) k)
                             (cong₂ (λ b w' → b + k * w') (sym (C.sp-eq dc)) word-eq))))))
                    (trans (+-assoc (R.readReg (R.State.regs s) sp) (k * slot-size) slot-size)
                           (cong (R.readReg (R.State.regs s) sp +_)
                                 (+-comm (k * slot-size) slot-size)))
    i-eq' : readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
    i-eq' = trans i-eq (cong (λ fr → SV-Ptr (AtStack fr k)) f-eq)
    post : R.State
    post = record s { memory = R.writeMem (R.State.memory s)
                                 (R.readReg (R.State.regs s) sp + slot-to-disp (suc k))
                                 (C.enc-sv hv (readReg (regs (floc fs)) Output))
                    ; pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = trans (step-sd {compile-trace prog} {s} {a0} {t0} {slot-size} fetch-rv)
                (cong just (cong₂ (λ a v → record s { memory = R.writeMem (R.State.memory s) a v
                                                    ; pc = R.State.pc s + 1 })
                                  addr-eq (C.out-eq dc)))
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    dataPost : C.FlatCorr hv (flat-exec-instr store-indirect-suc prog fs) post
    dataPost = C.sim-store-indirect-suc-stack k fs s _ dc i-eq' sk<ns disj (C.sets-mem-riscv64 s _ _ _)
    pco' : R.State.pc post ≡ blk-off prog (fpc (flat-exec-instr store-indirect-suc prog fs))
    pco' = trans (cong (_+ 1) po) (sym (blk-off-suc prog (fpc fs) store-indirect-suc ft))

------------------------------------------------------------------------
-- THE STACK-POINTER MOVES AND THE HEAP BUMP (0.65 G2).
--
-- RISC-V has no `sub`-with-immediate and no `add`-with-immediate distinct from
-- `addi`, so BOTH directions are `addi sp, sp, ±slots n` — the negative one
-- reaching `⊖` through `⊕-neg-suc`, exactly as `scratch-dec` does. x86-64 needs
-- two different opcodes for the same pair.
------------------------------------------------------------------------

-- alloc-stack ↔ `addi sp, sp, -(slots n)`. The negative immediate reaches the
-- ℕ view through `⊕-neg`, which handles `slots n ≡ 0` and `suc _` uniformly —
-- worth having in `Once.Word` rather than at each site, since every riscv64
-- decrement goes this way.
block-step-alloc-stack-step : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s
  → fetch prog (fpc fs) ≡ just (instr-alloc-stack n)
  → slots n ≤ R.readReg (R.State.regs s) sp
  → R.readReg (R.State.regs s) sp < R.W.modulus
  → R.step-not-halted (compile-trace prog) s
    ≡ just (record s { regs = R.writeReg (R.State.regs s) sp
                                (R.readReg (R.State.regs s) sp ∸ slots n)
                     ; pc = R.State.pc s + 1 })
block-step-alloc-stack-step {hv} prog fs s n cc ft fits sp<mod =
  subst (λ w → R.step-not-halted (compile-trace prog) s
               ≡ just (record s { regs = R.writeReg (R.State.regs s) sp w
                                ; pc = R.State.pc s + 1 }))
        (R.W.⊕-neg (R.readReg (R.State.regs s) sp) (slots n) fits sp<mod)
        (step-addi {compile-trace prog} {s} {sp} {sp} {ℤ.-_ (ℤ.+ (slots n))} fetch-rv)
  where
    po = pc-off cc
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s)
             ≡ just (addi sp sp (ℤ.-_ (ℤ.+ (slots n))))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-alloc-stack n) ft)

-- dealloc-stack ↔ `addi sp, sp, +(slots n)` — the other direction, one opcode
-- on RISC-V where x86-64 needs `add` against `sub`.
block-step-dealloc-stack-step : ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s
  → fetch prog (fpc fs) ≡ just (instr-dealloc-stack n)
  → R.readReg (R.State.regs s) sp + slots n < R.W.modulus
  → R.step-not-halted (compile-trace prog) s
    ≡ just (record s { regs = R.writeReg (R.State.regs s) sp
                                (R.readReg (R.State.regs s) sp + slots n)
                     ; pc = R.State.pc s + 1 })
block-step-dealloc-stack-step {hv} prog fs s n cc ft no-wrap =
  subst (λ w → R.step-not-halted (compile-trace prog) s
               ≡ just (record s { regs = R.writeReg (R.State.regs s) sp w
                                ; pc = R.State.pc s + 1 }))
        (trans (R.W.⊕-normʳ (R.readReg (R.State.regs s) sp) (slots n))
               (R.W.⊕≡+ (R.readReg (R.State.regs s) sp) (slots n) no-wrap))
        (step-addi {compile-trace prog} {s} {sp} {sp} {ℤ.+ (slots n)} fetch-rv)
  where
    po = pc-off cc
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s)
             ≡ just (addi sp sp (ℤ.+ (slots n)))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-dealloc-stack n) ft)

------------------------------------------------------------------------
-- THE TWO NOT-TAKEN FALL-THROUGHS (plan 0.65 G2).
--
-- A branch whose label is MISSING but which is NOT TAKEN never consults the
-- label, so it is an ordinary step and the engine dispatches it to a
-- LABEL-FREE block-step. That is why `BlockSteps` has these two fields at all.
--
-- The proofs are the not-taken clauses above with the label parameters
-- dropped — `beq` falls through on a non-zero tag whether or not the target
-- resolves, which is exactly the content.
------------------------------------------------------------------------
block-step-c-branch-nz : ∀ {hv : HeapView} prog fs s n m → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero n))
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag (suc m)
  → BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
block-step-c-branch-nz {hv} prog fs s n m cc h ft sc-eq = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (beq s3 zero (once n))
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft)
    s3-val : R.readReg (R.State.regs s) s3 ≡ suc m
    s3-val = trans (C.scratch-eq dc) (cong (C.enc-sv hv) sc-eq)
    not-taken : (R.readReg (R.State.regs s) s3 ≡ᵇ R.readReg (R.State.regs s) zero) ≡ false
    not-taken = cong (_≡ᵇ 0) s3-val
    post : R.State
    post = record s { pc = R.State.pc s + 1 }
    snh : R.step-not-halted (compile-trace prog) s ≡ just post
    snh = step-beq-not {compile-trace prog} {s} {s3} {zero} {once n} fetch-rv not-taken
    exec-eq : R.exec 1 (compile-trace prog) s ≡ just post
    exec-eq = exec-1 {compile-trace prog} {0} {s} {post} halt-s snh halt-s
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    result rewrite sc-eq = post , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc
                          ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc
                          ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                          ; heap-eq = C.heap-eq dc
                          ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = trans (cong (_+ 1) po)
                       (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-branch-scratch-zero n)) ft))
      ; ret-eq = ret-eq cc ; code-eq = code-eq cc }

block-step-c-branch-tag-nz : ∀ {hv : HeapView} prog fs s n loc m → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero n))
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
  → readLoc (floc fs) loc ≡ just (SV-Tag (suc m))
  → R.readMem (R.State.memory s) (R.effectiveAddr (R.State.regs s) t0 0) ≡ just (suc m)
  → BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
block-step-c-branch-tag-nz {hv} prog fs s n loc m cc h ft i-eq r-eq rd = result
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-ld : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld t1 t0 0)
    fetch-ld = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post-ld : R.State
    post-ld = record s { regs = R.writeReg (R.State.regs s) t1 (suc m) ; pc = R.State.pc s + 1 }
    step-ld' : R.step-not-halted (compile-trace prog) s ≡ just post-ld
    step-ld' = step-ld {compile-trace prog} {s} {t1} {t0} {0} {suc m} fetch-ld rd
    fetch-beq : R.fetch (compile-trace prog) (R.State.pc post-ld) ≡ just (beq t1 zero (once n))
    fetch-beq = trans (cong (λ p → R.fetch (compile-trace prog) (p + 1)) po)
                      (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)
    post : R.State
    post = record post-ld { pc = R.State.pc post-ld + 1 }
    step-b : R.step-not-halted (compile-trace prog) post-ld ≡ just post
    step-b = step-beq-not {compile-trace prog} {post-ld} {t1} {zero} {once n} fetch-beq refl
    exec-eq : R.exec 2 (compile-trace prog) s ≡ just post
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-ld} halt-s step-ld' halt-s)
                    (exec-1 {compile-trace prog} {0} {post-ld} {post} halt-s step-b halt-s)
    cond-eq : tag-zf (flat-read-tag (floc fs)) ≡ sv-is-zero (SV-Tag {FS} (suc m))
    cond-eq = cong tag-zf (trans (cong (flat-read-at (floc fs)) (cong sv-as-loc i-eq)) r-eq)
    result : BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
    result rewrite cond-eq = post , exec-eq , record
      { dataCorr = record { in1-eq = C.in1-eq dc ; out-eq = C.out-eq dc
                          ; scratch-eq = C.scratch-eq dc ; count-eq = C.count-eq dc ; clos-eq = C.clos-eq dc
                          ; halt-eq = C.halt-eq dc ; sp-eq = C.sp-eq dc ; frontier-eq = C.frontier-eq dc
                          ; dom-fresh = C.dom-fresh dc ; dom-written = C.dom-written dc ; dom-sized = C.dom-sized dc
                          ; heap-eq = C.heap-eq dc
                          ; lo-le = C.lo-le dc ; untouched = C.untouched dc ; stack-eq = C.stack-eq dc }
      ; pc-off = trans (+-assoc (R.State.pc s) 1 1)
                       (trans (cong (_+ 2) po)
                              (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-branch-tag-zero n)) ft)))
      ; ret-eq = ret-eq cc ; code-eq = code-eq cc }

------------------------------------------------------------------------
-- ALLOCATION (plan 0.65 G2) — `mv a0, s2 ; addi s2, s2, n*8`.
--
-- x86-64's `block-step-alloc-heap` with `s2` where it writes `%r15`, and one
-- field fewer in the post-state because riscv64 has no flags. The premise list
-- is the field's, verbatim: a view EXTENSION has to know the new block's
-- references are fresh and its cells unwritten, and `room` measures the bump
-- against the stack's HIGH-WATER MARK rather than the live `sp` — which is
-- what makes those cells provably unwritten (D085/D097).
--
-- The link register is untouched: both writes name a concrete register, so the
-- head row's claim carries by computation.
------------------------------------------------------------------------
block-step-alloc-heap : ∀ {hv : HeapView} prog fs s n → (cc : CompiledCorr hv prog fs s)
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-alloc-heap n)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Input1)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Scratch)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Count)
  → sv-below (next-heap-ref (falloc fs)) (fclosure fs)
  → (∀ hl → HDom hv hl → svm-below (next-heap-ref (falloc fs)) (heapMem (floc fs) hl))
  → (∀ (f : FrameSemantics.Frame FS) (k : Slot)
       → svm-below (next-heap-ref (falloc fs)) (stackMem (floc fs) f k))
  → (∀ hl → ref-id (heap-ref hl) ≡ next-heap-ref (falloc fs) → heapMem (floc fs) hl ≡ nothing)
  → (room : C.hfront hv + slots n ≤ C.lo hv)
  -- THE LAYOUT FITS IN THE ADDRESS SPACE (plan 0.70 phase C), exactly as on
  -- x86-64: `room` already bounds the bumped frontier by the high-water mark,
  -- so all that is missing is that the mark itself is representable.
  → C.lo hv < R.W.modulus
  → BlockStep (C.extend-view hv (next-heap-ref (falloc fs)) n (C.dom-fresh (dataCorr cc)) room)
              prog fs s (instr-alloc-heap n)
block-step-alloc-heap {hv} prog fs s n cc h ft wf1 wfs wfc wfcl wf-heap wf-stack fresh-abs room lo-fits =
  post-add , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                              ; ret-eq = ret-eq cc ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    fetch-mv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (mv a0 s2)
    fetch-mv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-alloc-heap n) ft)
    post-mv : R.State
    post-mv = record s { regs = R.writeReg (R.State.regs s) a0 (R.readReg (R.State.regs s) s2)
                       ; pc = R.State.pc s + 1 }
    step1 : R.step-not-halted (compile-trace prog) s ≡ just post-mv
    step1 = step-mv {compile-trace prog} {s} {a0} {s2} fetch-mv
    fetch-addi : R.fetch (compile-trace prog) (R.State.pc post-mv)
               ≡ just (addi s2 s2 (ℤ.+ (slots n)))
    fetch-addi = trans (cong (λ p → R.fetch (compile-trace prog) (p + 1)) po)
                       (fetch-block-2nd prog (fpc fs) (instr-alloc-heap n) ft)
    post-add : R.State
    post-add = record post-mv
                 { regs = R.writeReg (R.State.regs post-mv) s2
                            (R.readReg (R.State.regs post-mv) s2 + slots n)
                 ; pc = R.State.pc post-mv + 1 }
    -- `s2` IS the frontier (`frontier-eq`), so `room` bounds the bump by `lo`,
    -- and `lo-fits` carries it under the modulus.
    no-wrap : R.readReg (R.State.regs post-mv) s2 + slots n < R.W.modulus
    no-wrap = ≤-<-trans (subst (λ z → z + slots n ≤ C.lo hv)
                               (sym (C.frontier-eq dc)) room)
                        lo-fits
    wrap-free : R.readReg (R.State.regs post-mv) s2 R.W.⊕ R.W.fromℤ (ℤ.+ (slots n))
              ≡ R.readReg (R.State.regs post-mv) s2 + slots n
    wrap-free = trans (R.W.⊕-normʳ (R.readReg (R.State.regs post-mv) s2) (slots n))
                      (R.W.⊕≡+ (R.readReg (R.State.regs post-mv) s2) (slots n) no-wrap)
    step2 : R.step-not-halted (compile-trace prog) post-mv ≡ just post-add
    step2 = subst (λ w → R.step-not-halted (compile-trace prog) post-mv
                         ≡ just (record post-mv { regs = R.writeReg (R.State.regs post-mv) s2 w
                                                ; pc = R.State.pc post-mv + 1 }))
                  wrap-free
                  (step-addi {compile-trace prog} {post-mv} {s2} {s2} {ℤ.+ (slots n)} fetch-addi)
    exec-eq : R.exec 2 (compile-trace prog) s ≡ just post-add
    exec-eq = trans (exec-1 {compile-trace prog} {1} {s} {post-mv} halt-s step1 halt-s)
                    (exec-1 {compile-trace prog} {0} {post-mv} {post-add} halt-s step2 halt-s)
    dataPost : C.FlatCorr (C.extend-view hv (next-heap-ref (falloc fs)) n (C.dom-fresh dc) room)
                          (flat-exec-instr (instr-alloc-heap n) prog fs) post-add
    dataPost = C.sim-alloc-heap n fs s _ dc
                 wf1 wfs wfc wfcl wf-heap wf-stack fresh-abs room
                 (C.sets-2roles-riscv64 s role-out role-heap _ _ _ (λ ()))
    pco' : R.State.pc post-add ≡ blk-off prog (fpc (flat-exec-instr (instr-alloc-heap n) prog fs))
    pco' = trans (trans (cong (λ p → (p + 1) + 1) po) (+-assoc (blk-off prog (fpc fs)) 1 1))
                 (sym (blk-off-suc prog (fpc fs) (instr-alloc-heap n) ft))

------------------------------------------------------------------------
-- THE BODY MARKER (plan 0.65 G2) — `label (thunk n) ; addi sp,sp,-8b ;
-- sd ra, 8b(sp)`, and THE SPILL is the third instruction.
--
-- x86-64's marker is two instructions and writes no memory: its `call` already
-- put the return address in the cell, so its head-row conversion (`just` to
-- `nothing`) is the identity. RISC-V's `jalr` left the address in `ra`, so the
-- conversion here is a REAL STORE, and it lands on the head pending return's
-- own cell — the slot D086 gave the call.
--
-- That store is legal for one reason and it is worth naming: the CALLER'S BASE
-- IS ONE SLOT ABOVE IT. That is `GapNext`, which lives in `RetAddrs` and not in
-- `StackWindows` — the windows thread their floor as a `≤`, so from them alone
-- the caller could start exactly on the cell being written. The premises
-- `no-link` and `pend` are what put the head row within reach; the engine
-- proves both from the run (`thunk-entry-link` / `thunk-entry-ret`: the ONLY
-- way to a body entry is a call).
------------------------------------------------------------------------
block-step-c-thunk : ∀ {hv : HeapView} prog fs s n b r rpc rest → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk n b))
  → (lo' : ℕ) (lo'≤lo : lo' ≤ C.lo hv) (front-lo' : C.hfront hv ≤ lo')
  → lo' ≤ R.readReg (R.State.regs s) sp ∸ slots b
  → slots b ≤ R.readReg (R.State.regs s) sp
  → frame-slots (falloc fs) ≡ 0
  → R.readReg (R.State.regs s) sp < R.W.modulus
  → flink fs ≡ just r
  → fret fs ≡ rpc ∷ rest
  → BlockStepAt hv (C.descend-view hv lo' lo'≤lo front-lo') prog fs s (instr-ctrl (c-thunk n b))
block-step-c-thunk {hv} prog fs s n b r rpc rest cc h ft lo' lo'≤lo front-lo' lo'≤sp fits
                   empty-frame sp<mod no-link pend =
  post-sd , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                             ; ret-eq = retPost ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    -- step 1: the body-entry label (pc only)
    fetch-lab : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (label (thunk n))
    fetch-lab = trans (cong (R.fetch (compile-trace prog)) po)
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-thunk n b)) ft)
    post-lab : R.State
    post-lab = record s { pc = R.State.pc s + 1 }
    step-lab : R.step-not-halted (compile-trace prog) s ≡ just post-lab
    step-lab = step-label {compile-trace prog} {s} {thunk n} fetch-lab
    -- step 2: the reservation
    fetch-addi : R.fetch (compile-trace prog) (R.State.pc post-lab)
               ≡ just (addi sp sp (ℤ.-_ (ℤ.+ (slots b))))
    fetch-addi = trans (cong (λ q → R.fetch (compile-trace prog) (q + 1)) po)
                       (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-thunk n b)) ft)
    post-addi : R.State
    post-addi = record s { regs = R.writeReg (R.State.regs s) sp
                                    (R.readReg (R.State.regs s) sp ∸ slots b)
                         ; pc = R.State.pc s + 1 + 1 }
    step-addi' : R.step-not-halted (compile-trace prog) post-lab ≡ just post-addi
    step-addi' = subst (λ w → R.step-not-halted (compile-trace prog) post-lab
                              ≡ just (record s { regs = R.writeReg (R.State.regs s) sp w
                                               ; pc = R.State.pc s + 1 + 1 }))
                       (R.W.⊕-neg (R.readReg (R.State.regs s) sp) (slots b) fits sp<mod)
                       (step-addi {compile-trace prog} {post-lab} {sp} {sp}
                                  {ℤ.-_ (ℤ.+ (slots b))} fetch-addi)
    -- step 3: THE SPILL. `sp` is back where the abstract frame's window ends —
    -- `m∸n+n≡m fits` — which is the cell the call reserved.
    fetch-sd : R.fetch (compile-trace prog) (R.State.pc post-addi)
             ≡ just (sd ra sp (slots b))
    fetch-sd = trans (cong (R.fetch (compile-trace prog))
                           (trans (+-assoc (R.State.pc s) 1 1) (cong (_+ 2) po)))
                     (fetch-block-3rd prog (fpc fs) (instr-ctrl (c-thunk n b)) ft)
    waddr : ℕ
    waddr = R.effectiveAddr (R.State.regs post-addi) sp (slots b)
    post-sd : R.State
    post-sd = record post-addi
                { memory = R.writeMem (R.State.memory post-addi) waddr
                             (R.readReg (R.State.regs post-addi) ra)
                ; pc = R.State.pc post-addi + 1 }
    step-sd' : R.step-not-halted (compile-trace prog) post-addi ≡ just post-sd
    step-sd' = step-sd {compile-trace prog} {post-addi} {ra} {sp} {slots b} fetch-sd
    exec-eq : R.exec 3 (compile-trace prog) s ≡ just post-sd
    exec-eq = trans (exec-1 {compile-trace prog} {2} {s} {post-lab} halt-s step-lab halt-s)
              (trans (exec-1 {compile-trace prog} {1} {post-lab} {post-addi} halt-s step-addi' halt-s)
                     (exec-1 {compile-trace prog} {0} {post-addi} {post-sd} halt-s step-sd' halt-s))
    -- WHERE THE STORE LANDS: `(sp ∸ 8b) + 8b`, i.e. the pre-state's `sp`, which
    -- `sp-eq` puts at the current frame's base — and `empty-frame` makes that
    -- base the frame's window END.
    waddr-eq : waddr ≡ frame-base FS (current-frame (falloc fs))
             + slots (frame-slots (falloc fs))
    waddr-eq = trans (m∸n+n≡m fits)
               (trans (C.sp-eq dc)
                      (trans (sym (+-identityʳ (frame-base FS (current-frame (falloc fs)))))
                             (cong (λ z → frame-base FS (current-frame (falloc fs)) + slots z)
                                   (sym empty-frame))))
    -- THE HEAD ROW, at the pre-state: `flink` is live, so it is the arch's
    -- claim — `ra` holds the return address — and its `GapNext` is what makes
    -- the store miss the caller's window.
    head : C.RetAddrs (blk-off prog) (R.State.memory s) (riscv64-link-claim s)
                      (just r)
                      ((current-frame (falloc fs) , frame-slots (falloc fs))
                       ∷ saved-frames (falloc fs))
                      (rpc ∷ rest)
    head = subst₂ (λ lk rs' → C.RetAddrs (blk-off prog) (R.State.memory s)
                                (riscv64-link-claim s) lk (C.frames-of (falloc fs)) rs')
                  no-link pend (ret-eq cc)
    gap : C.GapNext (frame-base FS (current-frame (falloc fs))
                     + slots (frame-slots (falloc fs))) (saved-frames (falloc fs))
    gap = proj₁ (proj₂ head)
    -- the abstract post-state's frame is the SHIFTED one, and its window end is
    -- the same cell (D093's re-anchoring, `empty-frame` again)
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
    -- the data correspondence at the RESERVATION, then across the spill
    dataAddi : C.FlatCorr (C.descend-view hv lo' lo'≤lo front-lo')
                          (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs) post-addi
    dataAddi = C.sim-thunk b fs s _ dc lo' lo'≤lo front-lo' lo'≤sp fits
                           (C.sets-role-riscv64 s role-sp _ _)
    dataPost : C.FlatCorr (C.descend-view hv lo' lo'≤lo front-lo')
                          (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs) post-sd
    dataPost = C.corr-store-gap (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs)
                 post-addi post-sd (R.readReg (R.State.regs post-addi) ra) dataAddi
                 (λ _ → refl) refl
                 (cong (λ z → R.writeMem (R.State.memory post-addi) z
                                (R.readReg (R.State.regs post-addi) ra))
                       (trans waddr-eq (sym addr-eq)))
                 (subst (λ z → C.GapNext z (saved-frames (falloc fs))) (sym addr-eq) gap)
    pco' : R.State.pc post-sd
         ≡ blk-off prog (fpc (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs))
    pco' = trans (trans (+-assoc (R.State.pc s + 1) 1 1)
                        (trans (+-assoc (R.State.pc s) 1 2) (cong (_+ 3) po)))
                 (sym (blk-off-suc prog (fpc fs) (instr-ctrl (c-thunk n b)) ft))
    -- THE ROW CONVERSION, WHICH ON THIS ARCH IS THE STORE: the head cell now
    -- holds what `ra` held, and `head` says that was the return address. Every
    -- older row rides across by `GapNext` — the caller's base is one slot up.
    val-ra : ℕ
    val-ra = R.readReg (R.State.regs post-addi) ra
    spilled : C.RetAddrs (blk-off prog)
                (R.writeMem (R.State.memory s)
                   (frame-base FS (current-frame (falloc fs))
                    + slots (frame-slots (falloc fs))) val-ra)
                (riscv64-link-claim post-sd) nothing
                (C.frames-of (falloc fs)) (fret fs)
    spilled = subst (λ rs' → C.RetAddrs (blk-off prog)
                               (R.writeMem (R.State.memory s)
                                  (frame-base FS (current-frame (falloc fs))
                                   + slots (frame-slots (falloc fs))) val-ra)
                               (riscv64-link-claim post-sd) nothing
                               (C.frames-of (falloc fs)) rs')
                    (sym pend)
                    (C.ret-spill (blk-off prog) (R.State.memory s)
                       (riscv64-link-claim s) (riscv64-link-claim post-sd)
                       (stackMem (floc fs)) r
                       (current-frame (falloc fs)) (frame-slots (falloc fs)) val-ra
                       (saved-frames (falloc fs)) (rpc ∷ rest)
                       (proj₂ (proj₂ (C.stack-eq dc)))
                       -- WHAT IS SPILLED IS WHAT THE CLAIM SAID: the `addi` wrote
                       -- `sp`, so `ra` still holds the value the head row is about.
                       (λ w p → p)
                       head)
    retPost : C.RetAddrs (blk-off prog) (R.State.memory post-sd) (riscv64-link-claim post-sd)
                         (flink (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs))
                         (C.frames-of (falloc (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs)))
                         (fret (flat-exec-instr (instr-ctrl (c-thunk n b)) prog fs))
    retPost = C.ret-head (blk-off prog) (R.State.memory post-sd)
                         (riscv64-link-claim post-sd) nothing
                         (current-frame (falloc fs))
                         (shift-frame FS (current-frame (falloc fs)) b)
                         (frame-slots (falloc fs)) b
                         (saved-frames (falloc fs)) (fret fs)
                         addr-eq
                         (subst (λ m → C.RetAddrs (blk-off prog) m (riscv64-link-claim post-sd)
                                         nothing (C.frames-of (falloc fs)) (fret fs))
                                (cong (λ z → R.writeMem (R.State.memory s) z val-ra)
                                      (sym waddr-eq))
                                spilled)


------------------------------------------------------------------------
-- THE RETURN (D095) — `ld ra, 8b(sp) ; addi sp, sp, 8(b+1) ; ret`.
--
-- THREE instructions where x86-64 needs two, and the extra one is the mirror
-- of the marker's spill: RISC-V has no pop, so the return address must come
-- BACK into `ra` before `ret` can jump through it. That first `ld` writes a
-- register that is nobody's ROLE, which is what `corr-regs-agree` is for.
--
-- It is also why `ret-no-wrap` had to say `suc b`: this arch reaches the
-- caller's base in ONE `addi`, so the x86-64-shaped bound (which stopped at the
-- frame, the `ret` supplying the last slot) was short by exactly one slot.
--
-- Everything else is x86-64's proof: the address from `sp-eq` plus the bracket
-- premise `b ≡ frame-slots`, the value from `RetAddrs`' head, the new `sp` from
-- `GapNext`.
------------------------------------------------------------------------
block-step-c-ret : ∀ {hv : HeapView} prog fs s b rpc rest f₀ b₀ frs
  → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
  → fret fs ≡ rpc ∷ rest
  → b ≡ frame-slots (falloc fs)
  → saved-frames (falloc fs) ≡ (f₀ , b₀) ∷ frs
  → R.readReg (R.State.regs s) sp + slots (suc b) < R.W.modulus
  → flink fs ≡ nothing
  → BlockStep hv prog fs s (instr-ctrl (c-ret b))
block-step-c-ret {hv} prog fs s b rpc rest f₀ b₀ frs cc h ft req bslots feq no-wrap no-link =
  post-ret , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                              ; ret-eq = retPost ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    -- THE COMPONENT, at the cons shape of `fret` and with the head row already
    -- the MEMORY row (`no-link`).
    comp : C.RetAddrs (blk-off prog) (R.State.memory s) (riscv64-link-claim s) nothing
                      ((current-frame (falloc fs) , frame-slots (falloc fs))
                       ∷ saved-frames (falloc fs))
                      (rpc ∷ rest)
    comp = subst₂ (λ lk rs' → C.RetAddrs (blk-off prog) (R.State.memory s)
                                (riscv64-link-claim s) lk (C.frames-of (falloc fs)) rs')
                  no-link req (ret-eq cc)
    -- step 1: THE RELOAD. `sp` is the frame's base and `8b` its window end, so
    -- the address is exactly the cell the call reserved.
    addr-eq : R.effectiveAddr (R.State.regs s) sp (slots b)
            ≡ frame-base FS (current-frame (falloc fs)) + slots (frame-slots (falloc fs))
    addr-eq = trans (cong (_+ slots b) (C.sp-eq dc))
                    (cong (λ z → frame-base FS (current-frame (falloc fs)) + slots z) bslots)
    fetch-ld : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld ra sp (slots b))
    fetch-ld = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) (instr-ctrl (c-ret b)) ft)
    rd : R.readMem (R.State.memory s) (R.effectiveAddr (R.State.regs s) sp (slots b))
       ≡ just (blk-off prog rpc)
    rd = trans (cong (R.readMem (R.State.memory s)) addr-eq) (proj₁ comp)
    post-ld : R.State
    post-ld = record s { regs = R.writeReg (R.State.regs s) ra (blk-off prog rpc)
                       ; pc = R.State.pc s + 1 }
    step-ld' : R.step-not-halted (compile-trace prog) s ≡ just post-ld
    step-ld' = step-ld {compile-trace prog} {s} {ra} {sp} {slots b} {blk-off prog rpc}
                       fetch-ld rd
    -- the link register is nobody's role, so the data correspondence rides
    -- across the reload untouched
    dc-ld : C.FlatCorr hv fs post-ld
    dc-ld = C.corr-regs-agree fs s post-ld dc
              (λ ρ → C.role-off-ra s ρ (blk-off prog rpc)) refl refl
    -- step 2: the release, frame AND reserved slot in one instruction
    fetch-addi : R.fetch (compile-trace prog) (R.State.pc post-ld)
               ≡ just (addi sp sp (ℤ.+ (slots (suc b))))
    fetch-addi = trans (cong (λ q → R.fetch (compile-trace prog) (q + 1)) po)
                       (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-ret b)) ft)
    suc-slots : slots (suc b) ≡ slots b + slot-size
    suc-slots = +-comm slot-size (slots b)
    -- WRITTEN IN `sim-ret`'S SHAPE, not the instruction's: the emitter adds
    -- `slots (suc b)` in one go, the model reaches the same address as
    -- "frame, then the call's slot". Converting here rather than at the
    -- correspondence keeps the post-state literal the one `SetsRole` describes.
    newsp : ℕ
    newsp = R.readReg (R.State.regs post-ld) sp + slots b + slot-size
    wrap-free : R.readReg (R.State.regs post-ld) sp R.W.⊕ R.W.fromℤ (ℤ.+ (slots (suc b)))
              ≡ newsp
    wrap-free = trans (R.W.⊕-normʳ (R.readReg (R.State.regs s) sp) (slots (suc b)))
                (trans (R.W.⊕≡+ (R.readReg (R.State.regs s) sp) (slots (suc b)) no-wrap)
                (trans (cong (R.readReg (R.State.regs s) sp +_) suc-slots)
                       (sym (+-assoc (R.readReg (R.State.regs s) sp) (slots b) slot-size))))
    post-addi : R.State
    post-addi = record post-ld
                  { regs = R.writeReg (R.State.regs post-ld) sp newsp
                  ; pc = R.State.pc post-ld + 1 }
    step-addi' : R.step-not-halted (compile-trace prog) post-ld ≡ just post-addi
    step-addi' = subst (λ w → R.step-not-halted (compile-trace prog) post-ld
                              ≡ just (record post-ld
                                        { regs = R.writeReg (R.State.regs post-ld) sp w
                                        ; pc = R.State.pc post-ld + 1 }))
                       wrap-free
                       (step-addi {compile-trace prog} {post-ld} {sp} {sp}
                                  {ℤ.+ (slots (suc b))} fetch-addi)
    -- step 3: the jump through the reloaded link
    fetch-ret : R.fetch (compile-trace prog) (R.State.pc post-addi) ≡ just ret
    fetch-ret = trans (cong (R.fetch (compile-trace prog))
                            (trans (+-assoc (R.State.pc s) 1 1) (cong (_+ 2) po)))
                      (fetch-block-3rd prog (fpc fs) (instr-ctrl (c-ret b)) ft)
    post-ret : R.State
    post-ret = record post-addi { pc = R.readReg (R.State.regs post-addi) ra }
    step-ret' : R.step-not-halted (compile-trace prog) post-addi ≡ just post-ret
    step-ret' = step-ret {compile-trace prog} {post-addi} fetch-ret
    exec-eq : R.exec 3 (compile-trace prog) s ≡ just post-ret
    exec-eq = trans (exec-1 {compile-trace prog} {2} {s} {post-ld} halt-s step-ld' halt-s)
              (trans (exec-1 {compile-trace prog} {1} {post-ld} {post-addi} halt-s step-addi' halt-s)
                     (exec-1 {compile-trace prog} {0} {post-addi} {post-ret} halt-s step-ret' halt-s))
    -- THE CALLER'S BASE is one slot above the cell — `GapNext`, read through the
    -- frame list's shape — and that is where the `addi` lands `sp`.
    gap : frame-base FS (current-frame (falloc fs)) + slots (frame-slots (falloc fs))
          + slot-size
        ≡ frame-base FS f₀
    gap = subst (λ fr → C.GapNext (frame-base FS (current-frame (falloc fs))
                                   + slots (frame-slots (falloc fs))) fr)
                feq (proj₁ (proj₂ comp))
    base-leave : saved-frames (falloc fs) ≡ (f₀ , b₀) ∷ frs
               → frame-base FS (current-frame (leave-frame (falloc fs))) ≡ frame-base FS f₀
    base-leave e rewrite e = refl
    restores : R.readReg (R.State.regs post-ld) sp + slots b + slot-size
             ≡ frame-base FS (current-frame (leave-frame (falloc fs)))
    restores = trans (cong (_+ slot-size) addr-eq) (trans gap (sym (base-leave feq)))
    dataPost : C.FlatCorr hv (flat-exec-instr (instr-ctrl (c-ret b)) prog fs) post-ret
    dataPost = C.sim-ret b rpc rest fs post-ld post-ret dc-ld req restores
                 (C.sets-role-riscv64 post-ld role-sp _ _)
    pco' : R.State.pc post-ret ≡ blk-off prog (fpc (flat-exec-instr (instr-ctrl (c-ret b)) prog fs))
    pco' = cong (blk-off prog) (sym (do-ret-pc-∷ fs rpc rest req))
    -- THE TAIL IS THE POST-STATE'S COMPONENT. Memory never moved; only `ra` and
    -- `sp` did, and the rows below the head are memory reads.
    lk-post : flink (flat-exec-instr (instr-ctrl (c-ret b)) prog fs) ≡ nothing
    lk-post = trans (flink-do-ret (fret fs) fs) no-link
    frames-leave : saved-frames (falloc fs) ≡ (f₀ , b₀) ∷ frs
                 → C.frames-of (leave-frame (falloc fs)) ≡ saved-frames (falloc fs)
    frames-leave e rewrite e = refl
    retPost : C.RetAddrs (blk-off prog) (R.State.memory post-ret) (riscv64-link-claim post-ret)
                         (flink (flat-exec-instr (instr-ctrl (c-ret b)) prog fs))
                         (C.frames-of (falloc (flat-exec-instr (instr-ctrl (c-ret b)) prog fs)))
                         (fret (flat-exec-instr (instr-ctrl (c-ret b)) prog fs))
    retPost = subst (λ lk → C.RetAddrs (blk-off prog) (R.State.memory s)
                              (riscv64-link-claim post-ret) lk
                              (C.frames-of (falloc (flat-exec-instr (instr-ctrl (c-ret b)) prog fs)))
                              (fret (flat-exec-instr (instr-ctrl (c-ret b)) prog fs)))
                    (sym lk-post)
                    (subst₂ (C.RetAddrs (blk-off prog) (R.State.memory s)
                               (riscv64-link-claim post-ret) nothing)
                            (sym (trans (cong C.frames-of (do-ret-alloc fs)) (frames-leave feq)))
                            (sym (do-ret-fret-∷ fs rpc rest req))
                            -- `ra` changed, so the CLAIM changed — but at a
                            -- `nothing`-headed component it is never read.
                            (C.ret-agree-nothing (blk-off prog)
                               (R.State.memory s) (R.State.memory s)
                               (riscv64-link-claim s) (riscv64-link-claim post-ret)
                               (stackMem (floc fs))
                               (frame-base FS (current-frame (falloc fs))
                                + slots (frame-slots (falloc fs)))
                               (saved-frames (falloc fs)) rest
                               (λ _ _ → refl)
                               (proj₂ (proj₂ (C.stack-eq dc)))
                               (proj₂ (proj₂ comp))))

------------------------------------------------------------------------
-- THE CALL (D098) — `ld t1, 8(s1) ; addi sp, sp, -8 ; jalr ra, t1, 0`.
--
-- The middle instruction is the one added 2026-08-16, and it is the whole of
-- why `sp-eq` holds inside the call window: RISC-V's `jalr` does not move the
-- stack pointer, so the CALLER reserves the slot D086 gave it, exactly where
-- the abstract `enter-call` does.
--
-- What no emitter change can erase is the third instruction: `jalr` puts the
-- return address in `ra` and writes NO memory. So the post-state's head row is
-- the arch's link claim, and it stays that way until the callee's marker
-- spills. That is `flink`, and this is where it is set.
--
-- `t1`, not `t0`: `t0` is Input1, which the callee reads.
------------------------------------------------------------------------
block-step-call : ∀ {hv : HeapView} prog fs s hl ℓ jx → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just instr-call-closure
  → fclosure fs ≡ SV-Ptr (AtDynamic hl)
  → heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ)
  → HDom hv (sucHL hl)
  → FlatMachine.find-thunk {FS} prog ℓ ≡ just jx
  → (lo' : ℕ) (lo'≤lo : lo' ≤ C.lo hv) (front-lo' : C.hfront hv ≤ lo')
  → lo' ≤ R.readReg (R.State.regs s) sp ∸ slot-size
  → slot-size ≤ R.readReg (R.State.regs s) sp
  -- THE MACHINE IS FINITE: the caller's `addi sp, sp, -8` is a real subtract,
  -- so it needs the no-borrow range fact x86-64's hardware push never did.
  → R.readReg (R.State.regs s) sp < R.W.modulus
  → flink fs ≡ nothing
  → BlockStepAt hv (C.descend-view hv lo' lo'≤lo front-lo') prog fs s instr-call-closure
block-step-call {hv} prog fs s hl ℓ jx cc h ft ceq heq live fteq lo' lo'≤lo front-lo' lo'≤sp
                fits sp<mod no-link =
  post-jalr , exec-eq , record { dataCorr = dataPost ; pc-off = pco'
                               ; ret-eq = retPost ; code-eq = code-eq cc }
  where
    dc = dataCorr cc ; po = pc-off cc
    halt-s : R.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    -- step 1: THE TARGET. `s1` is the closure pointer, its second cell the code
    -- address, and that address is the body's index (D096/D097).
    s1-val : R.readReg (R.State.regs s) s1 ≡ haddr hv hl
    s1-val = trans (C.clos-eq dc) (cong (C.enc-sv hv) ceq)
    cell-addr : R.effectiveAddr (R.State.regs s) s1 slot-size ≡ haddr hv (sucHL hl)
    cell-addr = trans (cong (_+ slot-size) s1-val) (sym (C.haddr-suc hv hl))
    conc-res : R.find-label (compile-trace prog) (thunk ℓ) ≡ just (blk-off prog jx)
    conc-res = find-thunk-corr prog ℓ 0 jx fteq
    rd : R.readMem (R.State.memory s) (R.effectiveAddr (R.State.regs s) s1 slot-size)
       ≡ just (blk-off prog jx)
    rd = trans (cong (R.readMem (R.State.memory s)) cell-addr)
        (trans (C.heap-eq dc (sucHL hl) live)
        (trans (cong (C.enc-maybe hv) heq)
               (cong just (code-eq cc ℓ (blk-off prog jx) conc-res))))
    fetch-ld : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld t1 s1 slot-size)
    fetch-ld = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) instr-call-closure ft)
    post-ld : R.State
    post-ld = record s { regs = R.writeReg (R.State.regs s) t1 (blk-off prog jx)
                       ; pc = R.State.pc s + 1 }
    step-ld' : R.step-not-halted (compile-trace prog) s ≡ just post-ld
    step-ld' = step-ld {compile-trace prog} {s} {t1} {s1} {slot-size} {blk-off prog jx}
                       fetch-ld rd
    dc-ld : C.FlatCorr hv fs post-ld
    dc-ld = C.corr-regs-agree fs s post-ld dc
              (λ ρ → C.role-off-t1 s ρ (blk-off prog jx)) refl refl
    -- step 2: THE CALLER RESERVES THE SLOT
    fetch-addi : R.fetch (compile-trace prog) (R.State.pc post-ld)
               ≡ just (addi sp sp (ℤ.-_ (ℤ.+ slot-size)))
    fetch-addi = trans (cong (λ q → R.fetch (compile-trace prog) (q + 1)) po)
                       (fetch-block-2nd prog (fpc fs) instr-call-closure ft)
    post-addi : R.State
    post-addi = record post-ld
                  { regs = R.writeReg (R.State.regs post-ld) sp
                             (R.readReg (R.State.regs post-ld) sp ∸ slot-size)
                  ; pc = R.State.pc post-ld + 1 }
    step-addi' : R.step-not-halted (compile-trace prog) post-ld ≡ just post-addi
    step-addi' = subst (λ w → R.step-not-halted (compile-trace prog) post-ld
                              ≡ just (record post-ld
                                        { regs = R.writeReg (R.State.regs post-ld) sp w
                                        ; pc = R.State.pc post-ld + 1 }))
                       (R.W.⊕-neg (R.readReg (R.State.regs post-ld) sp) slot-size fits sp<mod)
                       (step-addi {compile-trace prog} {post-ld} {sp} {sp}
                                  {ℤ.-_ (ℤ.+ slot-size)} fetch-addi)
    -- step 3: the transfer, and the LINK
    fetch-jalr : R.fetch (compile-trace prog) (R.State.pc post-addi) ≡ just (jalr ra t1 0)
    fetch-jalr = trans (cong (R.fetch (compile-trace prog))
                             (trans (+-assoc (R.State.pc s) 1 1) (cong (_+ 2) po)))
                       (fetch-block-3rd prog (fpc fs) instr-call-closure ft)
    post-jalr : R.State
    post-jalr = record post-addi
                  { regs = R.writeReg (R.State.regs post-addi) ra (R.State.pc post-addi + 1)
                  ; pc = R.effectiveAddr (R.State.regs post-addi) t1 0 }
    step-jalr' : R.step-not-halted (compile-trace prog) post-addi ≡ just post-jalr
    step-jalr' = step-jalr {compile-trace prog} {post-addi} {ra} {t1} {0} fetch-jalr
    exec-eq : R.exec 3 (compile-trace prog) s ≡ just post-jalr
    exec-eq = trans (exec-1 {compile-trace prog} {2} {s} {post-ld} halt-s step-ld' halt-s)
              (trans (exec-1 {compile-trace prog} {1} {post-ld} {post-addi} halt-s step-addi' halt-s)
                     (exec-1 {compile-trace prog} {0} {post-addi} {post-jalr} halt-s step-jalr' halt-s))
    absPost : FlatState
    absPost = record fs { falloc = enter-call (falloc fs)
                        ; fret   = suc (fpc fs) ∷ fret fs
                        ; flink  = just (suc (fpc fs))
                        ; fpc    = jx }
    step-eq : flat-exec-instr instr-call-closure prog fs ≡ absPost
    step-eq = trans (cong (λ z → do-call-sv prog z fs) ceq)
             (trans (cong (λ z → do-call-code prog z fs) heq)
                    (cong (λ z → do-call-at z fs) fteq))
    dataAddi : C.FlatCorr (C.descend-view hv lo' lo'≤lo front-lo') absPost post-addi
    dataAddi = C.sim-call-frame jx fs post-ld post-addi dc-ld lo' lo'≤lo front-lo' lo'≤sp fits
                 (C.sets-role-riscv64 post-ld role-sp _ _)
    dataPost : C.FlatCorr (C.descend-view hv lo' lo'≤lo front-lo')
                          (flat-exec-instr instr-call-closure prog fs) post-jalr
    dataPost = subst (λ z → C.FlatCorr (C.descend-view hv lo' lo'≤lo front-lo') z post-jalr)
                     (sym step-eq)
                     (C.corr-regs-agree absPost post-addi post-jalr dataAddi
                        (λ ρ → C.role-off-ra post-addi ρ (R.State.pc post-addi + 1))
                        refl refl)
    pco' : R.State.pc post-jalr ≡ blk-off prog (fpc (flat-exec-instr instr-call-closure prog fs))
    pco' = trans (+-identityʳ (R.readReg (R.State.regs post-addi) t1))
                 (cong (λ z → blk-off prog (fpc z)) (sym step-eq))
    -- THE LINK, which is what the head row now claims
    ret-val : R.State.pc post-addi + 1 ≡ blk-off prog (suc (fpc fs))
    ret-val = trans (trans (+-assoc (R.State.pc s + 1) 1 1)
                           (trans (+-assoc (R.State.pc s) 1 2) (cong (_+ 3) po)))
                    (sym (blk-off-suc prog (fpc fs) instr-call-closure ft))
    newbase : R.readReg (R.State.regs post-ld) sp ∸ slot-size
            ≡ frame-base FS (shift-frame FS (current-frame (falloc fs)) 1)
    newbase = trans (cong (_∸ slot-size) (C.sp-eq dc-ld))
                    (trans (cong (λ w → frame-base FS (current-frame (falloc fs)) ∸ 1 * w)
                                 (sym word-eq))
                           (sym (shift-base FS (current-frame (falloc fs)) 1)))
    gap-post : C.GapNext (frame-base FS (shift-frame FS (current-frame (falloc fs)) 1) + slots 0)
                         (C.frames-of (falloc fs))
    gap-post = trans (cong (_+ slot-size) (trans (+-identityʳ _) (sym newbase)))
                     (trans (m∸n+n≡m fits) (C.sp-eq dc-ld))
    retPost : C.RetAddrs (blk-off prog) (R.State.memory post-jalr)
                         (riscv64-link-claim post-jalr)
                         (flink (flat-exec-instr instr-call-closure prog fs))
                         (C.frames-of (falloc (flat-exec-instr instr-call-closure prog fs)))
                         (fret (flat-exec-instr instr-call-closure prog fs))
    retPost = subst (λ z → C.RetAddrs (blk-off prog) (R.State.memory post-jalr)
                             (riscv64-link-claim post-jalr) (flink z)
                             (C.frames-of (falloc z)) (fret z))
                    (sym step-eq)
                    ( ret-val , gap-post , tail )
      where
        tail : C.RetAddrs (blk-off prog) (R.State.memory post-jalr)
                          (riscv64-link-claim post-jalr) nothing
                          (C.frames-of (falloc fs)) (fret fs)
        tail = C.ret-agree-nothing (blk-off prog) (R.State.memory s) (R.State.memory s)
                 (riscv64-link-claim s) (riscv64-link-claim post-jalr)
                 (stackMem (floc fs)) (C.lo hv) (C.frames-of (falloc fs)) (fret fs)
                 (λ _ _ → refl) (C.stack-eq dc)
                 (subst (λ lk → C.RetAddrs (blk-off prog) (R.State.memory s)
                                  (riscv64-link-claim s) lk
                                  (C.frames-of (falloc fs)) (fret fs))
                        no-link (ret-eq cc))

------------------------------------------------------------------------
-- THE TWO STUCK LOADS (plan 0.65 G2) — x86-64's `*-heap-empty-stuck`, at
-- riscv64's `ld`.
--
-- The abstract half is the engine's (`EE.stuck-result`); what an ARCH owes is
-- only "nothing more comes out of the concrete machine", and for a load through
-- a pointer to an UNWRITTEN cell that is `execInstr … ≡ nothing`, straight off
-- `heap-eq` — the view maps the cell (`dom`), so the concrete read is the
-- encoding of the abstract `nothing`.
------------------------------------------------------------------------
load-indirect-heap-empty-stuck : ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s
  → fetch prog (fpc fs) ≡ just load-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl
  → heapMem (floc fs) hl ≡ nothing
  → (R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld a0 t0 0))
    × (R.execInstr (compile-trace prog) s (ld a0 t0 0) ≡ nothing)
load-indirect-heap-empty-stuck {hv} prog fs s hl cc ft i-eq dom h-eq = fetch-rv , stuck
  where
    dc = dataCorr cc ; po = pc-off cc
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld a0 t0 0)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) load-indirect ft)
    t0-val : R.readReg (R.State.regs s) t0 ≡ haddr hv hl
    t0-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-eq : R.effectiveAddr (R.State.regs s) t0 0 ≡ haddr hv hl
    addr-eq = trans (+-identityʳ (R.readReg (R.State.regs s) t0)) t0-val
    rd : R.readMem (R.State.memory s) (R.effectiveAddr (R.State.regs s) t0 0) ≡ nothing
    rd = trans (cong (R.readMem (R.State.memory s)) addr-eq)
               (trans (C.heap-eq dc hl dom) (cong (C.enc-maybe hv) h-eq))
    stuck : R.execInstr (compile-trace prog) s (ld a0 t0 0) ≡ nothing
    stuck rewrite rd = refl

load-indirect-suc-heap-empty-stuck : ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s
  → fetch prog (fpc fs) ≡ just load-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)
  → heapMem (floc fs) (sucHL hl) ≡ nothing
  → (R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld a0 t0 slot-size))
    × (R.execInstr (compile-trace prog) s (ld a0 t0 slot-size) ≡ nothing)
load-indirect-suc-heap-empty-stuck {hv} prog fs s hl cc ft i-eq dom h-eq = fetch-rv , stuck
  where
    dc = dataCorr cc ; po = pc-off cc
    fetch-rv : R.fetch (compile-trace prog) (R.State.pc s) ≡ just (ld a0 t0 slot-size)
    fetch-rv = trans (cong (R.fetch (compile-trace prog)) po)
                     (fetch-block-head prog (fpc fs) load-indirect-suc ft)
    t0-val : R.readReg (R.State.regs s) t0 ≡ haddr hv hl
    t0-val = trans (C.in1-eq dc) (cong (C.enc-sv hv) i-eq)
    addr-eq : R.effectiveAddr (R.State.regs s) t0 slot-size ≡ haddr hv (sucHL hl)
    addr-eq = trans (cong (_+ slot-size) t0-val) (sym (C.haddr-suc hv hl))
    rd : R.readMem (R.State.memory s) (R.effectiveAddr (R.State.regs s) t0 slot-size) ≡ nothing
    rd = trans (cong (R.readMem (R.State.memory s)) addr-eq)
               (trans (C.heap-eq dc (sucHL hl) dom) (cong (C.enc-maybe hv) h-eq))
    stuck : R.execInstr (compile-trace prog) s (ld a0 t0 slot-size) ≡ nothing
    stuck rewrite rd = refl
