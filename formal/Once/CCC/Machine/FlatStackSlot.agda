-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatStackSlot   (Plan 0.54 rung D, item 2)
--
-- THE LIVE STACK WINDOW ONLY MOVES AT A FRAME OP: a `FrameFreeI` instruction
-- leaves `Registers.stackSlot` exactly where it found it.
--
-- `stackSlot` is the runtime slot counter the flat↔x86-64 correspondence uses
-- to bound the live frame, and `exec-abstract` writes it at exactly three
-- sites — `instr-alloc-stack` (incr), `instr-dealloc-stack` (decr),
-- `instr-push-frame` (reset to 0). `instr-pop-frame` does not touch it at all
-- (the structured layer leaves restoration to the caller). Everything else is
-- a register write, a memory write, a halt, or an identity.
--
-- Together with "the emitter emits no frame op" (`Once.CCC.Codegen.
-- FrameFreeTrace`) this makes the window CONSTANT along a run, which is what
-- `ConcFlatSim.run-stack-slot` needs to turn `slot-read-in-frame` — the residual
-- carrying the whole slot cluster — into arithmetic about the emitter's static
-- budget.
--
-- Proved by induction over `exec-abstract`, mutually with `ss-trace` /
-- `ss-case` / `ss-loop` so the NESTED `instr-case-on-tag` / `instr-loop` traces
-- are covered (mirroring `FlatRegTagWF`); that is why `FrameFreeI` is deep. The
-- lift to `flat-exec-instr` ENUMERATES the straight-line cases — a catch-all
-- there would not reduce `flat-exec-instr`'s own catch-all in the case tree.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatStackSlot (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CCC.Machine.SMCore
import Once.Allocator.AbstractInstance as AI
open FrameSemantics FS using (Frame)
open MemOps {FS}
open ExecFinal {FS}
open AbstractExec {FS}
open import Once.CCC.Machine.FrameFree using (FrameFreeI; FrameFreeT)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}

------------------------------------------------------------------------
-- "…has the same live window as". An EQUATION, so the cases compose by
-- `trans` rather than through a transport lemma.
------------------------------------------------------------------------
SameSlot : LocState FS → LocState FS → Set
SameSlot ls' ls = stackSlot (regs ls') ≡ stackSlot (regs ls)

-- the three shapes every non-frame instruction's post-state has
ss-write : ∀ (ls : LocState FS) (x : AbstractReg) (v : StoredValue FS)
         → SameSlot (record ls { regs = writeReg (regs ls) x v }) ls
ss-write ls x v = writeReg-preserves-stackSlot (regs ls) x v

ss-write-halt : ∀ (ls : LocState FS) (x : AbstractReg) (v : StoredValue FS) (b : Bool)
              → SameSlot (record ls { regs = writeReg (regs ls) x v ; halted = b }) ls
ss-write-halt ls x v b = writeReg-preserves-stackSlot (regs ls) x v

ss-mem : ∀ (ls : LocState FS) (loc : ValueLocation FS) (v : StoredValue FS)
       → SameSlot (writeLoc ls loc v) ls
ss-mem ls loc v = cong stackSlot (writeLoc-regs ls loc v)

------------------------------------------------------------------------
-- The aux-style helpers `exec-abstract` routes through: each is enumerated on
-- its `Maybe` argument (the halt route is a record update on `halted`).
------------------------------------------------------------------------
ss-load-resolved : ∀ (ls : LocState FS) (dst : AbstractReg) (ml : Maybe (ValueLocation FS))
                 → SameSlot (exec-load-via-resolved dst ml ls) ls
ss-load-resolved ls dst nothing    = refl
ss-load-resolved ls dst (just loc) = go (readLoc ls loc)
  where go : ∀ (mv : Maybe (StoredValue FS)) → SameSlot (exec-load-with-value dst mv ls) ls
        go (just v) = ss-write ls dst v
        go nothing  = refl

ss-load-suc-resolved : ∀ (ls : LocState FS) (dst : AbstractReg) (ml : Maybe (ValueLocation FS))
                     → SameSlot (exec-load-suc-via-resolved dst ml ls) ls
ss-load-suc-resolved ls dst nothing    = refl
ss-load-suc-resolved ls dst (just loc) = go (readLoc ls (sucLoc loc))
  where go : ∀ (mv : Maybe (StoredValue FS)) → SameSlot (exec-load-with-value dst mv ls) ls
        go (just v) = ss-write ls dst v
        go nothing  = refl

ss-store-resolved : ∀ (ls : LocState FS) (ml : Maybe (ValueLocation FS)) (v : StoredValue FS)
                  → SameSlot (exec-store-via-resolved ml v ls) ls
ss-store-resolved ls nothing    v = refl
ss-store-resolved ls (just loc) v = ss-mem ls loc v

ss-store-suc-resolved : ∀ (ls : LocState FS) (ml : Maybe (ValueLocation FS)) (v : StoredValue FS)
                      → SameSlot (exec-store-suc-via-resolved ml v ls) ls
ss-store-suc-resolved ls nothing    v = refl
ss-store-suc-resolved ls (just loc) v = ss-mem ls (sucLoc loc) v

-- the two slot reads (`load-from-slot` / `worklist-pop`, and `restore-input`):
-- a register write on a hit, a halt on an empty cell
ss-from-slot : ∀ (ls : LocState FS) (alloc : AllocState {FS}) (mv : Maybe (StoredValue FS))
             → SameSlot (proj₁ (exec-load-from-slot-with-value mv ls alloc)) ls
ss-from-slot ls alloc (just v) = ss-write ls Output v
ss-from-slot ls alloc nothing  = refl

ss-restore : ∀ (ls : LocState FS) (alloc : AllocState {FS}) (mv : Maybe (StoredValue FS))
           → SameSlot (proj₁ (exec-restore-input-with-value mv ls alloc)) ls
ss-restore ls alloc (just v) = ss-write ls Input1 v
ss-restore ls alloc nothing  = refl

-- the flat machine's own control moves (`fpc` / `halted` only)
ss-jump : ∀ (mpc : Maybe ℕ) (fs : FlatState)
        → stackSlot (regs (floc (do-jump mpc fs))) ≡ stackSlot (regs (floc fs))
ss-jump (just pc') fs = refl
ss-jump nothing    fs = refl

ss-branch : ∀ (b : Bool) (m : ℕ) (prog : AbstractTrace) (fs : FlatState)
          → stackSlot (regs (floc (do-branch b m prog fs))) ≡ stackSlot (regs (floc fs))
ss-branch true  m prog fs = ss-jump (find-label prog m) fs
ss-branch false m prog fs = refl

-- Plan 0.63 step 2a: THE POINT OF PUTTING THE FRAME ON THE MARKER. A
-- return releases the body's frame via `leave-frame`, which is an
-- AllocState-only update — the REGISTER FILE, and with it `stackSlot`, is
-- untouched. Had the reservation been a resurrected `instr-dealloc-stack`,
-- `exec-abstract`'s `decrStackSlot` would have broken this invariant.
ss-ret : ∀ (r : List ℕ) (fs : FlatState)
       → stackSlot (regs (floc (do-ret r fs))) ≡ stackSlot (regs (floc fs))
ss-ret []           fs = refl
ss-ret (pc' ∷ rest) fs = refl

ss-lea-indexed : ∀ (ls : LocState FS) (ml : Maybe (ValueLocation FS)) (idx : ℕ)
               → SameSlot (exec-lea-indexed-via ml idx ls) ls
ss-lea-indexed ls nothing    idx = refl
ss-lea-indexed ls (just loc) idx = ss-write ls Input1 (SV-Ptr (offsetLoc loc idx))

ss-reg-op : ∀ (ls : LocState FS) (op : RegOp) → SameSlot (exec-reg-op op ls) ls
ss-reg-op ls scratch-one        = ss-write ls Scratch (SV-Tag 1)
ss-reg-op ls scratch-zero       = ss-write ls Scratch (SV-Tag 0)
ss-reg-op ls scratch-dec        = ss-write ls Scratch (sv-pred (readReg (regs ls) Scratch))
ss-reg-op ls scratch-load-count = ss-write ls Scratch (readReg (regs ls) Count)
ss-reg-op ls count-zero         = ss-write ls Count (SV-Tag 0)
ss-reg-op ls count-inc          = ss-write ls Count (sv-succ (readReg (regs ls) Count))

------------------------------------------------------------------------
-- THE LOOP, as a plain FUEL induction over the reified `exec-loop-run`
-- (2026-07-31). It takes "the body runner preserves the window" as a
-- hypothesis and never calls into the mutual block, so it is structural — this
-- is what retired the `{-# TERMINATING #-}` this proof used to carry.
------------------------------------------------------------------------
mutual
  ss-loop-run : ∀ (run : BodyRunner) (fuel : ℕ) (ls : LocState FS) (alloc : AllocState {FS})
              → (∀ ls' alloc' → SameSlot (proj₁ (run ls' alloc')) ls')
              → SameSlot (proj₁ (exec-loop-run run fuel ls alloc)) ls
  ss-loop-run run zero    ls alloc h = refl
  ss-loop-run run (suc n) ls alloc h with halted ls
  ... | true  = refl
  ... | false with readReg (regs ls) Scratch
  ...   | SV-Tag zero    = refl
  ...   | SV-Tag (suc m) = ss-loop-run-go run n ls alloc h
  ...   | SV-Ptr _       = ss-loop-run-go run n ls alloc h
  ...   | SV-Lit _ _     = ss-loop-run-go run n ls alloc h
  ...   | SV-Code _      = ss-loop-run-go run n ls alloc h

  -- one iteration: run the body, RE-ANCHOR the stack/frame, recurse on fuel.
  -- The re-anchoring touches `stackMem` and the frame fields, not `regs`, so
  -- the body's equation transports unchanged.
  ss-loop-run-go : ∀ (run : BodyRunner) (n : ℕ) (ls : LocState FS) (alloc : AllocState {FS})
                 → (∀ ls' alloc' → SameSlot (proj₁ (run ls' alloc')) ls')
                 → SameSlot (proj₁ (exec-loop-run run n
                     (loop-reanchor-loc ls (proj₁ (run ls alloc)))
                     (loop-reanchor-alloc alloc (proj₂ (run ls alloc))))) ls
  ss-loop-run-go run n ls alloc h =
    trans (ss-loop-run run n _ _ h) (h ls alloc)

------------------------------------------------------------------------
-- THE INDUCTION over the structured semantics.
------------------------------------------------------------------------
mutual
  ss-abstract : ∀ (i : AbstractInstr) (ls : LocState FS) (alloc : AllocState {FS})
              → FrameFreeI i
              → SameSlot (proj₁ (exec-abstract i ls alloc)) ls
  ss-abstract mov-to-output ls alloc ff = ss-write ls Output (readReg (regs ls) Input1)
  ss-abstract mov-to-input  ls alloc ff = ss-write ls Input1 (readReg (regs ls) Output)
  ss-abstract mov-output-to-input2 ls alloc ff = ss-write ls Input2 (readReg (regs ls) Output)
  ss-abstract mov-input2-to-output ls alloc ff = ss-write ls Output (readReg (regs ls) Input2)
  ss-abstract load-indirect ls alloc ff =
    ss-load-resolved ls Output (sv-as-loc (readReg (regs ls) Input1))
  ss-abstract load-indirect-suc ls alloc ff =
    ss-load-suc-resolved ls Output (sv-as-loc (readReg (regs ls) Input1))
  ss-abstract (load-from-slot slot) ls alloc ff =
    ss-from-slot ls alloc (readLoc ls (AtStack (current-frame alloc) slot))
  ss-abstract (store-at-slot slot) ls alloc ff =
    ss-mem ls (AtStack (current-frame alloc) slot) (readReg (regs ls) Output)
  ss-abstract store-indirect ls alloc ff =
    ss-store-resolved ls (sv-as-loc (readReg (regs ls) Input1)) (readReg (regs ls) Output)
  ss-abstract store-indirect-suc ls alloc ff =
    ss-store-suc-resolved ls (sv-as-loc (readReg (regs ls) Input1)) (readReg (regs ls) Output)
  ss-abstract (lea-slot slot) ls alloc ff =
    ss-write ls Output (SV-Ptr (AtStack (current-frame alloc) slot))
  ss-abstract (restore-input slot) ls alloc ff =
    ss-restore ls alloc (readLoc ls (AtStack (current-frame alloc) slot))
  ss-abstract (lea-indexed slot) ls alloc ff =
    ss-lea-indexed ls (slot-base (readLoc ls (AtStack (current-frame alloc) slot)))
                      (sv-tag-val (readReg (regs ls) Scratch))
  -- THE THREE WRITERS — ruled out by `FrameFreeI`, which is `⊥` on them.
  ss-abstract (instr-alloc-stack n)   ls alloc ()
  ss-abstract (instr-dealloc-stack n) ls alloc ()
  ss-abstract (instr-push-frame cap)  ls alloc ()
  ss-abstract instr-pop-frame         ls alloc ()
  ss-abstract (instr-reclaim-to n)  ls alloc ff = refl
  ss-abstract instr-call-closure    ls alloc ff = refl
  ss-abstract (worklist-init slot)  ls alloc ff = refl
  ss-abstract (worklist-push slot)  ls alloc ff =
    ss-mem ls (AtStack (current-frame alloc) slot) (readReg (regs ls) Output)
  ss-abstract (worklist-pop slot)   ls alloc ff =
    ss-from-slot ls alloc (readLoc ls (AtStack (current-frame alloc) slot))
  ss-abstract (worklist-check slot) ls alloc ff = refl
  -- a SigOp writes ONLY `Output` and `halted`
  ss-abstract (instr-sigop si) ls alloc ff =
    ss-write-halt ls Output (exec-sigop-output si ls) (exec-sigop-halts si ls)
  ss-abstract (instr-load-const p v)   ls alloc ff = ss-write ls Output (SV-Lit p v)
  ss-abstract (instr-load-code-addr n) ls alloc ff = ss-write ls Output (SV-Code n)
  ss-abstract instr-save-closure-reg   ls alloc ff = refl
  ss-abstract (instr-load-tag-lit n)   ls alloc ff = ss-write ls Output (SV-Tag n)
  -- `instr-case-on-tag` has NO PRODUCER since Plan 0.54 item 6 — `case`
  -- compiles to flat control, so this route is unreachable.
  ss-abstract (instr-case-on-tag f g)  ls alloc ()
  ss-abstract (instr-alloc-heap n)     ls alloc ff =
    ss-write ls Output
      (SV-Ptr (AtDynamic (proj₁ (AI.alloc-impl n (next-heap-ref alloc)))))
  -- `instr-loop` has NO PRODUCER either (2026-07-31) — a retired fossil, `⊥` in
  -- the predicate, so this route is unreachable rather than proved. The generic
  -- `ss-loop-run` above is kept: it is what a future structured loop would need,
  -- and it is the fuel induction that retired this proof's pragma.
  ss-abstract (instr-loop body)        ls alloc ()
  ss-abstract (instr-reg-op op)        ls alloc ff = ss-reg-op ls op
  ss-abstract (instr-ctrl c)           ls alloc ff = refl

  ss-trace : ∀ (t : AbstractTrace) (ls : LocState FS) (alloc : AllocState {FS})
           → FrameFreeT t
           → SameSlot (proj₁ (exec-trace t ls alloc)) ls
  ss-trace []       ls alloc ff = refl
  ss-trace (i ∷ is) ls alloc ff with halted ls
  ... | true  = refl
  ... | false = trans (ss-trace is (proj₁ (exec-abstract i ls alloc))
                                   (proj₂ (exec-abstract i ls alloc)) (proj₂ ff))
                      (ss-abstract i ls alloc (proj₁ ff))

  ss-case : ∀ (mv : Maybe (StoredValue FS)) (f g : AbstractTrace)
              (ls : LocState FS) (alloc : AllocState {FS})
          → FrameFreeT f → FrameFreeT g
          → SameSlot (proj₁ (exec-case-dispatch mv f g ls alloc)) ls
  ss-case (just (SV-Tag zero))    f g ls alloc fff ffg = ss-trace f ls alloc fff
  ss-case (just (SV-Tag (suc _))) f g ls alloc fff ffg = ss-trace g ls alloc ffg
  ss-case (just (SV-Ptr _))       f g ls alloc fff ffg = refl
  ss-case (just (SV-Lit _ _))     f g ls alloc fff ffg = refl
  ss-case (just (SV-Code _))      f g ls alloc fff ffg = refl
  ss-case nothing                 f g ls alloc fff ffg = refl

------------------------------------------------------------------------
-- Lifted to the FLAT machine. The control cases move `fpc`/`halted` only; the
-- straight-line cases are `ss-abstract`; the frame-moving instructions are
-- `⊥`-elim (they are exactly the ones `FrameFreeI` excludes).
------------------------------------------------------------------------
flat-stack-slot : ∀ (i : AbstractInstr) (prog : AbstractTrace) (fs : FlatState)
                → FrameFreeI i
                → stackSlot (regs (floc (flat-exec-instr i prog fs)))
                    ≡ stackSlot (regs (floc fs))
flat-stack-slot (instr-ctrl (c-label m))               prog fs ff = refl
flat-stack-slot (instr-ctrl (c-thunk m b))             prog fs ff = refl
flat-stack-slot (instr-ctrl (c-ret b))                 prog fs ff = ss-ret (fret fs) fs
flat-stack-slot (instr-ctrl (c-jmp m))                 prog fs ff = ss-jump (find-label prog m) fs
flat-stack-slot (instr-ctrl (c-branch-scratch-zero m)) prog fs ff =
  ss-branch (sv-is-zero (readReg (regs (floc fs)) Scratch)) m prog fs
flat-stack-slot (instr-ctrl (c-branch-tag-zero m))     prog fs ff =
  ss-branch (tag-zf (flat-read-tag (floc fs))) m prog fs
flat-stack-slot (instr-alloc-stack n)   prog fs ()
flat-stack-slot (instr-dealloc-stack n) prog fs ()
flat-stack-slot (instr-push-frame cap)  prog fs ()
flat-stack-slot instr-pop-frame         prog fs ()
flat-stack-slot mov-to-output            prog fs ff = ss-abstract mov-to-output (floc fs) (falloc fs) ff
flat-stack-slot mov-to-input             prog fs ff = ss-abstract mov-to-input (floc fs) (falloc fs) ff
flat-stack-slot mov-output-to-input2     prog fs ff = ss-abstract mov-output-to-input2 (floc fs) (falloc fs) ff
flat-stack-slot mov-input2-to-output     prog fs ff = ss-abstract mov-input2-to-output (floc fs) (falloc fs) ff
flat-stack-slot load-indirect            prog fs ff = ss-abstract load-indirect (floc fs) (falloc fs) ff
flat-stack-slot load-indirect-suc        prog fs ff = ss-abstract load-indirect-suc (floc fs) (falloc fs) ff
flat-stack-slot (load-from-slot k)       prog fs ff = ss-abstract (load-from-slot k) (floc fs) (falloc fs) ff
flat-stack-slot (store-at-slot k)        prog fs ff = ss-abstract (store-at-slot k) (floc fs) (falloc fs) ff
flat-stack-slot store-indirect           prog fs ff = ss-abstract store-indirect (floc fs) (falloc fs) ff
flat-stack-slot store-indirect-suc       prog fs ff = ss-abstract store-indirect-suc (floc fs) (falloc fs) ff
flat-stack-slot (lea-slot k)             prog fs ff = ss-abstract (lea-slot k) (floc fs) (falloc fs) ff
flat-stack-slot (restore-input k)        prog fs ff = ss-abstract (restore-input k) (floc fs) (falloc fs) ff
flat-stack-slot (lea-indexed k)          prog fs ff = ss-abstract (lea-indexed k) (floc fs) (falloc fs) ff
flat-stack-slot (instr-reclaim-to k)     prog fs ff = ss-abstract (instr-reclaim-to k) (floc fs) (falloc fs) ff
flat-stack-slot instr-call-closure       prog fs ff = ss-abstract instr-call-closure (floc fs) (falloc fs) ff
flat-stack-slot (worklist-init k)        prog fs ff = ss-abstract (worklist-init k) (floc fs) (falloc fs) ff
flat-stack-slot (worklist-push k)        prog fs ff = ss-abstract (worklist-push k) (floc fs) (falloc fs) ff
flat-stack-slot (worklist-pop k)         prog fs ff = ss-abstract (worklist-pop k) (floc fs) (falloc fs) ff
flat-stack-slot (worklist-check k)       prog fs ff = ss-abstract (worklist-check k) (floc fs) (falloc fs) ff
flat-stack-slot (instr-sigop si)         prog fs ff = ss-abstract (instr-sigop si) (floc fs) (falloc fs) ff
flat-stack-slot (instr-load-const p v)   prog fs ff = ss-abstract (instr-load-const p v) (floc fs) (falloc fs) ff
flat-stack-slot (instr-load-code-addr k) prog fs ff = ss-abstract (instr-load-code-addr k) (floc fs) (falloc fs) ff
flat-stack-slot instr-save-closure-reg   prog fs ff = ss-abstract instr-save-closure-reg (floc fs) (falloc fs) ff
flat-stack-slot (instr-load-tag-lit k)   prog fs ff = ss-abstract (instr-load-tag-lit k) (floc fs) (falloc fs) ff
flat-stack-slot (instr-case-on-tag f g)  prog fs ff = ss-abstract (instr-case-on-tag f g) (floc fs) (falloc fs) ff
flat-stack-slot (instr-alloc-heap k)     prog fs ff = ss-abstract (instr-alloc-heap k) (floc fs) (falloc fs) ff
flat-stack-slot (instr-loop body)        prog fs ()
flat-stack-slot (instr-reg-op op)        prog fs ff = ss-abstract (instr-reg-op op) (floc fs) (falloc fs) ff
