-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNextSlot — the frame-discipline invariant
-- (Plan 0.36 task #8, value side): `exec-flat` preserves `next-slot`
-- (the stack-frame frontier) for any trace built from "slot-stable"
-- instructions.
--
-- This is the GENERAL codegen invariant the cata value side reduces to:
-- the algebra's `value-realized` IH requires `next-slot ≡ 0` (a fresh
-- frame), and the cata loop needs that to survive each layer. The cata
-- SCAFFOLD preserves next-slot (build-layer / descend, shown elsewhere);
-- here we close the loop on the ALGEBRA: only `instr-alloc-stack` and
-- `instr-reclaim-to` change `next-slot`, and `ir-to-trace` emits NEITHER
-- (heap-only pivot; `instr-loop` is likewise a retired fossil). So the
-- algebra's trace is slot-stable and its `exec-flat` preserves next-slot.
--
-- `SlotStable i` is ⊤ except for the three next-slot-touching / fossil
-- instructions; `flat-keeps-next-slot` is the per-instruction enumeration
-- (every other instruction leaves the allocator's `next-slot` field
-- alone — most leave the whole allocator, alloc-heap bumps only
-- next-heap-ref, the loads reduce through their Maybe to the same alloc);
-- `exec-flat-keeps-next-slot` lifts it over a slot-stable trace by fuel
-- induction.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNextSlot where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Allocation using (current-frame; next-slot; AllocState)
open import Once.CCC.Machine.SMCore
  using (halted; regs; readReg; Scratch; AtStack; AbstractInstr; AbstractTrace; LocState; StoredValue;
         SV-Tag; SV-Ptr; SV-Lit; SV-Code;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero;
         c-thunk; c-ret;
         load-from-slot; restore-input; instr-alloc-stack; instr-reclaim-to; instr-loop;
         instr-case-on-tag;
         mov-to-output; mov-to-input; mov-output-to-input2; mov-input2-to-output;
         load-indirect; load-indirect-suc; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; lea-indexed; instr-dealloc-stack; instr-push-frame; instr-pop-frame;
         instr-call-closure; worklist-init; worklist-push; worklist-pop; worklist-check;
         instr-sigop; instr-load-const; instr-load-code-addr; instr-save-closure-reg;
         instr-load-tag-lit; instr-alloc-heap; instr-reg-op;
         module MemOps; module AbstractExec)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Data.Product using (proj₂)

module CataNextSlot {FS : FrameSemantics} where
  open FlatMachine {FS}
  open MemOps {FS} using (readLoc)
  open AbstractExec {FS} using (exec-abstract; exec-trace; exec-case-dispatch; case-tag-at;
                                exec-load-from-slot-with-value; exec-restore-input-with-value)

  -- Maybe-helper allocator preservation (plain `refl` per case — NO `with`;
  -- proj₂ of these helpers is the input allocator in both branches).
  elfs-alloc : ∀ (m : Maybe (StoredValue FS)) (s : LocState FS) (alloc : AllocState {FS})
    → proj₂ (exec-load-from-slot-with-value m s alloc) ≡ alloc
  elfs-alloc (just v) s alloc = refl
  elfs-alloc nothing  s alloc = refl

  eris-alloc : ∀ (m : Maybe (StoredValue FS)) (s : LocState FS) (alloc : AllocState {FS})
    → proj₂ (exec-restore-input-with-value m s alloc) ≡ alloc
  eris-alloc (just v) s alloc = refl
  eris-alloc nothing  s alloc = refl

  -- Slot-stable = does NOT change `next-slot`. Only alloc-stack (bumps),
  -- reclaim-to (sets) do; instr-loop is a retired fossil (its exec-loop
  -- would restore next-slot, but ir-to-trace never emits it, so we exclude
  -- it rather than carry the exec-loop induction).
  -- 2026-07-31: the trace level is SPELLED OUT (`SlotStableT`) rather than
  -- routed through `AllI SlotStable`. Going through a predicate APPLICATION hid
  -- the structural decrease from foetus and cost a `{-# TERMINATING #-}` — a
  -- postulate in disguise (D062). Written mutually it is structural.
  mutual
    SlotStable : AbstractInstr → Set
    SlotStable (instr-alloc-stack _)    = ⊥
    SlotStable (instr-reclaim-to _)     = ⊥
    SlotStable (instr-loop _)           = ⊥   -- retired fossil (not emitted)
    -- case-on-tag dispatches to `exec-trace` on a sub-trace, so it preserves
    -- next-slot iff its sub-traces do.
    SlotStable (instr-case-on-tag f g)  = SlotStableT f × SlotStableT g
    {-# CATCHALL #-}
    SlotStable _                        = ⊤

    SlotStableT : AbstractTrace → Set
    SlotStableT []       = ⊤
    SlotStableT (i ∷ is) = SlotStable i × SlotStableT is

  -- exec-abstract-level next-slot preservation. Most instructions return the
  -- same allocator (alloc-heap bumps only next-heap-ref); the memory loads
  -- reduce through their Maybe to it.
  --
  -- 2026-07-31: case-on-tag recurses through an EXPLICIT mutual pair
  -- (`trace-keeps-next-slot` / `case-keeps-next-slot`) instead of the
  -- higher-order `exec-abstract-case-invariant`. Passing the per-instruction
  -- fact as a function ARGUMENT hid the structural decrease from foetus and
  -- cost the second `{-# TERMINATING #-}`; spelled out, `f`/`g` are visibly
  -- subterms of `instr-case-on-tag f g`.
  mutual
    abstract-keeps-next-slot : ∀ (i : AbstractInstr) → SlotStable i
      → ∀ (s : LocState FS) (alloc : AllocState {FS})
      → next-slot (proj₂ (exec-abstract i s alloc)) ≡ next-slot alloc
    abstract-keeps-next-slot (instr-ctrl _)        _ s alloc = refl
    abstract-keeps-next-slot mov-to-output         _ s alloc = refl
    abstract-keeps-next-slot mov-to-input          _ s alloc = refl
    abstract-keeps-next-slot mov-output-to-input2  _ s alloc = refl
    abstract-keeps-next-slot mov-input2-to-output  _ s alloc = refl
    abstract-keeps-next-slot load-indirect         _ s alloc = refl
    abstract-keeps-next-slot load-indirect-suc     _ s alloc = refl
    abstract-keeps-next-slot (store-at-slot k)     _ s alloc = refl
    abstract-keeps-next-slot store-indirect        _ s alloc = refl
    abstract-keeps-next-slot store-indirect-suc    _ s alloc = refl
    abstract-keeps-next-slot (lea-slot k)          _ s alloc = refl
    abstract-keeps-next-slot (lea-indexed k)       _ s alloc = refl
    abstract-keeps-next-slot (instr-dealloc-stack n) _ s alloc = refl
    abstract-keeps-next-slot (instr-push-frame c)  _ s alloc = refl
    abstract-keeps-next-slot instr-pop-frame       _ s alloc = refl
    abstract-keeps-next-slot instr-call-closure    _ s alloc = refl
    abstract-keeps-next-slot (worklist-init k)     _ s alloc = refl
    abstract-keeps-next-slot (worklist-push k)     _ s alloc = refl
    abstract-keeps-next-slot (worklist-check k)    _ s alloc = refl
    abstract-keeps-next-slot (instr-sigop si)      _ s alloc = refl
    abstract-keeps-next-slot (instr-load-const p v) _ s alloc = refl
    abstract-keeps-next-slot (instr-load-code-addr n) _ s alloc = refl
    abstract-keeps-next-slot instr-save-closure-reg _ s alloc = refl
    abstract-keeps-next-slot (instr-load-tag-lit n) _ s alloc = refl
    abstract-keeps-next-slot (instr-alloc-heap n)  _ s alloc = refl
    abstract-keeps-next-slot (instr-reg-op op)     _ s alloc = refl
    abstract-keeps-next-slot (worklist-pop slot)   _ s alloc =
      cong next-slot (elfs-alloc (readLoc s (AtStack (current-frame alloc) slot)) s alloc)
    abstract-keeps-next-slot (load-from-slot slot)  _ s alloc =
      cong next-slot (elfs-alloc (readLoc s (AtStack (current-frame alloc) slot)) s alloc)
    abstract-keeps-next-slot (restore-input slot)   _ s alloc =
      cong next-slot (eris-alloc (readLoc s (AtStack (current-frame alloc) slot)) s alloc)
    abstract-keeps-next-slot (instr-alloc-stack n) ()
    abstract-keeps-next-slot (instr-reclaim-to n)  ()
    abstract-keeps-next-slot (instr-loop body)     ()
    abstract-keeps-next-slot (instr-case-on-tag f g) (aft , agt) s alloc =
      case-keeps-next-slot (case-tag-at s) f g aft agt s alloc

    trace-keeps-next-slot : ∀ (t : AbstractTrace) → SlotStableT t
      → ∀ (s : LocState FS) (alloc : AllocState {FS})
      → next-slot (proj₂ (exec-trace t s alloc)) ≡ next-slot alloc
    trace-keeps-next-slot []       ss        s alloc = refl
    trace-keeps-next-slot (i ∷ is) (si , ss) s alloc with halted s
    ... | true  = refl
    ... | false =
      trans (trace-keeps-next-slot is ss (proj₁ (exec-abstract i s alloc))
                                         (proj₂ (exec-abstract i s alloc)))
            (abstract-keeps-next-slot i si s alloc)

    case-keeps-next-slot : ∀ (mv : Maybe (StoredValue FS)) (f g : AbstractTrace)
      → SlotStableT f → SlotStableT g
      → ∀ (s : LocState FS) (alloc : AllocState {FS})
      → next-slot (proj₂ (exec-case-dispatch mv f g s alloc)) ≡ next-slot alloc
    case-keeps-next-slot (just (SV-Tag zero))    f g sf sg s alloc = trace-keeps-next-slot f sf s alloc
    case-keeps-next-slot (just (SV-Tag (suc _))) f g sf sg s alloc = trace-keeps-next-slot g sg s alloc
    case-keeps-next-slot (just (SV-Ptr _))       f g sf sg s alloc = refl
    case-keeps-next-slot (just (SV-Lit _ _))     f g sf sg s alloc = refl
    case-keeps-next-slot (just (SV-Code _))      f g sf sg s alloc = refl
    case-keeps-next-slot nothing                 f g sf sg s alloc = refl

  -- Per-instruction: a slot-stable instruction's `flat-exec-instr`
  -- preserves `next-slot`. Control flow touches only `fpc`/`halted`
  -- (branches reduce both ways to a frame-preserving state); the straight
  -- instructions thread `exec-abstract`, whose `proj₂` is the same
  -- allocator (alloc-heap only bumps next-heap-ref; load-from-slot /
  -- restore-input reduce through their Maybe to the same allocator).
  flat-keeps-next-slot : ∀ (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr)
    → SlotStable i
    → next-slot (falloc (flat-exec-instr i prog fs)) ≡ next-slot (falloc fs)
  flat-keeps-next-slot prog fs (instr-ctrl (c-label _)) _ = refl
  -- Plan 0.63: the closure markers MOVE THE FRAME, but a frame move touches
  -- only `current-frame`/`saved-frames` — `next-slot` rides through it
  -- (0.61's `leave-frame-next-slot`; `enter-frame` is a plain record
  -- update, so its side is `refl`).
  flat-keeps-next-slot prog fs (instr-ctrl (c-thunk _ b)) _ = refl
  flat-keeps-next-slot prog fs (instr-ctrl (c-ret b)) _
    with fret fs
  ... | []     = leave-frame-next-slot (falloc fs)
  ... | _ ∷ _  = leave-frame-next-slot (falloc fs)
  flat-keeps-next-slot prog fs (instr-ctrl (c-jmp n)) _
    with find-label prog n
  ... | just _  = refl
  ... | nothing = refl
  flat-keeps-next-slot prog fs (instr-ctrl (c-branch-scratch-zero n)) _
    with sv-is-zero (readReg (regs (floc fs)) Scratch)
  ... | false = refl
  ... | true with find-label prog n
  ...   | just _  = refl
  ...   | nothing = refl
  flat-keeps-next-slot prog fs (instr-ctrl (c-branch-tag-zero n)) _
    with tag-zf (flat-read-tag (floc fs))
  ... | false = refl
  ... | true with find-label prog n
  ...   | just _  = refl
  ...   | nothing = refl
  flat-keeps-next-slot prog fs (load-from-slot slot) _
    with readLoc (floc fs) (AtStack (current-frame (falloc fs)) slot)
  ... | just _  = refl
  ... | nothing = refl
  flat-keeps-next-slot prog fs (restore-input slot) _
    with readLoc (floc fs) (AtStack (current-frame (falloc fs)) slot)
  ... | just _  = refl
  ... | nothing = refl
  flat-keeps-next-slot prog fs (worklist-pop slot) _
    with readLoc (floc fs) (AtStack (current-frame (falloc fs)) slot)
  ... | just _  = refl
  ... | nothing = refl
  flat-keeps-next-slot prog fs (instr-alloc-stack n)   ()
  flat-keeps-next-slot prog fs (instr-reclaim-to n)    ()
  flat-keeps-next-slot prog fs (instr-loop body)       ()
  -- non-ctrl, so flat-exec-instr = flat-step-straight ⇒ falloc = proj₂
  -- (exec-abstract …); delegate to the exec-abstract-level fact.
  flat-keeps-next-slot prog fs (instr-case-on-tag f g) ss =
    abstract-keeps-next-slot (instr-case-on-tag f g) ss (floc fs) (falloc fs)
  -- the rest leave `next-slot` alone (reg/heap writes, `exec-abstract`
  -- returns the same allocator — alloc-heap bumps only next-heap-ref).
  flat-keeps-next-slot prog fs mov-to-output           _ = refl
  flat-keeps-next-slot prog fs mov-to-input            _ = refl
  flat-keeps-next-slot prog fs mov-output-to-input2    _ = refl
  flat-keeps-next-slot prog fs mov-input2-to-output    _ = refl
  flat-keeps-next-slot prog fs load-indirect           _ = refl
  flat-keeps-next-slot prog fs load-indirect-suc       _ = refl
  flat-keeps-next-slot prog fs (store-at-slot k)       _ = refl
  flat-keeps-next-slot prog fs store-indirect          _ = refl
  flat-keeps-next-slot prog fs store-indirect-suc      _ = refl
  flat-keeps-next-slot prog fs (lea-slot k)            _ = refl
  flat-keeps-next-slot prog fs (lea-indexed k)         _ = refl
  -- Plan 0.61: these MOVE THE FRAME in the flat machine; the move touches only
  -- the frame fields, so `next-slot` still rides through.
  flat-keeps-next-slot prog fs (instr-dealloc-stack n) _ = leave-frame-next-slot (falloc fs)
  flat-keeps-next-slot prog fs (instr-push-frame c)    _ = refl
  flat-keeps-next-slot prog fs instr-pop-frame         _ = leave-frame-next-slot (falloc fs)
  flat-keeps-next-slot prog fs instr-call-closure      _ = refl
  flat-keeps-next-slot prog fs (worklist-init k)       _ = refl
  flat-keeps-next-slot prog fs (worklist-push k)       _ = refl
  flat-keeps-next-slot prog fs (worklist-check k)      _ = refl
  flat-keeps-next-slot prog fs (instr-sigop si)        _ = refl
  flat-keeps-next-slot prog fs (instr-load-const p v)  _ = refl
  flat-keeps-next-slot prog fs (instr-load-code-addr n) _ = refl
  flat-keeps-next-slot prog fs instr-save-closure-reg  _ = refl
  flat-keeps-next-slot prog fs (instr-load-tag-lit n)  _ = refl
  flat-keeps-next-slot prog fs (instr-alloc-heap n)    _ = refl
  flat-keeps-next-slot prog fs (instr-reg-op op)       _ = refl

  -- The trace-level predicate: every instruction is slot-stable.
  AllSlotStable : AbstractTrace → Set
  AllSlotStable = All SlotStable

  -- exec-flat over a slot-stable trace preserves next-slot — the frame
  -- -discipline invariant. The fuel induction lives in `Flat.agda`'s
  -- `exec-flat-invariant` (where the recursive `exec-flat`/`fetch` reduce;
  -- `open FlatMachine {FS}` makes them opaque here). We instantiate the
  -- projection `next-slot ∘ falloc`, the predicate `SlotStable`, and the
  -- per-instruction fact `flat-keeps-next-slot`; the off-end halt changes
  -- only `floc`, so it preserves `next-slot` (`refl`). Since the cata
  -- algebra's `ir-to-trace` emits only slot-stable instructions, its
  -- `exec-flat` leaves `next-slot` fixed — the algebra IH's `next-slot ≡ 0`
  -- precondition survives every cata layer.
  exec-flat-keeps-next-slot :
    ∀ (prog : AbstractTrace) → AllSlotStable prog → ∀ (n : ℕ) (fs : FlatState)
    → next-slot (falloc (exec-flat n prog fs)) ≡ next-slot (falloc fs)
  exec-flat-keeps-next-slot prog ss n fs =
    exec-flat-invariant (λ s → next-slot (falloc s)) SlotStable
      (λ i p f' si → flat-keeps-next-slot p f' i si) (λ _ → refl) prog ss n fs
