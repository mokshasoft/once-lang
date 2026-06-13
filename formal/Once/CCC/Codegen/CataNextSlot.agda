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

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Allocation using (current-frame; next-slot)
open import Once.CCC.Machine.SMCore
  using (halted; regs; readReg; Scratch; AtStack; AbstractInstr; AbstractTrace;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero;
         load-from-slot; restore-input; instr-alloc-stack; instr-reclaim-to; instr-loop;
         instr-case-on-tag;
         mov-to-output; mov-to-input; mov-output-to-input2; mov-input2-to-output;
         load-indirect; load-indirect-suc; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; lea-indexed; instr-dealloc-stack; instr-push-frame; instr-pop-frame;
         instr-call-closure; worklist-init; worklist-push; worklist-pop; worklist-check;
         instr-sigop; instr-load-const; instr-load-code-addr; instr-save-closure-reg;
         instr-load-tag-lit; instr-alloc-heap; instr-reg-op;
         module MemOps)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module CataNextSlot {FS : FrameSemantics} where
  open FlatMachine {FS}
  open MemOps {FS} using (readLoc)

  -- Slot-stable = does NOT change `next-slot`. Only alloc-stack (bumps),
  -- reclaim-to (sets) do; instr-loop is a retired fossil (its exec-loop
  -- would restore next-slot, but ir-to-trace never emits it, so we exclude
  -- it rather than carry the exec-loop induction).
  SlotStable : AbstractInstr → Set
  SlotStable (instr-alloc-stack _)    = ⊥
  SlotStable (instr-reclaim-to _)     = ⊥
  SlotStable (instr-loop _)           = ⊥   -- retired fossil (not emitted)
  SlotStable (instr-case-on-tag _ _)  = ⊥   -- runs sub-traces; needs the
                                            -- mutual-recursive treatment
  SlotStable _                        = ⊤

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
  flat-keeps-next-slot prog fs (instr-case-on-tag f g) ()
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
  flat-keeps-next-slot prog fs (instr-dealloc-stack n) _ = refl
  flat-keeps-next-slot prog fs (instr-push-frame c)    _ = refl
  flat-keeps-next-slot prog fs instr-pop-frame         _ = refl
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
