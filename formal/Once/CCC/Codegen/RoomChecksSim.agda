-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.RoomChecksSim — the room checks are transparent (D371).
--
-- Plan 0.123 A.4 step 5. The flat machine running `room-checks t` follows the
-- flat machine running `t`: a check is a no-op step, and every other step is
-- the same instruction at the mapped index (`RoomChecksFacts`). The state
-- relation is a LIFT: the image-with-checks state is the original one with its
-- program counter, return stack and link register moved by the index map —
-- memory, frames and the closure register are literally the same.
--
--   * `ret-map`: a return address `suc c` (one past a call at `c`) becomes
--     `suc (φ t c)`, one past the call in the image with checks — where the
--     call's check sits, so a return runs that check first;
--   * `PcRel i p`: `p` is `φ t i`, or the check just before it.
------------------------------------------------------------------------

module Once.CCC.Codegen.RoomChecksSim where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-room)
open import Once.CCC.Codegen.RoomChecks using (boundary?; stretch; checks; room-checks; max-entry)
open import Once.CCC.Codegen.RoomChecksFacts using (ψ; φ; bump; module RoomFacts)

module RoomSim {FS : FrameSemantics} (t : AbstractTrace) where
  open FlatMachine {FS}
  open RoomFacts {FS}

  P′ : AbstractTrace
  P′ = room-checks t

  -- where a return lands in the image with checks
  ret-map : ℕ → ℕ
  ret-map zero    = φ t zero
  ret-map (suc c) = suc (φ t c)

  -- THE LIFT: the same machine, its control moved by the map
  lift : FlatState → ℕ → FlatState
  lift fs p = record fs { fret = map ret-map (fret fs) ; flink = mmap ret-map (flink fs) ; fpc = p }

  -- the image-with-checks pc `p` stands for the original pc `i`: at its image,
  -- or on the check just before it
  PcRel : ℕ → ℕ → Set
  PcRel i p = (p ≡ φ t i) ⊎ ((suc p ≡ φ t i) × Σ ℕ (λ k → fetch P′ p ≡ just (instr-room k)))

  private
    -- past an instruction `x`: one place further, or two with `x`'s check between
    after-x : ∀ (c : ℕ) (x : AbstractInstr) → fetch t c ≡ just x
            → (b : Bool) → boundary? x ≡ b → PcRel (suc c) (suc (φ t c))
    after-x c x e false bf =
      inj₁ (cong suc (sym (trans (ψ-next t c e) (cong (λ z → suc (bump z (ψ t c))) bf))))
    after-x c x e true  bt =
      inj₂ ( cong suc (sym (trans (ψ-next t c e) (cong (λ z → suc (bump z (ψ t c))) bt)))
           , stretch (max-entry t) (Data.List.drop (suc c) t)
           , check-at (max-entry t) t c e bt )

  -- ONE PLACE ON: after the instruction at `c` (or a return to `suc c`), the
  -- image with checks is at `suc (φ t c)` — which stands for `suc c`.
  pcRel-after : ∀ (c : ℕ) → PcRel (suc c) (suc (φ t c))
  pcRel-after c with fetch t c in e
  ... | just x  = after-x c x e (boundary? x) refl
  ... | nothing = inj₁ (cong suc (sym (ψ-next-nothing t c e)))

  -- …so a return address maps to a pc that stands for it.
  pcRel-ret : ∀ (r : ℕ) → PcRel r (ret-map r)
  pcRel-ret zero    = inj₁ refl
  pcRel-ret (suc c) = pcRel-after c
