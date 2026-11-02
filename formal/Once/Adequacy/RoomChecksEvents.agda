-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.RoomChecksEvents — the room checks emit nothing (D371).
--
-- Plan 0.123 A.4 step 5. What the flat run of `room-checks t` shows, from a
-- lifted state, is what the flat run of `t` shows: at every fuel `n` of the
-- original there is a fuel `m` of the image with checks at which the two
-- `flat-events` are EQUAL. A check is one more step that emits no event and
-- moves on (`[] ▹ o` is `o`); every other step is the original's
-- (`RoomChecksSim.step-lift`), with the same state, hence the same events.
------------------------------------------------------------------------

module Once.Adequacy.RoomChecksEvents where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-room; module LocState)
open import Once.CCC.Codegen.RoomChecksFacts using (φ; module RoomFacts)
open import Once.CCC.Codegen.RoomChecksSim using (module RoomSim)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)

module RoomEvents {FS : FrameSemantics} (t : AbstractTrace) where
  open FlatMachine {FS}
  open RoomFacts {FS} using (fetch-room)
  open RoomSim {FS} t using (P′; lift; PcRel; step-lift)
  open FlatEventTrace {FS} using (flat-events; flat-events-step; flat-events-fetch; event-of)

  -- at the image of `fs`'s pc, and at any pc that stands for it
  ev-img : ∀ (n : ℕ) (fs : FlatState)
         → Σ ℕ (λ m → flat-events m P′ (lift fs (φ t (fpc fs))) ≡ flat-events n t fs)
  ev-rel : ∀ (n : ℕ) (fs : FlatState) (p : ℕ) → PcRel (fpc fs) p
         → Σ ℕ (λ m → flat-events m P′ (lift fs p) ≡ flat-events n t fs)

  private
    -- the original's fetch, from the image's: the same instruction (or none)
    ev-fetch : ∀ (n : ℕ) (fs : FlatState) (mi : Maybe AbstractInstr) → fetch t (fpc fs) ≡ mi
             → Σ ℕ (λ m → flat-events-fetch mi m P′ (lift fs (φ t (fpc fs))) ≡ flat-events-fetch mi n t fs)
    ev-fetch n fs nothing  _ = 0 , refl
    ev-fetch n fs (just i) _ with step-lift fs i
    ... | p , e , pr with ev-rel n (flat-exec-instr i t fs) p pr
    ...   | m , em = m , cong (event-of i fs ▹_) (trans (cong (flat-events m P′) e) em)
      where open import Once.IR.Semantics.Out using (_▹_)

    ev-step : ∀ (n : ℕ) (fs : FlatState) (h : Bool) → LocState.halted (floc fs) ≡ h
            → Σ ℕ (λ m → flat-events-step h m P′ (lift fs (φ t (fpc fs))) ≡ flat-events-step h n t fs)
    ev-step n fs true  _ = 0 , refl
    ev-step n fs false _ with ev-fetch n fs (fetch t (fpc fs)) refl
    ... | m , e = m , trans (cong (λ z → flat-events-fetch z m P′ (lift fs (φ t (fpc fs)))) (fetch-room t (fpc fs))) e

  ev-img zero    fs = 0 , refl
  ev-img (suc n) fs with ev-step n fs (LocState.halted (floc fs)) refl
  ... | m , e = suc m , e

  private
    -- on a check: one more step, emitting nothing, to the image
    ev-chk : ∀ (n : ℕ) (fs : FlatState) (p : ℕ) → suc p ≡ φ t (fpc fs)
           → ∀ (k : ℕ) → fetch P′ p ≡ just (instr-room k)
           → (h : Bool) → LocState.halted (floc fs) ≡ h
           → Σ ℕ (λ m → flat-events-step h m P′ (lift fs p) ≡ flat-events-step h n t fs)
    ev-chk n fs p sp k fk true  _  = 0 , refl
    ev-chk n fs p sp k fk false eh with ev-img (suc n) fs
    ... | m , e =
      m , trans (cong (λ z → flat-events-fetch z m P′ (lift fs p)) fk)
                (trans (cong (λ q → flat-events m P′ (lift fs q)) sp)
                       (trans e (cong (λ h → flat-events-step h n t fs) eh)))

  ev-rel n fs p (inj₁ refl) = ev-img n fs
  ev-rel zero    fs p (inj₂ _) = 0 , refl
  ev-rel (suc n) fs p (inj₂ (sp , k , fk)) with ev-chk n fs p sp k fk (LocState.halted (floc fs)) refl
  ... | m , e = suc m , e
