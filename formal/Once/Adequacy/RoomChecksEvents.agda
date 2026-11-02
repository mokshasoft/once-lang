-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.RoomChecksEvents — the room checks emit nothing (D371).
--
-- Plan 0.123 A.4 step 5. What the flat run of `room-checks t` shows, from a
-- lifted state, is what the flat run of `t` shows: at every fuel `n` of the
-- original there is a fuel `m` of the image with checks at which the two
-- `flat-events` are EQUAL, and so are the two control-step counts
-- (`flat-ctrls`) — one fuel for both, because the per-arch agreement
-- (`AgreeAt`) relates them at one fuel. A check is one more step that emits no
-- event and counts no control step (`ctrl-of (instr-room _) = 0`); every other
-- step is the original's (`RoomChecksSim.step-lift`), with the same state.
------------------------------------------------------------------------

module Once.Adequacy.RoomChecksEvents where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-room; module LocState)
open import Once.CCC.Codegen.RoomChecksFacts using (φ; module RoomFacts)
open import Once.CCC.Codegen.RoomChecksSim using (module RoomSim)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open import Once.IR.Semantics.Out using (_▹_)

module RoomEvents {FS : FrameSemantics} (t : AbstractTrace) where
  open FlatMachine {FS}
  open RoomFacts {FS} using (fetch-room)
  open RoomSim {FS} t using (P′; lift; PcRel; step-lift)
  open FlatEventTrace {FS}
    using (flat-events; flat-events-step; flat-events-fetch; event-of
          ; flat-ctrls; flat-ctrls-step; flat-ctrls-fetch; ctrl-of)

  -- the two runs show the same at fuels `m` and `n`
  Same : ℕ → FlatState → ℕ → FlatState → Set
  Same m X n fs = (flat-events m P′ X ≡ flat-events n t fs) × (flat-ctrls m P′ X ≡ flat-ctrls n t fs)

  -- at the image of `fs`'s pc, and at any pc that stands for it
  ev-img : ∀ (n : ℕ) (fs : FlatState) → Σ ℕ (λ m → Same m (lift fs (φ t (fpc fs))) n fs)
  ev-rel : ∀ (n : ℕ) (fs : FlatState) (p : ℕ) → PcRel (fpc fs) p → Σ ℕ (λ m → Same m (lift fs p) n fs)

  private
    -- the original's fetch, from the image's: the same instruction (or none)
    ev-fetch : ∀ (n : ℕ) (fs : FlatState) (mi : Maybe AbstractInstr)
             → Σ ℕ (λ m → (flat-events-fetch mi m P′ (lift fs (φ t (fpc fs))) ≡ flat-events-fetch mi n t fs)
                        × (flat-ctrls-fetch mi m P′ (lift fs (φ t (fpc fs))) ≡ flat-ctrls-fetch mi n t fs))
    ev-fetch n fs nothing = 0 , refl , refl
    ev-fetch n fs (just i) with step-lift fs i
    ... | p , e , pr with ev-rel n (flat-exec-instr i t fs) p pr
    ...   | m , ee , ec =
      m , cong (event-of i fs ▹_) (trans (cong (flat-events m P′) e) ee)
        , cong (ctrl-of i +_) (trans (cong (flat-ctrls m P′) e) ec)

    ev-step : ∀ (n : ℕ) (fs : FlatState) (h : Bool) → LocState.halted (floc fs) ≡ h
            → Σ ℕ (λ m → (flat-events-step h m P′ (lift fs (φ t (fpc fs))) ≡ flat-events-step h n t fs)
                       × (flat-ctrls-step h m P′ (lift fs (φ t (fpc fs))) ≡ flat-ctrls-step h n t fs))
    ev-step n fs true  _ = 0 , refl , refl
    ev-step n fs false _ with ev-fetch n fs (fetch t (fpc fs))
    ... | m , ee , ec =
      m , trans (cong (λ z → flat-events-fetch z m P′ (lift fs (φ t (fpc fs)))) (fetch-room t (fpc fs))) ee
        , trans (cong (λ z → flat-ctrls-fetch z m P′ (lift fs (φ t (fpc fs)))) (fetch-room t (fpc fs))) ec


  -- on a check: one more step, emitting nothing and counting nothing, to the
  -- image — given what the image shows (not recursive: `ev-rel` supplies it)
  chk : ∀ (n : ℕ) (fs : FlatState) (p : ℕ) → suc p ≡ φ t (fpc fs)
      → ∀ (k : ℕ) → fetch P′ p ≡ just (instr-room k)
      → ∀ (m : ℕ) → flat-events m P′ (lift fs (φ t (fpc fs))) ≡ flat-events (suc n) t fs
      → flat-ctrls m P′ (lift fs (φ t (fpc fs))) ≡ flat-ctrls (suc n) t fs
      → (h : Bool) → LocState.halted (floc fs) ≡ h
      → (flat-events-step h m P′ (lift fs p) ≡ flat-events-step h n t fs)
      × (flat-ctrls-step h m P′ (lift fs p) ≡ flat-ctrls-step h n t fs)
  chk n fs p sp k fk m ee ec true  _  = refl , refl
  chk n fs p sp k fk m ee ec false eh =
      trans (cong (λ z → flat-events-fetch z m P′ (lift fs p)) fk)
            (trans (cong (λ q → flat-events m P′ (lift fs q)) sp)
                   (trans ee (cong (λ h → flat-events-step h n t fs) eh)))
    , trans (cong (λ z → flat-ctrls-fetch z m P′ (lift fs p)) fk)
            (trans (cong (λ q → flat-ctrls m P′ (lift fs q)) sp)
                   (trans ec (cong (λ h → flat-ctrls-step h n t fs) eh)))
  ev-img zero    fs = 0 , refl , refl
  ev-img (suc n) fs with ev-step n fs (LocState.halted (floc fs)) refl
  ... | m , ee , ec = suc m , ee , ec

  ev-rel n fs p (inj₁ refl) = ev-img n fs
  ev-rel zero    fs p (inj₂ _) = 0 , refl , refl
  ev-rel (suc n) fs p (inj₂ (sp , k , fk)) with ev-img (suc n) fs
  ... | m , ee , ec with chk n fs p sp k fk m ee ec (LocState.halted (floc fs)) refl
  ...   | ee′ , ec′ = suc m , ee′ , ec′


  -- THE BOOT'S FUEL: from a check state (the lowered start is one), the fuel
  -- that matches the original's `suc n` is of the form `suc (suc N)` — the check
  -- step, then the original's first step. (`ev-rel` hides that shape in a Σ.)
  ev-boot : ∀ (n : ℕ) (fs : FlatState) (p : ℕ) → suc p ≡ φ t (fpc fs)
          → ∀ (k : ℕ) → fetch P′ p ≡ just (instr-room k)
          → Σ ℕ (λ N → Same (suc (suc N)) (lift fs p) (suc n) fs)
  ev-boot n fs p sp k fk with ev-step n fs (LocState.halted (floc fs)) refl
  ... | m , ee , ec with chk n fs p sp k fk (suc m) ee ec (LocState.halted (floc fs)) refl
  ...   | ee′ , ec′ = m , ee′ , ec′
