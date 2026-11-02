-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.RunLow — the run of the LOWERED image.
--
-- Plan 0.123 A.4 step 5 (D371). The backends lower `room-checks t`, the image
-- with the room checks, not `t`. `RunAt` (`RunContext`) and every fact in
-- `RunWF` stay what they were: facts about the run of `t`. A state of the
-- lowered image's run is the LIFT of a state of `t`'s run (`RoomChecksSim`):
-- the same memory, frames and closure register, its pc / return stack / link
-- register moved by the index map. `RunLow` says exactly that, and this module
-- carries each fact the engine needs across the lift:
--
--   * at a check, the fact is vacuous — `instr-room` reads no slot, calls
--     nothing, allocates nothing, jumps nowhere;
--   * anywhere else the lowered image holds `t`'s instruction (`fetch-room`),
--     and the fact is `RunWF`'s, at the state the lift is of.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Name using (CanonicalName)

module Once.Adequacy.ArchCorrectness.FlatCore.RunLow (o : CanonicalName)
  (FS : FrameSemantics)
  (slot-size : ℕ)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.CCC.Codegen.RoomChecksFacts using (φ; module RoomFacts)
open RoomFacts {FS} using (fetch-room)
open import Once.CCC.Codegen.RoomChecksSim using (module RoomSim)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (Sound)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq

-- THE RUN OF THE LOWERED IMAGE: `prog` is `t` with its checks, and `fs` is the
-- lift of a state `t`'s run reaches, at a pc that stands for that state's.
record RunLow (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkRunLow
  field
    run-src  : AbstractTrace
    run-at   : FlatState
    run-p    : ℕ
    run-prog : prog ≡ room-checks run-src
    run-img  : RunAt run-src run-at
    run-lift : fs ≡ RoomSim.lift {FS} run-src run-at run-p
    run-pc   : RoomSim.PcRel {FS} run-src (fpc run-at) run-p
open RunLow public

-- WHAT A LOWERED STATE FETCHES: a check, or `t`'s own instruction at the state
-- the lift is of (and then the lift is AT that state's image).
data LowView (src : AbstractTrace) (fs₀ : FlatState) (p : ℕ) (i : AbstractInstr) : Set where
  at-check : ∀ (k : ℕ) → i ≡ instr-room k → suc p ≡ φ src (fpc fs₀) → LowView src fs₀ p i
  at-image : p ≡ φ src (fpc fs₀) → fetch src (fpc fs₀) ≡ just i → LowView src fs₀ p i

low-view : ∀ (src : AbstractTrace) (fs₀ : FlatState) (p : ℕ) {i : AbstractInstr}
         → RoomSim.PcRel {FS} src (fpc fs₀) p
         → fetch (room-checks src) p ≡ just i → LowView src fs₀ p i
low-view src fs₀ p (inj₂ (sp , k , fk)) f = at-check k (just-injective (trans (sym f) fk)) sp
low-view src fs₀ p (inj₁ refl)          f = at-image refl (trans (sym (fetch-room src (fpc fs₀))) f)

-- a check is no instruction a site fact is about
room≢ : ∀ {k : ℕ} {i : AbstractInstr} → i ≡ instr-room k → (∀ {k′} → i ≡ instr-room k′ → ⊥) → ⊥
room≢ e ne = ne e

open import Once.CCC.Codegen.RoomChecksFacts using (ψ)
open RoomFacts {FS} using (ψ-zero)

------------------------------------------------------------------------
-- THE RUN GOES ON: a step of the lowered image keeps it a lift of `t`'s run.
-- A check only moves the lifted pc on to the state's image; any other step is
-- `t`'s own (`step-lift`), and `t`'s run takes it too (`reach-step`).
------------------------------------------------------------------------
low-step : ∀ (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr) → RunLow prog fs
         → fetch prog (fpc fs) ≡ just i → LocState.halted (floc fs) ≡ false
         → RunLow prog (flat-exec-instr i prog fs)
low-step .(room-checks src) .(RoomSim.lift {FS} src fs₀ p) i (mkRunLow src fs₀ p refl r refl pc) f h
  with low-view src fs₀ p pc f
... | at-check k refl sp = mkRunLow src fs₀ (suc p) refl r refl (inj₁ sp)
... | at-image refl fi with RoomSim.step-lift {FS} src fs₀ i
...   | p′ , e , pr′ =
  mkRunLow src (flat-exec-instr i src fs₀) p′ refl
    (mkRunAt (run-tbl r) (run-ir r) (run-emit r) (run-linked r) (reach-step i fs₀ (run-reach r) fi h))
    e pr′

-- …and NEVER FAULTS (D367 carried across the pass, `sound-room`).
low-sound : ∀ {prog fs} → RunLow prog fs → Sound prog fs
low-sound (mkRunLow src fs₀ p refl r refl pc) = RoomSim.sound-room {FS} src fs₀ p pc (run-sound r)

-- THE START: the lift of `t`'s start state at pc 0 — the start's check.
low-start : ∀ (src : AbstractTrace) (fs₀ : FlatState) → RunAt src fs₀ → fpc fs₀ ≡ 0
          → RunLow (room-checks src) (RoomSim.lift {FS} src fs₀ 0)
low-start src fs₀ r p0 =
  mkRunLow src fs₀ 0 refl r refl
    (inj₂ (subst (λ c → suc 0 ≡ φ src c) (sym p0) (cong suc (sym (ψ-zero src))) , _ , refl))
