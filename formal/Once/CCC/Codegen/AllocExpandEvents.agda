-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandEvents — the expanded run shows what the primitive
-- one shows (D468, 3c3b).
--
-- From related states, at every fuel `n` of the primitive program there is a
-- fuel `m` of its expansion at which the two `flat-events` are EQUAL and the
-- expansion counts at least the primitive's control steps (what `FlatShows`
-- reads: `k ≤ flat-ctrls`). By fuel: a halted state ends both runs alike (the
-- flags and `left` related), a pc off the program is off the expansion
-- (`fetch-none`), and a step is the expansion's steps (`dispatch`), whose events
-- are the step's own: both logs grow by them from related logs (`chain-log`,
-- `step-log`), so the chain's are the step's.
--
-- `Good` is what the primitive run keeps (the apex's reached states): the
-- fetched instruction emittable, the step not faulting, the store well formed.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandEvents {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Properties
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState; fetch; flat-exec-instr)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {FS} using (flat-events; flat-events-step; flat-events-fetch; event-of; flat-events-steps; chain-events
                               ; step-log; chain-log; flat-ctrls; flat-ctrls-step; flat-ctrls-fetch; ctrl-of; chain-ctrls; flat-ctrls-steps)
open import Once.IR.Semantics.Out using (Out; _▹_; ended; end-of-left)
open import Once.CCC.Machine.FrameFree using (EmittableI)
open import Once.CCC.Label using (LabelId; module LabelId)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandRel {FS} using (Rel; module Rel)
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off; fetch-none)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L)
import Once.CCC.Codegen.AllocExpandDispatch
import Once.CCC.Machine.FlatStoreWF

------------------------------------------------------------------------
-- A fuelled run's first step, unfolded
------------------------------------------------------------------------

ev-unfold : ∀ n prog (fs : FlatState) {i} → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just i
          → flat-events (suc n) prog fs ≡ event-of i fs ▹ flat-events n prog (flat-exec-instr i prog fs)
ev-unfold n prog fs h f = trans (cong (λ b → flat-events-step b n prog fs) h) (cong (λ mi → flat-events-fetch mi n prog fs) f)

ct-unfold : ∀ n prog (fs : FlatState) {i} → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just i
          → flat-ctrls (suc n) prog fs ≡ ctrl-of i + flat-ctrls n prog (flat-exec-instr i prog fs)
ct-unfold n prog fs h f = trans (cong (λ b → flat-ctrls-step b n prog fs) h) (cong (λ mi → flat-ctrls-fetch mi n prog fs) f)

ev-none : ∀ n prog (fs : FlatState) → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ nothing
        → flat-events (suc n) prog fs ≡ flat-events-fetch nothing n prog fs
ev-none n prog fs h f = trans (cong (λ b → flat-events-step b n prog fs) h) (cong (λ mi → flat-events-fetch mi n prog fs) f)

ct-none : ∀ n prog (fs : FlatState) → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ nothing
        → flat-ctrls (suc n) prog fs ≡ 0
ct-none n prog fs h f = trans (cong (λ b → flat-ctrls-step b n prog fs) h) (cong (λ mi → flat-ctrls-fetch mi n prog fs) f)

ev-halt : ∀ n prog (fs : FlatState) → LocState.halted (floc fs) ≡ true
        → flat-events (suc n) prog fs ≡ flat-events-step true n prog fs
ev-halt n prog fs h = cong (λ b → flat-events-step b n prog fs) h

ct-halt : ∀ n prog (fs : FlatState) → LocState.halted (floc fs) ≡ true → flat-ctrls (suc n) prog fs ≡ 0
ct-halt n prog fs h = cong (λ b → flat-ctrls-step b n prog fs) h

------------------------------------------------------------------------
-- ★ The two runs show the same
------------------------------------------------------------------------

module _ (C : Classes) (P : AbstractTrace) (Sz : ℕ → Set)
         (uniform  : ∀ k k′ → Sz k → Sz k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′)
         (fits     : ∀ k → k ≤ bsz C k)
         (in-range : ∀ k → cls C k < count C)
         (sz-alloc : ∀ n k → fetch P n ≡ just (instr-alloc-heap k) → Sz k)
         (sz-free  : ∀ n k → fetch P n ≡ just (instr-free-heap k) → Sz k)
         (img      : ∀ n m → fetch P n ≡ just (instr-ctrl (c-label m)) → LabelId.path m ≡ [])
         (jmp-lbl  : ∀ n m → fetch P n ≡ just (instr-ctrl (c-jmp m)) → LabelId.path m ≡ [])
         (br-lbl   : ∀ n m → fetch P n ≡ just (instr-ctrl (c-branch-tag-zero m)) → LabelId.path m ≡ [])
         where
  open Rel
  module D = Once.CCC.Codegen.AllocExpandDispatch {FS}
  module WF = Once.CCC.Machine.FlatStoreWF FS
  E = expand C P

  -- what the primitive run keeps
  record Keeps (Good : FlatState → Set) : Set where
    field
      g-step : ∀ {fs i} → Good fs → LocState.halted (floc fs) ≡ false → fetch P (fpc fs) ≡ just i → Good (flat-exec-instr i P fs)
      g-em   : ∀ {fs i} → Good fs → fetch P (fpc fs) ≡ just i → EmittableI i
      g-nf   : ∀ {fs i} → Good fs → LocState.halted (floc fs) ≡ false → fetch P (fpc fs) ≡ just i
             → LocState.faulted (floc (flat-exec-instr i P fs)) ≡ false
      g-wf   : ∀ {fs} → Good fs → WF.StoreWF (AllocState.next-heap-ref (falloc fs)) (floc fs)
      g-cw   : ∀ {fs} → Good fs → WF.sv-below (AllocState.next-heap-ref (falloc fs)) (fclosure fs)

  Same : ℕ → FlatState → ℕ → FlatState → Set
  Same m gs n fs = (flat-events m E gs ≡ flat-events n P fs) × (flat-ctrls n P fs ≤ flat-ctrls m E gs)

  module Run {Good : FlatState → Set} (K : Keeps Good) where
    open Keeps K

    -- the chain's events are the step's: both logs grow by them from related logs
    events-of : ∀ {fs gs gs′ i N} (R : Rel C P Sz fs gs) (c : FlatSteps E N gs gs′) → Rel C P Sz (flat-exec-instr i P fs) gs′
              → chain-events c ≡ event-of i fs
    events-of {fs} {gs} {gs′} {i} R c R′ =
      Data.List.Properties.++-cancelˡ (LocState.ev-log (floc gs)) (chain-events c) (event-of i fs)
        (trans (sym (chain-log c))
          (trans (L.LRel.l-log (r-loc R′))
            (trans (step-log i P fs) (cong (_++ event-of i fs) (sym (L.LRel.l-log (r-loc R)))))))

    ev : ∀ n {fs gs} → Good fs → Rel C P Sz fs gs → Σ ℕ λ m → Same m gs n fs
    ev zero    G R = 0 , refl , z≤n
    ev (suc n) {fs} {gs} G R = by-h (LocState.halted (floc fs)) refl
      where
        hg : ∀ {b} → LocState.halted (floc fs) ≡ b → LocState.halted (floc gs) ≡ b
        hg e = trans (L.LRel.l-halt (r-loc R)) e

        by-f : ∀ mi → fetch P (fpc fs) ≡ mi → LocState.halted (floc fs) ≡ false → Σ ℕ λ m → Same m gs (suc n) fs
        by-f nothing ef h =
          1 , trans (ev-none 0 E gs (hg h) (trans (cong (fetch E) (r-pc R)) (fetch-none C 0 P (fpc fs) ef))) (sym (ev-none n P fs h ef))
            , subst (_≤ flat-ctrls 1 E gs) (sym (ct-none n P fs h ef)) z≤n
        by-f (just i) ef h = go (D.dispatch C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl R i ef (g-em G ef) h (g-nf G h ef) (g-wf G) (g-cw G))
          where
            go : D.Step C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl i fs gs → Σ ℕ λ m → Same m gs (suc n) fs
            go (N , gs′ , c , cb , R′) = go′ (ev n (g-step G h ef) R′)
              where
                go′ : Σ ℕ (λ m → Same m gs′ n (flat-exec-instr i P fs)) → Σ ℕ λ m → Same m gs (suc n) fs
                go′ (m′ , ee , ec) =
                  suc N + m′
                  , trans (flat-events-steps c m′) (trans (cong₂ _▹_ (events-of {i = i} R c R′) ee) (sym (ev-unfold n P fs h ef)))
                  , subst (_≤ flat-ctrls (suc N + m′) E gs) (sym (ct-unfold n P fs h ef))
                      (subst (ctrl-of i + flat-ctrls n P (flat-exec-instr i P fs) ≤_) (sym (flat-ctrls-steps c m′))
                        (Data.Nat.Properties.+-mono-≤ cb ec))

        by-h : ∀ b → LocState.halted (floc fs) ≡ b → Σ ℕ λ m → Same m gs (suc n) fs
        by-h true  e =
          1 , trans (ev-halt 0 E gs (hg e)) (trans (cong (λ l → ended (end-of-left l)) (L.LRel.l-left (r-loc R))) (sym (ev-halt n P fs e)))
            , subst (_≤ flat-ctrls 1 E gs) (sym (ct-halt n P fs e)) z≤n
        by-h false e = by-f (fetch P (fpc fs)) refl e
